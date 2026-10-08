-- Prove2me | solution 1 for ReedGGN.Regulator.example_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:53:33.03211+00:00
-- url     : https://prove2.me/submissions/f20abea6-ea36-4cec-82f1-e046466542be

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation
import Definitions.Def_ReedGGN_Regulator_FluidInput

open ReedGGN.Regulator MeasureTheory Filter Topology
set_option maxHeartbeats 0

private theorem tail_dirac (t : ℝ) :
    tail (Measure.dirac 1) t = if t < 1 then 1 else 0 := by
  by_cases h : t < 1 <;> simp [tail, Measure.dirac_apply', Set.indicator_apply, Set.mem_Ioi, h]

private theorem input_dirac (t : ℝ) (ht : 0 ≤ t) :
    fluidInput 1 (tail (Measure.dirac 1)) (Measure.dirac 1) t =
      if t < 1 then 1 + t else 1 := by
  classical
  simp only [fluidInput, min_self, sub_self, max_self, zero_mul, one_mul, add_zero,
    tail_dirac]
  by_cases h : t < 1
  · simp only [if_pos h]
    have hi : (∫ s in Set.Icc 0 t, if t - s < 1 then (1 : ℝ) else 0) = t := by
      calc
        _ = ∫ s in Set.Icc 0 t, (1 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro s hs
          exact if_pos (by linarith [hs.1])
        _ = t := by simp [ht, Real.volume_Icc]
    rw [hi]
  · simp only [if_neg h, zero_add]
    have hf : (fun s : ℝ => if t - s < 1 then (1 : ℝ) else 0) =
        (Set.Ioi (t - 1)).indicator (fun _ => (1 : ℝ)) := by
      funext s
      simp only [Set.indicator_apply, Set.mem_Ioi]
      congr 1
      exact propext (by constructor <;> intro hs <;> linarith)
    rw [hf, setIntegral_indicator measurableSet_Ioi]
    have hs : Set.Icc 0 t ∩ Set.Ioi (t - 1) = Set.Ioc (t - 1) t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · tauto
      · intro hs; exact ⟨⟨by linarith, hs.2⟩, hs.1⟩
    rw [hs]
    simp [Real.volume_Ioc]

private theorem recurrence (Q : ℝ → ℝ) :
    SolvesRegulator (Measure.dirac 1) (-1)
      (fluidInput 1 (tail (Measure.dirac 1)) (Measure.dirac 1)) Q ↔
    ∀ t, 0 ≤ t → Q t = if t < 1 then 1 + t else 1 + max (Q (t - 1) - 1) 0 := by
  classical
  simp only [SolvesRegulator, input_dirac]
  constructor <;> intro h t ht
  · have he := h t ht
    rw [input_dirac t ht, setIntegral_dirac] at he
    by_cases hlt : t < 1
    · simpa [hlt, not_le.mpr hlt, Set.mem_Icc] using he
    · simpa [hlt, le_of_not_gt hlt, Set.mem_Icc, sub_eq_add_neg] using he
  · have he := h t ht
    rw [input_dirac t ht, setIntegral_dirac]
    by_cases hlt : t < 1
    · simpa [hlt, not_le.mpr hlt, Set.mem_Icc] using he
    · simpa [hlt, le_of_not_gt hlt, Set.mem_Icc, sub_eq_add_neg] using he

private theorem saw_cadlag : IsCadlag (fun t : ℝ => 1 + t - (⌊t⌋ : ℝ)) := by
  constructor
  · intro t ht
    have hf : Filter.Tendsto (fun x : ℝ => (⌊x⌋ : ℝ)) (nhdsWithin t (Set.Ici t))
        (nhds (⌊t⌋ : ℝ)) :=
      (tendsto_pure_nhds (fun n : ℤ => (n : ℝ)) _).comp (tendsto_floor_right_pure_floor t)
    exact (continuousWithinAt_const.add continuousWithinAt_id).sub hf
  · intro t ht
    refine ⟨1 + t - ((⌈t⌉ - 1 : ℤ) : ℝ), ?_⟩
    have hf : Filter.Tendsto (fun x : ℝ => (⌊x⌋ : ℝ)) (nhdsWithin t (Set.Iio t))
        (nhds (((⌈t⌉ - 1 : ℤ) : ℝ))) :=
      (tendsto_pure_nhds (fun n : ℤ => (n : ℝ)) _).comp (tendsto_floor_left_pure_ceil_sub_one t)
    exact ((tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)).sub hf)

theorem solution :
    IsCadlag (fun t : ℝ => 1 + t - (⌊t⌋ : ℝ)) ∧
    SolvesRegulator (Measure.dirac 1) (-1)
      (fluidInput 1 (tail (Measure.dirac 1)) (Measure.dirac 1))
      (fun t : ℝ => 1 + t - (⌊t⌋ : ℝ)) ∧
    (∀ Q : ℝ → ℝ, IsCadlag Q →
      SolvesRegulator (Measure.dirac 1) (-1)
        (fluidInput 1 (tail (Measure.dirac 1)) (Measure.dirac 1)) Q →
      Set.EqOn Q (fun t : ℝ => 1 + t - (⌊t⌋ : ℝ)) (Set.Ici 0)) := by
  refine ⟨saw_cadlag, ?_, ?_⟩
  · rw [recurrence]
    intro t ht
    by_cases h : t < 1
    · rw [if_pos h, Int.floor_eq_zero_iff.mpr ⟨ht, h⟩]
      norm_num
    · rw [if_neg h, Int.floor_sub_one]
      have hf := Int.floor_le t
      have hg := Int.lt_floor_add_one t
      push_cast
      rw [max_eq_left (by linarith)]
      ring
  · intro Q hQ hsol
    have h := recurrence Q |>.mp hsol
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have hall : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → t < n →
        Q t = 1 + t - (⌊t⌋ : ℝ) := by
      intro n
      induction n with
      | zero => intro t ht hn; norm_num at hn; linarith
      | succ n ih =>
        intro t ht hn
        by_cases hlt : t < 1
        · rw [h t ht, if_pos hlt, Int.floor_eq_zero_iff.mpr ⟨ht, hlt⟩]
          norm_num
        · rw [h t ht, if_neg hlt, ih (t - 1) (by linarith) (by push_cast at hn ⊢; linarith)]
          have hf := Int.floor_le (t - 1)
          rw [max_eq_left (by linarith), Int.floor_sub_one]
          push_cast
          ring
    exact hall n t ht hn


#print axioms solution
