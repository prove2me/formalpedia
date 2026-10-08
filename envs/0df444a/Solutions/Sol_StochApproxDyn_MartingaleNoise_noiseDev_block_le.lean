-- Prove2me | solution 1 for StochApproxDyn.MartingaleNoise.noiseDev_block_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:19:55.334308+00:00
-- url     : https://prove2.me/submissions/695c5e8c-f1fb-4c10-b577-5747ffc4b471

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace NoiseDevBlockBbe

open StochApproxDyn.MartingaleNoise

lemma stepIndex_bdd (γ : ℕ → ℝ) (hγ : IsStepSequence γ) (t : ℝ) :
    BddAbove {k : ℕ | StochApproxDyn.Interpolation.tau γ k ≤ t} := by
  obtain ⟨N, hN⟩ := (hγ.2.1.eventually (eventually_gt_atTop t)).exists_forall_of_atTop
  refine ⟨N, fun k hk => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have h1 := hN k hlt.le
  have h2 : StochApproxDyn.Interpolation.tau γ k ≤ t := hk
  simp only [StochApproxDyn.Interpolation.tau] at h2
  linarith

lemma stepIndex_mono (γ : ℕ → ℝ) (hγ : IsStepSequence γ) : Monotone (stepIndex γ) := by
  intro s t hst
  unfold stepIndex
  rcases Set.eq_empty_or_nonempty {k : ℕ | StochApproxDyn.Interpolation.tau γ k ≤ s} with h | h
  · rw [h, csSup_empty]; exact bot_le
  · exact csSup_le_csSup (stepIndex_bdd γ hγ t) h (fun k hk => le_trans hk hst)

lemma noisePath_intervalIntegrable {d : ℕ} (γ : ℕ → ℝ) (hγ : IsStepSequence γ)
    (U : ℕ → EuclideanSpace ℝ (Fin d)) (a b : ℝ) :
    IntervalIntegrable (noisePath γ U) volume a b := by
  have hmono := stepIndex_mono γ hγ
  have hmeas : Measurable (noisePath γ U) := by
    have h1 : Measurable (stepIndex γ) := hmono.measurable
    have h2 : Measurable (fun n : ℕ => U (n + 1)) := measurable_from_nat
    exact h2.comp h1
  rw [intervalIntegrable_iff]
  set N := stepIndex γ (max a b)
  refine Measure.integrableOn_of_bounded (M := ∑ k ∈ Finset.range (N + 1), ‖U (k + 1)‖)
    (by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) ?_)
      rw [Real.volume_interval]; exact ENNReal.ofReal_lt_top)
    hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  have hx' : x ≤ max a b := (Set.uIoc_subset_uIcc hx).2
  have hk : stepIndex γ x ≤ N := hmono hx'
  unfold noisePath
  exact Finset.single_le_sum (f := fun k => ‖U (k + 1)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

lemma int_le_noiseDev {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) (a T c : ℝ)
    (h1 : a ≤ c) (h2 : c ≤ a + T) :
    ‖∫ s in a..c, noisePath γ U s‖ₑ ≤ noiseDev γ U a T := by
  unfold noiseDev
  have hmem : c - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have := le_iSup₂ (f := fun h (_ : h ∈ Set.Icc (0 : ℝ) T) =>
    ‖∫ s in a..(a + h), noisePath γ U s‖ₑ) (c - a) hmem
  simpa using this

end NoiseDevBlockBbe

open StochApproxDyn.MartingaleNoise in
theorem solution {d : ℕ} (γ : ℕ → ℝ) (hγ : IsStepSequence γ)
    (U : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℝ) (hT : 0 < T) (k : ℕ) (t : ℝ)
    (hkt : (k : ℝ) * T ≤ t) (htk : t < ((k : ℝ) + 1) * T) :
    noiseDev γ U t T ≤ 2 * noiseDev γ U ((k : ℝ) * T) T + noiseDev γ U (((k : ℝ) + 1) * T) T := by
  set A := StochApproxDyn.MartingaleNoise.noiseDev γ U ((k : ℝ) * T) T
  set B := StochApproxDyn.MartingaleNoise.noiseDev γ U (((k : ℝ) + 1) * T) T
  set f := StochApproxDyn.MartingaleNoise.noisePath γ U
  have hI : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    NoiseDevBlockBbe.noisePath_intervalIntegrable γ hγ U
  have hk1 : ((k : ℝ) + 1) * T = (k : ℝ) * T + T := by ring
  unfold StochApproxDyn.MartingaleNoise.noiseDev
  refine iSup₂_le (fun h hh => ?_)
  obtain ⟨h0, hTle⟩ := hh
  have hA : ∀ c, (k : ℝ) * T ≤ c → c ≤ (k : ℝ) * T + T → ‖∫ s in (k : ℝ) * T..c, f s‖ₑ ≤ A :=
    fun c h1 h2 => NoiseDevBlockBbe.int_le_noiseDev γ U _ T c h1 h2
  have hsplit : (∫ s in t..(t + h), f s) =
      (∫ s in (k : ℝ) * T..(t + h), f s) - ∫ s in (k : ℝ) * T..t, f s :=
    (intervalIntegral.integral_interval_sub_left (hI _ _) (hI _ _)).symm
  have htA : ‖∫ s in (k : ℝ) * T..t, f s‖ₑ ≤ A := hA t hkt (by linarith)
  by_cases hc : t + h ≤ ((k : ℝ) + 1) * T
  · rw [hsplit]
    calc ‖(∫ s in (k : ℝ) * T..(t + h), f s) - ∫ s in (k : ℝ) * T..t, f s‖ₑ
        ≤ ‖∫ s in (k : ℝ) * T..(t + h), f s‖ₑ + ‖∫ s in (k : ℝ) * T..t, f s‖ₑ := enorm_sub_le
      _ ≤ A + A := add_le_add (hA _ (by linarith) (by linarith)) htA
      _ = 2 * A := (two_mul A).symm
      _ ≤ 2 * A + B := le_self_add
  · rw [not_le] at hc
    have hsplit2 : (∫ s in (k : ℝ) * T..(t + h), f s) =
        (∫ s in (k : ℝ) * T..((k : ℝ) + 1) * T, f s) + ∫ s in ((k : ℝ) + 1) * T..(t + h), f s :=
      (intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _)).symm
    have hB : ‖∫ s in ((k : ℝ) + 1) * T..(t + h), f s‖ₑ ≤ B :=
      NoiseDevBlockBbe.int_le_noiseDev γ U _ T _ hc.le (by linarith)
    have hA2 : ‖∫ s in (k : ℝ) * T..((k : ℝ) + 1) * T, f s‖ₑ ≤ A :=
      hA _ (by linarith) (by linarith)
    rw [hsplit, hsplit2]
    calc ‖(∫ s in (k : ℝ) * T..((k : ℝ) + 1) * T, f s) + (∫ s in ((k : ℝ) + 1) * T..(t + h), f s)
            - ∫ s in (k : ℝ) * T..t, f s‖ₑ
        ≤ ‖(∫ s in (k : ℝ) * T..((k : ℝ) + 1) * T, f s) + (∫ s in ((k : ℝ) + 1) * T..(t + h), f s)‖ₑ
            + ‖∫ s in (k : ℝ) * T..t, f s‖ₑ := enorm_sub_le
      _ ≤ (‖∫ s in (k : ℝ) * T..((k : ℝ) + 1) * T, f s‖ₑ
            + ‖∫ s in ((k : ℝ) + 1) * T..(t + h), f s‖ₑ) + ‖∫ s in (k : ℝ) * T..t, f s‖ₑ :=
          add_le_add (enorm_add_le _ _) le_rfl
      _ ≤ (A + B) + A := add_le_add (add_le_add hA2 hB) htA
      _ = 2 * A + B := by rw [two_mul]; ring
