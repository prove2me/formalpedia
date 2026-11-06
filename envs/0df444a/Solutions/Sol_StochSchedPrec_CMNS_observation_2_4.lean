-- Prove2me | solution 1 for StochSchedPrec.CMNS.observation_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:51:05.00717+00:00
-- url     : https://prove2.me/submissions/ae6a0878-c62f-426d-a3b5-38a818b1f2be

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (L : Fin (Fintype.card V) ≃ V) (β : ℝ) (hβ : 0 ≤ β) (μ : V → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (p : V → ℝ) (hp : ∀ j, 0 ≤ p j) (S : V → ℝ) (hS : IsCMNSRun m A r L β μ p S) :
    (∀ (j : V) (t : ℝ), charge m A r L p S j t ≤ β * μ j) ∧
    (∀ (j : V) (t : ℝ), availTime A r p S j ≤ t → t < S j →
      ∀ k, IsDelayed A r L p S k t → k ∈ before L j) ∧
    (∀ t : ℝ, busy p S t < m → (∃ i, t < S i ∧ avail A r p S i t) →
      ∃ k, IsDelayed A r L p S k t) := by
  classical
  obtain ⟨hfeas, _, hidle, hthr⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · -- (i): the charge never exceeds the threshold
    intro k t
    -- measurability in time
    have hlt : ∀ c : ℝ, Measurable fun t : ℝ => t < c := fun c =>
      measurableSet_setOfPred.1 measurableSet_Iio
    have hle : ∀ c : ℝ, Measurable fun t : ℝ => c ≤ t := fun c =>
      measurableSet_setOfPred.1 measurableSet_Ici
    have hav : ∀ i, Measurable fun t => avail A r p S i t := fun i =>
      (hle (r i)).and (Measurable.forall fun i' => Measurable.imp measurable_const (hle _))
    have hfirst : ∀ (q : V → ℝ → Prop), (∀ i, Measurable (q i)) → ∀ k,
        Measurable fun t => IsFirstWith L (fun i => q i t) k := by
      intro q hq k
      exact (hq k).and (Measurable.forall fun i => Measurable.imp (hq i) measurable_const)
    have hD : Measurable fun t => IsDelayed A r L p S k t := by
      refine Measurable.and (Measurable.exists fun i => ?_) ?_
      · exact (hfirst (fun i t => t < S i) (fun i => hlt _) i).and (hav i).not
      · exact hfirst (fun i t => t < S i ∧ avail A r p S i t) (fun i => (hlt _).and (hav i)) k
    have hbusy_eq : ∀ t, (busy p S t : ℝ) = ∑ j, if S j ≤ t ∧ t < S j + p j then (1 : ℝ) else 0 := by
      intro t
      unfold busy
      rw [Finset.sum_boole]
    have hbm : Measurable fun t => (busy p S t : ℝ) := by
      simp only [hbusy_eq]
      refine Finset.measurable_fun_sum _ (fun j _ => Measurable.ite ?_ measurable_const
        measurable_const)
      exact ((hle (S j)).and (hlt _)).setOf
    set f : ℝ → ℝ := fun s => if IsDelayed A r L p S k s then ((m : ℝ) - (busy p S s : ℝ)) else 0
      with hf
    have hfm : Measurable f := Measurable.ite hD.setOf (measurable_const.sub hbm) measurable_const
    have hbusy_le : ∀ s, (busy p S s : ℝ) ≤ m := fun s => by exact_mod_cast hfeas.2.2 s
    have hbusy_card : ∀ s, (busy p S s : ℝ) ≤ Fintype.card V := fun s => by
      unfold busy
      exact_mod_cast Finset.card_filter_le _ _
    have hf0 : ∀ s, 0 ≤ f s := by
      intro s
      simp only [hf]
      split_ifs
      · linarith [hbusy_le s]
      · exact le_rfl
    have hfb : ∀ s, ‖f s‖ ≤ m := by
      intro s
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 s)]
      simp only [hf]
      split_ifs
      · have : (0 : ℝ) ≤ busy p S s := Nat.cast_nonneg _
        linarith
      · exact_mod_cast Nat.zero_le m
    have hII : ∀ a b, IntervalIntegrable f volume a b := by
      intro a b
      refine (intervalIntegrable_const (c := (m : ℝ))).mono_fun' hfm.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall hfb
    set F : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..s, f x with hFdef
    have hFeq : ∀ s, charge m A r L p S k s = F s := fun s => rfl
    have hFc : Continuous F := intervalIntegral.continuous_primitive hII 0
    have hpos : ∀ s, 0 < f s → F s < β * μ k := by
      intro s hs
      simp only [hf] at hs
      split_ifs at hs with hd
      · have hb : busy p S s < m := by
          have : (busy p S s : ℝ) < m := by linarith
          exact_mod_cast this
        rw [← hFeq]
        exact hthr s k hb hd
      · exact absurd hs (lt_irrefl 0)
    have hc0 : 0 ≤ β * μ k := mul_nonneg hβ (hμ k)
    rw [hFeq]
    rcases le_or_gt t 0 with ht | ht
    · have : F t = -∫ x in t..0, f x := by
        simp only [hFdef]; rw [intervalIntegral.integral_symm]
      rw [this]
      have : 0 ≤ ∫ x in t..0, f x := intervalIntegral.integral_nonneg ht (fun x _ => hf0 x)
      linarith
    by_contra hcon
    push Not at hcon
    set K := {x ∈ Set.Icc (0 : ℝ) t | F x ≤ β * μ k} with hK
    have hKc : IsClosed K := isClosed_Icc.inter (isClosed_le hFc continuous_const)
    have h0K : (0 : ℝ) ∈ K := by
      refine ⟨⟨le_rfl, ht.le⟩, ?_⟩
      simp [hFdef, hc0]
    have hKb : BddAbove K := ⟨t, fun x hx => hx.1.2⟩
    set t0 := sSup K with ht0
    have ht0K : t0 ∈ K := hKc.csSup_mem ⟨0, h0K⟩ hKb
    have ht0t : t0 < t := by
      rcases lt_or_eq_of_le ht0K.1.2 with h | h
      · exact h
      · exfalso; have := ht0K.2; rw [h] at this; linarith
    have hzero : ∀ x ∈ Set.Ioc t0 t, f x = 0 := by
      intro x hx
      have hFx : β * μ k < F x := by
        by_contra hle'
        push Not at hle'
        have hxK : x ∈ K := ⟨⟨by linarith [ht0K.1.1, hx.1], hx.2⟩, hle'⟩
        have := le_csSup hKb hxK
        linarith [hx.1]
      rcases lt_or_eq_of_le (hf0 x) with h | h
      · have := hpos x h; linarith
      · exact h.symm
    have hint0 : ∫ x in t0..t, f x = 0 := by
      rw [intervalIntegral.integral_of_le ht0t.le]
      rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => hzero x hx)]
      simp
    have hsplit : F t - F t0 = ∫ x in t0..t, f x := by
      simp only [hFdef]
      exact intervalIntegral.integral_interval_sub_left (hII 0 t) (hII 0 t0)
    have := ht0K.2
    linarith
  · -- (ii)
    intro j t hav ht k hk
    have hjav : avail A r p S j t := by
      unfold availTime at hav
      rw [Finset.fold_max_le] at hav
      refine ⟨hav.1, fun i hi => hav.2 i ?_⟩
      simp [hi]
    have := hk.2.2 j ⟨ht, hjav⟩
    simp [before, this]
  · -- (iii)
    intro t hb ⟨i, hi⟩
    obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun i => t < S i ∧ avail A r p S i t) (fun i => L.symm i)
      ⟨i, by simp [hi]⟩
    obtain ⟨i0, hi0, hi0min⟩ := Finset.exists_min_image
      (Finset.univ.filter fun i => t < S i) (fun i => L.symm i) ⟨i, by simp [hi.1]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hi0
    have hfirst0 : IsFirstWith L (fun i => t < S i) i0 :=
      ⟨hi0, fun i' hi' => hi0min i' (by simp [hi'])⟩
    refine ⟨k, ⟨i0, hfirst0, hidle t hb i0 hfirst0⟩, hk, fun i' hi' => hkmin i' (by simp [hi'])⟩
