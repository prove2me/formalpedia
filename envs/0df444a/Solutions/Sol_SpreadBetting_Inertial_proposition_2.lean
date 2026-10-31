-- Prove2me | solution 1 for SpreadBetting.Inertial.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:33:05.083506+00:00
-- url     : https://prove2.me/submissions/4f7ffaa4-a364-4615-81ad-a7aa55fc6134

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace SBFAux
open SpreadBetting.Inertial

lemma feps_cont {M : Market} (hM : M.Standing) : Continuous M.feps :=
  hM.feps_contDiff.continuous

lemma Feps_sub {M : Market} (hM : M.Standing) (a b : ℝ) :
    Feps M b - Feps M a = ∫ t in a..b, M.feps t := by
  unfold Feps
  exact intervalIntegral.integral_Iic_sub_Iic hM.feps_integrable.integrableOn
    hM.feps_integrable.integrableOn

lemma Feps_continuous {M : Market} (hM : M.Standing) : Continuous (Feps M) := by
  have h : Feps M = fun b => Feps M 0 + ∫ t in (0:ℝ)..b, M.feps t := by
    ext b; have := Feps_sub hM 0 b; linarith
  rw [h]
  exact continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => (feps_cont hM).intervalIntegrable a b) 0)

lemma Feps_neg {M : Market} (hM : M.Standing) (x : ℝ) : Feps M x + Feps M (-x) = 1 := by
  have h1 := intervalIntegral.integral_Iic_add_Ioi (b := x) (μ := volume)
    hM.feps_integrable.integrableOn hM.feps_integrable.integrableOn
  rw [hM.feps_integral] at h1
  have h2 : ∫ t in Set.Ioi x, M.feps t = ∫ t in Set.Iic (-x), M.feps t := by
    have : ∫ t in Set.Ioi x, M.feps t = ∫ t in Set.Ioi x, M.feps (-t) := by
      congr 1; ext t; exact hM.feps_symm t
    rw [this, integral_comp_neg_Ioi]
  unfold Feps
  linarith

lemma Feps_zero {M : Market} (hM : M.Standing) : Feps M 0 = 1 / 2 := by
  have := Feps_neg hM 0
  rw [neg_zero] at this
  linarith

lemma Feps_mono {M : Market} (hM : M.Standing) {a b : ℝ} (hab : a ≤ b) :
    Feps M a ≤ Feps M b := by
  have h := Feps_sub hM a b
  have : 0 ≤ ∫ t in a..b, M.feps t :=
    intervalIntegral.integral_nonneg hab (fun t _ => hM.feps_nonneg t)
  linarith

lemma Feps_lt {M : Market} (hM : M.Standing) (a b : ℝ) (hab : a < b)
    (hpos : ∀ t ∈ Set.Ioo a b, 0 < M.feps t) : Feps M a < Feps M b := by
  have h := Feps_sub hM a b
  have : 0 < ∫ t in a..b, M.feps t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((feps_cont hM).intervalIntegrable a b) hpos hab
  linarith

lemma F_continuous {M : Market} (hM : M.Standing) (i : Fin 2) : Continuous (F M i) := by
  unfold F
  exact (Feps_continuous hM).comp (continuous_id.sub continuous_const)

lemma F_mono {M : Market} (hM : M.Standing) (i : Fin 2) : Monotone (F M i) := by
  intro a b hab
  unfold F
  exact Feps_mono hM (by linarith)

lemma med_mem {M : Market} (i : Fin 2) : med M i = M.m0 ∨ med M i = M.m1 := by
  unfold med
  split_ifs
  · left; rfl
  · right; rfl

/-- strict increase of `F_i` to the left of any `y ∈ [m0, m1]`. -/
lemma F_lt_of_lt {M : Market} (hM : M.Standing) (i : Fin 2) {x y : ℝ}
    (hy : y ∈ Set.Icc M.m0 M.m1) (hxy : x < y) : F M i x < F M i y := by
  have h1 := hM.sL_lt_m0
  have h2 := hM.m0_lt_m1
  have hR : M.m1 - M.sL ≤ max (M.sH - M.m0) (M.m1 - M.sL) := le_max_right _ _
  set δ := M.m0 - M.sL with hδ
  set x' := max x (y - δ) with hx'
  have hx'y : x' < y := max_lt hxy (by linarith)
  have hle : F M i x ≤ F M i x' := F_mono hM i (le_max_left _ _)
  have hlt : F M i x' < F M i y := by
    unfold F
    apply Feps_lt hM _ _ (by linarith)
    intro t ht
    apply hM.feps_pos
    have hlo : y - δ ≤ x' := le_max_right _ _
    rw [abs_le]
    rcases med_mem (M := M) i with h | h <;> rw [h] at ht <;>
      constructor <;> linarith [ht.1, ht.2, hy.1, hy.2]
  linarith

lemma F_strictMonoOn {M : Market} (hM : M.Standing) (i : Fin 2) :
    StrictMonoOn (F M i) (Set.Icc M.m0 M.m1) :=
  fun _ _ _ hb hab => F_lt_of_lt hM i hb hab

lemma Finv_F {M : Market} (hM : M.Standing) (i : Fin 2) {y : ℝ}
    (hy : y ∈ Set.Icc M.m0 M.m1) : Finv M i (F M i y) = y := by
  unfold Finv
  apply IsLeast.csInf_eq
  refine ⟨show F M i y ≤ F M i y from le_refl _, ?_⟩
  intro x hx
  by_contra hcon
  push_neg at hcon
  have := F_lt_of_lt hM i hy hcon
  simp only [Set.mem_setOf_eq] at hx
  linarith

lemma exists_F_eq {M : Market} (hM : M.Standing) (i : Fin 2) {v : ℝ}
    (hv : v ∈ Set.Icc (F M i M.m0) (F M i M.m1)) : ∃ y ∈ Set.Icc M.m0 M.m1, F M i y = v := by
  have := intermediate_value_Icc hM.m0_lt_m1.le (F_continuous hM i).continuousOn hv
  obtain ⟨y, hy, hFy⟩ := this
  exact ⟨y, hy, hFy⟩

lemma F_Finv {M : Market} (hM : M.Standing) (i : Fin 2) {v : ℝ}
    (hv : v ∈ Set.Icc (F M i M.m0) (F M i M.m1)) :
    Finv M i v ∈ Set.Icc M.m0 M.m1 ∧ F M i (Finv M i v) = v := by
  obtain ⟨y, hy, hFy⟩ := exists_F_eq hM i hv
  rw [← hFy, Finv_F hM i hy]
  exact ⟨hy, rfl⟩

/-- reflection: `F_1(m0+m1-x) = 1 - F_0(x)`. -/
lemma F1_reflect {M : Market} (hM : M.Standing) (x : ℝ) :
    F M 1 (M.m0 + M.m1 - x) = 1 - F M 0 x := by
  unfold F med
  simp only [Fin.isValue, one_ne_zero, if_false, if_true]
  have := Feps_neg hM (x - M.m0)
  have e : M.m0 + M.m1 - x - M.m1 = -(x - M.m0) := by ring
  rw [e]
  linarith

lemma F1_m1 {M : Market} (hM : M.Standing) : F M 1 M.m1 = 1 / 2 := by
  unfold F med; simp only [Fin.isValue, one_ne_zero, if_false, sub_self]; exact Feps_zero hM

lemma F0_m0 {M : Market} (hM : M.Standing) : F M 0 M.m0 = 1 / 2 := by
  unfold F med; simp only [Fin.isValue, if_true, sub_self]; exact Feps_zero hM

lemma F0_m1 {M : Market} (hM : M.Standing) : F M 0 M.m1 = 1 - alpha M := by
  have := F1_reflect hM M.m1
  have e : M.m0 + M.m1 - M.m1 = M.m0 := by ring
  rw [e] at this
  unfold alpha
  linarith

lemma F1_m0 {M : Market} : F M 1 M.m0 = alpha M := rfl

end SBFAux

open SpreadBetting.Inertial SBFAux in
theorem solution (M : Market) (hM : M.Standing) (ρp : ℕ → ℝ)
    (hρ : ∀ z : ℕ, 1 ≤ z → ρp z ∈ Set.Ioo 0 (1 / 2 - alpha M)) :
    (∀ z : ℤ, sTilde M ρp z ∈ Set.Icc M.m0 M.m1 ∧
      F M 0 (sTilde M ρp (-z)) = 1 / 2 + rhoExt M ρp z ∧
      F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z) ∧
    (∀ s' ρ' : ℤ → ℝ, (∀ z, s' z ∈ Set.Icc M.m0 M.m1) →
      (∀ z : ℤ, 0 < z → ρ' z = ρp z.toNat) →
      (∀ z : ℤ, F M 0 (s' (-z)) = 1 / 2 + ρ' z ∧ F M 1 (s' z) = 1 / 2 - ρ' z) →
      s' = sTilde M ρp ∧ ρ' = rhoExt M ρp) := by
  have hm := hM.m0_lt_m1
  -- the basic facts at a positive index
  have basic : ∀ n : ℕ, 1 ≤ n →
      Finv M 1 (1 / 2 - ρp n) ∈ Set.Icc M.m0 M.m1 ∧
      F M 1 (Finv M 1 (1 / 2 - ρp n)) = 1 / 2 - ρp n ∧
      Finv M 0 (1 / 2 + ρp n) ∈ Set.Icc M.m0 M.m1 ∧
      F M 0 (Finv M 0 (1 / 2 + ρp n)) = 1 / 2 + ρp n ∧
      F M 0 (Finv M 1 (1 / 2 - ρp n)) = 1 - F M 1 (Finv M 0 (1 / 2 + ρp n)) := by
    intro n hn
    obtain ⟨hp0, hp1⟩ := hρ n hn
    have ha := F_Finv hM 1 (v := 1 / 2 - ρp n) (by
      rw [F1_m0, F1_m1 hM]; constructor <;> linarith)
    have hb := F_Finv hM 0 (v := 1 / 2 + ρp n) (by
      rw [F0_m0 hM, F0_m1 hM]; constructor <;> linarith)
    set a := Finv M 1 (1 / 2 - ρp n)
    set b := Finv M 0 (1 / 2 + ρp n)
    have hb' : M.m0 + M.m1 - b ∈ Set.Icc M.m0 M.m1 := by
      constructor <;> linarith [hb.1.1, hb.1.2]
    have hrefl := F1_reflect hM b
    have hab : a = M.m0 + M.m1 - b := by
      apply (F_strictMonoOn hM 1).injOn ha.1 hb'
      rw [ha.2, hrefl, hb.2]; ring
    refine ⟨ha.1, ha.2, hb.1, hb.2, ?_⟩
    have h2 := F1_reflect hM a
    have e : M.m0 + M.m1 - a = b := by rw [hab]; ring
    rw [e] at h2
    linarith
  have hmid : M.m0 + M.m1 - (M.m0 + M.m1) / 2 = (M.m0 + M.m1) / 2 := by ring
  have hmidF : F M 0 ((M.m0 + M.m1) / 2) + F M 1 ((M.m0 + M.m1) / 2) = 1 := by
    have := F1_reflect hM ((M.m0 + M.m1) / 2)
    rw [hmid] at this; linarith
  have hmidI : (M.m0 + M.m1) / 2 ∈ Set.Icc M.m0 M.m1 := by
    constructor <;> linarith
  have part1 : ∀ z : ℤ, sTilde M ρp z ∈ Set.Icc M.m0 M.m1 ∧
      F M 0 (sTilde M ρp (-z)) = 1 / 2 + rhoExt M ρp z ∧
      F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z := by
    intro z
    rcases lt_trichotomy 0 z with hz | hz | hz
    · have hn : 1 ≤ z.toNat := by omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := basic z.toNat hn
      have hnz : ¬ (0 < -z) := by omega
      have hnz' : -z ≠ 0 := by omega
      have e : (-(-z)).toNat = z.toNat := by rw [neg_neg]
      simp only [sTilde, rhoExt, if_pos hz, if_neg hnz, if_neg hnz', e]
      exact ⟨h1, h4, h2⟩
    · subst hz
      simp only [sTilde, rhoExt, lt_irrefl, if_false, if_true, neg_zero]
      refine ⟨hmidI, ?_, ?_⟩ <;> linarith
    · have hn : 1 ≤ (-z).toNat := by omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := basic (-z).toNat hn
      have hnz : ¬ (0 < z) := by omega
      have hnz' : z ≠ 0 := by omega
      have hpz : 0 < -z := by omega
      simp only [sTilde, rhoExt, if_neg hnz, if_neg hnz', if_pos hpz]
      refine ⟨h3, ?_, ?_⟩
      · rw [h5]; ring
      · ring
  refine ⟨part1, ?_⟩
  intro s' ρ' hs' hρ' hF
  have hs_eq : s' = sTilde M ρp := by
    funext z
    rcases lt_trichotomy 0 z with hz | hz | hz
    · apply (F_strictMonoOn hM 1).injOn (hs' z) (part1 z).1
      rw [(hF z).2, (part1 z).2.2, hρ' z hz]
      simp only [rhoExt, if_pos hz]
    · subst hz
      have h1 := hF 0
      rw [neg_zero] at h1
      have hsum : F M 0 (s' 0) + F M 1 (s' 0) = 1 := by linarith [h1.1, h1.2]
      simp only [sTilde, lt_irrefl, if_false, if_true]
      -- G = F0 + F1 is strictly increasing on [m0, m1]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have a1 := F_lt_of_lt hM 0 hmidI hlt
        have a2 := F_lt_of_lt hM 1 hmidI hlt
        linarith
      · have a1 := F_lt_of_lt hM 0 (hs' 0) hlt
        have a2 := F_lt_of_lt hM 1 (hs' 0) hlt
        linarith
    · have hpz : 0 < -z := by omega
      apply (F_strictMonoOn hM 0).injOn (hs' z) (part1 z).1
      have h1 := (hF (-z)).1
      rw [neg_neg] at h1
      have h2 := (part1 (-z)).2.1
      rw [neg_neg] at h2
      rw [h1, h2, hρ' (-z) hpz]
      simp only [rhoExt, if_pos hpz]
  refine ⟨hs_eq, ?_⟩
  funext z
  have h1 := (hF z).2
  have h2 := (part1 z).2.2
  rw [hs_eq] at h1
  linarith
