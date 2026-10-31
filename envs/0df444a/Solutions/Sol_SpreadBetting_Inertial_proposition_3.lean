-- Prove2me | solution 1 for SpreadBetting.Inertial.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:55:11.322118+00:00
-- url     : https://prove2.me/submissions/27e6e72e-834e-4f4a-834e-144b392ff880
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain
import Definitions.Def_GittinsIndex
import Theorems.Thm_SpreadBetting_Inertial_proposition_K_2
import Theorems.Thm_SpreadBetting_Inertial_lemma_G_2
import Theorems.Thm_SpreadBetting_Inertial_proposition_2
import Theorems.Thm_SpreadBetting_Inertial_lemma_H_1

open MeasureTheory ProbabilityTheory Filter Topology Finset

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

namespace SBRedAux
open SpreadBetting.Inertial SBFAux

lemma Feps_nonneg {M : Market} (hM : M.Standing) (x : ℝ) : 0 ≤ Feps M x := by
  unfold Feps
  exact setIntegral_nonneg measurableSet_Iic (fun t _ => hM.feps_nonneg t)

lemma F_mem {M : Market} (hM : M.Standing) (i : Fin 2) (x : ℝ) :
    0 ≤ F M i x ∧ F M i x ≤ 1 := by
  unfold F
  refine ⟨Feps_nonneg hM _, ?_⟩
  have := Feps_neg hM (x - med M i)
  have := Feps_nonneg hM (-(x - med M i))
  linarith

/-- the threshold `belowZbar` is a `belowWB` threshold. -/
lemma belowZbar_eq (M : Market) (ρp : ℕ → ℝ) (hne : (zbarSet M ρp).Nonempty) :
    ∃ Zb : WithBot ℤ, belowZbar M ρp = belowWB Zb := by
  by_cases hb : BddBelow (zbarSet M ρp)
  · refine ⟨((zbar M ρp : ℤ) : WithBot ℤ), ?_⟩
    funext z
    apply propext
    unfold belowZbar belowWB zbar
    rw [WithBot.coe_lt_coe]
    constructor
    · intro h
      exact h _ (Int.csInf_mem hne hb)
    · intro h w hw
      exact lt_of_lt_of_le h (csInf_le hb hw)
  · refine ⟨⊥, ?_⟩
    funext z
    apply propext
    unfold belowZbar belowWB
    rw [not_bddBelow_iff] at hb
    obtain ⟨w, hw, hwz⟩ := hb (z + 1)
    constructor
    · intro h
      have := h w hw
      omega
    · intro h
      exact absurd h (WithBot.not_lt_bot _)

lemma xiStar_eq (M : Market) (ρp : ℕ → ℝ) (Zb : WithBot ℤ)
    (h : belowZbar M ρp = belowWB Zb) (i : Fin 2) :
    xiStar M ρp i = threshStrat i (belowWB Zb) := by
  unfold xiStar; rw [h]

/-- monotonicity of `cumExp` in the reward, for a nonnegative strategy -/
lemma cumExp_mono {M : Market} (hM : M.Standing) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy)
    (hξ : ∀ h z a, 0 ≤ ξ h z a) (g1 g2 : ℤ → ℝ) (hg : ∀ z, g1 z ≤ g2 z) :
    ∀ T h z, cumExp M ρp i ξ (fun z _ _ => g1 z) T h z ≤ cumExp M ρp i ξ (fun z _ _ => g2 z) T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp]
    have hF := F_mem hM i (sTilde M ρp z)
    have hFb : 0 ≤ Fbar M i (sTilde M ρp z) := by unfold Fbar; linarith
    have a1 := ih (h ++ [(1, .pos)]) (z + 1)
    have a2 := ih (h ++ [(-1, .neg)]) (z - 1)
    have a3 := ih (h ++ [(1, .wait)]) (z + 1)
    have a4 := ih (h ++ [(-1, .wait)]) (z - 1)
    have b := hg z
    have p1 := hξ h z .pos
    have p2 := hξ h z .neg
    have p3 := hξ h z .wait
    have e1 := mul_le_mul_of_nonneg_left (add_le_add b a1) p1
    have e2 := mul_le_mul_of_nonneg_left (add_le_add b a2) p2
    have e3 := mul_le_mul_of_nonneg_left (add_le_add b a3) hFb
    have e4 := mul_le_mul_of_nonneg_left (add_le_add b a4) hF.1
    have e5 := mul_le_mul_of_nonneg_left (add_le_add e3 e4) p3
    linarith

lemma cumExp_smul (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) (c : ℝ) (g : ℤ → ℝ) :
    ∀ T h z, cumExp M ρp i ξ (fun z _ _ => c * g z) T h z
      = c * cumExp M ρp i ξ (fun z _ _ => g z) T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp, ih]
    ring

lemma xiStar_nonneg (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) :
    ∀ h z a, 0 ≤ xiStar M ρp i h z a := by
  intro h z a
  unfold xiStar threshStrat
  split_ifs <;> norm_num

end SBRedAux

namespace SBRedAux2
open SpreadBetting.Inertial SBFAux SBRedAux

variable {M : Market} {ρp : ℕ → ℝ}

def P2 (M : Market) (ρp : ℕ → ℝ) : Prop :=
  ∀ z : ℤ, sTilde M ρp z ∈ Set.Icc M.m0 M.m1 ∧
      F M 0 (sTilde M ρp (-z)) = 1 / 2 + rhoExt M ρp z ∧
      F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z

lemma sTilde_neg (hM : M.Standing) (hP : P2 M ρp) (z : ℤ) :
    sTilde M ρp (-z) = M.m0 + M.m1 - sTilde M ρp z := by
  have h1 := (hP z).2.1
  have h2 := (hP z).2.2
  have hI := (hP (-z)).1
  have hI' := (hP z).1
  have hr := F1_reflect hM (sTilde M ρp (-z))
  have hmem : M.m0 + M.m1 - sTilde M ρp (-z) ∈ Set.Icc M.m0 M.m1 := by
    constructor <;> linarith [hI.1, hI.2]
  have : M.m0 + M.m1 - sTilde M ρp (-z) = sTilde M ρp z := by
    apply (F_strictMonoOn hM 1).injOn hmem hI'
    rw [hr, h1, h2]; ring
  linarith

lemma Fbar0_eq (hP : P2 M ρp) (z : ℤ) :
    Fbar M 0 (sTilde M ρp z) = F M 1 (sTilde M ρp (-z)) ∧
    F M 0 (sTilde M ρp z) = Fbar M 1 (sTilde M ρp (-z)) := by
  have h1 := (hP (-z)).2.1
  have h2 := (hP (-z)).2.2
  rw [neg_neg] at h1
  unfold Fbar
  constructor <;> linarith

lemma cumExp_reflect (hP : P2 M ρp) (below : ℤ → Prop) (g : ℤ → ℝ) :
    ∀ T h h' z, cumExp M ρp 0 (threshStrat 0 below) (fun z _ _ => g z) T h z
      = cumExp M ρp 1 (threshStrat 1 below) (fun z _ _ => g (-z)) T h' (-z) := by
  intro T
  induction T with
  | zero => intro h h' z; simp [cumExp]
  | succ T ih =>
    intro h h' z
    have i1 := ih (h ++ [(1, .wait)]) (h' ++ [(-1, .wait)]) (z + 1)
    have i2 := ih (h ++ [(-1, .wait)]) (h' ++ [(1, .wait)]) (z - 1)
    have i3 := ih (h ++ [(-1, .neg)]) (h' ++ [(1, .pos)]) (z - 1)
    rw [show -(z + 1) = -z - 1 by ring] at i1
    rw [show -(z - 1) = -z + 1 by ring] at i2 i3
    obtain ⟨f1, f2⟩ := Fbar0_eq hP z
    simp only [cumExp, threshStrat, neg_neg]
    by_cases hb : below (-z)
    · simp only [hb, if_true, Fin.isValue, zero_ne_one, if_false]
      simp only [reduceCtorEq, if_false, if_true]
      rw [i3]; ring
    · simp only [hb, if_false, Fin.isValue, zero_ne_one, if_true]
      simp only [reduceCtorEq, if_false, if_true]
      rw [i1, i2, f1, f2]; ring

lemma upProb_reflect (hM : M.Standing) (hP : P2 M ρp) (below : ℤ → Prop) (x : ℤ) :
    upProb M ρp 0 (threshStrat 0 below) (-x) = 1 - upProb M ρp 1 (threshStrat 1 below) x := by
  unfold upProb threshStrat
  simp only [neg_neg]
  by_cases hb : below x
  · simp [hb]
  · simp only [hb, neg_neg, if_false, Fin.isValue, zero_ne_one, if_true]
    simp only [reduceCtorEq, if_false, zero_add, one_mul, add_zero]
    have hF0 := F_mem hM 0 (sTilde M ρp (-x))
    have hF1 := F_mem hM 1 (sTilde M ρp x)
    have h1 := (Fbar0_eq hP (-x)).1
    rw [neg_neg] at h1
    rw [h1]
    unfold Fbar
    rw [min_eq_right hF1.2, max_eq_right hF1.1, min_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring

lemma kernel_reflect (hM : M.Standing) (hP : P2 M ρp) (below : ℤ → Prop) (x : ℤ) :
    chainKernel M ρp 0 (threshStrat 0 below) (MeasurableEquiv.neg ℤ x)
      = (chainKernel M ρp 1 (threshStrat 1 below) x).map (MeasurableEquiv.neg ℤ) := by
  have hup := upProb_reflect hM hP below x
  have hm : Measurable (MeasurableEquiv.neg ℤ) := (MeasurableEquiv.neg ℤ).measurable
  show (ENNReal.ofReal (upProb M ρp 0 (threshStrat 0 below) (-x)) • Measure.dirac (-x + 1)
      + ENNReal.ofReal (1 - upProb M ρp 0 (threshStrat 0 below) (-x)) • Measure.dirac (-x - 1))
    = (ENNReal.ofReal (upProb M ρp 1 (threshStrat 1 below) x) • Measure.dirac (x + 1)
      + ENNReal.ofReal (1 - upProb M ρp 1 (threshStrat 1 below) x) • Measure.dirac (x - 1)).map
        (MeasurableEquiv.neg ℤ)
  rw [Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul, Measure.map_dirac' hm,
    Measure.map_dirac' hm, hup]
  simp only [MeasurableEquiv.neg_apply, sub_sub_cancel]
  rw [add_comm]
  congr 2 <;> ring


lemma dist_bounds (hM : M.Standing) (hP : P2 M ρp) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ z : ℤ,
      c1 * rhoExt M ρp z ≤ |sTilde M ρp z - M.m1| ∧ |sTilde M ρp z - M.m1| ≤ c2 * rhoExt M ρp z := by
  have hm := hM.m0_lt_m1
  set I := Set.Icc (M.m0 - M.m1) 0 with hI
  have hIc : IsCompact I := isCompact_Icc
  have hIne : I.Nonempty := ⟨0, by constructor <;> linarith⟩
  have hcont := feps_cont hM
  obtain ⟨tmin, htmin, hmin⟩ := hIc.exists_isMinOn hIne hcont.continuousOn
  obtain ⟨tmax, htmax, hmax⟩ := hIc.exists_isMaxOn hIne hcont.continuousOn
  have hposI : ∀ t ∈ I, 0 < M.feps t := by
    intro t ht
    apply hM.feps_pos
    rw [abs_le]
    have h1 := hM.sL_lt_m0
    have : M.m1 - M.sL ≤ max (M.sH - M.m0) (M.m1 - M.sL) := le_max_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hfmin : 0 < M.feps tmin := hposI _ htmin
  have hfmax : 0 < M.feps tmax := hposI _ htmax
  refine ⟨1 / M.feps tmax, 1 / M.feps tmin, by positivity, by positivity, ?_⟩
  intro z
  obtain ⟨hs, -, hF1⟩ := hP z
  set s := sTilde M ρp z with hsdef
  have habs : |s - M.m1| = M.m1 - s := by
    rw [abs_of_nonpos (by linarith [hs.2])]; ring
  have hrho : rhoExt M ρp z = ∫ t in (s - M.m1)..0, M.feps t := by
    have h1 : F M 1 s = Feps M (s - M.m1) := by unfold F med; simp
    have h2 := Feps_sub hM (s - M.m1) 0
    rw [Feps_zero hM] at h2
    linarith
  have hle : s - M.m1 ≤ 0 := by linarith [hs.2]
  have hint := (hcont.intervalIntegrable (μ := volume) (s - M.m1) 0)
  have lo : ∫ t in (s - M.m1)..0, M.feps tmin ≤ ∫ t in (s - M.m1)..0, M.feps t :=
    intervalIntegral.integral_mono_on hle intervalIntegrable_const hint
      (fun t ht => hmin ⟨by linarith [ht.1, hs.1], ht.2⟩)
  have hi : ∫ t in (s - M.m1)..0, M.feps t ≤ ∫ t in (s - M.m1)..0, M.feps tmax :=
    intervalIntegral.integral_mono_on hle hint intervalIntegrable_const
      (fun t ht => hmax ⟨by linarith [ht.1, hs.1], ht.2⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at lo hi
  rw [habs, hrho]
  constructor
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hfmax]
    nlinarith
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hfmin]
    nlinarith

end SBRedAux2

namespace SBL5Aux
open SpreadBetting.Inertial

variable {M : Market} {ρp : ℕ → ℝ}

noncomputable def oneStep (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy)
    (w : ℤ → Act → ℤ → ℝ) (h : List (ℤ × Act)) (z : ℤ) : ℝ :=
  ξ h z .pos * w z .pos 1 + ξ h z .neg * w z .neg (-1)
    + ξ h z .wait * (Fbar M i (sTilde M ρp z) * w z .wait 1 + F M i (sTilde M ρp z) * w z .wait (-1))

lemma cumExp_congr (i : Fin 2) (ξ : Strategy) (w1 w2 : ℤ → Act → ℤ → ℝ)
    (hw : ∀ h z, oneStep M ρp i ξ w1 h z = oneStep M ρp i ξ w2 h z) :
    ∀ T h z, cumExp M ρp i ξ w1 T h z = cumExp M ρp i ξ w2 T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    have e := hw h z
    unfold oneStep at e
    simp only [cumExp, ih]
    linear_combination e

lemma cumExp_add (i : Fin 2) (ξ : Strategy) (w1 w2 : ℤ → Act → ℤ → ℝ) :
    ∀ T h z, cumExp M ρp i ξ (fun z a d => w1 z a d + w2 z a d) T h z
      = cumExp M ρp i ξ w1 T h z + cumExp M ρp i ξ w2 T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp, ih]
    ring

lemma cumExp_smul' (i : Fin 2) (ξ : Strategy) (k : ℝ) (w : ℤ → Act → ℤ → ℝ) :
    ∀ T h z, cumExp M ρp i ξ (fun z a d => k * w z a d) T h z = k * cumExp M ρp i ξ w T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp, ih]
    ring

lemma cumExp_const (i : Fin 2) (ξ : Strategy)
    (hξ : ∀ h z, ξ h z .pos + ξ h z .wait + ξ h z .neg = 1) (k : ℝ) :
    ∀ T h z, cumExp M ρp i ξ (fun _ _ _ => k) T h z = k * T := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp, ih]
    have e := hξ h z
    unfold Fbar
    push_cast
    linear_combination (k + k * T) * e

lemma threshStrat_sum (i : Fin 2) (below : ℤ → Prop) :
    ∀ h z, threshStrat i below h z .pos + threshStrat i below h z .wait
      + threshStrat i below h z .neg = 1 := by
  intro h z
  unfold threshStrat
  split_ifs <;> simp_all

end SBL5Aux

namespace SBP3Aux
open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2

variable {M : Market} {ρp : ℕ → ℝ}

lemma rho_bounds (hM : M.Standing) (hP : P2 M ρp) (z : ℤ) :
    0 ≤ rhoExt M ρp z ∧ rhoExt M ρp z ≤ 1 / 2 := by
  obtain ⟨hs, -, hF⟩ := hP z
  have h1 := F_mono hM 1 hs.2
  have h0 := F_mono hM 1 hs.1
  rw [F1_m1 hM] at h1
  have hα : 0 ≤ F M 1 M.m0 := (F_mem hM 1 M.m0).1
  constructor <;> linarith

/-- discrete Cauchy–Schwarz / Jensen for the expectation recursion -/
lemma cumExp_sq (hM : M.Standing) (i : Fin 2) (ξ : Strategy) (hξ : ∀ h z a, 0 ≤ ξ h z a)
    (hsum : ∀ h z, ξ h z .pos + ξ h z .wait + ξ h z .neg = 1) (g : ℤ → ℝ) :
    ∀ T h z, (cumExp M ρp i ξ (fun z _ _ => g z) T h z) ^ 2
      ≤ T * cumExp M ρp i ξ (fun z _ _ => g z ^ 2) T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp]
    set a := g z
    set C := fun h z => cumExp M ρp i ξ (fun z _ _ => g z) T h z with hC
    set D := fun h z => cumExp M ρp i ξ (fun z _ _ => g z ^ 2) T h z with hD
    set x1 := C (h ++ [(1, .pos)]) (z + 1)
    set x2 := C (h ++ [(-1, .neg)]) (z - 1)
    set x3 := C (h ++ [(1, .wait)]) (z + 1)
    set x4 := C (h ++ [(-1, .wait)]) (z - 1)
    set y1 := D (h ++ [(1, .pos)]) (z + 1)
    set y2 := D (h ++ [(-1, .neg)]) (z - 1)
    set y3 := D (h ++ [(1, .wait)]) (z + 1)
    set y4 := D (h ++ [(-1, .wait)]) (z - 1)
    have i1 : x1 ^ 2 ≤ T * y1 := ih _ _
    have i2 : x2 ^ 2 ≤ T * y2 := ih _ _
    have i3 : x3 ^ 2 ≤ T * y3 := ih _ _
    have i4 : x4 ^ 2 ≤ T * y4 := ih _ _
    set p1 := ξ h z .pos
    set p2 := ξ h z .neg
    set p3 := ξ h z .wait * Fbar M i (sTilde M ρp z)
    set p4 := ξ h z .wait * F M i (sTilde M ρp z)
    have hF := F_mem hM i (sTilde M ρp z)
    have q1 : 0 ≤ p1 := hξ _ _ _
    have q2 : 0 ≤ p2 := hξ _ _ _
    have q3 : 0 ≤ p3 := mul_nonneg (hξ _ _ _) (by unfold Fbar; linarith)
    have q4 : 0 ≤ p4 := mul_nonneg (hξ _ _ _) hF.1
    have hs : p1 + p2 + p3 + p4 = 1 := by
      have := hsum h z
      simp only [p1, p2, p3, p4, Fbar]; linarith [this]
    have eC : p1 * (a + x1) + p2 * (a + x2) + ξ h z .wait * (Fbar M i (sTilde M ρp z) * (a + x3)
        + F M i (sTilde M ρp z) * (a + x4)) = a + (p1 * x1 + p2 * x2 + p3 * x3 + p4 * x4) := by
      simp only [p3, p4]; linear_combination a * hs
    have eD : p1 * (a ^ 2 + y1) + p2 * (a ^ 2 + y2) + ξ h z .wait * (Fbar M i (sTilde M ρp z) *
        (a ^ 2 + y3) + F M i (sTilde M ρp z) * (a ^ 2 + y4))
        = a ^ 2 + (p1 * y1 + p2 * y2 + p3 * y3 + p4 * y4) := by
      simp only [p3, p4]; linear_combination a ^ 2 * hs
    rw [eC, eD]
    set b := p1 * x1 + p2 * x2 + p3 * x3 + p4 * x4 with hb
    set E := p1 * y1 + p2 * y2 + p3 * y3 + p4 * y4 with hE
    -- Jensen
    have hJ : b ^ 2 ≤ p1 * x1 ^ 2 + p2 * x2 ^ 2 + p3 * x3 ^ 2 + p4 * x4 ^ 2 := by
      have e : p1 * x1 ^ 2 + p2 * x2 ^ 2 + p3 * x3 ^ 2 + p4 * x4 ^ 2 - b ^ 2
          = p1 * (x1 - b) ^ 2 + p2 * (x2 - b) ^ 2 + p3 * (x3 - b) ^ 2 + p4 * (x4 - b) ^ 2 := by
        rw [hb]; linear_combination (-(p1 * x1 + p2 * x2 + p3 * x3 + p4 * x4) ^ 2) * hs
      have : 0 ≤ p1 * (x1 - b) ^ 2 + p2 * (x2 - b) ^ 2 + p3 * (x3 - b) ^ 2 + p4 * (x4 - b) ^ 2 := by
        positivity
      linarith
    have hJ2 : b ^ 2 ≤ T * E := by
      have m1 := mul_le_mul_of_nonneg_left i1 q1
      have m2 := mul_le_mul_of_nonneg_left i2 q2
      have m3 := mul_le_mul_of_nonneg_left i3 q3
      have m4 := mul_le_mul_of_nonneg_left i4 q4
      have e : (T : ℝ) * E = p1 * (T * y1) + p2 * (T * y2) + p3 * (T * y3) + p4 * (T * y4) := by
        rw [hE]; ring
      linarith
    push_cast
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp only [Nat.cast_zero, zero_mul] at hJ2
      have hb0 : b = 0 := by
        have := sq_nonneg b
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hJ2 this)
      have hE0 : E = 0 := by
        simp only [hE, y1, y2, y3, y4, D, cumExp]; ring
      rw [hb0, hE0]; simp
    · have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
      have e1 : (T : ℝ) * (T + 1) * a ^ 2 + (T + 1) * b ^ 2 - T * (a + b) ^ 2
          = (T * a - b) ^ 2 := by ring
      have e2 : ((T : ℝ) + 1) * b ^ 2 ≤ (T + 1) * (T * E) :=
        mul_le_mul_of_nonneg_left hJ2 (by positivity)
      have key : (T : ℝ) * (a + b) ^ 2 ≤ T * ((T + 1) * (a ^ 2 + E)) := by
        nlinarith [sq_nonneg ((T : ℝ) * a - b)]
      exact le_of_mul_le_mul_left key hTpos

lemma sum_rho_le_log (M : Market) (r : ℝ) (hr : 0 < r) (hr0 : 0 < r0 M) (T : ℕ) (hT : 3 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, rhoIP M r t ≤ (2 / r) * Real.log T := by
  have h1 : ∀ t ∈ Finset.Icc 1 T, rhoIP M r t ≤ (1 / r) * (1 / (t : ℝ)) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.1 ht).1
    unfold rhoIP
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have h2 : ∑ t ∈ Finset.Icc 1 T, (1 / (t : ℝ)) ≤ 1 + Real.log T := by
    have hh := harmonic_le_one_add_log T
    have e : ∀ n : ℕ, ((harmonic n : ℚ) : ℝ) = ∑ t ∈ Finset.Icc 1 n, (1 / (t : ℝ)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [harmonic_succ, Finset.sum_Icc_succ_top (by omega), ← ihn]
        push_cast; ring
    rw [e] at hh; exact hh
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have h3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  calc ∑ t ∈ Finset.Icc 1 T, rhoIP M r t ≤ ∑ t ∈ Finset.Icc 1 T, (1 / r) * (1 / (t : ℝ)) :=
        Finset.sum_le_sum h1
    _ = (1 / r) * ∑ t ∈ Finset.Icc 1 T, (1 / (t : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (1 / r) * (1 + Real.log T) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (2 / r) * Real.log T := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]; linarith

lemma r0_pos' (hM : M.Standing) : 0 < r0 M := by
  unfold r0
  have h1 := F_lt_of_lt hM 1 (y := M.m1) ⟨hM.m0_lt_m1.le, le_refl _⟩
    (x := (M.m0 + M.m1) / 2) (by linarith [hM.m0_lt_m1])
  rw [F1_m1 hM] at h1
  exact inv_pos.2 (by linarith)

end SBP3Aux

open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2 SBL5Aux SBP3Aux in
theorem solution (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r)
    (hr : r < rbar M) :
    let ρp := rhoIP M r
    let ξ := xiStar M ρp 1
    -- (P3:1)
    (∃ M₀ : ℤ, ∀ Mx : ℤ, M₀ ≤ Mx → ∃ L : ℝ,
      Tendsto (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => indic (z ≤ Mx)) T [] 0) atTop (𝓝 L)) ∧
    -- (P3:2)
    (Tendsto (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z) T [] 0) atTop atTop ∧
      IsBigOP (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z) T [] 0)
        (fun T : ℕ => Real.sqrt (T * Real.log T))) ∧
    -- (P3:3)
    (Tendsto (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => lossFn M ρp (belowZbar M ρp) z) T [] 0)
        atTop atTop ∧
      IsBigOP (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => lossFn M ρp (belowZbar M ρp) z) T [] 0)
        (fun T : ℕ => Real.log T)) := by
  intro ρp ξ
  obtain ⟨hsv, hreg⟩ := lemma_H_1 M hM r hr0 hr
  have hP : P2 M ρp := (proposition_2 M hM ρp hsv.1).1
  have hc := hM.c_pos
  have hc1 := hM.c_lt_one
  -- r < 2 and r < r̄₁
  have hr2 : r < 2 := by
    have : rbar M ≤ 2 := by unfold rbar; split_ifs <;> exact min_le_left _ _
    linarith
  have hr1 : (r : EReal) < rbar1 M := by
    unfold rbar1
    unfold rbar at hr
    split_ifs with hz
    · rw [if_pos hz] at hr
      exact EReal.coe_lt_coe_iff.2 (lt_of_lt_of_le hr
        (le_trans (min_le_right _ _) (min_le_right _ _)))
    · exact EReal.coe_lt_top r
  obtain ⟨⟨hGpos, hGneg⟩, -⟩ := lemma_G_2 M hM r hr0 hr2 hr1
  have hne : (zbarSet M ρp).Nonempty := by
    by_cases hj : 0 < (2 - M.c) * (1 / 2 - alpha M) - M.c / 2
    · exact (hGpos hj).1
    · have hnb := hGneg (not_lt.1 hj)
      by_contra hE
      rw [Set.not_nonempty_iff_eq_empty] at hE
      exact hnb (hE ▸ bddBelow_empty)
  obtain ⟨Zb, hZb⟩ := belowZbar_eq M ρp hne
  have hξ : ξ = threshStrat 1 (belowWB Zb) := xiStar_eq M ρp Zb hZb 1
  obtain ⟨hK1, -, hK3, -⟩ := proposition_K_2 M hM ρp hsv Zb
  obtain ⟨hLdiv, hLO⟩ := hK3 hreg
  have hξn : ∀ h z a, 0 ≤ ξ h z a := xiStar_nonneg M ρp 1
  have hξs : ∀ h z, ξ h z .pos + ξ h z .wait + ξ h z .neg = 1 := by
    rw [hξ]; exact threshStrat_sum 1 _
  set R : ℕ → ℝ := fun T => cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z) T [] 0 with hR
  set Ls : ℕ → ℝ := fun T => cumExp M ρp 1 ξ
    (fun z _ _ => lossFn M ρp (belowZbar M ρp) z) T [] 0 with hLs
  have hLs' : Ls = fun T => cumExp M ρp 1 (threshStrat 1 (belowWB Zb))
      (fun z _ _ => lossFn M ρp (belowWB Zb) z) T [] 0 := by
    rw [hLs, hξ, hZb]
  -- (P3:3)
  have hrr := r0_pos' hM
  have P33 : Tendsto Ls atTop atTop ∧ IsBigOP Ls (fun T : ℕ => Real.log T) := by
    rw [hLs']
    refine ⟨hLdiv, ?_⟩
    obtain ⟨C, T0, hC⟩ := hLO
    have hCnn : 0 ≤ C := by
      have h := hC (max T0 1) (le_max_left _ _)
      have hs : 0 < ∑ t ∈ Finset.Icc 1 (max T0 1), rhoIP M r t := by
        apply Finset.sum_pos
        · intro t _; unfold rhoIP; positivity
        · exact ⟨1, Finset.mem_Icc.2 ⟨le_refl _, le_max_right _ _⟩⟩
      have := abs_nonneg (cumExp M ρp 1 (threshStrat 1 (belowWB Zb))
        (fun z _ _ => lossFn M ρp (belowWB Zb) z) (max T0 1) [] 0)
      by_contra hneg
      push_neg at hneg
      nlinarith
    refine ⟨C * (2 / r), max T0 3, fun T hT => ?_⟩
    have h1 := hC T (le_trans (le_max_left _ _) hT)
    have h2 := sum_rho_le_log M r hr0 hrr T (le_trans (le_max_right _ _) hT)
    calc _ ≤ C * ∑ t ∈ Finset.Icc 1 T, ρp t := h1
      _ ≤ C * ((2 / r) * Real.log T) := mul_le_mul_of_nonneg_left h2 hCnn
      _ = C * (2 / r) * Real.log T := by ring
  -- pointwise comparisons of the loss with ρ
  have hlo : ∀ z, (4 - 2 * M.c) * rhoExt M ρp z ^ 2 ≤ lossFn M ρp (belowZbar M ρp) z := by
    intro z
    obtain ⟨h0, h1⟩ := rho_bounds hM hP z
    unfold lossFn
    split_ifs
    · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - M.c) h0)
        (by linarith : (0:ℝ) ≤ 1 - 2 * rhoExt M ρp z)]
    · exact le_refl _
  have hhi : ∀ z, lossFn M ρp (belowZbar M ρp) z ≤ (2 - M.c) * rhoExt M ρp z := by
    intro z
    obtain ⟨h0, h1⟩ := rho_bounds hM hP z
    unfold lossFn
    split_ifs
    · exact le_refl _
    · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - M.c) h0)
        (by linarith : (0:ℝ) ≤ 1 - 2 * rhoExt M ρp z)]
  have hLR : ∀ T, Ls T ≤ (2 - M.c) * R T := by
    intro T
    have := cumExp_mono hM ρp 1 ξ hξn _ (fun z => (2 - M.c) * rhoExt M ρp z) hhi T [] 0
    rw [cumExp_smul] at this
    exact this
  have hQL : ∀ T, (4 - 2 * M.c) * cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z ^ 2) T [] 0
      ≤ Ls T := by
    intro T
    have := cumExp_mono hM ρp 1 ξ hξn (fun z => (4 - 2 * M.c) * rhoExt M ρp z ^ 2) _ hlo T [] 0
    rw [cumExp_smul] at this
    exact this
  have hR0 : ∀ T, 0 ≤ R T := by
    intro T
    have := cumExp_mono hM ρp 1 ξ hξn (fun z => 0 * rhoExt M ρp z) (fun z => rhoExt M ρp z)
      (fun z => by simpa using (rho_bounds hM hP z).1) T [] 0
    rw [cumExp_smul, zero_mul] at this
    exact this
  refine ⟨?_, ⟨?_, ?_⟩, P33⟩
  · rw [hξ]; exact hK1
  · -- divergence
    have : Tendsto (fun T => (1 / (2 - M.c)) * Ls T) atTop atTop :=
      P33.1.const_mul_atTop (by apply div_pos one_pos; linarith)
    refine tendsto_atTop_mono (fun T => ?_) this
    have := hLR T
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
    linarith
  · obtain ⟨C, T0, hC⟩ := P33.2
    have hk : 0 < 4 - 2 * M.c := by linarith
    refine ⟨Real.sqrt (max C 0 / (4 - 2 * M.c)), T0, fun T hT => ?_⟩
    have h1 := hC T hT
    have hsq := cumExp_sq (ρp := ρp) hM 1 ξ hξn hξs (fun z => rhoExt M ρp z) T [] 0
    have hq := hQL T
    show |R T| ≤ _
    rw [abs_of_nonneg (hR0 T)]
    have hlogT : 0 ≤ Real.log T := Real.log_natCast_nonneg T
    have hLsT : Ls T ≤ max C 0 * Real.log T := by
      have := le_abs_self (Ls T)
      have := mul_le_mul_of_nonneg_right (le_max_left C 0) hlogT
      linarith
    have hQ : cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z ^ 2) T [] 0
        ≤ max C 0 / (4 - 2 * M.c) * Real.log T := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hk]; linarith
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    calc R T ^ 2 ≤ T * cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z ^ 2) T [] 0 := hsq
      _ ≤ T * (max C 0 / (4 - 2 * M.c) * Real.log T) := mul_le_mul_of_nonneg_left hQ hT0
      _ = max C 0 / (4 - 2 * M.c) * (T * Real.log T) := by ring
