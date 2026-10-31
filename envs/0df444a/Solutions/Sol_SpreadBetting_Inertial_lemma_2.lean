-- Prove2me | solution 1 for SpreadBetting.Inertial.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:20:59.117989+00:00
-- url     : https://prove2.me/submissions/97f4565e-f61e-494b-b497-9fea2892c879
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain
import Theorems.Thm_SpreadBetting_Inertial_lemma_G_1
import Theorems.Thm_SpreadBetting_Inertial_lemma_G_2
import Theorems.Thm_SpreadBetting_Inertial_lemma_L_2
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

namespace SBL3Aux
open SpreadBetting.Inertial

variable {M : Market} {ρp : ℕ → ℝ}

lemma Lam_zero (Z : ℤ) : Lam M ρp Z 0 =
    (1 / 2 - rhoExt M ρp Z) / (1 / 2 + rhoExt M ρp Z) := by
  simp [Lam]

lemma Lam_succ (Z : ℤ) (n : ℕ) : Lam M ρp Z (n + 1) = Lam M ρp Z n *
    ((1 / 2 - rhoExt M ρp (Z + (n + 1 : ℕ))) / (1 / 2 + rhoExt M ρp (Z + (n + 1 : ℕ)))) := by
  unfold Lam
  rw [Finset.prod_range_succ]

/-- closed forms of `Jbar1` when `z̄` is finite -/
lemma Jbar1_up (hne : (zbarSet M ρp).Nonempty) (hb : BddBelow (zbarSet M ρp)) (n : ℕ) :
    Jbar1 M ρp (zbar M ρp + n) = jPlusZ M ρp 1 (zbar M ρp - 1) *
      ∑' m : ℕ, Lam M ρp (zbar M ρp) (n + m) := by
  unfold Jbar1
  rw [if_pos ⟨hne, hb⟩]
  have h1 : (zbar M ρp + n - zbar M ρp).toNat = n := by omega
  have h2 : (zbar M ρp - (zbar M ρp + n)).toNat = 0 := by omega
  rw [h1, h2]
  simp

lemma Jbar1_down (hne : (zbarSet M ρp).Nonempty) (hb : BddBelow (zbarSet M ρp)) (m : ℕ) :
    Jbar1 M ρp (zbar M ρp - m) = jPlusZ M ρp 1 (zbar M ρp - 1) *
      ∑' k : ℕ, Lam M ρp (zbar M ρp) k
      + ∑ k ∈ Finset.Icc 1 m, jPlusZ M ρp 1 (zbar M ρp - k) := by
  unfold Jbar1
  rw [if_pos ⟨hne, hb⟩]
  have h1 : (zbar M ρp - m - zbar M ρp).toNat = 0 := by omega
  have h2 : (zbar M ρp - (zbar M ρp - m)).toNat = m := by omega
  rw [h1, h2]
  simp only [zero_add]


/-- the Bellman equation for `Jbar1` when `z̄` is finite, from the closed forms -/
lemma bellman1 (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hne : (zbarSet M ρp).Nonempty) (hb : BddBelow (zbarSet M ρp))
    (hρ : ∀ z, 0 ≤ rhoExt M ρp z ∧ rhoExt M ρp z ≤ 1 / 2)
    (hj : ∀ z, jPlusZ M ρp 1 z = (2 - c) * rhoExt M ρp z - c / 2)
    (hjm : ∀ z, jMinusZ M ρp 1 z = -(2 - c) * rhoExt M ρp z - c / 2)
    (hF : ∀ z, F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z)
    (hFb : ∀ z, Fbar M 1 (sTilde M ρp z) = 1 / 2 + rhoExt M ρp z)
    (H22 : ∀ z, (jPlusZ M ρp 1 z * (1 / 2 + rhoExt M ρp z)
        < jPlusZ M ρp 1 (z - 1) * (1 / 2 - rhoExt M ρp z) ↔ zbar M ρp ≤ z))
    (H14a : ∀ z, rhoExt M ρp z - rhoExt M ρp (z + 1) < c / (2 - c))
    (H14b : ∀ z, (1 / 2 - rhoExt M ρp z) / (1 / 2 + rhoExt M ρp z)
        < ((2 - c) * rhoExt M ρp (z + 1) + c / 2) / ((2 - c) * rhoExt M ρp z + c / 2))
    (hsum : Summable (Lam M ρp (zbar M ρp))) (z : ℤ) :
    Jbar1 M ρp z = max (max (jPlusZ M ρp 1 z + Jbar1 M ρp (z + 1))
        (jMinusZ M ρp 1 z + Jbar1 M ρp (z - 1)))
      (Fbar M 1 (sTilde M ρp z) * Jbar1 M ρp (z + 1) + F M 1 (sTilde M ρp z) * Jbar1 M ρp (z - 1)) := by
  set Z := zbar M ρp with hZ
  set ρ := rhoExt M ρp with hρdef
  set Λ := Lam M ρp Z with hΛ
  set a := jPlusZ M ρp 1 (Z - 1) with ha
  set S : ℕ → ℝ := fun n => ∑' m : ℕ, Λ (n + m) with hSdef
  have h2c : 0 < 2 - c := by linarith
  have hS : ∀ n, S n = Λ n + S (n + 1) := by
    intro n
    have hs : Summable (fun m => Λ (n + m)) := by
      have := (summable_nat_add_iff n).2 hsum
      exact this.congr (fun m => by rw [add_comm])
    simp only [hSdef]
    rw [hs.tsum_eq_zero_add]
    simp only [add_zero]
    congr 1
    apply tsum_congr; intro m; congr 1; ring
  have hq : ∀ w, (1 / 2 - ρ w) / (1 / 2 + ρ w) * (1 / 2 + ρ w) = 1 / 2 - ρ w := by
    intro w; have h := hρ w; rw [div_mul_cancel₀]; linarith
  have hqnn : ∀ w, 0 ≤ (1 / 2 - ρ w) / (1 / 2 + ρ w) := by
    intro w; have := hρ w; apply div_nonneg <;> linarith
  have hΛ0 : Λ 0 = (1 / 2 - ρ Z) / (1 / 2 + ρ Z) := Lam_zero Z
  have hΛs : ∀ n : ℕ, Λ (n + 1) = Λ n * ((1 / 2 - ρ (Z + (n + 1 : ℕ))) / (1 / 2 + ρ (Z + (n + 1 : ℕ)))) :=
    fun n => Lam_succ Z n
  have hΛnn : ∀ n, 0 ≤ Λ n := by
    intro n; induction n with
    | zero => rw [hΛ0]; exact hqnn Z
    | succ n ih => rw [hΛs]; exact mul_nonneg ih (hqnn _)
  have hup : ∀ n : ℕ, Jbar1 M ρp (Z + n) = a * S n := fun n => Jbar1_up hne hb n
  have hdown : ∀ m : ℕ, Jbar1 M ρp (Z - m) = a * S 0
      + ∑ k ∈ Finset.Icc 1 m, jPlusZ M ρp 1 (Z - k) := by
    intro m; rw [Jbar1_down hne hb m]; simp only [hSdef, zero_add]; rfl
  -- chain: j(Z+n) < a Λ n
  have chain : ∀ n : ℕ, jPlusZ M ρp 1 (Z + n) < a * Λ n := by
    intro n
    induction n with
    | zero =>
      have h := (H22 Z).2 (le_refl _)
      have hp : 0 < 1 / 2 + ρ Z := by have := hρ Z; linarith
      simp only [Nat.cast_zero, add_zero]
      rw [hΛ0]
      have e : a * ((1 / 2 - ρ Z) / (1 / 2 + ρ Z)) * (1 / 2 + ρ Z) = a * (1 / 2 - ρ Z) := by
        rw [mul_assoc, hq]
      have := (lt_div_iff₀ hp).2 (by rw [← ha] at h; exact h)
      calc jPlusZ M ρp 1 Z < a * (1 / 2 - ρ Z) / (1 / 2 + ρ Z) := this
        _ = a * ((1 / 2 - ρ Z) / (1 / 2 + ρ Z)) := by ring
    | succ n ih =>
      set w := Z + ((n + 1 : ℕ) : ℤ)
      have h := (H22 w).2 (by simp only [w]; push_cast; omega)
      have hw1 : w - 1 = Z + n := by simp only [w]; push_cast; ring
      rw [hw1] at h
      have hp : 0 < 1 / 2 + ρ w := by have := hρ w; linarith
      have h' : jPlusZ M ρp 1 w < jPlusZ M ρp 1 (Z + n) * ((1 / 2 - ρ w) / (1 / 2 + ρ w)) := by
        rw [mul_div_assoc', lt_div_iff₀ hp]; exact h
      calc jPlusZ M ρp 1 w < jPlusZ M ρp 1 (Z + n) * ((1 / 2 - ρ w) / (1 / 2 + ρ w)) := h'
        _ ≤ a * Λ n * ((1 / 2 - ρ w) / (1 / 2 + ρ w)) :=
          mul_le_mul_of_nonneg_right ih.le (hqnn w)
        _ = a * Λ (n + 1) := by rw [hΛs]; ring
  -- chain for g = (2-c)ρ + c/2
  have gpos : ∀ w, 0 < (2 - c) * ρ w + c / 2 := by
    intro w; have := hρ w; nlinarith
  have chain2 : ∀ k : ℕ, ((2 - c) * ρ Z + c / 2) * Λ k < (2 - c) * ρ (Z + (k + 1 : ℕ)) + c / 2 := by
    intro k
    induction k with
    | zero =>
      have h := H14b Z
      rw [lt_div_iff₀ (gpos Z)] at h
      rw [hΛ0]; simp only [Nat.cast_zero, zero_add, Nat.cast_one]
      linarith
    | succ k ih =>
      set w := Z + ((k + 1 : ℕ) : ℤ)
      have h := H14b w
      rw [lt_div_iff₀ (gpos w)] at h
      have hw : w + 1 = Z + ((k + 1 + 1 : ℕ) : ℤ) := by simp [w]; ring
      rw [hw] at h
      rw [hΛs]
      calc ((2 - c) * ρ Z + c / 2) * (Λ k * ((1 / 2 - ρ w) / (1 / 2 + ρ w)))
          = (((2 - c) * ρ Z + c / 2) * Λ k) * ((1 / 2 - ρ w) / (1 / 2 + ρ w)) := by ring
        _ ≤ ((2 - c) * ρ w + c / 2) * ((1 / 2 - ρ w) / (1 / 2 + ρ w)) :=
          mul_le_mul_of_nonneg_right ih.le (hqnn w)
        _ < _ := by linarith
  have ha_lt : a < (2 - c) * ρ Z + c / 2 := by
    rw [ha, hj]
    have h := H14a (Z - 1)
    rw [sub_add_cancel] at h
    rw [lt_div_iff₀ h2c] at h
    nlinarith
  have hbluff : ∀ w, jMinusZ M ρp 1 w + jPlusZ M ρp 1 (w - 1) < 0 := by
    intro w
    rw [hj, hjm]
    have h := H14a (w - 1)
    rw [sub_add_cancel, lt_div_iff₀ h2c] at h
    nlinarith
  -- case analysis
  rcases le_or_gt Z z with hz | hz
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = Z + n := ⟨(z - Z).toNat, by omega⟩
    have e1 : Z + n + 1 = Z + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have eA : jPlusZ M ρp 1 (Z + n) + Jbar1 M ρp (Z + n + 1) ≤ Jbar1 M ρp (Z + n) := by
      rw [e1, hup, hup, hS n]
      have := chain n
      linarith
    have eC : Fbar M 1 (sTilde M ρp (Z + n)) * Jbar1 M ρp (Z + n + 1)
        + F M 1 (sTilde M ρp (Z + n)) * Jbar1 M ρp (Z + n - 1) = Jbar1 M ρp (Z + n) := by
      rw [hF, hFb, e1, hup, hup]
      rcases n with _ | k
      · have e2 : Z + ((0 : ℕ) : ℤ) - 1 = Z - ((1 : ℕ) : ℤ) := by simp
        rw [e2, hdown]
        simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one]
        rw [← ha]
        have h0 := hS 0
        have hq0 := hq Z
        rw [← hΛ0] at hq0
        simp only [Nat.cast_zero, add_zero, zero_add]
        linear_combination (-a) * hq0 - a * (1 / 2 + ρ Z) * h0
      · have e2 : Z + ((k + 1 : ℕ) : ℤ) - 1 = Z + k := by push_cast; ring
        rw [e2, hup]
        have h1 := hS (k + 1)
        have h0 := hS k
        have hk := hΛs k
        have hqw := hq (Z + ((k + 1 : ℕ) : ℤ))
        linear_combination (-a * (1 / 2 + ρ (Z + ((k + 1 : ℕ) : ℤ)))) * h1
          + (a * (1 / 2 - ρ (Z + ((k + 1 : ℕ) : ℤ)))) * h0
          + (-a * (1 / 2 + ρ (Z + ((k + 1 : ℕ) : ℤ)))) * hk + (-a * Λ k) * hqw
    have eB : jMinusZ M ρp 1 (Z + n) + Jbar1 M ρp (Z + n - 1) < Jbar1 M ρp (Z + n) := by
      rcases n with _ | k
      · have e2 : Z + ((0 : ℕ) : ℤ) - 1 = Z - ((1 : ℕ) : ℤ) := by simp
        rw [e2, hdown]
        simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one]
        have h := hbluff Z
        have e3 : Jbar1 M ρp (Z + ((0 : ℕ) : ℤ)) = a * S 0 := hup 0
        rw [e3]
        simp only [Nat.cast_zero, add_zero] at h ⊢
        linarith
      · have e2 : Z + ((k + 1 : ℕ) : ℤ) - 1 = Z + k := by push_cast; ring
        rw [e2, hup, hup, hS k]
        have h1 := chain2 k
        have h2 : a * Λ k ≤ ((2 - c) * ρ Z + c / 2) * Λ k :=
          mul_le_mul_of_nonneg_right ha_lt.le (hΛnn k)
        rw [hjm]
        linarith
    rw [eC]
    exact (max_eq_right (max_le eA eB.le)).symm
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, z = Z - ((m + 1 : ℕ) : ℤ) := ⟨(Z - z - 1).toNat, by omega⟩
    have eup : Z - ((m + 1 : ℕ) : ℤ) + 1 = Z - (m : ℤ) := by push_cast; ring
    have edn : Z - ((m + 1 : ℕ) : ℤ) - 1 = Z - ((m + 2 : ℕ) : ℤ) := by push_cast; ring
    have hJz : Jbar1 M ρp (Z - ((m + 1 : ℕ) : ℤ))
        = jPlusZ M ρp 1 (Z - ((m + 1 : ℕ) : ℤ)) + Jbar1 M ρp (Z - (m : ℤ)) := by
      rw [hdown, hdown, Finset.sum_Icc_succ_top (by omega)]
      ring
    have hJdn : Jbar1 M ρp (Z - ((m + 2 : ℕ) : ℤ))
        = Jbar1 M ρp (Z - ((m + 1 : ℕ) : ℤ)) + jPlusZ M ρp 1 (Z - ((m + 1 : ℕ) : ℤ) - 1) := by
      rw [hdown, hdown, show m + 2 = (m + 1) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
      rw [show Z - (((m + 1 + 1 : ℕ)) : ℤ) = Z - ((m + 1 : ℕ) : ℤ) - 1 by push_cast; ring]
      ring
    rw [eup, edn]
    have hnot := mt (H22 (Z - ((m + 1 : ℕ) : ℤ))).1 (by omega)
    push_neg at hnot
    have eC : Fbar M 1 (sTilde M ρp (Z - ((m + 1 : ℕ) : ℤ))) * Jbar1 M ρp (Z - (m : ℤ))
        + F M 1 (sTilde M ρp (Z - ((m + 1 : ℕ) : ℤ))) * Jbar1 M ρp (Z - ((m + 2 : ℕ) : ℤ))
        ≤ Jbar1 M ρp (Z - ((m + 1 : ℕ) : ℤ)) := by
      rw [hJdn, hF, hFb]
      have e4 : Jbar1 M ρp (Z - (m : ℤ)) = Jbar1 M ρp (Z - ((m + 1 : ℕ) : ℤ))
          - jPlusZ M ρp 1 (Z - ((m + 1 : ℕ) : ℤ)) := by rw [hJz]; ring
      rw [e4]
      nlinarith [hnot]
    have eB : jMinusZ M ρp 1 (Z - ((m + 1 : ℕ) : ℤ)) + Jbar1 M ρp (Z - ((m + 2 : ℕ) : ℤ))
        < Jbar1 M ρp (Z - ((m + 1 : ℕ) : ℤ)) := by
      rw [hJdn]
      have := hbluff (Z - ((m + 1 : ℕ) : ℤ))
      linarith
    rw [← hJz]
    rw [max_eq_left (le_of_lt eB), max_eq_left eC]

end SBL3Aux
namespace SBL2Aux
open SpreadBetting.Inertial SBFAux SBRedAux

variable {M : Market} {ρp : ℕ → ℝ}

/-- threshold strategy weights under `H_1` with threshold `Z` -/
lemma ts_pos (Z z : ℤ) (h : List (ℤ × Act)) :
    threshStrat 1 (fun w => w < Z) h z .pos = if z < Z then 1 else 0 := by
  unfold threshStrat; split_ifs <;> simp_all
lemma ts_neg (Z z : ℤ) (h : List (ℤ × Act)) :
    threshStrat 1 (fun w => w < Z) h z .neg = 0 := by
  unfold threshStrat; split_ifs <;> simp_all
lemma ts_wait (Z z : ℤ) (h : List (ℤ × Act)) :
    threshStrat 1 (fun w => w < Z) h z .wait = if z < Z then 0 else 1 := by
  unfold threshStrat; split_ifs <;> simp_all

/-- one-step unfolding of `termExp` for the threshold strategy -/
lemma termExp_succ (Z : ℤ) (g : ℤ → ℝ) (T : ℕ) (h : List (ℤ × Act)) (z : ℤ) :
    termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g (T + 1) h z
      = if z < Z then termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T (h ++ [(1, .pos)]) (z + 1)
        else Fbar M 1 (sTilde M ρp z) * termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T
              (h ++ [(1, .wait)]) (z + 1)
          + F M 1 (sTilde M ρp z) * termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T
              (h ++ [(-1, .wait)]) (z - 1) := by
  simp only [termExp, ts_pos, ts_neg, ts_wait]
  split_ifs <;> ring

lemma cumExp_succ' (Z : ℤ) (f : ℤ → ℝ) (T : ℕ) (h : List (ℤ × Act)) (z : ℤ) :
    cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) (T + 1) h z
      = if z < Z then f z + cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) T
            (h ++ [(1, .pos)]) (z + 1)
        else f z + (Fbar M 1 (sTilde M ρp z) * cumExp M ρp 1 (threshStrat 1 (fun w => w < Z))
              (fun w _ _ => f w) T (h ++ [(1, .wait)]) (z + 1)
          + F M 1 (sTilde M ρp z) * cumExp M ρp 1 (threshStrat 1 (fun w => w < Z))
              (fun w _ _ => f w) T (h ++ [(-1, .wait)]) (z - 1)) := by
  simp only [cumExp, ts_pos, ts_neg, ts_wait]
  unfold Fbar
  split_ifs <;> ring

/-- history independence -/
lemma termExp_hist (Z : ℤ) (g : ℤ → ℝ) : ∀ T h h' z,
    termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T h z
      = termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T h' z := by
  intro T; induction T with
  | zero => intro h h' z; rfl
  | succ T ih =>
    intro h h' z
    rw [termExp_succ, termExp_succ]
    split_ifs
    · exact ih _ _ _
    · rw [ih (h ++ [((1 : ℤ), Act.wait)]) (h' ++ [((1 : ℤ), Act.wait)]),
        ih (h ++ [((-1 : ℤ), Act.wait)]) (h' ++ [((-1 : ℤ), Act.wait)])]

lemma cumExp_hist (Z : ℤ) (f : ℤ → ℝ) : ∀ T h h' z,
    cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) T h z
      = cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) T h' z := by
  intro T; induction T with
  | zero => intro h h' z; rfl
  | succ T ih =>
    intro h h' z
    rw [cumExp_succ', cumExp_succ']
    split_ifs
    · rw [ih _ (h' ++ [((1 : ℤ), Act.pos)])]
    · rw [ih (h ++ [((1 : ℤ), Act.wait)]) (h' ++ [((1 : ℤ), Act.wait)]),
        ih (h ++ [((-1 : ℤ), Act.wait)]) (h' ++ [((-1 : ℤ), Act.wait)])]

/-- Dynkin formula from a one-step harmonic relation -/
lemma dynkin (hM : M.Standing) (Z : ℤ) (f J : ℤ → ℝ)
    (h1 : ∀ z, z < Z → J z = f z + J (z + 1))
    (h2 : ∀ z, Z ≤ z → J z = f z + (Fbar M 1 (sTilde M ρp z) * J (z + 1)
        + F M 1 (sTilde M ρp z) * J (z - 1))) :
    ∀ T h z, cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) T h z
      + termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) J T h z = J z := by
  intro T; induction T with
  | zero => intro h z; simp [cumExp, termExp]
  | succ T ih =>
    intro h z
    rw [cumExp_succ', termExp_succ]
    split_ifs with hz
    · have := ih (h ++ [(1, .pos)]) (z + 1); rw [h1 z hz]; linarith
    · have a1 := ih (h ++ [(1, .wait)]) (z + 1)
      have a2 := ih (h ++ [(-1, .wait)]) (z - 1)
      rw [h2 z (not_lt.1 hz)]
      linear_combination Fbar M 1 (sTilde M ρp z) * a1 + F M 1 (sTilde M ρp z) * a2

/-- `cumExp (T+1) = cumExp T + termExp T` -/
lemma cumExp_termExp (Z : ℤ) (f : ℤ → ℝ) : ∀ T h z,
    cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) (T + 1) h z
      = cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) T h z
        + termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) f T h z := by
  intro T; induction T with
  | zero =>
    intro h z
    rw [cumExp_succ']
    simp only [cumExp, termExp]
    unfold Fbar
    split_ifs <;> ring
  | succ T ih =>
    intro h z
    rw [cumExp_succ' Z f (T + 1) h z, cumExp_succ' Z f T h z, termExp_succ Z f T h z]
    split_ifs <;> simp only [ih] <;> ring

/-- invariance: the chain started at `z ≥ L` with `L ≤ Z - 1` stays `≥ L` -/
lemma termExp_congr (Z L : ℤ) (hL : L ≤ Z - 1) (g g' : ℤ → ℝ) (hg : ∀ w, L ≤ w → g w = g' w) :
    ∀ T h z, L ≤ z → termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T h z
      = termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g' T h z := by
  intro T; induction T with
  | zero => intro h z hz; exact hg z hz
  | succ T ih =>
    intro h z hz
    rw [termExp_succ, termExp_succ]
    split_ifs with hzZ
    · exact ih _ _ (by omega)
    · rw [ih _ (z + 1) (by omega), ih _ (z - 1) (by omega)]

lemma termExp_mono (hM : M.Standing) (Z L : ℤ) (hL : L ≤ Z - 1) (g g' : ℤ → ℝ)
    (hg : ∀ w, L ≤ w → g w ≤ g' w) :
    ∀ T h z, L ≤ z → termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T h z
      ≤ termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g' T h z := by
  intro T; induction T with
  | zero => intro h z hz; exact hg z hz
  | succ T ih =>
    intro h z hz
    rw [termExp_succ, termExp_succ]
    split_ifs with hzZ
    · exact ih _ _ (by omega)
    · have hF := F_mem hM 1 (sTilde M ρp z)
      have hFb : 0 ≤ Fbar M 1 (sTilde M ρp z) := by unfold Fbar; linarith
      have a1 := mul_le_mul_of_nonneg_left (ih (h ++ [(1, .wait)]) (z + 1) (by omega)) hFb
      have a2 := mul_le_mul_of_nonneg_left (ih (h ++ [(-1, .wait)]) (z - 1) (by omega)) hF.1
      linarith

lemma termExp_affine (Z : ℤ) (a b : ℝ) (g : ℤ → ℝ) : ∀ T h z,
    termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w => a + b * g w) T h z
      = a + b * termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T h z := by
  intro T; induction T with
  | zero => intro h z; rfl
  | succ T ih =>
    intro h z
    rw [termExp_succ, termExp_succ, ih, ih, ih]
    unfold Fbar
    split_ifs <;> ring

/-- shift below the threshold -/
lemma termExp_shift (Z : ℤ) (g : ℤ → ℝ) : ∀ (k T : ℕ) (h : List (ℤ × Act)) (z : ℤ), z + (k : ℤ) ≤ Z →
    termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g (T + k) h z
      = termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) g T h (z + k) := by
  intro k; induction k with
  | zero => intro T h z _; simp
  | succ k ih =>
    intro T h z hz
    rw [show T + (k + 1) = (T + k) + 1 by ring, termExp_succ, if_pos (by omega),
      termExp_hist Z g _ _ h, ih T h (z + 1) (by push_cast at hz ⊢; omega)]
    congr 1; push_cast; ring

end SBL2Aux

namespace SBL2Aux2
open SpreadBetting.Inertial

lemma prod_Icc_reindex (q : ℤ → ℝ) (a n : ℤ) (han : a ≤ n) :
    ∏ m ∈ Finset.Icc a n, q m = ∏ j ∈ Finset.range ((n - a).toNat + 1), q (a + j) := by
  apply Finset.prod_nbij' (fun m => (m - a).toNat) (fun j => a + j)
  · intro m hm; simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at *; omega
  · intro j hm; simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at *; omega
  · intro m hm; simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at *; omega
  · intro j hm; simp
  · intro m hm; simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at *; congr 1; omega

lemma sum_Icc_le_tsum (g : ℕ → ℝ) (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k) (a b : ℤ) :
    ∑ n ∈ Finset.Icc a b, g (n - a).toNat ≤ ∑' k, g k := by
  have e : ∑ n ∈ Finset.Icc a b, g (n - a).toNat
      = ∑ k ∈ Finset.range (b - a + 1).toNat, g k := by
    apply Finset.sum_nbij' (fun m => (m - a).toNat) (fun j => a + j)
    · intro m hm; simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at *; omega
    · intro j hm; simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at *; omega
    · intro m hm; simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_range, Finset.coe_Icc, Finset.coe_range, Set.mem_Icc, Set.mem_Iio] at *; omega
    · intro j hm; simp
    · intro m hm; rfl
  rw [e]
  exact hg.sum_le_tsum _ (fun k _ => hg0 k)


open SBL2Aux SBFAux SBRedAux

variable {M : Market} {ρp : ℕ → ℝ}

lemma termExp_const (Z : ℤ) (U : ℝ) (T : ℕ) (h : List (ℤ × Act)) (z : ℤ) :
    termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun _ => U) T h z = U := by
  have := termExp_affine (M := M) (ρp := ρp) Z U 0 (fun _ => 0) T h z
  simp only [zero_mul, add_zero] at this
  exact this

lemma cumExp_eq_sum (Z : ℤ) (f : ℤ → ℝ) (z : ℤ) : ∀ T,
    cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) T [] z
      = ∑ t ∈ Finset.range T, termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) f t [] z := by
  intro T; induction T with
  | zero => simp [cumExp]
  | succ T ih => rw [cumExp_termExp, ih, Finset.sum_range_succ]

lemma indic_nonneg (P : Prop) : 0 ≤ indic P := by
  unfold indic; split_ifs <;> norm_num

lemma trans_abstract (hM : M.Standing) (Z Mx : ℤ) (ut : ℤ → ℝ) (U : ℝ)
    (hU : ∀ w, Z - 2 < w → ut w ≤ U)
    (hid : ∀ z : ℤ, Z - 2 < z → ∀ T : ℕ, 1 ≤ T →
        cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun z _ _ => indic (z ≤ Mx)) T [] z
          = termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) ut T [] z - ut z) :
    ∀ z, Tendsto (fun T => termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
      (fun w => indic (w ≤ Mx)) T [] z) atTop (𝓝 0) := by
  have main : ∀ z, Z - 1 ≤ z → Tendsto (fun T => termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
      (fun w => indic (w ≤ Mx)) T [] z) atTop (𝓝 0) := by
    intro z hz
    set P := fun T => termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
      (fun w => indic (w ≤ Mx)) T [] z with hP
    have hP0 : ∀ t, 0 ≤ P t := by
      intro t
      have := termExp_mono (M := M) (ρp := ρp) hM Z (Z - 1) (le_refl _) (fun _ => 0)
        (fun w => indic (w ≤ Mx)) (fun w _ => indic_nonneg _) t [] z hz
      rw [termExp_const] at this
      exact this
    have hsum : Summable P := by
      apply summable_of_sum_range_le (c := max 0 (U - ut z)) hP0
      intro T
      rcases Nat.eq_zero_or_pos T with hT | hT
      · subst hT; simp
      · have e := cumExp_eq_sum (M := M) (ρp := ρp) Z (fun w => indic (w ≤ Mx)) z T
        rw [hid z (by omega) T hT] at e
        have hle := termExp_mono (M := M) (ρp := ρp) hM Z (Z - 1) (le_refl _) ut (fun _ => U)
          (fun w hw => hU w (by omega)) T [] z hz
        rw [termExp_const] at hle
        have : ∑ t ∈ Finset.range T, P t = termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) ut T [] z
            - ut z := e.symm
        rw [this]
        exact le_trans (by linarith) (le_max_right _ _)
    exact hsum.tendsto_atTop_zero
  intro z
  by_cases hz : Z - 1 ≤ z
  · exact main z hz
  · set k := (Z - 1 - z).toNat with hk
    have hzk : z + (k : ℤ) = Z - 1 := by omega
    have h := main (z + k) (by omega)
    rw [← tendsto_add_atTop_iff_nat k]
    refine h.congr (fun T => ?_)
    rw [termExp_shift Z _ k T [] z (by omega)]


lemma ut_bound (Z Mx : ℤ) (hZM : Z - 2 < Mx) (ut : ℤ → ℝ)
    (hmono : StrictMonoOn ut {w : ℤ | Z - 2 < w})
    (hform : ∀ w, Mx + 2 ≤ w → ut w = (1 + ∑ n ∈ Finset.Icc (Mx + 2) (w - 1),
        ∏ m ∈ Finset.Icc (Mx + 2) n, (1 / 2 - rhoExt M ρp m) / (1 / 2 + rhoExt M ρp m)) * ut (Mx + 2))
    (hpos : 0 < ut (Mx + 2))
    (hq : ∀ m, 0 ≤ (1 / 2 - rhoExt M ρp m) / (1 / 2 + rhoExt M ρp m))
    (hs : Summable (Lam M ρp (Mx + 2))) :
    ∀ w, Z - 2 < w → ut w ≤ (1 + ∑' k, Lam M ρp (Mx + 2) k) * ut (Mx + 2) := by
  have hL0 : ∀ k, 0 ≤ Lam M ρp (Mx + 2) k := fun k => Finset.prod_nonneg (fun j _ => hq _)
  have htn : 0 ≤ ∑' k, Lam M ρp (Mx + 2) k := tsum_nonneg hL0
  intro w hw
  by_cases hw2 : Mx + 2 ≤ w
  · rw [hform w hw2]
    apply mul_le_mul_of_nonneg_right _ hpos.le
    have e : ∑ n ∈ Finset.Icc (Mx + 2) (w - 1), ∏ m ∈ Finset.Icc (Mx + 2) n,
        (1 / 2 - rhoExt M ρp m) / (1 / 2 + rhoExt M ρp m)
        = ∑ n ∈ Finset.Icc (Mx + 2) (w - 1), Lam M ρp (Mx + 2) (n - (Mx + 2)).toNat := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [prod_Icc_reindex _ _ _ hn.1]
      rfl
    rw [e]
    have := sum_Icc_le_tsum _ hs hL0 (Mx + 2) (w - 1)
    linarith
  · push_neg at hw2
    have h1 := hmono hw (show Z - 2 < Mx + 2 by omega) hw2
    have : ut (Mx + 2) ≤ (1 + ∑' k, Lam M ρp (Mx + 2) k) * ut (Mx + 2) := by nlinarith
    linarith

end SBL2Aux2

open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2 SBL3Aux SBL2Aux SBL2Aux2 in
theorem solution (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    (∀ z : ℤ, Tendsto (fun T : ℕ => cumExp M ρp 1 (xiStar M ρp 1)
        (fun z _ _ => jPlusZ M ρp 1 z * indic (belowZbar M ρp z)) T [] z) atTop
        (𝓝 (Jbar1 M ρp z))) ∧
    (∀ z : ℤ, Tendsto (fun T : ℕ => cumExp M ρp 0 (xiStar M ρp 0)
        (fun z _ _ => jMinusZ M ρp 0 z * indic (belowZbar M ρp (-z))) T [] z) atTop
        (𝓝 (Jbar0 M ρp z))) := by
  intro ρp
  have hc := hM.c_pos
  have hc1 := hM.c_lt_one
  have hm := hM.m0_lt_m1
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
  obtain ⟨-, -, -, -, hG13, -⟩ := lemma_G_1 M hM r hr0
  obtain ⟨⟨hGpos, hGneg⟩, -, -, hG23⟩ := lemma_G_2 M hM r hr0 hr2 hr1
  obtain ⟨hsv, -⟩ := lemma_H_1 M hM r hr0 hr
  have hP : P2 M ρp := (proposition_2 M hM ρp hsv.1).1
  have hFz : ∀ z, F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z := fun z => (hP z).2.2
  have hFbz : ∀ z, Fbar M 1 (sTilde M ρp z) = 1 / 2 + rhoExt M ρp z := by
    intro z; unfold Fbar; rw [hFz]; ring
  have hρ : ∀ z, 0 ≤ rhoExt M ρp z ∧ rhoExt M ρp z ≤ 1 / 2 := by
    intro z
    obtain ⟨hs, -, hF⟩ := hP z
    have h1 := F_mono hM 1 hs.2
    have h0 := F_mono hM 1 hs.1
    rw [F1_m1 hM] at h1
    have hα : 0 ≤ F M 1 M.m0 := (F_mem hM 1 M.m0).1
    constructor <;> linarith
  have hq : ∀ w, (1 / 2 - rhoExt M ρp w) / (1 / 2 + rhoExt M ρp w) * (1 / 2 + rhoExt M ρp w)
      = 1 / 2 - rhoExt M ρp w := by
    intro w; have h := hρ w; rw [div_mul_cancel₀]; linarith
  have hqnn : ∀ w, 0 ≤ (1 / 2 - rhoExt M ρp w) / (1 / 2 + rhoExt M ρp w) := by
    intro w; have := hρ w; apply div_nonneg <;> linarith
  -- hypotheses of Lemma L.2
  have hr0p : 0 < r0 M := by
    unfold r0
    have h1 := F_lt_of_lt hM 1 (y := M.m1) ⟨hm.le, le_refl _⟩
      (x := (M.m0 + M.m1) / 2) (by linarith)
    rw [F1_m1 hM] at h1
    exact inv_pos.2 (by linarith)
  have hαmid : alpha M < F M 1 ((M.m0 + M.m1) / 2) :=
    F_lt_of_lt hM 1 ⟨by linarith, by linarith⟩ (by linarith)
  have hinvr0 : 1 / r0 M = 1 / 2 - F M 1 ((M.m0 + M.m1) / 2) := by
    unfold r0; rw [one_div, inv_inv]
  have hρL2 : ∀ z : ℕ, 1 ≤ z → ρp z ∈ Set.Ioo 0 (1 / 2 - alpha M) := hsv.1
  have hbdd : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ, 1 ≤ z → ρp z ≤ 1 / 2 - alpha M - δ := by
    refine ⟨1 / 2 - alpha M - 1 / (r0 M + r), ?_, ?_⟩
    · have : 1 / (r0 M + r) < 1 / r0 M := one_div_lt_one_div_of_lt hr0p (by linarith)
      linarith
    · intro z hz
      have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
      show 1 / (r0 M + r * z) ≤ _
      have : 1 / (r0 M + r * z) ≤ 1 / (r0 M + r) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith
  have hne : (zbarSet M ρp).Nonempty := by
    by_cases hj' : 0 < (2 - M.c) * (1 / 2 - alpha M) - M.c / 2
    · exact (hGpos hj').1
    · have hnb := hGneg (not_lt.1 hj')
      by_contra hE
      rw [Set.not_nonempty_iff_eq_empty] at hE
      exact hnb (hE ▸ bddBelow_empty)
  have part1 : ∀ z : ℤ, Tendsto (fun T : ℕ => cumExp M ρp 1 (xiStar M ρp 1)
        (fun z _ _ => jPlusZ M ρp 1 z * indic (belowZbar M ρp z)) T [] z) atTop
        (𝓝 (Jbar1 M ρp z)) := by
    by_cases hb : BddBelow (zbarSet M ρp)
    swap
    · -- z̄ = -∞: nothing is ever below the threshold
      have hfalse : ∀ w, ¬ belowZbar M ρp w := by
        intro w hw
        rw [not_bddBelow_iff] at hb
        obtain ⟨v, hv, hvw⟩ := hb (w + 1)
        have := hw v hv
        omega
      have h0 : ∀ w, Jbar1 M ρp w = 0 := by
        intro w; unfold Jbar1; rw [if_neg (fun h => hb h.2)]
      intro z
      rw [h0]
      apply tendsto_const_nhds.congr
      intro T
      have e : (fun (w : ℤ) (_ : Act) (_ : ℤ) => jPlusZ M ρp 1 w * indic (belowZbar M ρp w))
          = (fun w _ _ => 0 * jPlusZ M ρp 1 w) := by
        funext w a d
        unfold indic; rw [if_neg (hfalse w)]; ring
      rw [e, SBL5Aux.cumExp_smul', zero_mul]
    · set Z := zbar M ρp with hZ
      have hbel : belowZbar M ρp = fun w => w < Z := by
        funext w; apply propext
        unfold belowZbar
        constructor
        · intro h; exact h _ (Int.csInf_mem hne hb)
        · intro h v hv; exact lt_of_lt_of_le h (csInf_le hb hv)
      have hx : xiStar M ρp 1 = threshStrat 1 (fun w => w < Z) := by unfold xiStar; rw [hbel]
      set a := jPlusZ M ρp 1 (Z - 1) with ha
      set Λ := Lam M ρp Z with hΛ
      set S : ℕ → ℝ := fun n => ∑' m : ℕ, Λ (n + m) with hSdef
      have hsum : Summable Λ := hG13 (by linarith) Z
      have hS : ∀ n, S n = Λ n + S (n + 1) := by
        intro n
        have hs : Summable (fun m => Λ (n + m)) := by
          have := (summable_nat_add_iff n).2 hsum
          exact this.congr (fun m => by rw [add_comm])
        simp only [hSdef]
        rw [hs.tsum_eq_zero_add]
        simp only [add_zero]
        congr 1
        apply tsum_congr; intro m; congr 1; ring
      have hΛ0 : Λ 0 = (1 / 2 - rhoExt M ρp Z) / (1 / 2 + rhoExt M ρp Z) := Lam_zero Z
      have hΛs : ∀ n : ℕ, Λ (n + 1) = Λ n * ((1 / 2 - rhoExt M ρp (Z + (n + 1 : ℕ)))
          / (1 / 2 + rhoExt M ρp (Z + (n + 1 : ℕ)))) := fun n => Lam_succ Z n
      have hΛnn : ∀ n, 0 ≤ Λ n := fun n => Finset.prod_nonneg (fun j _ => hqnn _)
      have hSnn : ∀ n, 0 ≤ S n := fun n => tsum_nonneg (fun m => hΛnn _)
      have hup : ∀ n : ℕ, Jbar1 M ρp (Z + n) = a * S n := fun n => Jbar1_up hne hb n
      have hdown : ∀ m : ℕ, Jbar1 M ρp (Z - m) = a * S 0
          + ∑ k ∈ Finset.Icc 1 m, jPlusZ M ρp 1 (Z - k) := by
        intro m; rw [Jbar1_down hne hb m]; simp only [hSdef, zero_add]; rfl
      have hjpos : ∀ w, w < Z → 0 < jPlusZ M ρp 1 w := by
        intro w hw; apply hG23; rw [hbel]; exact hw
      have hapos : 0 < a := hjpos _ (by omega)
      -- the one-step relations (G.12)
      set f : ℤ → ℝ := fun w => jPlusZ M ρp 1 w * indic (w < Z) with hf
      have hg1 : ∀ w, w < Z → Jbar1 M ρp w = f w + Jbar1 M ρp (w + 1) := by
        intro w hw
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, w = Z - ((m + 1 : ℕ) : ℤ) := ⟨(Z - w - 1).toNat, by omega⟩
        have eup : Z - ((m + 1 : ℕ) : ℤ) + 1 = Z - (m : ℤ) := by push_cast; ring
        rw [eup, hdown, hdown, Finset.sum_Icc_succ_top (by omega)]
        simp only [hf, indic, if_pos hw]
        ring
      have hg2 : ∀ w, Z ≤ w → Jbar1 M ρp w = f w + (Fbar M 1 (sTilde M ρp w) * Jbar1 M ρp (w + 1)
          + F M 1 (sTilde M ρp w) * Jbar1 M ρp (w - 1)) := by
        intro w hw
        have hf0 : f w = 0 := by simp only [hf, indic, if_neg (not_lt.2 hw)]; ring
        rw [hf0, zero_add]
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = Z + n := ⟨(w - Z).toNat, by omega⟩
        have e1 : Z + n + 1 = Z + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [hFz, hFbz, e1, hup, hup]
        rcases n with _ | k
        · have e2 : Z + ((0 : ℕ) : ℤ) - 1 = Z - ((1 : ℕ) : ℤ) := by simp
          rw [e2, hdown]
          simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one]
          rw [← ha]
          have h0 := hS 0
          have hq0 := hq Z
          rw [← hΛ0] at hq0
          simp only [Nat.cast_zero, add_zero, zero_add]
          linear_combination a * hq0 + a * (1 / 2 + rhoExt M ρp Z) * h0
        · have e2 : Z + ((k + 1 : ℕ) : ℤ) - 1 = Z + k := by push_cast; ring
          rw [e2, hup]
          have h1 := hS (k + 1)
          have h0 := hS k
          have hk := hΛs k
          have hqw := hq (Z + ((k + 1 : ℕ) : ℤ))
          linear_combination (a * (1 / 2 + rhoExt M ρp (Z + ((k + 1 : ℕ) : ℤ)))) * h1
            + (-a * (1 / 2 - rhoExt M ρp (Z + ((k + 1 : ℕ) : ℤ)))) * h0
            + (a * (1 / 2 + rhoExt M ρp (Z + ((k + 1 : ℕ) : ℤ)))) * hk + (a * Λ k) * hqw
      have hdyn := dynkin (M := M) (ρp := ρp) hM Z f (Jbar1 M ρp) hg1 hg2
      -- nonnegativity of J̄
      have hJnn : ∀ w, 0 ≤ Jbar1 M ρp w := by
        intro w
        by_cases hw : Z ≤ w
        · obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = Z + n := ⟨(w - Z).toNat, by omega⟩
          rw [hup]; exact mul_nonneg hapos.le (hSnn n)
        · obtain ⟨m, rfl⟩ : ∃ m : ℕ, w = Z - m := ⟨(Z - w).toNat, by omega⟩
          rw [hdown]
          apply add_nonneg (mul_nonneg hapos.le (hSnn 0))
          apply Finset.sum_nonneg; intro k hk
          exact (hjpos _ (by rw [Finset.mem_Icc] at hk; omega)).le
      -- tails of S vanish
      have hStail : Tendsto S atTop (𝓝 0) := by
        have := tendsto_sum_nat_add Λ
        refine this.congr (fun n => ?_)
        simp only [hSdef]; apply tsum_congr; intro m; rw [add_comm]
      intro z
      -- E J̄(Z_{T+1}) → 0
      have hterm : Tendsto (fun T => termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
          (Jbar1 M ρp) T [] z) atTop (𝓝 0) := by
        set L := min z (Z - 1) with hLdef
        have hLZ : L ≤ Z - 1 := min_le_right _ _
        have hLz : L ≤ z := min_le_left _ _
        rw [Metric.tendsto_atTop]
        intro ε hε
        have hev : ∀ᶠ n in atTop, a * S n < ε / 2 := by
          have : Tendsto (fun n => a * S n) atTop (𝓝 0) := by
            simpa using hStail.const_mul a
          exact (tendsto_order.1 this).2 _ (by linarith)
        obtain ⟨N, hN⟩ := eventually_atTop.1 hev
        set Mε : ℤ := Z + N with hMε
        set B : ℝ := ∑ w ∈ Finset.Icc L Mε, Jbar1 M ρp w with hB
        have hB0 : 0 ≤ B := Finset.sum_nonneg (fun w _ => hJnn w)
        have hdom : ∀ w, L ≤ w → Jbar1 M ρp w ≤ ε / 2 + B * indic (w ≤ Mε) := by
          intro w hw
          by_cases hwM : w ≤ Mε
          · have : Jbar1 M ρp w ≤ B :=
              Finset.single_le_sum (fun v _ => hJnn v) (Finset.mem_Icc.2 ⟨hw, hwM⟩)
            unfold indic; rw [if_pos hwM]; linarith
          · obtain ⟨n, hn⟩ : ∃ n : ℕ, w = Z + n := ⟨(w - Z).toNat, by omega⟩
            have hnN : N ≤ n := by omega
            unfold indic; rw [if_neg hwM, hn, hup]
            have := hN n hnN
            linarith
        -- transience from Lemma L.2
        have hL2 := (lemma_L_2 M hM ρp hρL2 hbdd).1 Z Mε (by omega)
        obtain ⟨-, hβ, hmono, hid⟩ := hL2
        have hPT : Tendsto (fun T => termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
            (fun w => indic (w ≤ Mε)) T [] z) atTop (𝓝 0) := by
          refine trans_abstract (M := M) (ρp := ρp) hM Z Mε _ _
            (ut_bound Z Mε (by omega) _ hmono ?_ ?_ hqnn (hG13 (by linarith) _)) hid z
          · intro w hw
            beta_reduce
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega : ¬ Mε + 2 ≤ Mε),
              if_neg (by omega : Mε + 2 ≠ Mε + 1),
              Finset.Icc_eq_empty (show ¬ (Mε + 2 ≤ Mε + 2 - 1) by omega)]
            simp
          · beta_reduce
            rw [if_neg (by omega : ¬ Mε + 2 ≤ Mε), if_neg (by omega : Mε + 2 ≠ Mε + 1),
              Finset.Icc_eq_empty (show ¬ (Mε + 2 ≤ Mε + 2 - 1) by omega)]
            simpa using hβ
        -- conclude
        have hbound : ∀ T, termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (Jbar1 M ρp) T [] z
            ≤ ε / 2 + B * termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
              (fun w => indic (w ≤ Mε)) T [] z := by
          intro T
          rw [← termExp_affine]
          exact termExp_mono hM Z L hLZ _ _ hdom T [] z hLz
        have hlow : ∀ T, 0 ≤ termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (Jbar1 M ρp) T [] z := by
          intro T
          have := termExp_mono (M := M) (ρp := ρp) hM Z L hLZ (fun _ => 0) (Jbar1 M ρp)
            (fun w _ => hJnn w) T [] z hLz
          rwa [termExp_const] at this
        have hev2 : ∀ᶠ T in atTop, B * termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
              (fun w => indic (w ≤ Mε)) T [] z < ε / 2 := by
          have : Tendsto (fun T => B * termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
              (fun w => indic (w ≤ Mε)) T [] z) atTop (𝓝 0) := by
            simpa using hPT.const_mul B
          exact (tendsto_order.1 this).2 _ (by linarith)
        obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev2
        refine ⟨T0, fun T hT => ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (hlow T)]
        have := hbound T
        have := hT0 T hT
        linarith
      rw [hx, hbel]
      have hconv : Tendsto (fun T => Jbar1 M ρp z - termExp M ρp 1 (threshStrat 1 (fun w => w < Z))
          (Jbar1 M ρp) T [] z) atTop (𝓝 (Jbar1 M ρp z - 0)) := tendsto_const_nhds.sub hterm
      rw [sub_zero] at hconv
      refine hconv.congr (fun T => ?_)
      have := hdyn T [] z
      simp only [hf] at this
      linarith
  refine ⟨part1, ?_⟩
  intro z
  have h := part1 (-z)
  unfold Jbar0
  have hjm0 : ∀ w, jMinusZ M ρp 0 (-w) = jPlusZ M ρp 1 w := by
    intro w
    obtain ⟨f1, f2⟩ := Fbar0_eq hP (-w)
    rw [neg_neg] at f1 f2
    unfold jMinusZ jPlusZ jMinus jPlus
    rw [f2]
    unfold Fbar at f1 ⊢
    rw [f1]
  refine h.congr (fun T => ?_)
  unfold xiStar
  rw [cumExp_reflect hP (belowZbar M ρp)
    (fun w => jMinusZ M ρp 0 w * indic (belowZbar M ρp (-w))) T [] [] z]
  congr 1
  funext w a d
  rw [neg_neg, hjm0 w]
