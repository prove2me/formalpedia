-- Prove2me | solution 1 for SpreadBetting.Inertial.lemma_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:09:34.660301+00:00
-- url     : https://prove2.me/submissions/109bcee5-adb3-41db-a556-b320383768ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain
import Theorems.Thm_SpreadBetting_Inertial_lemma_G_1
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
open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2 SBL3Aux in
theorem solution (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    (∀ z : ℤ, Jbar1 M ρp z = max (max (jPlusZ M ρp 1 z + Jbar1 M ρp (z + 1))
        (jMinusZ M ρp 1 z + Jbar1 M ρp (z - 1)))
      (Fbar M 1 (sTilde M ρp z) * Jbar1 M ρp (z + 1) + F M 1 (sTilde M ρp z) * Jbar1 M ρp (z - 1))) ∧
    (∀ z : ℤ, Jbar0 M ρp z = max (max (jPlusZ M ρp 0 z + Jbar0 M ρp (z + 1))
        (jMinusZ M ρp 0 z + Jbar0 M ρp (z - 1)))
      (Fbar M 0 (sTilde M ρp z) * Jbar0 M ρp (z + 1) + F M 0 (sTilde M ρp z) * Jbar0 M ρp (z - 1))) := by
  intro ρp
  have hc := hM.c_pos
  have hc1 := hM.c_lt_one
  have hr2 : r < 2 := by
    have : rbar M ≤ 2 := by unfold rbar; split_ifs <;> exact min_le_left _ _
    linarith
  have hrb0 : r < rbar0 M := by
    have : rbar M ≤ rbar0 M := by
      unfold rbar; split_ifs
      · exact le_trans (min_le_right _ _) (min_le_left _ _)
      · exact min_le_right _ _
    linarith
  have hr1 : (r : EReal) < rbar1 M := by
    unfold rbar1
    unfold rbar at hr
    split_ifs with hz
    · rw [if_pos hz] at hr
      exact EReal.coe_lt_coe_iff.2 (lt_of_lt_of_le hr
        (le_trans (min_le_right _ _) (min_le_right _ _)))
    · exact EReal.coe_lt_top r
  obtain ⟨-, -, -, -, hG13, hG14⟩ := lemma_G_1 M hM r hr0
  obtain ⟨⟨hGpos, hGneg⟩, hG22, -, -⟩ := lemma_G_2 M hM r hr0 hr2 hr1
  obtain ⟨hsv, -⟩ := lemma_H_1 M hM r hr0 hr
  have hP : P2 M ρp := (proposition_2 M hM ρp hsv.1).1
  have hFz : ∀ z, F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z := fun z => (hP z).2.2
  have hFbz : ∀ z, Fbar M 1 (sTilde M ρp z) = 1 / 2 + rhoExt M ρp z := by
    intro z; unfold Fbar; rw [hFz]; ring
  have hρ : ∀ z, 0 ≤ rhoExt M ρp z ∧ rhoExt M ρp z ≤ 1 / 2 - alpha M := by
    intro z
    obtain ⟨hs, -, hF⟩ := hP z
    have h1 := F_mono hM 1 hs.2
    have h0 := F_mono hM 1 hs.1
    rw [F1_m1 hM] at h1
    rw [F1_m0] at h0
    constructor <;> linarith
  have hα : 0 ≤ alpha M := (F_mem hM 1 M.m0).1
  have hj : ∀ z, jPlusZ M ρp 1 z = (2 - M.c) * rhoExt M ρp z - M.c / 2 := by
    intro z; unfold jPlusZ jPlus; rw [hFz, hFbz]; ring
  have hjm : ∀ z, jMinusZ M ρp 1 z = -(2 - M.c) * rhoExt M ρp z - M.c / 2 := by
    intro z; unfold jMinusZ jMinus; rw [hFz, hFbz]; ring
  have hne : (zbarSet M ρp).Nonempty := by
    by_cases hj' : 0 < (2 - M.c) * (1 / 2 - alpha M) - M.c / 2
    · exact (hGpos hj').1
    · have hnb := hGneg (not_lt.1 hj')
      by_contra hE
      rw [Set.not_nonempty_iff_eq_empty] at hE
      exact hnb (hE ▸ bddBelow_empty)
  have part1 : ∀ z : ℤ, Jbar1 M ρp z = max (max (jPlusZ M ρp 1 z + Jbar1 M ρp (z + 1))
        (jMinusZ M ρp 1 z + Jbar1 M ρp (z - 1)))
      (Fbar M 1 (sTilde M ρp z) * Jbar1 M ρp (z + 1) + F M 1 (sTilde M ρp z) * Jbar1 M ρp (z - 1)) := by
    intro z
    by_cases hb : BddBelow (zbarSet M ρp)
    · obtain ⟨-, hH14a, hH14b⟩ := (hG14 hrb0 z)
      refine bellman1 M.c hc hc1 hne hb (fun w => ⟨(hρ w).1, by linarith [(hρ w).2]⟩) hj hjm hFz hFbz
        (hG22 hne hb) (fun w => (hG14 hrb0 w).2.1) (fun w => (hG14 hrb0 w).2.2)
        (hG13 (by linarith) _) z
    · have h0 : ∀ w, Jbar1 M ρp w = 0 := by
        intro w; unfold Jbar1; rw [if_neg (fun h => hb h.2)]
      have hjp : (2 - M.c) * (1 / 2 - alpha M) - M.c / 2 ≤ 0 := by
        by_contra h; push_neg at h; exact hb (hGpos h).2
      rw [h0, h0, h0, hj, hjm]
      have := hρ z
      have e1 : (2 - M.c) * rhoExt M ρp z - M.c / 2 + 0 ≤ 0 := by nlinarith
      have e2 : -(2 - M.c) * rhoExt M ρp z - M.c / 2 + 0 ≤ 0 := by nlinarith
      simp only [mul_zero, add_zero] at e1 e2 ⊢
      rw [max_eq_right (max_le e1 e2)]
  refine ⟨part1, ?_⟩
  intro z
  have h := part1 (-z)
  obtain ⟨f1, f2⟩ := Fbar0_eq hP z
  have ej : jPlusZ M ρp 0 z = jMinusZ M ρp 1 (-z) := by
    unfold jPlusZ jMinusZ jPlus jMinus; rw [f1, f2]
  have ejm : jMinusZ M ρp 0 z = jPlusZ M ρp 1 (-z) := by
    unfold jPlusZ jMinusZ jPlus jMinus; rw [f1, f2]
  have eJ1 : Jbar0 M ρp (z + 1) = Jbar1 M ρp (-z - 1) := by unfold Jbar0; congr 1; ring
  have eJ2 : Jbar0 M ρp (z - 1) = Jbar1 M ρp (-z + 1) := by unfold Jbar0; congr 1; ring
  have eJ0 : Jbar0 M ρp z = Jbar1 M ρp (-z) := rfl
  rw [eJ0, eJ1, eJ2, ej, ejm, f1, f2, h, max_comm (jMinusZ M ρp 1 (-z) + _), add_comm (F M 1 _ * _)]
