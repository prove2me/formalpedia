-- Prove2me | solution 1 for SpreadBetting.Inertial.lemma_L_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:32:53.630995+00:00
-- url     : https://prove2.me/submissions/d2e9fb88-f260-43e2-93c4-552e29a3f8f5

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain
import Theorems.Thm_SpreadBetting_Inertial_proposition_2

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

namespace SBLL2Aux
open SpreadBetting.Inertial SBFAux SBRedAux SBL2Aux

variable {M : Market} {ρp : ℕ → ℝ}

lemma sum_Icc_left {f : ℤ → ℝ} {a b : ℤ} (h : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, f n = f a + ∑ n ∈ Finset.Icc (a + 1) b, f n := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, Finset.sum_insert (by simp)]

lemma prod_Icc_left {f : ℤ → ℝ} {a b : ℤ} (h : a ≤ b) :
    ∏ n ∈ Finset.Icc a b, f n = f a * ∏ n ∈ Finset.Icc (a + 1) b, f n := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, Finset.prod_insert (by simp)]

lemma sum_Icc_right {f : ℤ → ℝ} {a b : ℤ} (h : a ≤ b + 1) :
    ∑ n ∈ Finset.Icc a (b + 1), f n = ∑ n ∈ Finset.Icc a b, f n + f (b + 1) := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one h, Finset.sum_insert (by simp), add_comm]

lemma prod_Icc_right {f : ℤ → ℝ} {a b : ℤ} (h : a ≤ b + 1) :
    ∏ n ∈ Finset.Icc a (b + 1), f n = (∏ n ∈ Finset.Icc a b, f n) * f (b + 1) := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one h, Finset.prod_insert (by simp), mul_comm]

/-- Dynkin identity on the invariant set `{z ≥ L}` -/
lemma dynkin_on (hM : M.Standing) (Z L : ℤ) (hL : L ≤ Z - 1) (f J : ℤ → ℝ)
    (h1 : ∀ z, L ≤ z → z < Z → J z = f z + J (z + 1))
    (h2 : ∀ z, Z ≤ z → J z = f z + (Fbar M 1 (sTilde M ρp z) * J (z + 1)
        + F M 1 (sTilde M ρp z) * J (z - 1))) :
    ∀ T h z, L ≤ z → cumExp M ρp 1 (threshStrat 1 (fun w => w < Z)) (fun w _ _ => f w) T h z
      + termExp M ρp 1 (threshStrat 1 (fun w => w < Z)) J T h z = J z := by
  intro T; induction T with
  | zero => intro h z _; simp [cumExp, termExp]
  | succ T ih =>
    intro h z hz
    rw [cumExp_succ', termExp_succ]
    split_ifs with hzZ
    · have := ih (h ++ [(1, .pos)]) (z + 1) (by omega); rw [h1 z hz hzZ]; linarith
    · have a1 := ih (h ++ [(1, .wait)]) (z + 1) (by omega)
      have a2 := ih (h ++ [(-1, .wait)]) (z - 1) (by omega)
      rw [h2 z (not_lt.1 hzZ)]
      linear_combination Fbar M 1 (sTilde M ρp z) * a1 + F M 1 (sTilde M ρp z) * a2

lemma strictMonoOn_of_succ (u : ℤ → ℝ) (L : ℤ) (h : ∀ w, L < w → u (w - 1) < u w) :
    StrictMonoOn u {z : ℤ | L ≤ z} := by
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + (k + 1 : ℕ) := ⟨(b - a - 1).toNat, by omega⟩
  induction k with
  | zero => have := h (a + 1) (by omega); simpa using this
  | succ k ih =>
    have h1 := ih (by omega) (by push_cast; omega)
    have h2 := h (a + ((k + 1 + 1 : ℕ) : ℤ)) (by push_cast; omega)
    have e : a + ((k + 1 + 1 : ℕ) : ℤ) - 1 = a + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at h2
    linarith

end SBLL2Aux

namespace SBLL2Fin
open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2 SBL2Aux SBLL2Aux

variable {M : Market} {ρp : ℕ → ℝ}

lemma alpha_pos (hM : M.Standing) : 0 < alpha M := by
  unfold alpha F med
  simp only [Fin.isValue, one_ne_zero, if_false]
  have h1 := hM.sL_lt_m0
  have h2 := hM.m0_lt_m1
  have hlt := Feps_lt hM (-(M.m1 - M.sL)) (M.m0 - M.m1) (by linarith) (by
    intro t ht
    apply hM.feps_pos
    have : M.m1 - M.sL ≤ max (M.sH - M.m0) (M.m1 - M.sL) := le_max_right _ _
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  have := Feps_nonneg hM (-(M.m1 - M.sL))
  linarith

lemma rho_strict (hM : M.Standing) (hP : P2 M ρp)
    (hρ : ∀ z : ℕ, 1 ≤ z → ρp z ∈ Set.Ioo 0 (1 / 2 - alpha M)) (z : ℤ) :
    0 < rhoExt M ρp z ∧ rhoExt M ρp z < 1 / 2 := by
  have hα := alpha_pos hM
  have hm := hM.m0_lt_m1
  obtain ⟨hs, h0, hF⟩ := hP z
  have hlow : alpha M ≤ F M 1 (sTilde M ρp z) := F_mono hM 1 hs.1
  refine ⟨?_, by linarith⟩
  -- strictly below m1
  have hlt : sTilde M ρp z < M.m1 := by
    rcases lt_trichotomy 0 z with hz | hz | hz
    · -- z > 0: F_1(s̃ z) = 1/2 - ρp > ... < 1/2
      have hpos := (hρ z.toNat (by omega)).1
      have : rhoExt M ρp z = ρp z.toNat := by rw [rhoExt, if_pos hz]
      by_contra hc
      have : sTilde M ρp z = M.m1 := le_antisymm hs.2 (not_lt.1 hc)
      rw [this, F1_m1 hM] at hF
      linarith
    · subst hz; simp only [sTilde, lt_irrefl, if_false, if_true]; linarith
    · have hpz : 0 < -z := by omega
      have h1 := (hP (-z)).2.1
      rw [neg_neg] at h1
      have hval : rhoExt M ρp (-z) = ρp (-z).toNat := by rw [rhoExt, if_pos hpz]
      have hlt2 := (hρ (-z).toNat (by omega)).2
      by_contra hc
      have : sTilde M ρp z = M.m1 := le_antisymm hs.2 (not_lt.1 hc)
      rw [this, F0_m1 hM, hval] at h1
      linarith
  have := F_lt_of_lt hM 1 (y := M.m1) ⟨hm.le, le_refl _⟩ hlt
  rw [F1_m1 hM] at this
  linarith

end SBLL2Fin

namespace SBLL2Fin2
open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2 SBL2Aux SBLL2Aux

variable {M : Market} {ρp : ℕ → ℝ}

lemma L2_fin (hM : M.Standing)
    (hρ01 : ∀ z, 0 < rhoExt M ρp z ∧ rhoExt M ρp z < 1 / 2)
    (hF : ∀ z, F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z)
    (Zb Mx : ℤ) (hZM : Zb - 2 < Mx) :
      let ρ := rhoExt M ρp
      let q : ℤ → ℝ := fun m => (1 / 2 - ρ m) / (1 / 2 + ρ m)
      let βt : ℝ := -(∏ m ∈ Finset.Icc Zb Mx, q m)
        - ∑ k ∈ Finset.Icc Zb Mx, (1 / (1 / 2 - ρ k)) * ∏ m ∈ Finset.Icc k Mx, q m
      let β : ℝ := -q (Mx + 1) * βt
      let ut : ℤ → ℝ := fun z =>
        if z ≤ Mx then
          (1 + ∑ n ∈ Finset.Icc (z + 1) Mx,
              ∏ m ∈ Finset.Icc n Mx, (1 / 2 + ρ m) / (1 / 2 - ρ m)) * βt
            + ∑ n ∈ Finset.Icc (z + 1) Mx, ∑ k ∈ Finset.Icc n Mx,
                (1 / (1 / 2 + ρ k)) * ∏ m ∈ Finset.Icc n k, (1 / 2 + ρ m) / (1 / 2 - ρ m)
        else if z = Mx + 1 then 0
        else (1 + ∑ n ∈ Finset.Icc (Mx + 2) (z - 1), ∏ m ∈ Finset.Icc (Mx + 2) n, q m) * β
      let ξ := threshStrat 1 (fun z => z < Zb)
      βt < 0 ∧ 0 < β ∧ StrictMonoOn ut {z : ℤ | Zb - 2 < z} ∧
      ∀ z : ℤ, Zb - 2 < z → ∀ T : ℕ, 1 ≤ T →
        cumExp M ρp 1 ξ (fun z _ _ => indic (z ≤ Mx)) T [] z
          = termExp M ρp 1 ξ ut T [] z - ut z := by
  intro ρ q βt β ut ξ
  set p : ℤ → ℝ := fun m => (1 / 2 + ρ m) / (1 / 2 - ρ m) with hp
  have hpos := fun m => (hρ01 m).1
  have hlt := fun m => (hρ01 m).2
  have hqpos : ∀ m, 0 < q m := fun m => div_pos (by linarith [hlt m]) (by linarith [hpos m])
  have hppos : ∀ m, 0 < p m := fun m => div_pos (by linarith [hpos m]) (by linarith [hlt m])
  have hpq : ∀ m, p m * q m = 1 := by
    intro m; simp only [hp, q]; have := hpos m; have := hlt m
    have : 1 + 2 * ρ m ≠ 0 := by linarith
    have : 1 - 2 * ρ m ≠ 0 := by linarith
    field_simp
  have hpm : ∀ m, (1 / 2 - ρ m) * p m = 1 / 2 + ρ m := by
    intro m; simp only [hp]; have := hlt m
    have : 1 - 2 * ρ m ≠ 0 := by linarith
    field_simp
  have hqm : ∀ m, (1 / 2 + ρ m) * q m = 1 / 2 - ρ m := by
    intro m; simp only [q]; have := hpos m
    have : 1 + 2 * ρ m ≠ 0 := by linarith
    field_simp
  -- the building blocks
  set A : ℤ → ℝ := fun z => ∏ m ∈ Finset.Icc z Mx, p m with hA
  set Q : ℤ → ℝ := fun z => ∏ m ∈ Finset.Icc z Mx, q m with hQ
  set E : ℤ → ℝ := fun z => ∑ k ∈ Finset.Icc z Mx, (1 / (1 / 2 + ρ k)) * ∏ m ∈ Finset.Icc z k, p m
    with hE
  set W : ℤ → ℝ := fun z => ∑ k ∈ Finset.Icc z Mx, (1 / (1 / 2 - ρ k)) * Q k with hW
  set B : ℤ → ℝ := fun z => ∑ n ∈ Finset.Icc z Mx, A n with hB
  set C : ℤ → ℝ := fun z => ∑ n ∈ Finset.Icc z Mx, E n with hC
  have eA : ∀ z, z ≤ Mx → A z = p z * A (z + 1) := fun z hz => prod_Icc_left hz
  have eQ : ∀ z, z ≤ Mx → Q z = q z * Q (z + 1) := fun z hz => prod_Icc_left hz
  have eB : ∀ z, z ≤ Mx → B z = A z + B (z + 1) := fun z hz => sum_Icc_left hz
  have eC : ∀ z, z ≤ Mx → C z = E z + C (z + 1) := fun z hz => sum_Icc_left hz
  have eW : ∀ z, z ≤ Mx → W z = 1 / (1 / 2 - ρ z) * Q z + W (z + 1) := fun z hz => sum_Icc_left hz
  have eE : ∀ z, z ≤ Mx → E z = p z * (1 / (1 / 2 + ρ z) + E (z + 1)) := by
    intro z hz
    simp only [hE]
    rw [sum_Icc_left hz, Finset.Icc_self, Finset.prod_singleton, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [prod_Icc_left (show z ≤ k by omega)]
      ring
  have top : A (Mx + 1) = 1 ∧ Q (Mx + 1) = 1 ∧ E (Mx + 1) = 0 ∧ W (Mx + 1) = 0 ∧
      B (Mx + 1) = 0 ∧ C (Mx + 1) = 0 := by
    have h : Finset.Icc (Mx + 1) Mx = ∅ := Finset.Icc_eq_empty (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hA, hQ, hE, hW, hB, hC, h]
  -- A Q = 1 and A W = E, by downward induction
  have hAQW : ∀ k : ℕ, A (Mx + 1 - k) * Q (Mx + 1 - k) = 1 ∧
      A (Mx + 1 - k) * W (Mx + 1 - k) = E (Mx + 1 - k) := by
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero, sub_zero, top.1, top.2.1, top.2.2.1, top.2.2.2.1]; norm_num
    | succ k ih =>
      set z := Mx + 1 - ((k + 1 : ℕ) : ℤ) with hz
      have hz1 : z + 1 = Mx + 1 - (k : ℤ) := by rw [hz]; push_cast; ring
      have hzM : z ≤ Mx := by rw [hz]; push_cast; omega
      rw [← hz1] at ih
      obtain ⟨i1, i2⟩ := ih
      rw [eA z hzM, eQ z hzM, eW z hzM, eE z hzM]
      have h1 := hpq z
      have h2 := hpm z
      have hl := hlt z
      have hp' := hpos z
      constructor
      · calc p z * A (z + 1) * (q z * Q (z + 1)) = (p z * q z) * (A (z + 1) * Q (z + 1)) := by ring
          _ = 1 := by rw [h1, i1, one_mul]
      · rw [eQ z hzM]
        have e1 : 1 / (1 / 2 - ρ z) = p z * (1 / (1 / 2 + ρ z)) := by
          simp only [hp]
          have : 1 + 2 * ρ z ≠ 0 := by linarith
          have : 1 - 2 * ρ z ≠ 0 := by linarith
          field_simp
        calc p z * A (z + 1) * (1 / (1 / 2 - ρ z) * (q z * Q (z + 1)) + W (z + 1))
            = 1 / (1 / 2 - ρ z) * ((p z * q z) * (A (z + 1) * Q (z + 1)))
              + p z * (A (z + 1) * W (z + 1)) := by ring
          _ = p z * (1 / (1 / 2 + ρ z) + E (z + 1)) := by rw [h1, i1, i2, e1]; ring
  -- values of ut
  have hβt : βt = -Q Zb - W Zb := rfl
  have hβ : β = -q (Mx + 1) * βt := rfl
  have ut_low : ∀ z, z ≤ Mx → ut z = (1 + B (z + 1)) * βt + C (z + 1) := by
    intro z hz; simp only [ut, if_pos hz]; rfl
  have ut_mid : ut (Mx + 1) = 0 := by simp only [ut, if_neg (by omega : ¬ Mx + 1 ≤ Mx)]; simp
  set Q' : ℤ → ℝ := fun n => ∏ m ∈ Finset.Icc (Mx + 2) n, q m with hQ'
  set G : ℤ → ℝ := fun z => ∑ n ∈ Finset.Icc (Mx + 2) (z - 1), Q' n with hG
  have ut_high : ∀ z, Mx + 2 ≤ z → ut z = (1 + G z) * β := by
    intro z hz
    simp only [ut, if_neg (by omega : ¬ z ≤ Mx), if_neg (by omega : z ≠ Mx + 1)]
    rfl
  have hQ'1 : Q' (Mx + 1) = 1 := by simp [hQ', Finset.Icc_eq_empty (show ¬ (Mx + 2 ≤ Mx + 1) by omega)]
  have eQ' : ∀ z, Mx + 2 ≤ z → Q' z = Q' (z - 1) * q z := by
    intro z hz
    have := prod_Icc_right (f := q) (a := Mx + 2) (b := z - 1) (by omega)
    rw [sub_add_cancel] at this
    exact this
  have hUp : ∀ z, Mx + 2 ≤ z → ut z - ut (z - 1) = Q' (z - 1) * β := by
    intro z hz
    rcases eq_or_lt_of_le hz with h | h
    · subst h
      rw [ut_high _ le_rfl, show Mx + 2 - 1 = Mx + 1 by ring, ut_mid, hQ'1]
      have : G (Mx + 2) = 0 := by
        simp [hG, Finset.Icc_eq_empty (show ¬ (Mx + 2 ≤ Mx + 2 - 1) by omega)]
      rw [this]; ring
    · rw [ut_high z hz, ut_high (z - 1) (by omega)]
      have : G z = G (z - 1) + Q' (z - 1) := by
        simp only [hG]
        have := sum_Icc_right (f := Q') (a := Mx + 2) (b := z - 1 - 1) (by omega)
        rw [show z - 1 - 1 + 1 = z - 1 by ring] at this
        exact this
      rw [this]; ring
  -- D and its recursion
  set D : ℤ → ℝ := fun z => -(A z * βt + E z) with hDdef
  have hD : ∀ z, z ≤ Mx + 1 → ut z - ut (z - 1) = D z := by
    intro z hz
    rcases eq_or_lt_of_le hz with h | h
    · subst h
      rw [ut_mid, show Mx + 1 - 1 = Mx by ring, ut_low Mx le_rfl]
      simp only [hDdef, top.1, top.2.2.1, top.2.2.2.2.1, top.2.2.2.2.2]
      ring
    · rw [ut_low z (by omega), ut_low (z - 1) (by omega), sub_add_cancel,
        eB z (by omega), eC z (by omega)]
      simp only [hDdef]; ring
  have hDrec : ∀ z, z ≤ Mx → (1 / 2 - ρ z) * D z = (1 / 2 + ρ z) * D (z + 1) - 1 := by
    intro z hz
    simp only [hDdef]
    rw [eA z hz, eE z hz]
    have h1 := hpm z
    have hp' := hpos z
    have e : (1 / 2 - ρ z) * (p z * (1 / (1 / 2 + ρ z))) = 1 := by
      rw [← mul_assoc, h1]
      have : 1 + 2 * ρ z ≠ 0 := by linarith
      field_simp
    linear_combination (-(A (z + 1) * βt + E (z + 1))) * h1 - e
  have hDZb : D Zb = 1 := by
    obtain ⟨i1, i2⟩ := hAQW (Mx + 1 - Zb).toNat
    have e : Mx + 1 - ((Mx + 1 - Zb).toNat : ℤ) = Zb := by omega
    rw [e] at i1 i2
    simp only [hDdef, hβt]
    linear_combination i1 + i2
  -- the harmonic relations
  have hut_eq : ∀ z, Zb ≤ z → (1 / 2 + ρ z) * (ut (z + 1) - ut z)
      - (1 / 2 - ρ z) * (ut z - ut (z - 1)) = indic (z ≤ Mx) := by
    intro z hz
    by_cases hzM : z ≤ Mx
    · have d1 := hD (z + 1) (by omega)
      rw [add_sub_cancel_right] at d1
      rw [d1, hD z (by omega)]
      unfold indic; rw [if_pos hzM]
      linarith [hDrec z hzM]
    · unfold indic; rw [if_neg hzM]
      by_cases hz1 : z = Mx + 1
      · subst hz1
        have d1 := hUp (Mx + 1 + 1) (by omega)
        rw [add_sub_cancel_right] at d1
        rw [d1, hQ'1, hD (Mx + 1) le_rfl]
        simp only [hDdef, top.1, top.2.2.1, hβ]
        linear_combination (-βt) * hqm (Mx + 1)
      · have d1 := hUp (z + 1) (by omega)
        rw [add_sub_cancel_right] at d1
        rw [d1, hUp z (by omega), eQ' z (by omega)]
        linear_combination (Q' (z - 1) * β) * hqm z
  -- Dynkin
  have hdyn := dynkin_on (M := M) (ρp := ρp) hM Zb (Zb - 1) le_rfl (fun z => indic (z ≤ Mx))
    (fun z => -ut z)
    (by
      intro z hz1 hz2
      have hz : z = Zb - 1 := by omega
      subst hz
      have := hD Zb (by omega)
      rw [sub_add_cancel]
      unfold indic; rw [if_pos (by omega)]
      linarith)
    (by
      intro z hz
      have := hut_eq z hz
      rw [hF z]
      unfold Fbar; rw [hF z]
      linarith)
  -- D positive on [Zb, Mx+1]
  have hDpos : ∀ k : ℕ, Zb + k ≤ Mx + 1 → 0 < D (Zb + k) := by
    intro k
    induction k with
    | zero => intro _; simp [hDZb]
    | succ k ih =>
      intro hk
      have h1 := ih (by push_cast at hk; omega)
      have h2 := hDrec (Zb + k) (by push_cast at hk; omega)
      have e : Zb + ((k + 1 : ℕ) : ℤ) = Zb + k + 1 := by push_cast; ring
      rw [e]
      have hl := hlt (Zb + k)
      have hp' := hpos (Zb + k)
      by_contra hc
      push_neg at hc
      nlinarith
  have hQpos : ∀ n, 0 < Q' n := fun n => Finset.prod_pos (fun m _ => hqpos m)
  have hW0 : 0 ≤ W Zb := by
    apply Finset.sum_nonneg; intro k _
    apply mul_nonneg (by have := hlt k; apply div_nonneg <;> linarith)
    exact (Finset.prod_pos (fun m _ => hqpos m)).le
  have hβtneg : βt < 0 := by
    rw [hβt]
    have : 0 < Q Zb := Finset.prod_pos (fun m _ => hqpos m)
    linarith
  have hβpos : 0 < β := by
    rw [hβ]; have := hqpos (Mx + 1); nlinarith
  refine ⟨hβtneg, hβpos, ?_, ?_⟩
  · have H := strictMonoOn_of_succ ut (Zb - 1) (by
      intro w hw
      by_cases hw2 : w ≤ Mx + 1
      · have := hD w hw2
        have := hDpos (w - Zb).toNat (by omega)
        rw [show Zb + ((w - Zb).toNat : ℤ) = w by omega] at this
        linarith
      · have := hUp w (by omega)
        have := mul_pos (hQpos (w - 1)) hβpos
        linarith)
    intro a ha b hb hab
    exact H (show Zb - 1 ≤ a by simp only [Set.mem_setOf_eq] at ha; omega)
      (show Zb - 1 ≤ b by simp only [Set.mem_setOf_eq] at hb; omega) hab
  · intro z hz T _
    have h := hdyn T [] z (by omega)
    have e := termExp_affine (M := M) (ρp := ρp) Zb 0 (-1) ut T [] z
    simp only [zero_add, neg_one_mul] at e
    rw [e] at h
    linarith

end SBLL2Fin2

namespace SBLL2Inf
open SpreadBetting.Inertial SBFAux SBRedAux SBLL2Aux

variable {M : Market} {ρp : ℕ → ℝ}

lemma wait_cum (f : ℤ → ℝ) (T : ℕ) (h : List (ℤ × Act)) (z : ℤ) :
    cumExp M ρp 1 (threshStrat 1 (fun _ => False)) (fun w _ _ => f w) (T + 1) h z
      = f z + (Fbar M 1 (sTilde M ρp z) * cumExp M ρp 1 (threshStrat 1 (fun _ => False))
            (fun w _ _ => f w) T (h ++ [(1, .wait)]) (z + 1)
          + F M 1 (sTilde M ρp z) * cumExp M ρp 1 (threshStrat 1 (fun _ => False))
            (fun w _ _ => f w) T (h ++ [(-1, .wait)]) (z - 1)) := by
  simp only [cumExp, threshStrat]
  simp only [if_true, if_false, reduceCtorEq, zero_mul, zero_add, one_mul]
  unfold Fbar; ring

lemma wait_term (g : ℤ → ℝ) (T : ℕ) (h : List (ℤ × Act)) (z : ℤ) :
    termExp M ρp 1 (threshStrat 1 (fun _ => False)) g (T + 1) h z
      = Fbar M 1 (sTilde M ρp z) * termExp M ρp 1 (threshStrat 1 (fun _ => False)) g T
            (h ++ [(1, .wait)]) (z + 1)
          + F M 1 (sTilde M ρp z) * termExp M ρp 1 (threshStrat 1 (fun _ => False)) g T
            (h ++ [(-1, .wait)]) (z - 1) := by
  simp only [termExp, threshStrat]
  simp only [if_true, if_false, reduceCtorEq, zero_mul, zero_add, one_mul]

lemma dynkin_wait (f u : ℤ → ℝ)
    (hrel : ∀ z, Fbar M 1 (sTilde M ρp z) * (u (z + 1) - u z)
        - F M 1 (sTilde M ρp z) * (u z - u (z - 1)) = f z) :
    ∀ T h z, cumExp M ρp 1 (threshStrat 1 (fun _ => False)) (fun w _ _ => f w) T h z
      = termExp M ρp 1 (threshStrat 1 (fun _ => False)) u T h z - u z := by
  intro T; induction T with
  | zero => intro h z; simp [cumExp, termExp]
  | succ T ih =>
    intro h z
    rw [wait_cum, wait_term, ih, ih]
    have := hrel z
    unfold Fbar at this ⊢
    linear_combination (-1) * this

/-- the increments of the Lyapunov function for `Z̄ = -∞` -/
lemma exists_u (ρ : ℤ → ℝ) (hρ01 : ∀ z, 0 < ρ z ∧ ρ z < 1 / 2)
    (η : ℝ) (hη : 0 < η) (hηρ : ∀ m, m ≤ 0 → η ≤ ρ m) (Mx : ℤ) :
    ∃ u : ℤ → ℝ, StrictMono u ∧ ∀ z, (1 / 2 + ρ z) * (u (z + 1) - u z)
        - (1 / 2 - ρ z) * (u z - u (z - 1)) = indic (z ≤ Mx) := by
  set q : ℤ → ℝ := fun m => (1 / 2 - ρ m) / (1 / 2 + ρ m) with hq
  have hpos := fun m => (hρ01 m).1
  have hlt := fun m => (hρ01 m).2
  have hη2 : η < 1 / 2 := lt_of_le_of_lt (hηρ 0 le_rfl) (hlt 0)
  set θ : ℝ := (1 / 2 - η) / (1 / 2 + η) with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; linarith
  have hq0 : ∀ m, 0 < q m := fun m => div_pos (by linarith [hlt m]) (by linarith [hpos m])
  have hq1 : ∀ m, q m ≤ 1 := fun m => by
    rw [hq]; simp only; rw [div_le_one (by linarith [hpos m])]; linarith [hpos m]
  have hqθ : ∀ m, m ≤ 0 → q m ≤ θ := by
    intro m hm
    rw [hq, hθ]; simp only
    rw [div_le_div_iff₀ (by linarith [hpos m]) (by linarith)]
    nlinarith [hηρ m hm]
  have hqm : ∀ m, (1 / 2 + ρ m) * q m = 1 / 2 - ρ m := by
    intro m; simp only [hq]; have := hpos m
    have : 1 + 2 * ρ m ≠ 0 := by linarith
    field_simp
  -- the series
  set a : ℕ → ℤ → ℝ := fun j z => (1 / (1 / 2 + ρ (z - j))) * ∏ i ∈ Finset.range j, q (z - i)
    with ha
  have ha_succ : ∀ j z, a (j + 1) z = q z * a j (z - 1) := by
    intro j z
    simp only [ha]
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, sub_zero]
    have e : ∀ i : ℕ, z - ((i + 1 : ℕ) : ℤ) = z - 1 - (i : ℤ) := by intro i; push_cast; ring
    simp only [e]
    push_cast
    ring_nf
  have hprod : ∀ z : ℤ, ∀ j : ℕ, ∏ i ∈ Finset.range j, q (z - i) ≤ θ ^ j / θ ^ z.toNat := by
    intro z j
    induction j with
    | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, pow_zero]
      rw [le_div_iff₀ (pow_pos hθ0 _), one_mul]
      exact pow_le_one₀ hθ0.le hθ1.le
    | succ j ih =>
      rw [Finset.prod_range_succ]
      by_cases hj : z.toNat ≤ j
      · have hqz := hqθ (z - j) (by omega)
        have hnn : 0 ≤ ∏ i ∈ Finset.range j, q (z - i) :=
          Finset.prod_nonneg (fun i _ => (hq0 _).le)
        calc (∏ i ∈ Finset.range j, q (z - i)) * q (z - j) ≤ θ ^ j / θ ^ z.toNat * θ :=
              mul_le_mul ih hqz (hq0 _).le (by positivity)
          _ = θ ^ (j + 1) / θ ^ z.toNat := by rw [pow_succ]; ring
      · have h1 : (∏ i ∈ Finset.range j, q (z - i)) * q (z - j) ≤ 1 := by
          have := Finset.prod_le_one (s := Finset.range (j + 1)) (f := fun i : ℕ => q (z - i))
            (fun i _ => (hq0 _).le) (fun i _ => hq1 _)
          rwa [Finset.prod_range_succ] at this
        refine le_trans h1 ?_
        rw [le_div_iff₀ (pow_pos hθ0 _), one_mul]
        exact pow_le_pow_of_le_one hθ0.le hθ1.le (by omega)
  have ha0 : ∀ j z, 0 ≤ a j z := fun j z =>
    mul_nonneg (by have := hpos (z - j); positivity) (Finset.prod_nonneg (fun i _ => (hq0 _).le))
  have hsum : ∀ z, Summable (fun j => a j z) := by
    intro z
    apply Summable.of_nonneg_of_le (fun j => ha0 j z) (f := fun j => 2 * (θ ^ j / θ ^ z.toNat))
    · intro j
      simp only [ha]
      have h1 : 1 / (1 / 2 + ρ (z - j)) ≤ 2 := by
        rw [div_le_iff₀ (by linarith [hpos (z - j)])]; linarith [hpos (z - j)]
      exact mul_le_mul h1 (hprod z j) (Finset.prod_nonneg (fun i _ => (hq0 _).le)) (by norm_num)
    · apply Summable.mul_left
      simp only [div_eq_mul_inv]
      exact (summable_geometric_of_lt_one hθ0.le hθ1).mul_right _
  set S : ℤ → ℝ := fun z => ∑' j, a j z with hS
  have hSrec : ∀ z, S z = 1 / (1 / 2 + ρ z) + q z * S (z - 1) := by
    intro z
    simp only [hS]
    rw [(hsum z).tsum_eq_zero_add]
    simp only [ha_succ, tsum_mul_left]
    simp [ha]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    have := hSrec z
    have h1 : 0 < 1 / (1 / 2 + ρ z) := by have := hpos z; positivity
    have h2 : 0 ≤ q z * S (z - 1) := mul_nonneg (hq0 z).le (tsum_nonneg (fun j => ha0 j _))
    linarith
  set d : ℤ → ℝ := fun z => if z ≤ Mx then S z else S Mx * ∏ m ∈ Finset.Icc (Mx + 1) z, q m
    with hd
  have hdpos : ∀ z, 0 < d z := by
    intro z; simp only [hd]; split_ifs
    · exact hSpos z
    · exact mul_pos (hSpos Mx) (Finset.prod_pos (fun m _ => hq0 m))
  have hdrel : ∀ z, (1 / 2 + ρ z) * d z - (1 / 2 - ρ z) * d (z - 1) = indic (z ≤ Mx) := by
    intro z
    unfold indic
    by_cases hz : z ≤ Mx
    · rw [if_pos hz]
      simp only [hd, if_pos hz, if_pos (show z - 1 ≤ Mx by omega)]
      rw [hSrec z]
      have := hpos z
      have e : (1 / 2 + ρ z) * (1 / (1 / 2 + ρ z)) = 1 := by field_simp
      linear_combination e + S (z - 1) * hqm z
    · rw [if_neg hz]
      simp only [hd, if_neg hz]
      by_cases hz1 : z = Mx + 1
      · subst hz1
        rw [if_pos (by omega : Mx + 1 - 1 ≤ Mx), Finset.Icc_self, Finset.prod_singleton,
          show Mx + 1 - 1 = Mx by ring]
        linear_combination S Mx * hqm (Mx + 1)
      · rw [if_neg (by omega : ¬ z - 1 ≤ Mx)]
        have := prod_Icc_right (f := q) (a := Mx + 1) (b := z - 1) (by omega)
        rw [sub_add_cancel] at this
        rw [this]
        linear_combination (S Mx * ∏ m ∈ Finset.Icc (Mx + 1) (z - 1), q m) * hqm z
  -- the function u
  set u : ℤ → ℝ := fun z => ∑ k ∈ Finset.Ico 0 z, d k - ∑ k ∈ Finset.Ico z 0, d k with hu
  have hinc : ∀ z, u (z + 1) - u z = d z := by
    intro z
    simp only [hu]
    by_cases hz : 0 ≤ z
    · rw [← Finset.insert_Ico_right_eq_Ico_add_one hz, Finset.sum_insert (by simp),
        Finset.Ico_eq_empty (by omega : ¬ z + 1 < 0), Finset.Ico_eq_empty (by omega : ¬ z < 0)]
      simp
    · rw [Finset.Ico_eq_empty (by omega : ¬ 0 < z + 1), Finset.Ico_eq_empty (by omega : ¬ 0 < z),
        ← Finset.insert_Ico_add_one_left_eq_Ico (by omega : z < 0), Finset.sum_insert (by simp)]
      ring
  refine ⟨u, strictMono_int_of_lt_succ (fun n => by have := hinc n; have := hdpos n; linarith), ?_⟩
  intro z
  have h1 := hinc z
  have h2 := hinc (z - 1)
  rw [sub_add_cancel] at h2
  rw [h1, h2]
  exact hdrel z

end SBLL2Inf

open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2 SBLL2Aux SBLL2Fin SBLL2Fin2 SBLL2Inf in
theorem solution (M : Market) (hM : M.Standing) (ρp : ℕ → ℝ)
    (hρ : ∀ z : ℕ, 1 ≤ z → ρp z ∈ Set.Ioo 0 (1 / 2 - alpha M))
    (hbdd : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ, 1 ≤ z → ρp z ≤ 1 / 2 - alpha M - δ) :
    -- Z̄ ∈ ℤ: the closed form (L.2)–(L.3)
    (∀ Zb Mx : ℤ, Zb - 2 < Mx →
      let ρ := rhoExt M ρp
      let q : ℤ → ℝ := fun m => (1 / 2 - ρ m) / (1 / 2 + ρ m)
      let βt : ℝ := -(∏ m ∈ Finset.Icc Zb Mx, q m)
        - ∑ k ∈ Finset.Icc Zb Mx, (1 / (1 / 2 - ρ k)) * ∏ m ∈ Finset.Icc k Mx, q m
      let β : ℝ := -q (Mx + 1) * βt
      let ut : ℤ → ℝ := fun z =>
        if z ≤ Mx then
          (1 + ∑ n ∈ Finset.Icc (z + 1) Mx,
              ∏ m ∈ Finset.Icc n Mx, (1 / 2 + ρ m) / (1 / 2 - ρ m)) * βt
            + ∑ n ∈ Finset.Icc (z + 1) Mx, ∑ k ∈ Finset.Icc n Mx,
                (1 / (1 / 2 + ρ k)) * ∏ m ∈ Finset.Icc n k, (1 / 2 + ρ m) / (1 / 2 - ρ m)
        else if z = Mx + 1 then 0
        else (1 + ∑ n ∈ Finset.Icc (Mx + 2) (z - 1), ∏ m ∈ Finset.Icc (Mx + 2) n, q m) * β
      let ξ := threshStrat 1 (fun z => z < Zb)
      βt < 0 ∧ 0 < β ∧ StrictMonoOn ut {z : ℤ | Zb - 2 < z} ∧
      ∀ z : ℤ, Zb - 2 < z → ∀ T : ℕ, 1 ≤ T →
        cumExp M ρp 1 ξ (fun z _ _ => indic (z ≤ Mx)) T [] z
          = termExp M ρp 1 ξ ut T [] z - ut z) ∧
    -- Z̄ = -∞
    (∀ Mx : ℤ, ∃ ut : ℤ → ℝ, StrictMono ut ∧
      ∀ z : ℤ, ∀ T : ℕ, 1 ≤ T →
        cumExp M ρp 1 (threshStrat 1 (fun _ => False)) (fun z _ _ => indic (z ≤ Mx)) T [] z
          = termExp M ρp 1 (threshStrat 1 (fun _ => False)) ut T [] z - ut z) := by
  have hP : P2 M ρp := (proposition_2 M hM ρp hρ).1
  have hρ01 := rho_strict hM hP hρ
  have hF : ∀ z, F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z := fun z => (hP z).2.2
  refine ⟨fun Zb Mx hZM => L2_fin hM hρ01 hF Zb Mx hZM, ?_⟩
  intro Mx
  obtain ⟨δ, hδ, hδb⟩ := hbdd
  have hδ' : δ < 1 / 2 - alpha M := by
    have h1 := (hρ 1 le_rfl).1
    have h2 := hδb 1 le_rfl
    linarith
  have hα := alpha_pos hM
  have hm := hM.m0_lt_m1
  obtain ⟨ys, hys, hFys⟩ := exists_F_eq hM 0 (v := 1 - alpha M - δ) (by
    rw [F0_m0 hM, F0_m1 hM]; constructor <;> linarith)
  have hys1 : ys < M.m1 := by
    rcases lt_or_eq_of_le hys.2 with h | h
    · exact h
    · rw [h, F0_m1 hM] at hFys; linarith
  have hη1 : 0 < 1 / 2 - F M 1 ys := by
    have := F_lt_of_lt hM 1 (y := M.m1) ⟨hm.le, le_refl _⟩ hys1
    rw [F1_m1 hM] at this; linarith
  set η := min (1 / 2 - F M 1 ys) (rhoExt M ρp 0) with hη
  have hηpos : 0 < η := lt_min hη1 (hρ01 0).1
  have hηρ : ∀ m, m ≤ 0 → η ≤ rhoExt M ρp m := by
    intro m hm0
    rcases eq_or_lt_of_le hm0 with h | h
    · subst h; exact min_le_right _ _
    · obtain ⟨hs, -, hFm⟩ := hP m
      have h0 := (hP (-m)).2.1
      rw [neg_neg] at h0
      have hval : rhoExt M ρp (-m) = ρp (-m).toNat := by rw [rhoExt, if_pos (by omega)]
      have hb := hδb (-m).toNat (by omega)
      have hle : sTilde M ρp m ≤ ys := by
        by_contra hc
        push_neg at hc
        have := F_lt_of_lt hM 0 hs hc
        rw [h0, hval, hFys] at this
        linarith
      have := F_mono hM 1 hle
      have : η ≤ 1 / 2 - F M 1 ys := min_le_left _ _
      linarith
  obtain ⟨u, hu, hrel⟩ := exists_u (rhoExt M ρp) hρ01 η hηpos hηρ Mx
  refine ⟨u, hu, fun z T _ => dynkin_wait (fun w => indic (w ≤ Mx)) u ?_ T [] z⟩
  intro w
  rw [hF w]
  unfold Fbar; rw [hF w]
  have := hrel w
  linarith
