-- Prove2me | solution 1 for SpreadBetting.Inertial.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:00:20.261989+00:00
-- url     : https://prove2.me/submissions/daf541aa-8751-49a4-b079-4dda90184cf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Theorems.Thm_SpreadBetting_Inertial_lemma_1
import Theorems.Thm_SpreadBetting_Inertial_lemma_2
import Theorems.Thm_SpreadBetting_Inertial_lemma_3
import Theorems.Thm_SpreadBetting_Inertial_lemma_G_2

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

namespace SBT3Aux
open SpreadBetting.Inertial SBFAux SBRedAux

variable {M : Market} {ρp : ℕ → ℝ}

noncomputable def wV (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) : ℤ → Act → ℤ → ℝ :=
  fun z a _ => match a with
    | .pos => jPlus M i (sTilde M ρp z)
    | .neg => jMinus M i (sTilde M ρp z)
    | .wait => 0

lemma V_eq (i : Fin 2) (ξ : Strategy) (T : ℕ) (z : ℤ) :
    V M ρp i ξ T z = cumExp M ρp i ξ (wV M ρp i) T [] z := rfl

lemma termExp_nonneg (hM : M.Standing) (i : Fin 2) (ξ : Strategy) (hξ : ∀ h z a, 0 ≤ ξ h z a)
    (g : ℤ → ℝ) (hg : ∀ z, 0 ≤ g z) : ∀ T h z, 0 ≤ termExp M ρp i ξ g T h z := by
  intro T
  induction T with
  | zero => intro h z; exact hg z
  | succ T ih =>
    intro h z
    simp only [termExp]
    have hF := F_mem hM i (sTilde M ρp z)
    have hFb : 0 ≤ Fbar M i (sTilde M ρp z) := by unfold Fbar; linarith
    have p1 := hξ h z .pos
    have p2 := hξ h z .neg
    have p3 := hξ h z .wait
    have a1 := ih (h ++ [(1, .pos)]) (z + 1)
    have a2 := ih (h ++ [(-1, .neg)]) (z - 1)
    have a3 := ih (h ++ [(1, .wait)]) (z + 1)
    have a4 := ih (h ++ [(-1, .wait)]) (z - 1)
    exact add_nonneg (add_nonneg (mul_nonneg p1 a1) (mul_nonneg p2 a2))
      (mul_nonneg p3 (add_nonneg (mul_nonneg hFb a3) (mul_nonneg hF.1 a4)))

/-- verification: a nonnegative supersolution of the Bellman inequalities bounds the profit -/
lemma verif (hM : M.Standing) (i : Fin 2) (J : ℤ → ℝ)
    (hB1 : ∀ z, jPlusZ M ρp i z + J (z + 1) ≤ J z)
    (hB2 : ∀ z, jMinusZ M ρp i z + J (z - 1) ≤ J z)
    (hB3 : ∀ z, Fbar M i (sTilde M ρp z) * J (z + 1) + F M i (sTilde M ρp z) * J (z - 1) ≤ J z)
    (ξ : Strategy) (hadm : Admissible ξ) :
    ∀ T h z, cumExp M ρp i ξ (wV M ρp i) T h z + termExp M ρp i ξ J T h z ≤ J z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp, termExp]
  | succ T ih =>
    intro h z
    simp only [cumExp, termExp, wV]
    have hF := F_mem hM i (sTilde M ρp z)
    have hFb : 0 ≤ Fbar M i (sTilde M ρp z) := by unfold Fbar; linarith
    have p1 := hadm.1 h z .pos
    have p2 := hadm.1 h z .neg
    have p3 := hadm.1 h z .wait
    have hs := hadm.2 h z
    have i1 := ih (h ++ [(1, .pos)]) (z + 1)
    have i2 := ih (h ++ [(-1, .neg)]) (z - 1)
    have i3 := ih (h ++ [(1, .wait)]) (z + 1)
    have i4 := ih (h ++ [(-1, .wait)]) (z - 1)
    have b1 := hB1 z
    have b2 := hB2 z
    have b3 := hB3 z
    unfold jPlusZ at b1
    unfold jMinusZ at b2
    have e1 := mul_le_mul_of_nonneg_left (add_le_add_left i1 (jPlus M i (sTilde M ρp z))) p1
    have e2 := mul_le_mul_of_nonneg_left (add_le_add_left i2 (jMinus M i (sTilde M ρp z))) p2
    have e3 := mul_le_mul_of_nonneg_left i3 hFb
    have e4 := mul_le_mul_of_nonneg_left i4 hF.1
    have e5 := mul_le_mul_of_nonneg_left (add_le_add e3 e4) p3
    have f1 := mul_le_mul_of_nonneg_left b1 p1
    have f2 := mul_le_mul_of_nonneg_left b2 p2
    have f3 := mul_le_mul_of_nonneg_left b3 p3
    have hJ : (ξ h z .pos + ξ h z .wait + ξ h z .neg) * J z = J z := by rw [hs, one_mul]
    nlinarith

lemma V_le (hM : M.Standing) (i : Fin 2) (J : ℤ → ℝ) (hJ0 : ∀ z, 0 ≤ J z)
    (hB1 : ∀ z, jPlusZ M ρp i z + J (z + 1) ≤ J z)
    (hB2 : ∀ z, jMinusZ M ρp i z + J (z - 1) ≤ J z)
    (hB3 : ∀ z, Fbar M i (sTilde M ρp z) * J (z + 1) + F M i (sTilde M ρp z) * J (z - 1) ≤ J z)
    (ξ : Strategy) (hadm : Admissible ξ) (T : ℕ) (z : ℤ) : V M ρp i ξ T z ≤ J z := by
  rw [V_eq]
  have h1 := verif hM i J hB1 hB2 hB3 ξ hadm T [] z
  have h2 := termExp_nonneg (ρp := ρp) hM i ξ hadm.1 J hJ0 T [] z
  linarith

lemma liV_le (hM : M.Standing) (i : Fin 2) (J : ℤ → ℝ) (hJ0 : ∀ z, 0 ≤ J z)
    (hB1 : ∀ z, jPlusZ M ρp i z + J (z + 1) ≤ J z)
    (hB2 : ∀ z, jMinusZ M ρp i z + J (z - 1) ≤ J z)
    (hB3 : ∀ z, Fbar M i (sTilde M ρp z) * J (z + 1) + F M i (sTilde M ρp z) * J (z - 1) ≤ J z)
    (ξ : Strategy) (hadm : Admissible ξ) (z : ℤ) : liV M ρp i ξ z ≤ (J z : EReal) := by
  unfold liV
  apply Filter.liminf_le_of_frequently_le'
  apply Filter.Frequently.of_forall
  intro T
  exact EReal.coe_le_coe_iff.2 (V_le hM i J hJ0 hB1 hB2 hB3 ξ hadm T z)

lemma threshStrat_adm (i : Fin 2) (below : ℤ → Prop) : Admissible (threshStrat i below) := by
  refine ⟨?_, ?_⟩
  · intro h z a
    unfold threshStrat
    split_ifs <;> norm_num
  · intro h z
    have := SBL5Aux.threshStrat_sum i below h z
    linarith

end SBT3Aux

open SpreadBetting.Inertial SBFAux SBRedAux SBL5Aux SBT3Aux in
theorem solution (M : Market) (hM : M.Standing) :
    0 < rbar M ∧
    ∀ r : ℝ, 0 < r → r < rbar M →
      let ρp := rhoIP M r
      -- (T3:1)
      (∀ (i : Fin 2) (z : ℤ), Jval M ρp i z < ⊤) ∧
      -- (T3:2): z̄ ∈ ℤ ∪ {-∞} and the threshold strategy (4.4) is a best response (2.3)
      (zbarSet M ρp).Nonempty ∧ ∀ i : Fin 2, IsBestResponse M ρp i (xiStar M ρp i) := by
  have hc := hM.c_pos
  have hc1 := hM.c_lt_one
  have hr0pos : 0 < r0 M := by
    unfold r0
    have h1 := F_lt_of_lt hM 1 (y := M.m1) ⟨hM.m0_lt_m1.le, le_refl _⟩
      (x := (M.m0 + M.m1) / 2) (by linarith [hM.m0_lt_m1])
    rw [F1_m1 hM] at h1
    exact inv_pos.2 (by linarith)
  have hz0 : 1 ≤ zeta0 M := le_max_left _ _
  have hrb0 : 0 < rbar0 M := by
    unfold rbar0
    apply div_pos (mul_pos hc hr0pos)
    apply mul_pos (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · unfold rbar
    split_ifs with hz
    · apply lt_min (by norm_num) (lt_min hrb0 ?_)
      apply div_pos (by linarith) (by linarith)
    · exact lt_min (by norm_num) hrb0
  intro r hr0 hr ρp
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
  obtain ⟨hL1, -⟩ := lemma_1 M hM r hr0 hr
  obtain ⟨hL2a, hL2b⟩ := lemma_2 M hM r hr0 hr
  obtain ⟨hL3a, hL3b⟩ := lemma_3 M hM r hr0 hr
  -- the bounding functions
  have hJ1 : ∀ z, 0 ≤ Jbar1 M ρp z := fun z => (hL1 z).1
  have hJ0 : ∀ z, 0 ≤ Jbar0 M ρp z := fun z => by unfold Jbar0; exact (hL1 (-z)).1
  have B : ∀ (A B C D : ℝ), D = max (max A B) C → A ≤ D ∧ B ≤ D ∧ C ≤ D := by
    intro A B C D h
    rw [h]
    exact ⟨le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  have hB1 := fun z => B _ _ _ _ (hL3a z)
  have hB0 := fun z => B _ _ _ _ (hL3b z)
  have le1 := fun ξ hξ z => liV_le hM 1 (Jbar1 M ρp) hJ1 (fun z => (hB1 z).1)
    (fun z => (hB1 z).2.1) (fun z => (hB1 z).2.2) ξ hξ z
  have le0 := fun ξ hξ z => liV_le hM 0 (Jbar0 M ρp) hJ0 (fun z => (hB0 z).1)
    (fun z => (hB0 z).2.1) (fun z => (hB0 z).2.2) ξ hξ z
  -- the value of the threshold strategy
  have star1 : liV M ρp 1 (xiStar M ρp 1) 0 = (Jbar1 M ρp 0 : EReal) := by
    unfold liV
    apply Tendsto.liminf_eq
    apply (continuous_coe_real_ereal.tendsto _).comp
    refine (hL2a 0).congr (fun T => ?_)
    rw [V_eq]
    apply cumExp_congr
    intro h z
    unfold oneStep wV xiStar threshStrat jPlusZ indic
    by_cases hb : belowZbar M (rhoIP M r) z <;> simp [hb] <;> rfl
  have star0 : liV M ρp 0 (xiStar M ρp 0) 0 = (Jbar0 M ρp 0 : EReal) := by
    unfold liV
    apply Tendsto.liminf_eq
    apply (continuous_coe_real_ereal.tendsto _).comp
    refine (hL2b 0).congr (fun T => ?_)
    rw [V_eq]
    apply cumExp_congr
    intro h z
    unfold oneStep wV xiStar threshStrat jMinusZ indic
    by_cases hb : belowZbar M (rhoIP M r) (-z) <;> simp [hb] <;> rfl
  have hBR : ∀ (i : Fin 2) (J : ℤ → ℝ),
      (∀ ξ, Admissible ξ → ∀ z, liV M ρp i ξ z ≤ (J z : EReal)) →
      liV M ρp i (xiStar M ρp i) 0 = (J 0 : EReal) →
      (∀ z, Jval M ρp i z < ⊤) ∧ IsBestResponse M ρp i (xiStar M ρp i) := by
    intro i J hle hstar
    have hsup : ∀ z, (⨆ ξ' : {ξ' : Strategy // Admissible ξ'}, liV M ρp i ξ'.1 z) ≤ (J z : EReal) :=
      fun z => iSup_le (fun ξ' => hle ξ'.1 ξ'.2 z)
    refine ⟨fun z => lt_of_le_of_lt (hsup z) (EReal.coe_lt_top _), ?_, ?_, ?_⟩
    · exact threshStrat_adm i _
    · intro _ ξ' hξ'
      rw [hstar]; exact hle ξ' hξ' 0
    · intro htop
      exfalso
      have := hsup 0
      rw [htop] at this
      exact absurd this (not_le.2 (EReal.coe_lt_top _))
  obtain ⟨hJv1, hbr1⟩ := hBR 1 (Jbar1 M ρp) le1 star1
  obtain ⟨hJv0, hbr0⟩ := hBR 0 (Jbar0 M ρp) le0 star0
  refine ⟨?_, hne, ?_⟩
  · intro i; fin_cases i
    · exact hJv0
    · exact hJv1
  · intro i; fin_cases i
    · exact hbr0
    · exact hbr1
