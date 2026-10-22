-- Prove2me | solution 1 for PharmaEPR.Welfare.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:21:27.192721+00:00
-- url     : https://prove2.me/submissions/89a7f87b-bf8d-4a03-b529-d781ce135a2d

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

set_option autoImplicit false

namespace P4X
open PharmaEPR.Welfare

/-! ## Integrals -/

lemma inner_min (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ y in (0:ℝ)..1, min y x = x - x ^ 2 / 2 := by
  have hc : Continuous (fun y : ℝ => min y x) := continuous_id.min continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ y in (0:ℝ)..x, min y x = ∫ y in (0:ℝ)..x, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    exact min_eq_left hy.2
  have h2 : ∫ y in x..1, min y x = ∫ y in x..1, x := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx1] at hy
    exact min_eq_right hy.1
  rw [h1, h2, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma inner_min1 : ∫ y in (0:ℝ)..1, min y (1:ℝ) = 1 / 2 := by
  have : ∫ y in (0:ℝ)..1, min y (1:ℝ) = ∫ y in (0:ℝ)..1, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    exact min_eq_left hy.2
  rw [this, integral_id]; norm_num

lemma outer_poly (A B C : ℝ) :
    ∫ x in (0:ℝ)..1, (A + B * x + C * x ^ 2) = A + B / 2 + C / 3 := by
  have i1 : IntervalIntegrable (fun x : ℝ => A + B * x) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => A + B * x).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => C * x ^ 2) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => C * x ^ 2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun _ : ℝ => A) MeasureTheory.volume 0 1 :=
    (continuous_const).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun x : ℝ => B * x) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => B * x).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num
  ring

lemma E2N {f : ℝ → ℝ → ℝ} (A B C : ℝ) (hf : ∀ x y, f x y = A + B * x + C * min y x) :
    E2 f = A + B / 2 + C / 3 := by
  unfold E2
  have hin : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      (∫ y in (0:ℝ)..1, f x y) = A + (B + C) * x + (-C / 2) * x ^ 2 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp_rw [hf]
    have hI1 : IntervalIntegrable (fun _ : ℝ => A + B * x) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun y : ℝ => C * min y x) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.min continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      inner_min x hx.1 hx.2, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [intervalIntegral.integral_congr hin, outer_poly]
  ring

lemma E2O {f : ℝ → ℝ → ℝ} (A B C : ℝ) (hf : ∀ x y, f x y = A + B * x + C * min y 1) :
    E2 f = A + B / 2 + C / 2 := by
  unfold E2
  have hin : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      (∫ y in (0:ℝ)..1, f x y) = (A + C / 2) + B * x + 0 * x ^ 2 := by
    intro x _
    simp_rw [hf]
    have hI1 : IntervalIntegrable (fun _ : ℝ => A + B * x) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun y : ℝ => C * min y (1:ℝ)) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.min continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      inner_min1, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [intervalIntegral.integral_congr hin, outer_poly]
  ring

/-! ## Pieces of the game -/

variable {P : Params} {a : Action}

lemma presc_N (h : ¬ OverPrescribes P a) (x : ℝ) : presc P a x = x := by
  simp [presc, h]

lemma presc_O (h : OverPrescribes P a) (x : ℝ) : presc P a x = 1 := by
  simp [presc, h]

lemma doc_N (hN : ¬ OverPrescribes P a) :
    E2 (fun x _ => docUtil P a x (presc P a x)) = (P.up - a.p + a.etaD) / 2 := by
  refine (E2N 0 (P.up - a.p + a.etaD) 0 ?_).trans (by ring)
  intro x z; simp only [docUtil, presc_N hN]; ring

lemma sale_N (hN : ¬ OverPrescribes P a) :
    E2 (fun x _ => a.p * presc P a x) = a.p / 2 := by
  refine (E2N 0 a.p 0 ?_).trans (by ring)
  intro x z; simp only [presc_N hN]; ring

lemma ccEC_N (hN : ¬ OverPrescribes P a) (y : Policy) :
    complianceCost P .EC y a = P.k * y.r / 6 := by
  simp only [complianceCost]
  refine (E2N 0 (P.k * y.r) (-(P.k * y.r)) ?_).trans (by ring)
  intro x z; simp only [used, presc_N hN]; ring

lemma ccSR_N (hN : ¬ OverPrescribes P a) (y : Policy) :
    complianceCost P .SR y a = y.t / 2 := by
  simp only [complianceCost]
  refine (E2N 0 y.t 0 ?_).trans (by ring)
  intro x z; simp only [presc_N hN]; ring

lemma plSR_N (hN : ¬ OverPrescribes P a) (y : Policy) :
    plannerSurplus P .SR y a = y.t / 2 - P.k * y.r / 6 := by
  simp only [plannerSurplus]
  refine (E2N 0 (y.t - P.k * y.r) (P.k * y.r) ?_).trans (by ring)
  intro x z; simp only [used, presc_N hN]; ring

lemma env_N (hN : ¬ OverPrescribes P a) (y : Policy) :
    E2 (envDisutil P y a) = P.epsE / 2 - P.epsE * y.r / 6 := by
  refine (E2N 0 (P.epsE * (1 - y.r)) (P.epsE * y.r) ?_).trans (by ring)
  intro x z; simp only [envDisutil, used, presc_N hN]; ring

lemma soc_N (hN : ¬ OverPrescribes P a) (y : Policy) :
    E2 (socDisutil P y a) = P.epsS * (1 - y.r) / 6 := by
  refine (E2N 0 (P.epsS * (1 - y.r)) (-(P.epsS * (1 - y.r))) ?_).trans (by ring)
  intro x z; simp only [socDisutil, used, presc_N hN]; ring

lemma doc_O (hO : OverPrescribes P a) :
    E2 (fun x _ => docUtil P a x (presc P a x)) =
      P.up / 2 - a.p + a.etaD - P.od * (1 - a.etaP) / 2 := by
  refine (E2O (-a.p + a.etaD - P.od * (1 - a.etaP)) (P.up + P.od * (1 - a.etaP)) 0 ?_).trans
    (by ring)
  intro x z; simp only [docUtil, presc_O hO]; ring

lemma sale_O (hO : OverPrescribes P a) :
    E2 (fun x _ => a.p * presc P a x) = a.p := by
  refine (E2O a.p 0 0 ?_).trans (by ring)
  intro x z; simp only [presc_O hO]; ring

lemma ccEC_O (hO : OverPrescribes P a) (y : Policy) :
    complianceCost P .EC y a = P.k * y.r / 2 := by
  simp only [complianceCost]
  refine (E2O (P.k * y.r) 0 (-(P.k * y.r)) ?_).trans (by ring)
  intro x z; simp only [used, presc_O hO]; ring

lemma ccSR_O (hO : OverPrescribes P a) (y : Policy) :
    complianceCost P .SR y a = y.t := by
  simp only [complianceCost]
  refine (E2O y.t 0 0 ?_).trans (by ring)
  intro x z; simp only [presc_O hO]; ring

lemma plSR_O (hO : OverPrescribes P a) (y : Policy) :
    plannerSurplus P .SR y a = y.t - P.k * y.r / 2 := by
  simp only [plannerSurplus]
  refine (E2O (y.t - P.k * y.r) 0 (P.k * y.r) ?_).trans (by ring)
  intro x z; simp only [used, presc_O hO]; ring

lemma env_O (hO : OverPrescribes P a) (y : Policy) :
    E2 (envDisutil P y a) = P.epsE * (1 - y.r) + P.epsE * y.r / 2 := by
  refine (E2O (P.epsE * (1 - y.r)) 0 (P.epsE * y.r) ?_).trans (by ring)
  intro x z; simp only [envDisutil, used, presc_O hO]; ring

lemma soc_O (hO : OverPrescribes P a) (y : Policy) :
    E2 (socDisutil P y a) = P.epsS * (1 - y.r) / 2 := by
  refine (E2O (P.epsS * (1 - y.r)) 0 (-(P.epsS * (1 - y.r))) ?_).trans (by ring)
  intro x z; simp only [socDisutil, used, presc_O hO]; ring

noncomputable def ccN (P : Params) (m : EPRModel) (y : Policy) : ℝ :=
  match m with
  | .EC => P.k * y.r / 6
  | .SR => y.t / 2

noncomputable def ccO (P : Params) (m : EPRModel) (y : Policy) : ℝ :=
  match m with
  | .EC => P.k * y.r / 2
  | .SR => y.t

lemma prof_N (hN : ¬ OverPrescribes P a) (m : EPRModel) (y : Policy) :
    prodProfit P m y a = a.p / 2 - P.alpha * a.etaD ^ 2 - P.beta * a.etaP ^ 2 - ccN P m y := by
  cases m
  · simp only [prodProfit, sale_N hN, ccEC_N hN, ccN]
  · simp only [prodProfit, sale_N hN, ccSR_N hN, ccN]

lemma prof_O (hO : OverPrescribes P a) (m : EPRModel) (y : Policy) :
    prodProfit P m y a = a.p - P.alpha * a.etaD ^ 2 - P.beta * a.etaP ^ 2 - ccO P m y := by
  cases m
  · simp only [prodProfit, sale_O hO, ccEC_O hO, ccO]
  · simp only [prodProfit, sale_O hO, ccSR_O hO, ccO]

lemma wel_N (hN : ¬ OverPrescribes P a) (m : EPRModel) (y : Policy) :
    welfare P m y a = (P.up - a.p + a.etaD) / 2 + prodProfit P m y a + plannerSurplus P m y a
      - (P.epsE / 2 - P.epsE * y.r / 6) - P.epsS * (1 - y.r) / 6 := by
  simp only [welfare, doc_N hN, env_N hN, soc_N hN]

lemma wel_O (hO : OverPrescribes P a) (m : EPRModel) (y : Policy) :
    welfare P m y a = (P.up / 2 - a.p + a.etaD - P.od * (1 - a.etaP) / 2) + prodProfit P m y a
      + plannerSurplus P m y a
      - (P.epsE * (1 - y.r) + P.epsE * y.r / 2) - P.epsS * (1 - y.r) / 2 := by
  simp only [welfare, doc_O hO, env_O hO, soc_O hO]

/-! ## The two candidate producer actions -/

noncomputable def aN (P : Params) : Action := ⟨P.up + 1, 1, 0⟩
def aO : Action := ⟨1, 1, 1⟩

noncomputable def WN (P : Params) (r : ℝ) : ℝ :=
  (P.up + 1) / 2 - P.alpha - P.k * r / 6 - (P.epsE / 2 - P.epsE * r / 6) - P.epsS * (1 - r) / 6

noncomputable def WO (P : Params) (r : ℝ) : ℝ :=
  P.up / 2 + 1 - P.alpha - P.beta - P.k * r / 2 - (P.epsE * (1 - r) + P.epsE * r / 2)
    - P.epsS * (1 - r) / 2

lemma nOP_aN (hP : Regime P) : ¬ OverPrescribes P (aN P) := by
  obtain ⟨hu, -, -, hb, hbo, -⟩ := hP
  simp only [OverPrescribes, aN]; intro h; nlinarith

lemma OP_aO : OverPrescribes P aO := by
  simp only [OverPrescribes, aO]; norm_num

lemma profN (hP : Regime P) (m : EPRModel) (y : Policy) :
    prodProfit P m y (aN P) = (P.up + 1) / 2 - P.alpha - ccN P m y := by
  rw [prof_N (nOP_aN hP)]; simp only [aN]; ring

lemma profO (m : EPRModel) (y : Policy) :
    prodProfit P m y aO = 1 - P.alpha - P.beta - ccO P m y := by
  rw [prof_O OP_aO]; simp only [aO]; ring

lemma welN (hP : Regime P) (m : EPRModel) (y : Policy) :
    welfare P m y (aN P) = WN P y.r := by
  rw [wel_N (nOP_aN hP), profN hP]
  cases m
  · simp only [plannerSurplus, ccN, aN, WN]; ring
  · rw [plSR_N (nOP_aN hP)]; simp only [ccN, aN, WN]; ring

lemma welO (m : EPRModel) (y : Policy) :
    welfare P m y aO = WO P y.r := by
  rw [wel_O OP_aO, profO]
  cases m
  · simp only [plannerSurplus, ccO, aO, WO]; ring
  · rw [plSR_O OP_aO]; simp only [ccO, aO, WO]; ring

lemma feas_aN (hP : Regime P) : ProdFeasible P (aN P) := by
  refine ⟨by simp [aN], by simp [aN], by simp [aN], by simp [aN], fun x _ => ?_⟩
  rw [presc_N (nOP_aN hP)]
  have : docUtil P (aN P) x x = 0 := by simp only [docUtil, aN]; ring
  rw [this]

lemma feas_aO (hP : Regime P) : ProdFeasible P aO := by
  obtain ⟨hu, -⟩ := hP
  refine ⟨by simp [aO], by simp [aO], by simp [aO], by simp [aO], fun x hx => ?_⟩
  rw [presc_O OP_aO]
  have : docUtil P aO x 1 = P.up * x := by simp only [docUtil, aO]; ring
  rw [this]; exact mul_nonneg hu hx.1

lemma bound_N (hP : Regime P) (hf : ProdFeasible P a) (hN : ¬ OverPrescribes P a)
    (m : EPRModel) (y : Policy) :
    prodProfit P m y a ≤ prodProfit P m y (aN P) ∧
    (prodProfit P m y (aN P) ≤ prodProfit P m y a → a = aN P) := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, hb, hbo, hab, hk, -, -⟩ := hP'
  obtain ⟨hd0, hd1, hq0, hq1, hx⟩ := hf
  have hp : a.p ≤ P.up + a.etaD := by
    have := hx 1 ⟨zero_le_one, le_rfl⟩
    rw [presc_N hN] at this; simp only [docUtil] at this; nlinarith
  have hfac' : 0 < 1 / 2 - P.alpha * (1 + a.etaD) := by
    nlinarith [mul_le_mul_of_nonneg_left hd1 ha.le]
  have h1 : 0 ≤ (1 - a.etaD) * (1 / 2 - P.alpha * (1 + a.etaD)) :=
    mul_nonneg (by linarith) hfac'.le
  have h2 : 0 ≤ P.beta * a.etaP ^ 2 := by positivity
  rw [prof_N hN, profN hP]
  refine ⟨by nlinarith, fun hle => ?_⟩
  have e1 : (1 - a.etaD) * (1 / 2 - P.alpha * (1 + a.etaD)) = 0 := by nlinarith
  have e2 : P.beta * a.etaP ^ 2 = 0 := by nlinarith
  have hd : a.etaD = 1 := by
    rcases mul_eq_zero.1 e1 with h | h
    · linarith
    · linarith
  have hq2 : a.etaP ^ 2 = 0 := by
    rcases mul_eq_zero.1 e2 with h | h
    · linarith
    · exact h
  have hq : a.etaP = 0 := by nlinarith
  have hp' : a.p = P.up + 1 := by
    rw [hd, hq] at hle; nlinarith
  show (⟨a.p, a.etaD, a.etaP⟩ : Action) = aN P
  rw [hp', hd, hq]; rfl

lemma bound_O (hP : Regime P) (hf : ProdFeasible P a) (hO : OverPrescribes P a)
    (m : EPRModel) (y : Policy) :
    prodProfit P m y a ≤ prodProfit P m y aO ∧
    (prodProfit P m y aO ≤ prodProfit P m y a → a = aO) := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, hb, hbo, hab, hk, -, -⟩ := hP'
  obtain ⟨hd0, hd1, hq0, hq1, -⟩ := hf
  have hp : a.p + P.od * (1 - a.etaP) ≤ a.etaD := hO
  have f1 : 0 < 1 - P.alpha * (1 + a.etaD) := by
    nlinarith [mul_le_mul_of_nonneg_left hd1 ha.le]
  have f2 : 0 < P.od - P.beta * (1 + a.etaP) := by
    nlinarith [mul_le_mul_of_nonneg_left hq1 hb.le]
  have h1 : 0 ≤ (1 - a.etaD) * (1 - P.alpha * (1 + a.etaD)) := mul_nonneg (by linarith) f1.le
  have h2 : 0 ≤ (1 - a.etaP) * (P.od - P.beta * (1 + a.etaP)) := mul_nonneg (by linarith) f2.le
  rw [prof_O hO, profO]
  refine ⟨by nlinarith, fun hle => ?_⟩
  have e1 : (1 - a.etaD) * (1 - P.alpha * (1 + a.etaD)) = 0 := by nlinarith
  have e2 : (1 - a.etaP) * (P.od - P.beta * (1 + a.etaP)) = 0 := by nlinarith
  have hd : a.etaD = 1 := by
    rcases mul_eq_zero.1 e1 with h | h
    · linarith
    · linarith
  have hq : a.etaP = 1 := by
    rcases mul_eq_zero.1 e2 with h | h
    · linarith
    · linarith
  have hp' : a.p = 1 := by
    rw [hd, hq] at hle hp; nlinarith
  show (⟨a.p, a.etaD, a.etaP⟩ : Action) = aO
  rw [hp', hd, hq]; rfl

lemma opt_iff (hP : Regime P) (m : EPRModel) (y : Policy) (a : Action) :
    ProdOptimal P m y a ↔
      (a = aN P ∧ prodProfit P m y aO ≤ prodProfit P m y (aN P)) ∨
      (a = aO ∧ prodProfit P m y (aN P) ≤ prodProfit P m y aO) := by
  constructor
  · rintro ⟨hf, hmax⟩
    by_cases h : OverPrescribes P a
    · have hb := bound_O hP hf h m y
      have := hb.2 (hmax aO (feas_aO hP))
      subst this
      exact Or.inr ⟨rfl, hmax _ (feas_aN hP)⟩
    · have hb := bound_N hP hf h m y
      have := hb.2 (hmax (aN P) (feas_aN hP))
      subst this
      exact Or.inl ⟨rfl, hmax _ (feas_aO hP)⟩
  · rintro (⟨rfl, hle⟩ | ⟨rfl, hle⟩)
    · refine ⟨feas_aN hP, fun a' ha' => ?_⟩
      by_cases h : OverPrescribes P a'
      · exact (bound_O hP ha' h m y).1.trans hle
      · exact (bound_N hP ha' h m y).1
    · refine ⟨feas_aO hP, fun a' ha' => ?_⟩
      by_cases h : OverPrescribes P a'
      · exact (bound_O hP ha' h m y).1
      · exact (bound_N hP ha' h m y).1.trans hle

/-! ## Achievable sets -/

def NE (P : Params) : Set ℝ := Set.Icc 0 1 ∩ {r | 3 * (1 - 2 * P.beta - P.up) ≤ 2 * P.k * r} ∩
  {r | P.k * r ≤ 3 * (P.up + 1 - 2 * P.alpha)}
def OE (P : Params) : Set ℝ := Set.Icc 0 1 ∩ {r | 2 * P.k * r ≤ 3 * (1 - 2 * P.beta - P.up)} ∩
  {r | P.k * r ≤ 2 * (1 - P.alpha - P.beta)}
def NS (P : Params) : Set ℝ := Set.Icc 0 1 ∩ {_r | 1 - 2 * P.beta - P.up ≤ P.up + 1 - 2 * P.alpha} ∩
  {r | P.k * r ≤ 3 * (P.up + 1 - 2 * P.alpha)}
def OS (P : Params) : Set ℝ := Set.Icc 0 1 ∩ {r | P.k * r ≤ 2 * (1 - 2 * P.beta - P.up)} ∩
  {r | P.k * r ≤ 2 * (1 - P.alpha - P.beta)}

lemma mNE {r : ℝ} : r ∈ NE P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ 3 * (1 - 2 * P.beta - P.up) ≤ 2 * P.k * r) ∧
    P.k * r ≤ 3 * (P.up + 1 - 2 * P.alpha) := Iff.rfl
lemma mOE {r : ℝ} : r ∈ OE P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ 2 * P.k * r ≤ 3 * (1 - 2 * P.beta - P.up)) ∧
    P.k * r ≤ 2 * (1 - P.alpha - P.beta) := Iff.rfl
lemma mNS {r : ℝ} : r ∈ NS P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ 1 - 2 * P.beta - P.up ≤ P.up + 1 - 2 * P.alpha) ∧
    P.k * r ≤ 3 * (P.up + 1 - 2 * P.alpha) := Iff.rfl
lemma mOS {r : ℝ} : r ∈ OS P ↔ ((0 ≤ r ∧ r ≤ 1) ∧ P.k * r ≤ 2 * (1 - 2 * P.beta - P.up)) ∧
    P.k * r ≤ 2 * (1 - P.alpha - P.beta) := Iff.rfl

lemma outN_EC (hP : Regime P) {r : ℝ} (hr : r ∈ NE P) : Outcome P .EC ⟨r, 0⟩ (aN P) := by
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mNE.1 hr
  refine ⟨h0, h1, (fun h => by cases h), (opt_iff hP _ _ _).2 (Or.inl ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profN hP]; simp only [ccN]; linarith
  · simp only [plannerSurplus]; exact le_rfl

lemma outO_EC (hP : Regime P) {r : ℝ} (hr : r ∈ OE P) : Outcome P .EC ⟨r, 0⟩ aO := by
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mOE.1 hr
  refine ⟨h0, h1, (fun h => by cases h), (opt_iff hP _ _ _).2 (Or.inr ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profO]; simp only [ccO]; linarith
  · simp only [plannerSurplus]; exact le_rfl

lemma outN_SR (hP : Regime P) {r : ℝ} (hr : r ∈ NS P) :
    Outcome P .SR ⟨r, P.up + 1 - 2 * P.alpha⟩ (aN P) := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, -⟩ := hP'
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mNS.1 hr
  refine ⟨h0, h1, (fun _ => by show (0:ℝ) ≤ P.up + 1 - 2 * P.alpha; linarith),
    (opt_iff hP _ _ _).2 (Or.inl ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profN hP]; simp only [ccN]; linarith
  · rw [plSR_N (nOP_aN hP)]; simp only; linarith

lemma outO_SR (hP : Regime P) {r : ℝ} (hr : r ∈ OS P) :
    Outcome P .SR ⟨r, P.k * r / 2⟩ aO := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, hb, hbo, hab, hk, -⟩ := hP'
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mOS.1 hr
  have hkr : 0 ≤ P.k * r := mul_nonneg hk.le h0
  refine ⟨h0, h1, (fun _ => by show (0:ℝ) ≤ P.k * r / 2; linarith),
    (opt_iff hP _ _ _).2 (Or.inr ⟨rfl, ?_⟩), ?_, ?_⟩
  · rw [profN hP, profO]; simp only [ccN, ccO]; linarith
  · rw [profO]; simp only [ccO]; linarith
  · rw [plSR_O OP_aO]; simp only; linarith

lemma achEC (hP : Regime P) : achievable P .EC = WN P '' NE P ∪ WO P '' OE P := by
  ext w
  constructor
  · rintro ⟨y, a, ⟨hr0, hr1, -, hopt, hpr, -⟩, rfl⟩
    rcases (opt_iff hP _ _ _).1 hopt with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
    · rw [profN hP, profO] at hle; rw [profN hP] at hpr
      simp only [ccN, ccO] at hle hpr
      exact Or.inl ⟨y.r, mNE.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩, (welN hP _ _).symm⟩
    · rw [profN hP, profO] at hle; rw [profO] at hpr
      simp only [ccN, ccO] at hle hpr
      exact Or.inr ⟨y.r, mOE.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩, (welO _ _).symm⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨⟨r, 0⟩, aN P, outN_EC hP hr, welN hP _ _⟩
    · exact ⟨⟨r, 0⟩, aO, outO_EC hP hr, welO _ _⟩

lemma achSR (hP : Regime P) : achievable P .SR = WN P '' NS P ∪ WO P '' OS P := by
  ext w
  constructor
  · rintro ⟨y, a, ⟨hr0, hr1, ht, hopt, hpr, hpl⟩, rfl⟩
    have ht := ht rfl
    rcases (opt_iff hP _ _ _).1 hopt with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
    · rw [profN hP, profO] at hle; rw [profN hP] at hpr; rw [plSR_N (nOP_aN hP)] at hpl
      simp only [ccN, ccO] at hle hpr
      exact Or.inl ⟨y.r, mNS.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩, (welN hP _ _).symm⟩
    · rw [profN hP, profO] at hle; rw [profO] at hpr; rw [plSR_O OP_aO] at hpl
      simp only [ccN, ccO] at hle hpr
      exact Or.inr ⟨y.r, mOS.2 ⟨⟨⟨hr0, hr1⟩, by linarith⟩, by linarith⟩, (welO _ _).symm⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨_, aN P, outN_SR hP hr, welN hP _ _⟩
    · exact ⟨_, aO, outO_SR hP hr, welO _ _⟩

lemma noOP_mem (hP : Regime P) {r : ℝ} (hr : r ∈ NE P) : WN P r ∈ achievableNoOP P .EC :=
  ⟨⟨r, 0⟩, aN P, outN_EC hP hr, nOP_aN hP, welN hP _ _⟩

/-! ## Compactness and maxima -/

lemma cNE : IsCompact (NE P) :=
  (isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))).inter_right
    (isClosed_le (by fun_prop) continuous_const)
lemma cOE : IsCompact (OE P) :=
  (isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)).inter_right
    (isClosed_le (by fun_prop) continuous_const)
lemma cNS : IsCompact (NS P) :=
  (isCompact_Icc.inter_right (isClosed_le continuous_const continuous_const)).inter_right
    (isClosed_le (by fun_prop) continuous_const)
lemma cOS : IsCompact (OS P) :=
  (isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)).inter_right
    (isClosed_le (by fun_prop) continuous_const)

lemma contWN : Continuous (fun r => WN P r) := by simp only [WN]; fun_prop
lemma contWO : Continuous (fun r => WO P r) := by simp only [WO]; fun_prop

lemma greatest_of {S : Set ℝ} (hc : IsCompact S) (hne : S.Nonempty) : IsGreatest S (sSup S) :=
  ⟨hc.sSup_mem hne, fun _ hx => le_csSup hc.bddAbove hx⟩

lemma cpt_EC (hP : Regime P) : IsCompact (achievable P .EC) := by
  rw [achEC hP]; exact (cNE.image contWN).union (cOE.image contWO)

lemma cpt_SR (hP : Regime P) : IsCompact (achievable P .SR) := by
  rw [achSR hP]; exact (cNS.image contWN).union (cOS.image contWO)

lemma ne_EC (hP : Regime P) : (achievable P .EC).Nonempty := by
  rw [achEC hP]
  obtain ⟨hu, ha, ha4, hb, hbo, hab, hk, -, -⟩ := hP
  by_cases h : 0 ≤ 1 - 2 * P.beta - P.up
  · exact ⟨WO P 0, Or.inr ⟨0, mOE.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩, rfl⟩⟩
  · exact ⟨WN P 0, Or.inl ⟨0, mNE.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩, rfl⟩⟩

lemma ne_SR (hP : Regime P) : (achievable P .SR).Nonempty := by
  rw [achSR hP]
  obtain ⟨hu, ha, ha4, hb, hbo, hab, hk, -, -⟩ := hP
  by_cases h : 0 ≤ 1 - 2 * P.beta - P.up
  · exact ⟨WO P 0, Or.inr ⟨0, mOS.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩, rfl⟩⟩
  · exact ⟨WN P 0, Or.inl ⟨0, mNS.2 ⟨⟨⟨le_rfl, zero_le_one⟩, by linarith⟩, by linarith⟩, rfl⟩⟩

lemma greatest (hP : Regime P) (m : EPRModel) : IsGreatest (achievable P m) (optW P m) := by
  cases m
  · exact greatest_of (cpt_EC hP) (ne_EC hP)
  · exact greatest_of (cpt_SR hP) (ne_SR hP)

lemma NE_NS (hus : uSR P ≤ P.up) : NE P ⊆ NS P := by
  intro r hr
  obtain ⟨⟨h01, -⟩, h3⟩ := mNE.1 hr
  unfold uSR at hus
  exact mNS.2 ⟨⟨h01, by linarith⟩, h3⟩

lemma OE_OS (hP : Regime P) : OE P ⊆ OS P := by
  intro r hr
  have hk : 0 < P.k := hP.2.2.2.2.2.2.1
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := mOE.1 hr
  have hkr : 0 ≤ P.k * r := mul_nonneg hk.le h0
  exact mOS.2 ⟨⟨⟨h0, h1⟩, by linarith⟩, h3⟩

lemma sub_ECSR (hP : Regime P) (hus : uSR P ≤ P.up) :
    achievable P .EC ⊆ achievable P .SR := by
  rw [achEC hP, achSR hP]
  rintro x (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
  · exact Or.inl ⟨r, NE_NS hus hr, rfl⟩
  · exact Or.inr ⟨r, OE_OS hP hr, rfl⟩

lemma le_ECSR (hP : Regime P) (hus : uSR P ≤ P.up) : optW P .EC ≤ optW P .SR :=
  csSup_le_csSup (cpt_SR hP).bddAbove (ne_EC hP) (sub_ECSR hP hus)

lemma NE_empty (hP : Regime P) (hkb : P.k < kBar P) : NE P = ∅ := by
  have hk : 0 < P.k := hP.2.2.2.2.2.2.1
  ext r; simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, -⟩ := mNE.1 hr
  unfold kBar at hkb
  have : P.k * r ≤ P.k := by nlinarith
  linarith

lemma NS_empty (hus : P.up < uSR P) : NS P = ∅ := by
  ext r; simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  obtain ⟨⟨-, h2⟩, -⟩ := mNS.1 hr
  unfold uSR at hus
  linarith

lemma OE_eq_OS (hP : Regime P) (hkb : P.k < kBar P) : OE P = OS P := by
  have hk : 0 < P.k := hP.2.2.2.2.2.2.1
  unfold kBar at hkb
  ext r; rw [mOE, mOS]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, -⟩, h3⟩
    have : P.k * r ≤ P.k := by nlinarith
    exact ⟨⟨⟨h0, h1⟩, by linarith⟩, h3⟩
  · rintro ⟨⟨⟨h0, h1⟩, -⟩, h3⟩
    have : P.k * r ≤ P.k := by nlinarith
    exact ⟨⟨⟨h0, h1⟩, by linarith⟩, h3⟩

/-! ## Varying the environmental disutility -/

def Qe (P : Params) (e : ℝ) : Params := { P with epsE := e }

lemma regQ (hP : Regime P) {e : ℝ} (he : 0 ≤ e) : Regime (Qe P e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9⟩ := hP
  exact ⟨h1, h2, h3, h4, h5, h6, h7, he, h9⟩

noncomputable def rN (P : Params) : ℝ := min 1 (3 * (P.up + 1 - 2 * P.alpha) / P.k)

lemma rN_pos (hP : Regime P) : 0 < rN P := by
  obtain ⟨hu, ha, ha4, -, -, -, hk, -, -⟩ := hP
  exact lt_min one_pos (div_pos (by linarith) hk)

lemma rN_le1 : rN P ≤ 1 := min_le_left _ _

lemma rN_k (hP : Regime P) : P.k * rN P ≤ 3 * (P.up + 1 - 2 * P.alpha) := by
  have hk : 0 < P.k := hP.2.2.2.2.2.2.1
  have h : rN P ≤ 3 * (P.up + 1 - 2 * P.alpha) / P.k := min_le_right _ _
  rw [le_div_iff₀ hk] at h; linarith

lemma rN_ge (hP : Regime P) {r : ℝ} (h1 : r ≤ 1) (h2 : P.k * r ≤ 3 * (P.up + 1 - 2 * P.alpha)) :
    r ≤ rN P := by
  have hk : 0 < P.k := hP.2.2.2.2.2.2.1
  exact le_min h1 (by rw [le_div_iff₀ hk]; linarith)

lemma rN_mem (hP : Regime P) (hkb : kBar P ≤ P.k) : rN P ∈ NE P := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, hb, -, -, hk, -, -⟩ := hP'
  refine mNE.2 ⟨⟨⟨(rN_pos hP).le, rN_le1⟩, ?_⟩, rN_k hP⟩
  unfold kBar at hkb
  rcases min_cases (1:ℝ) (3 * (P.up + 1 - 2 * P.alpha) / P.k) with ⟨h, -⟩ | ⟨h, -⟩
  · have e : rN P = 1 := h
    rw [e]; linarith
  · have e : rN P = 3 * (P.up + 1 - 2 * P.alpha) / P.k := h
    have hk0 : P.k ≠ 0 := hk.ne'
    have : P.k * rN P = 3 * (P.up + 1 - 2 * P.alpha) := by rw [e]; field_simp
    linarith

lemma key (hP : Regime P) {e r : ℝ}
    (he : max 0 (P.k - P.epsS) + 3 * (1 + P.epsS) / rN P ≤ e)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : WO (Qe P e) r ≤ WN (Qe P e) (rN P) := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, hb, -, -, hk, -, hs⟩ := hP'
  have hrN := rN_pos hP
  have hm1 : P.k - P.epsS ≤ max 0 (P.k - P.epsS) := le_max_right _ _
  have hpos : 0 ≤ 3 * (1 + P.epsS) / rN P := by positivity
  have hX0 : 0 ≤ e + P.epsS - P.k := by linarith
  have hX : 3 * (1 + P.epsS) ≤ (e + P.epsS - P.k) * rN P := by
    have h1 : 3 * (1 + P.epsS) / rN P ≤ e + P.epsS - P.k := by linarith
    rwa [div_le_iff₀ hrN] at h1
  have h2 : r * (e + P.epsS - P.k) ≤ e + P.epsS - P.k := mul_le_of_le_one_left hX0 hr1
  simp only [WO, WN, Qe]
  nlinarith

lemma envelope {K : Set ℝ} (V : ℝ → ℝ → ℝ) (M : ℝ → ℝ) {lo hi e1 e2 : ℝ}
    (hV : ∀ r ∈ K, lo * (e2 - e1) ≤ V e2 r - V e1 r ∧ V e2 r - V e1 r ≤ hi * (e2 - e1))
    (h1 : IsGreatest ((V e1) '' K) (M e1)) (h2 : IsGreatest ((V e2) '' K) (M e2)) :
    lo * (e2 - e1) ≤ M e2 - M e1 ∧ M e2 - M e1 ≤ hi * (e2 - e1) := by
  obtain ⟨r1, hr1, hm1⟩ := h1.1
  obtain ⟨r2, hr2, hm2⟩ := h2.1
  have a1 : V e2 r1 ≤ M e2 := h2.2 ⟨r1, hr1, rfl⟩
  have a2 : V e1 r2 ≤ M e1 := h1.2 ⟨r2, hr2, rfl⟩
  have b1 := hV r1 hr1
  have b2 := hV r2 hr2
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

lemma threshold (A B : ℝ → ℝ)
    (hmono : ∀ e1 e2, 0 ≤ e1 → e1 ≤ e2 → B e2 - B e1 ≤ A e2 - A e1)
    (hlip : ∀ e1 e2, 0 ≤ e1 → e1 ≤ e2 → (A e2 - B e2) - (A e1 - B e1) ≤ 2 * (e2 - e1))
    (e0 : ℝ) (he0 : 0 ≤ e0) (h0 : B e0 ≤ A e0) :
    ∃ T : ℝ, ∀ e, 0 ≤ e → (T ≤ e → B e ≤ A e) ∧ (e < T → A e < B e) := by
  let S : Set ℝ := {e | 0 ≤ e ∧ B e ≤ A e}
  have hne : S.Nonempty := ⟨e0, he0, h0⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have hT0 : 0 ≤ sInf S := le_csInf hne (fun x hx => hx.1)
  have hTS : B (sInf S) ≤ A (sInf S) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt hne
      (show sInf S < sInf S + (B (sInf S) - A (sInf S)) / 4 by linarith)
    have hle : sInf S ≤ s := csInf_le hbdd hs
    have h3 := hlip (sInf S) s hT0 hle
    have h4 : B s ≤ A s := hs.2
    linarith
  refine ⟨sInf S, fun e he => ⟨fun hTe => ?_, fun heT => ?_⟩⟩
  · have := hmono (sInf S) e hT0 hTe; linarith
  · by_contra hcon
    push Not at hcon
    exact absurd (csInf_le hbdd ⟨he, hcon⟩) (not_le.2 heT)

lemma clause6 (hP : Regime P) (hkb : kBar P ≤ P.k) : ∃ T : ℝ, ∀ e : ℝ, 0 ≤ e →
    (T ≤ e → optW (Qe P e) .SR ≤ optW (Qe P e) .EC ∧
      optW (Qe P e) .EC ∈ achievableNoOP (Qe P e) .EC) ∧
    (e < T → optW (Qe P e) .EC ≤ optW (Qe P e) .SR) := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, hb, hbo, hab, hk, -, hs⟩ := hP'
  have hrNm := rN_mem hP hkb
  have hrN := rN_pos hP
  have he0 : 0 ≤ max 0 (P.k - P.epsS) + 3 * (1 + P.epsS) / rN P := by
    have : (0:ℝ) ≤ max 0 (P.k - P.epsS) := le_max_left _ _
    have : 0 ≤ 3 * (1 + P.epsS) / rN P := by positivity
    linarith
  by_cases hus : uSR P ≤ P.up
  · refine ⟨max 0 (P.k - P.epsS) + 3 * (1 + P.epsS) / rN P, fun e he =>
      ⟨fun hTe => ?_, fun _ => le_ECSR (regQ hP he) hus⟩⟩
    have hQ := regQ hP he
    have hX0 : 0 ≤ e + P.epsS - P.k := by
      have : P.k - P.epsS ≤ max 0 (P.k - P.epsS) := le_max_right _ _
      have : 0 ≤ 3 * (1 + P.epsS) / rN P := by positivity
      linarith
    have hSR : ∀ x ∈ achievable (Qe P e) .SR, x ≤ WN (Qe P e) (rN P) := by
      rw [achSR hQ]
      rintro x (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
      · obtain ⟨⟨⟨h0, h1⟩, -⟩, h3⟩ := mNS.1 hr
        have hle : r ≤ rN P := rN_ge hP h1 h3
        have := mul_nonneg (sub_nonneg.2 hle) hX0
        simp only [WN, Qe]
        nlinarith
      · obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := mOS.1 hr
        exact key hP hTe h0 h1
    have hwEC : WN (Qe P e) (rN P) ∈ achievable (Qe P e) .EC := by
      rw [achEC hQ]; exact Or.inl ⟨rN P, hrNm, rfl⟩
    have hsub := sub_ECSR hQ hus
    have gEC : IsGreatest (achievable (Qe P e) .EC) (WN (Qe P e) (rN P)) :=
      ⟨hwEC, fun x hx => hSR x (hsub hx)⟩
    have gSR : IsGreatest (achievable (Qe P e) .SR) (WN (Qe P e) (rN P)) := ⟨hsub hwEC, hSR⟩
    have e1 : optW (Qe P e) .EC = WN (Qe P e) (rN P) := gEC.csSup_eq
    have e2 : optW (Qe P e) .SR = WN (Qe P e) (rN P) := gSR.csSup_eq
    refine ⟨by rw [e1, e2], ?_⟩
    rw [e1]; exact noOP_mem hQ hrNm
  · push Not at hus
    have hNS : NS P = ∅ := NS_empty hus
    have achSR' : ∀ e, 0 ≤ e → achievable (Qe P e) .SR = WO (Qe P e) '' OS P := by
      intro e he
      rw [achSR (regQ hP he), show NS (Qe P e) = ∅ from hNS, Set.image_empty, Set.empty_union]
      rfl
    have hAg : ∀ e, IsGreatest (WN (Qe P e) '' NE P) (sSup (WN (Qe P e) '' NE P)) := fun e =>
      greatest_of ((cNE (P := P)).image (contWN (P := Qe P e))) ⟨_, rN P, hrNm, rfl⟩
    have hBg : ∀ e, 0 ≤ e → IsGreatest (WO (Qe P e) '' OS P) (optW (Qe P e) .SR) := by
      intro e he
      have := greatest (regQ hP he) .SR
      rwa [achSR' e he] at this
    have slN : ∀ e1 e2 : ℝ, e1 ≤ e2 → ∀ r ∈ NE P,
        (-1/2) * (e2 - e1) ≤ WN (Qe P e2) r - WN (Qe P e1) r ∧
        WN (Qe P e2) r - WN (Qe P e1) r ≤ (-1/3) * (e2 - e1) := by
      intro e1 e2 h12 r hr
      obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := mNE.1 hr
      have i1 := mul_nonneg (sub_nonneg.2 h12) h0
      have i2 := mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 h1)
      simp only [WN, Qe]
      constructor <;> nlinarith
    have slO : ∀ e1 e2 : ℝ, e1 ≤ e2 → ∀ r ∈ OS P,
        (-1) * (e2 - e1) ≤ WO (Qe P e2) r - WO (Qe P e1) r ∧
        WO (Qe P e2) r - WO (Qe P e1) r ≤ (-1/2) * (e2 - e1) := by
      intro e1 e2 h12 r hr
      obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := mOS.1 hr
      have i1 := mul_nonneg (sub_nonneg.2 h12) h0
      have i2 := mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 h1)
      simp only [WO, Qe]
      constructor <;> nlinarith
    have h0 : optW (Qe P (max 0 (P.k - P.epsS) + 3 * (1 + P.epsS) / rN P)) .SR ≤
        sSup (WN (Qe P (max 0 (P.k - P.epsS) + 3 * (1 + P.epsS) / rN P)) '' NE P) := by
      obtain ⟨r, hr, hrw⟩ := (hBg _ he0).1
      obtain ⟨⟨⟨h0, h1⟩, -⟩, -⟩ := mOS.1 hr
      rw [← hrw]
      exact (key hP le_rfl h0 h1).trans ((hAg _).2 ⟨rN P, hrNm, rfl⟩)
    obtain ⟨T, hT⟩ := threshold (fun e => sSup (WN (Qe P e) '' NE P))
      (fun e => optW (Qe P e) .SR)
      (fun e1 e2 h1 h12 => by
        have a := envelope (K := NE P) (fun e r => WN (Qe P e) r)
          (fun e => sSup (WN (Qe P e) '' NE P)) (slN e1 e2 h12) (hAg e1) (hAg e2)
        have b := envelope (K := OS P) (fun e r => WO (Qe P e) r)
          (fun e => optW (Qe P e) .SR) (slO e1 e2 h12) (hBg e1 h1) (hBg e2 (h1.trans h12))
        try simp only at a b ⊢
        nlinarith [a.1, b.2])
      (fun e1 e2 h1 h12 => by
        have a := envelope (K := NE P) (fun e r => WN (Qe P e) r)
          (fun e => sSup (WN (Qe P e) '' NE P)) (slN e1 e2 h12) (hAg e1) (hAg e2)
        have b := envelope (K := OS P) (fun e r => WO (Qe P e) r)
          (fun e => optW (Qe P e) .SR) (slO e1 e2 h12) (hBg e1 h1) (hBg e2 (h1.trans h12))
        try simp only at a b ⊢
        nlinarith [a.2, b.1])
      _ he0 h0
    refine ⟨T, fun e he => ⟨fun hTe => ?_, fun heT => ?_⟩⟩
    · have hQ := regQ hP he
      have hBA : optW (Qe P e) .SR ≤ sSup (WN (Qe P e) '' NE P) := (hT e he).1 hTe
      have gEC : IsGreatest (achievable (Qe P e) .EC) (sSup (WN (Qe P e) '' NE P)) := by
        refine ⟨?_, ?_⟩
        · rw [achEC hQ]; exact Or.inl ((hAg e).1)
        · rw [achEC hQ]
          rintro x (hx | ⟨r, hr, rfl⟩)
          · exact (hAg e).2 hx
          · exact ((hBg e he).2 ⟨r, OE_OS hQ hr, rfl⟩).trans hBA
      have e1 : optW (Qe P e) .EC = sSup (WN (Qe P e) '' NE P) := gEC.csSup_eq
      refine ⟨by rw [e1]; exact hBA, ?_⟩
      rw [e1]
      obtain ⟨r, hr, hrw⟩ := (hAg e).1
      rw [← hrw]; exact noOP_mem hQ hr
    · have hQ := regQ hP he
      have hAB : sSup (WN (Qe P e) '' NE P) < optW (Qe P e) .SR := (hT e he).2 heT
      show sSup _ ≤ _
      apply csSup_le (ne_EC hQ)
      rw [achEC hQ]
      rintro x (hx | ⟨r, hr, rfl⟩)
      · exact ((hAg e).2 hx).trans hAB.le
      · exact (hBg e he).2 ⟨r, OE_OS hQ hr, rfl⟩

end P4X

open PharmaEPR.Welfare in
theorem solution (P : Params) (hP : Regime P) :
    IsGreatest (achievable P .EC) (optW P .EC) ∧
    IsGreatest (achievable P .SR) (optW P .SR) ∧
    (P.up < uEC P → optW P .EC = optW P .SR) ∧
    (uEC P ≤ P.up → P.up < uSR P → P.k < kBar P →
      optW P .EC = optW P .SR) ∧
    (uSR P ≤ P.up → P.k < kBar P →
      optW P .EC ≤ optW P .SR) ∧
    (uEC P ≤ P.up → kBar P ≤ P.k →
      ∃ epsilonT : ℝ, ∀ e : ℝ, 0 ≤ e →
        let Q : Params := { P with epsE := e }
        IsGreatest (achievable Q .EC) (optW Q .EC) ∧
        IsGreatest (achievable Q .SR) (optW Q .SR) ∧
        (epsilonT ≤ e →
          optW Q .SR ≤ optW Q .EC ∧
          optW Q .EC ∈ achievableNoOP Q .EC) ∧
        (e < epsilonT → optW Q .EC ≤ optW Q .SR)) := by
  have hP' := hP
  obtain ⟨hu, ha, ha4, hb, hbo, hab, hk, -, hs⟩ := hP'
  refine ⟨P4X.greatest hP .EC, P4X.greatest hP .SR, ?_, ?_, ?_, ?_⟩
  · intro h; exfalso; unfold uEC at h; linarith
  · intro _ hus hkb
    show sSup (achievable P .EC) = sSup (achievable P .SR)
    rw [P4X.achEC hP, P4X.achSR hP, P4X.NE_empty hP hkb, P4X.NS_empty hus, P4X.OE_eq_OS hP hkb]
  · intro hus _; exact P4X.le_ECSR hP hus
  · intro _ hkb
    obtain ⟨T, hT⟩ := P4X.clause6 hP hkb
    refine ⟨T, fun e he => ?_⟩
    intro Q
    exact ⟨P4X.greatest (P4X.regQ hP he) .EC, P4X.greatest (P4X.regQ hP he) .SR,
      (hT e he).1, (hT e he).2⟩
