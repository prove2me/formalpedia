-- Prove2me | solution 1 for OmniPool.BOPS.proposition_2_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:28:53.529799+00:00
-- url     : https://prove2.me/submissions/8de0da74-2418-4085-914a-b834736c5d6a

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPoolProp3Aux
open OmniPool.BOPS

lemma uniq {f : ℝ → ℝ} {x y : ℝ} (hx : IsUniqueMaxNonneg f x) (hy : 0 ≤ y)
    (hopt : ∀ q : ℝ, 0 ≤ q → f q ≤ f y) : y = x := by
  by_contra hne
  have := hx.2 y hy hne
  have := hopt x hx.1
  linarith

lemma uniq_opt {f : ℝ → ℝ} {x : ℝ} (hx : IsUniqueMaxNonneg f x) :
    ∀ q : ℝ, 0 ≤ q → f q ≤ f x := by
  intro q hq
  by_cases h : q = x
  · rw [h]
  · exact (hx.2 q hq h).le

variable {Ω : Type*} [MeasurableSpace Ω]

lemma intA (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (c q : ℝ) :
    Integrable (fun ω => min (Dm ω) (max (q - c * Ds ω) 0)) P := by
  have h1 : Integrable (fun ω => q - c * Ds ω) P :=
    (integrable_const q).sub (hDsi.const_mul c)
  have h2 : Integrable (fun ω => max (q - c * Ds ω) 0) P := h1.sup (integrable_const 0)
  exact hDmi.inf h2

/-- With `k ≤ t`, the BOPS profit equals the textbook form. -/
lemma profitP_eq (M : Market) (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hkt : M.k ≤ M.t) (φs q : ℝ) :
    profitP M P Ds Dm φs q = M.pb * ∫ ω, min (φs * Ds ω) q ∂P
      + M.co * ∫ ω, min (Dm ω) (max (q - φs * Ds ω) 0) ∂P - M.cb * q
      + (M.po - M.co) * ∫ ω, Dm ω ∂P := by
  have hb : bopsInd M = 1 := by simp [bopsInd, hkt]
  have hA := intA P Ds Dm hDsi hDmi φs q
  have e1 : (fun ω => min (bopsInd M * Dm ω) (max (q - φs * Ds ω) 0))
      = fun ω => min (Dm ω) (max (q - φs * Ds ω) 0) := by
    funext ω; rw [hb, one_mul]
  have e2 : (fun ω => (1 - bopsInd M) * Dm ω
        + max (bopsInd M * Dm ω - max (q - φs * Ds ω) 0) 0)
      = fun ω => Dm ω - min (Dm ω) (max (q - φs * Ds ω) 0) := by
    funext ω; rw [hb]
    rcases le_total (Dm ω) (max (q - φs * Ds ω) 0) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  unfold profitP
  rw [e1, e2, integral_sub hDmi hA]
  ring

lemma profitP_one_zero (M : Market) (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω)
    (hDm0 : ∀ ω, 0 ≤ Dm ω) (hkt : M.k ≤ M.t) :
    profitP M P Ds Dm 1 0 = (M.po - M.co) * ∫ ω, Dm ω ∂P := by
  rw [profitP_eq M P Ds Dm hDsi hDmi hkt]
  have e1 : (fun ω => min (1 * Ds ω) (0:ℝ)) = fun _ => (0:ℝ) := by
    funext ω; rw [one_mul, min_eq_right (hDs0 ω)]
  have e2 : (fun ω => min (Dm ω) (max ((0:ℝ) - 1 * Ds ω) 0)) = fun _ => (0:ℝ) := by
    funext ω
    rw [max_eq_right (by linarith [hDs0 ω]), min_eq_right (hDm0 ω)]
  rw [e1, e2]; simp

lemma profitP_zero_le (M : Market) (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P)
    (hDm0 : ∀ ω, 0 ≤ Dm ω) (hkt : M.k ≤ M.t) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (q : ℝ) (hq : 0 ≤ q) :
    profitP M P Ds Dm 0 q ≤ (M.po - M.co) * ∫ ω, Dm ω ∂P := by
  rw [profitP_eq M P Ds Dm hDsi hDmi hkt]
  have e1 : (fun ω => min (0 * Ds ω) q) = fun _ => (0:ℝ) := by
    funext ω; rw [zero_mul, min_eq_left hq]
  have hA := intA P Ds Dm hDsi hDmi 0 q
  have hle : ∫ ω, min (Dm ω) (max (q - 0 * Ds ω) 0) ∂P ≤ q := by
    have : ∫ ω, min (Dm ω) (max (q - 0 * Ds ω) 0) ∂P ≤ ∫ _ω, q ∂P := by
      apply integral_mono hA (integrable_const q)
      intro ω
      simp only [zero_mul, sub_zero, max_eq_left hq]
      exact min_le_right _ _
    simpa using this
  rw [e1]; simp only [integral_zero, mul_zero, zero_add]
  have : M.co * ∫ ω, min (Dm ω) (max (q - 0 * Ds ω) 0) ∂P ≤ M.cb * q := by
    calc M.co * ∫ ω, min (Dm ω) (max (q - 0 * Ds ω) 0) ∂P ≤ M.co * q :=
          mul_le_mul_of_nonneg_left hle hco
      _ ≤ M.cb * q := mul_le_mul_of_nonneg_right hcocb hq
  linarith

lemma profitB_le_profitP (M : Market) (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P)
    (hDm0 : ∀ ω, 0 ≤ Dm ω) (hkt : M.k ≤ M.t) (hco : 0 ≤ M.co) (q : ℝ) :
    profitB M P Ds Dm 1 0 q ≤ profitP M P Ds Dm 1 q := by
  rw [profitP_eq M P Ds Dm hDsi hDmi hkt]
  unfold profitB
  have e1 : (fun ω => min (0 * Dm ω + 1 * Ds ω) q) = fun ω => min (1 * Ds ω) q := by
    funext ω; rw [zero_mul, zero_add]
  have e2 : (fun ω => (1 - (0:ℝ)) * Dm ω) = fun ω => Dm ω := by
    funext ω; ring
  rw [e1, e2]
  have : 0 ≤ ∫ ω, min (Dm ω) (max (q - 1 * Ds ω) 0) ∂P :=
    integral_nonneg (fun ω => le_min (hDm0 ω) (le_max_right _ _))
  nlinarith [mul_nonneg hco this]

lemma profitB_zero_zero (M : Market) (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q) :
    profitB M P Ds Dm 0 0 q = - M.cb * q + (M.po - M.co) * ∫ ω, Dm ω ∂P := by
  unfold profitB
  have e1 : (fun ω => min (0 * Dm ω + 0 * Ds ω) q) = fun _ => (0:ℝ) := by
    funext ω; rw [zero_mul, zero_mul, add_zero, min_eq_left hq]
  have e2 : (fun ω => (1 - (0:ℝ)) * Dm ω) = fun ω => Dm ω := by
    funext ω; ring
  rw [e1, e2]; simp only [integral_zero, mul_zero, zero_add]; ring

lemma profitB_one_zero_zero (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (Ds Dm : Ω → ℝ) (hDs0 : ∀ ω, 0 ≤ Ds ω) :
    profitB M P Ds Dm 1 0 0 = (M.po - M.co) * ∫ ω, Dm ω ∂P := by
  unfold profitB
  have e1 : (fun ω => min (0 * Dm ω + 1 * Ds ω) (0:ℝ)) = fun _ => (0:ℝ) := by
    funext ω; rw [zero_mul, zero_add, one_mul, min_eq_right (hDs0 ω)]
  have e2 : (fun ω => (1 - (0:ℝ)) * Dm ω) = fun ω => Dm ω := by
    funext ω; ring
  rw [e1, e2]; simp

lemma fillB_one_zero_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (Ds Dm : Ω → ℝ) (hDs0 : ∀ ω, 0 ≤ Ds ω) : fillB P Ds Dm 1 0 0 = 0 := by
  unfold fillB
  rw [if_neg (by norm_num)]
  have e1 : (fun ω => min (0 * Dm ω + 1 * Ds ω) (0:ℝ)) = fun _ => (0:ℝ) := by
    funext ω; rw [zero_mul, zero_add, one_mul, min_eq_right (hDs0 ω)]
  rw [e1]; simp

lemma fillP_one_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (Ds : Ω → ℝ) (hDs0 : ∀ ω, 0 ≤ Ds ω) : fillP P Ds 1 0 = 0 := by
  unfold fillP
  rw [if_neg (by norm_num)]
  have e1 : (fun ω => min (1 * Ds ω) (0:ℝ)) = fun _ => (0:ℝ) := by
    funext ω; rw [one_mul, min_eq_right (hDs0 ω)]
  rw [e1]; simp

lemma fillB_one_zero_nonneg (P : Measure Ω) [IsProbabilityMeasure P]
    (Ds Dm : Ω → ℝ) (hDs0 : ∀ ω, 0 ≤ Ds ω) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ fillB P Ds Dm 1 0 q := by
  unfold fillB
  rw [if_neg (by norm_num)]
  apply div_nonneg
  · exact integral_nonneg (fun ω => le_min (by simp [hDs0 ω]) hq)
  · exact integral_nonneg (fun ω => by simp [hDs0 ω])

end OmniPoolProp3Aux

open OmniPool.BOPS OmniPoolProp3Aux in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hreg : M.k ≤ min M.t (zetaP P Ds qp * M.ub)) :
    bopsInd M = 1 ∧ (∃ e, IsParetoREE_P M P Ds Dm e) ∧
      ∀ e, IsParetoREE_P M P Ds Dm e → e.q = qp ∧ e.φs = 1 := by
  have hkt : M.k ≤ M.t := le_trans hreg (min_le_left _ _)
  have hkp : M.k ≤ fillP P Ds 1 qp * M.ub := le_trans hreg (min_le_right _ _)
  have hP10 := profitP_one_zero M P Ds Dm hDsi hDmi hDs0 hDm0 hkt
  have hPqp0 : profitP M P Ds Dm 1 0 ≤ profitP M P Ds Dm 1 qp := uniq_opt hqp 0 le_rfl
  let eStar : BopsOutcome := ⟨qp, fillP P Ds 1 qp, 1⟩
  have hStarREE : IsREE_P M P Ds Dm eStar := by
    refine ⟨?_, hqp.1, uniq_opt hqp, rfl⟩
    show (1:ℝ) = choiceP M (fillP P Ds 1 qp)
    unfold choiceP; rw [if_pos hkp]
  have hStarU : 0 ≤ fillP P Ds 1 qp * M.ub - M.k := by linarith
  -- classification
  have classP : ∀ e : BopsOutcome, IsREE_P M P Ds Dm e →
      (e.φs = 1 ∧ e.q = qp ∧ e.ζ = fillP P Ds 1 qp) ∨ e.φs = 0 := by
    intro e ⟨hc, hq, hopt, hζ⟩
    unfold choiceP at hc
    split_ifs at hc with h1
    · rw [hc] at hopt hζ
      have hqe : e.q = qp := uniq hqp hq hopt
      rw [hqe] at hζ
      exact Or.inl ⟨hc, hqe, hζ⟩
    · exact Or.inr hc
  have hStarPareto : IsParetoREE_P M P Ds Dm eStar := by
    refine ⟨hStarREE, ?_⟩
    intro e he
    rcases classP e he with ⟨hc, hqe, hζ⟩ | hc
    · unfold retailerP storeUtilP
      rw [hc, hqe, hζ]
      exact ⟨le_rfl, le_rfl⟩
    · unfold retailerP storeUtilP
      rw [hc]
      refine ⟨?_, ?_⟩
      · have := profitP_zero_le M P Ds Dm hDsi hDmi hDm0 hkt hco hcocb e.q he.2.1
        show profitP M P Ds Dm 0 e.q ≤ profitP M P Ds Dm 1 qp
        linarith
      · show 0 * (e.ζ * M.ub - M.k) ≤ 1 * (fillP P Ds 1 qp * M.ub - M.k)
        linarith
  refine ⟨by simp [bopsInd, hkt], ⟨eStar, hStarPareto⟩, ?_⟩
  intro e he
  rcases classP e he.1 with ⟨hc, hqe, -⟩ | hc
  · exact ⟨hqe, hc⟩
  · exfalso
    have hdom := he.2 eStar hStarREE
    have hr : profitP M P Ds Dm 1 qp ≤ profitP M P Ds Dm 0 e.q := by
      have := hdom.1; unfold retailerP at this; rw [hc] at this; exact this
    have hz := profitP_zero_le M P Ds Dm hDsi hDmi hDm0 hkt hco hcocb e.q he.1.2.1
    have hq0 : qp = 0 := by
      by_contra hne
      have := hqp.2 0 le_rfl (Ne.symm hne)
      linarith
    rw [hq0, fillP_one_zero P Ds hDs0] at hkp
    linarith
