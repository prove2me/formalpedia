-- Prove2me | solution 1 for OmniPool.BOPS.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:23:33.192741+00:00
-- url     : https://prove2.me/submissions/ef5e10e2-61c8-45ec-b3f1-8dba90dc380b

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

end OmniPoolProp3Aux

open OmniPool.BOPS OmniPoolProp3Aux in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qs : ℝ) (hqs : IsUniqueMaxNonneg (profitB M P Ds Dm 1 0) qs)
    (qsm : ℝ) (hqsm : IsUniqueMaxNonneg (profitB M P Ds Dm 1 1) qsm)
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hlo : zetaSM P Ds Dm qsm * M.ub - M.uo + M.t < M.k)
    (hhi : M.k ≤ min M.t (zetaP P Ds qp * M.ub)) :
    (∃ e, IsParetoREE_B M P Ds Dm e) ∧ (∃ e, IsParetoREE_P M P Ds Dm e) ∧
      ∀ eB eP, IsParetoREE_B M P Ds Dm eB → IsParetoREE_P M P Ds Dm eP →
        retailerB M P Ds Dm eB ≤ retailerP M P Ds Dm eP := by
  have hkt : M.k ≤ M.t := le_trans hhi (min_le_left _ _)
  have hkp : M.k ≤ fillP P Ds 1 qp * M.ub := le_trans hhi (min_le_right _ _)
  have htuo : M.t ≤ M.uo := le_trans (le_max_left _ _) hU
  -- key values
  have hP10 := profitP_one_zero M P Ds Dm hDsi hDmi hDs0 hDm0 hkt
  have hPqp0 : profitP M P Ds Dm 1 0 ≤ profitP M P Ds Dm 1 qp := uniq_opt hqp 0 le_rfl
  have hB10 := profitB_one_zero_zero M P Ds Dm hDs0
  have hBqs0 : profitB M P Ds Dm 1 0 0 ≤ profitB M P Ds Dm 1 0 qs := uniq_opt hqs 0 le_rfl
  -- classification of BASE equilibria
  have classB : ∀ e : BaseOutcome, IsREE_B M P Ds Dm e →
      (e.φs = 0 ∧ e.φm = 0) ∨ (e.φs = 1 ∧ e.φm = 0 ∧ e.q = qs ∧
        e.ζ = fillB P Ds Dm 1 0 qs ∧ choiceB M (fillB P Ds Dm 1 0 qs) = (1, 0)) := by
    intro e ⟨hc, hq, hopt, hζ⟩
    unfold choiceB at hc
    split_ifs at hc with h1 h2
    · -- (1,1): impossible
      simp only [Prod.mk.injEq] at hc
      obtain ⟨hs, hm⟩ := hc
      rw [hs, hm] at hopt hζ
      have hqe : e.q = qsm := uniq hqsm hq hopt
      rw [hqe] at hζ
      have : e.ζ = zetaSM P Ds Dm qsm := hζ
      rw [this] at h1
      linarith
    · simp only [Prod.mk.injEq] at hc
      obtain ⟨hs, hm⟩ := hc
      rw [hs, hm] at hopt hζ
      have hqe : e.q = qs := uniq hqs hq hopt
      rw [hqe] at hζ
      right
      refine ⟨hs, hm, hqe, hζ, ?_⟩
      rw [← hζ]; unfold choiceB; rw [if_neg h1, if_pos h2]
    · simp only [Prod.mk.injEq] at hc
      left; exact hc
  have retB_le : ∀ e : BaseOutcome, IsREE_B M P Ds Dm e →
      retailerB M P Ds Dm e ≤ profitP M P Ds Dm 1 qp := by
    intro e he
    rcases classB e he with ⟨hs, hm⟩ | ⟨hs, hm, hq, -, -⟩
    · unfold retailerB; rw [hs, hm, profitB_zero_zero M P Ds Dm e.q he.2.1]
      nlinarith [he.2.1]
    · unfold retailerB; rw [hs, hm, hq]
      calc profitB M P Ds Dm 1 0 qs ≤ profitP M P Ds Dm 1 qs :=
            profitB_le_profitP M P Ds Dm hDsi hDmi hDm0 hkt hco qs
        _ ≤ profitP M P Ds Dm 1 qp := uniq_opt hqp qs hqs.1
  -- BOPS candidate
  let eStar : BopsOutcome := ⟨qp, fillP P Ds 1 qp, 1⟩
  have hStarREE : IsREE_P M P Ds Dm eStar := by
    refine ⟨?_, hqp.1, uniq_opt hqp, rfl⟩
    show (1:ℝ) = choiceP M (fillP P Ds 1 qp)
    unfold choiceP; rw [if_pos hkp]
  have hStarU : 0 ≤ fillP P Ds 1 qp * M.ub - M.k := by
    linarith
  have hStarPareto : IsParetoREE_P M P Ds Dm eStar := by
    refine ⟨hStarREE, ?_⟩
    intro e ⟨hc, hq, hopt, hζ⟩
    unfold choiceP at hc
    split_ifs at hc with h1
    · rw [hc] at hopt hζ
      have hqe : e.q = qp := uniq hqp hq hopt
      rw [hqe] at hζ
      unfold retailerP storeUtilP
      rw [hc, hqe, hζ]
      exact ⟨le_rfl, le_rfl⟩
    · unfold retailerP storeUtilP
      rw [hc]
      refine ⟨?_, ?_⟩
      · have := profitP_zero_le M P Ds Dm hDsi hDmi hDm0 hkt hco hcocb e.q hq
        show profitP M P Ds Dm 0 e.q ≤ profitP M P Ds Dm 1 qp
        linarith
      · show 0 * (e.ζ * M.ub - M.k) ≤ 1 * (fillP P Ds 1 qp * M.ub - M.k)
        linarith
  refine ⟨?_, ⟨eStar, hStarPareto⟩, ?_⟩
  · -- BASE existence
    by_cases h1 : choiceB M (fillB P Ds Dm 1 0 qs) = (1, 0)
    · let e1 : BaseOutcome := ⟨qs, fillB P Ds Dm 1 0 qs, 1, 0⟩
      have hU1 : 0 ≤ fillB P Ds Dm 1 0 qs * M.ub - M.k := by
        unfold choiceB at h1
        split_ifs at h1 with ha hb
        · simp at h1
        · exact hb
        · simp at h1
      refine ⟨e1, ⟨h1.symm, hqs.1, uniq_opt hqs, rfl⟩, ?_⟩
      intro e he
      rcases classB e he with ⟨hs, hm⟩ | ⟨hs, hm, hq, hζ, -⟩
      · refine ⟨?_, ?_, ?_⟩
        · unfold retailerB; rw [hs, hm, profitB_zero_zero M P Ds Dm e.q he.2.1]
          show _ ≤ profitB M P Ds Dm 1 0 qs
          nlinarith [he.2.1]
        · unfold storeUtilB; rw [hs]
          show 0 * (e.ζ * M.ub - M.k) ≤ 1 * (fillB P Ds Dm 1 0 qs * M.ub - M.k)
          linarith
        · unfold omniUtilB; rw [hm]
          show 0 * (e.ζ * M.ub - M.k) + (1 - 0) * (M.uo - M.t)
            ≤ 0 * (fillB P Ds Dm 1 0 qs * M.ub - M.k) + (1 - 0) * (M.uo - M.t)
          simp
      · refine ⟨?_, ?_, ?_⟩
        · unfold retailerB; rw [hs, hm, hq]
        · unfold storeUtilB; rw [hs, hζ]
        · unfold omniUtilB; rw [hm, hζ]
    · let e0 : BaseOutcome := ⟨0, 0, 0, 0⟩
      have hc0 : choiceB M 0 = (0, 0) := by
        unfold choiceB
        rw [if_neg (by linarith), if_neg (by linarith)]
      refine ⟨e0, ⟨hc0.symm, le_rfl, ?_, ?_⟩, ?_⟩
      · intro q hq
        show profitB M P Ds Dm 0 0 q ≤ profitB M P Ds Dm 0 0 0
        rw [profitB_zero_zero M P Ds Dm q hq, profitB_zero_zero M P Ds Dm 0 le_rfl]
        nlinarith
      · show (0:ℝ) = fillB P Ds Dm 0 0 0
        unfold fillB; simp
      · intro e he
        rcases classB e he with ⟨hs, hm⟩ | ⟨-, -, -, -, hc⟩
        · refine ⟨?_, ?_, ?_⟩
          · unfold retailerB; rw [hs, hm, profitB_zero_zero M P Ds Dm e.q he.2.1]
            show _ ≤ profitB M P Ds Dm 0 0 0
            rw [profitB_zero_zero M P Ds Dm 0 le_rfl]
            nlinarith [he.2.1]
          · unfold storeUtilB; rw [hs]
            show 0 * (e.ζ * M.ub - M.k) ≤ 0 * (0 * M.ub - M.k)
            simp
          · unfold omniUtilB; rw [hm]
            show 0 * (e.ζ * M.ub - M.k) + (1 - 0) * (M.uo - M.t)
              ≤ 0 * (0 * M.ub - M.k) + (1 - 0) * (M.uo - M.t)
            simp
        · exact absurd hc h1
  · intro eB eP hB hP
    have h1 := retB_le eB hB.1
    have h2 := (hP.2 eStar hStarREE).1
    exact le_trans h1 h2
