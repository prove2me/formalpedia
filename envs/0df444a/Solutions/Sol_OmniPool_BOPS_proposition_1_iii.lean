-- Prove2me | solution 1 for OmniPool.BOPS.proposition_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:28:55.202765+00:00
-- url     : https://prove2.me/submissions/608b347d-b97d-4da1-b6ae-0ed79d7deb1f

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
    (qs : ℝ) (hqs : IsUniqueMaxNonneg (profitB M P Ds Dm 1 0) qs)
    (qsm : ℝ) (hqsm : IsUniqueMaxNonneg (profitB M P Ds Dm 1 1) qsm)
    (hreg : max (zetaS P Ds Dm qs * M.ub) (zetaSM P Ds Dm qsm * M.ub - (M.uo - M.t)) < M.k) :
    (∃ e, IsParetoREE_B M P Ds Dm e) ∧
      ∀ e, IsParetoREE_B M P Ds Dm e → e.q = 0 ∧ e.φs = 0 ∧ e.φm = 0 := by
  have hlo : zetaSM P Ds Dm qsm * M.ub - (M.uo - M.t) < M.k := lt_of_le_of_lt (le_max_right _ _) hreg
  have hs : fillB P Ds Dm 1 0 qs * M.ub < M.k := lt_of_le_of_lt (le_max_left _ _) hreg
  have htuo : M.t ≤ M.uo := le_trans (le_max_left _ _) hU
  have classB : ∀ e : BaseOutcome, IsREE_B M P Ds Dm e →
      (e.φs = 0 ∧ e.φm = 0) ∨ (e.φs = 1 ∧ e.φm = 0 ∧ e.q = qs ∧
        e.ζ = fillB P Ds Dm 1 0 qs ∧ choiceB M (fillB P Ds Dm 1 0 qs) = (1, 0)) := by
    intro e ⟨hc, hq, hopt, hζ⟩
    unfold choiceB at hc
    split_ifs at hc with h1 h2
    · simp only [Prod.mk.injEq] at hc
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
  have class0 : ∀ e : BaseOutcome, IsREE_B M P Ds Dm e → e.φs = 0 ∧ e.φm = 0 ∧ e.q = 0 := by
    intro e he
    rcases classB e he with ⟨hs0, hm0⟩ | ⟨-, -, -, -, hc⟩
    · refine ⟨hs0, hm0, ?_⟩
      have hopt := he.2.2.1 0 le_rfl
      rw [hs0, hm0, profitB_zero_zero M P Ds Dm 0 le_rfl,
        profitB_zero_zero M P Ds Dm e.q he.2.1] at hopt
      nlinarith [he.2.1]
    · exfalso
      unfold choiceB at hc
      split_ifs at hc with ha hb
      · simp at hc
      · linarith
      · simp at hc
  let e0 : BaseOutcome := ⟨0, 0, 0, 0⟩
  have hc0 : choiceB M 0 = (0, 0) := by
    unfold choiceB
    rw [if_neg (by linarith), if_neg (by linarith)]
  have hREE0 : IsREE_B M P Ds Dm e0 := by
    refine ⟨hc0.symm, le_rfl, ?_, ?_⟩
    · intro q hq
      show profitB M P Ds Dm 0 0 q ≤ profitB M P Ds Dm 0 0 0
      rw [profitB_zero_zero M P Ds Dm q hq, profitB_zero_zero M P Ds Dm 0 le_rfl]
      nlinarith
    · show (0:ℝ) = fillB P Ds Dm 0 0 0
      unfold fillB; simp
  refine ⟨⟨e0, hREE0, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨hs0, hm0, hq0⟩ := class0 e he
    refine ⟨?_, ?_, ?_⟩
    · unfold retailerB; rw [hs0, hm0, hq0]
    · unfold storeUtilB; rw [hs0]
      show 0 * (e.ζ * M.ub - M.k) ≤ 0 * (0 * M.ub - M.k)
      simp
    · unfold omniUtilB; rw [hm0]
      show 0 * (e.ζ * M.ub - M.k) + (1 - 0) * (M.uo - M.t)
        ≤ 0 * (0 * M.ub - M.k) + (1 - 0) * (M.uo - M.t)
      simp
  · intro e he
    obtain ⟨hs0, hm0, hq0⟩ := class0 e he.1
    exact ⟨hq0, hs0, hm0⟩
