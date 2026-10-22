-- Prove2me | solution 1 for OmniPool.BOPS.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:30:13.772695+00:00
-- url     : https://prove2.me/submissions/83c4e8fa-8255-46cf-b282-7599db53e4d8

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
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hkt : M.k ≤ M.t) :
    qp ≤ qsm ∧ qs ≤ qp ∧ zetaS P Ds Dm qs ≤ zetaP P Ds qp := by
  -- the pooled-sales term A(q) = E[min(Dm, (q - Ds)^+)]
  set A : ℝ → ℝ := fun q => ∫ ω, min (Dm ω) (max (q - 1 * Ds ω) 0) ∂P with hAdef
  have hAmono : ∀ a b : ℝ, a ≤ b → A a ≤ A b := by
    intro a b hab
    apply integral_mono (intA P Ds Dm hDsi hDmi 1 a) (intA P Ds Dm hDsi hDmi 1 b)
    intro ω
    exact min_le_min_left _ (max_le_max_right _ (by linarith))
  -- generic comparative statics: adding a nondecreasing term moves the maximizer up
  have shift : ∀ (f F g : ℝ → ℝ) (x y : ℝ), IsUniqueMaxNonneg f x → IsUniqueMaxNonneg F y →
      (∀ q, F q = f q + g q) → (∀ a b : ℝ, a ≤ b → g a ≤ g b) → x ≤ y := by
    intro f F g x y hx hy hF hg
    by_contra hlt
    push_neg at hlt
    have h1 : F x ≤ F y := uniq_opt hy x hx.1
    have h2 : f y < f x := hx.2 y hy.1 (ne_of_lt hlt)
    have h3 := hg y x hlt.le
    rw [hF, hF] at h1
    linarith
  -- profitP = profitB(1,0) + co A
  have hPB : ∀ q, profitP M P Ds Dm 1 q = profitB M P Ds Dm 1 0 q + M.co * A q := by
    intro q
    rw [profitP_eq M P Ds Dm hDsi hDmi hkt]
    unfold profitB
    have e1 : (fun ω => min (0 * Dm ω + 1 * Ds ω) q) = fun ω => min (1 * Ds ω) q := by
      funext ω; rw [zero_mul, zero_add]
    have e2 : (fun ω => (1 - (0:ℝ)) * Dm ω) = fun ω => Dm ω := by
      funext ω; ring
    rw [e1, e2]
    simp only [hAdef]
    ring
  -- profitB(1,1) = profitP + (pb - co) A - (po - co) E[Dm]
  have hBP : ∀ q, profitB M P Ds Dm 1 1 q
      = profitP M P Ds Dm 1 q + ((M.pb - M.co) * A q - (M.po - M.co) * ∫ ω, Dm ω ∂P) := by
    intro q
    rw [profitP_eq M P Ds Dm hDsi hDmi hkt]
    unfold profitB
    have hmin : Integrable (fun ω => min (1 * Ds ω) q) P :=
      (hDsi.const_mul 1).inf (integrable_const q)
    have e1 : (fun ω => min (1 * Dm ω + 1 * Ds ω) q)
        = fun ω => min (1 * Ds ω) q + min (Dm ω) (max (q - 1 * Ds ω) 0) := by
      funext ω
      have h0 := hDm0 ω
      simp only [one_mul]
      rcases le_total q (Ds ω) with h | h
      · rw [min_eq_right (by linarith), min_eq_right h, max_eq_right (by linarith),
          min_eq_right h0]; ring
      · rw [min_eq_left h, max_eq_left (by linarith)]
        rcases le_total (Dm ω) (q - Ds ω) with h' | h'
        · rw [min_eq_left h', min_eq_left (by linarith)]; ring
        · rw [min_eq_right h', min_eq_right (by linarith)]; ring
    have e2 : (fun ω => (1 - (1:ℝ)) * Dm ω) = fun _ => (0:ℝ) := by
      funext ω; ring
    rw [e1, e2, integral_add hmin (intA P Ds Dm hDsi hDmi 1 q)]
    simp only [hAdef, integral_zero]
    ring
  have hsp : qs ≤ qp := shift _ _ (fun q => M.co * A q) qs qp hqs hqp hPB
    (fun a b hab => mul_le_mul_of_nonneg_left (hAmono a b hab) hco)
  have hpsm : qp ≤ qsm := shift _ _ (fun q => (M.pb - M.co) * A q - (M.po - M.co) * ∫ ω, Dm ω ∂P)
    qp qsm hqp hqsm hBP
    (fun a b hab => by
      have := mul_le_mul_of_nonneg_left (hAmono a b hab) (by linarith : (0:ℝ) ≤ M.pb - M.co)
      linarith)
  refine ⟨hpsm, hsp, ?_⟩
  show fillB P Ds Dm 1 0 qs ≤ fillP P Ds 1 qp
  unfold fillB fillP
  rw [if_neg (by norm_num), if_neg (by norm_num)]
  have e1 : (fun ω => min (0 * Dm ω + 1 * Ds ω) qs) = fun ω => min (1 * Ds ω) qs := by
    funext ω; rw [zero_mul, zero_add]
  have e2 : (fun ω => 0 * Dm ω + 1 * Ds ω) = fun ω => Ds ω := by
    funext ω; ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ hmus.le
  apply integral_mono ((hDsi.const_mul 1).inf (integrable_const qs))
    ((hDsi.const_mul 1).inf (integrable_const qp))
  intro ω
  exact min_le_min_left _ hsp
