-- Prove2me | solution 1 for RiskPremiaDMP.Equivalence.surplus_characterization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:22:13.090448+00:00
-- url     : https://prove2.me/submissions/d7453bfa-595f-41b7-be6a-4cd31f5aa6dd

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

open RiskPremiaDMP.Equivalence

namespace Aux_RiskPremia_SC
open RiskPremiaDMP.Equivalence

theorem diff2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) : Differentiable ℝ f ∧ Differentiable ℝ (deriv f) := by
  have h : ContDiff ℝ (1 + 1) f := by rw [one_add_one_eq_two]; exact hf
  obtain ⟨h1, _, h2⟩ := contDiff_succ_iff_deriv.mp h
  exact ⟨h1, h2.differentiable (by norm_num)⟩

theorem py (F : ℝ → ℝ → ℝ) (hF : ContDiff ℝ 2 (Function.uncurry F)) (m : ℝ) :
    ContDiff ℝ 2 (fun y' => F y' m) :=
  hF.comp (contDiff_id.prodMk contDiff_const)

theorem pm (F : ℝ → ℝ → ℝ) (hF : ContDiff ℝ 2 (Function.uncurry F)) (y : ℝ) :
    ContDiff ℝ 2 (fun m' => F y m') :=
  hF.comp (contDiff_const.prodMk contDiff_id)

theorem lin1 (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (s : ℝ) :
    deriv (fun x => f x + s * g x) = (fun x => deriv f x + s * deriv g x) ∧
    deriv (fun x => deriv f x + s * deriv g x) = (fun x => deriv (fun x' => deriv f x') x + s * deriv (fun x' => deriv g x') x) := by
  obtain ⟨hf1, hf2⟩ := diff2 f hf
  obtain ⟨hg1, hg2⟩ := diff2 g hg
  have e1 : deriv (fun x => f x + s * g x) = fun x => deriv f x + s * deriv g x := by
    funext x
    exact ((hf1 x).hasDerivAt.add ((hg1 x).hasDerivAt.const_mul s)).deriv
  refine ⟨e1, ?_⟩
  funext x
  exact ((hf2 x).hasDerivAt.add ((hg2 x).hasDerivAt.const_mul s)).deriv

theorem genP_lin (a b c d : ℝ) (F G : ℝ → ℝ → ℝ) (hF : ContDiff ℝ 2 (Function.uncurry F))
    (hG : ContDiff ℝ 2 (Function.uncurry G)) (s y m : ℝ) :
    genP a b c d (fun y m => F y m + s * G y m) y m = genP a b c d F y m + s * genP a b c d G y m := by
  unfold genP d1 d11 d2 d22
  obtain ⟨y1, y2⟩ := lin1 _ _ (py F hF m) (py G hG m) s
  obtain ⟨m1, m2⟩ := lin1 _ _ (pm F hF y) (pm G hG y) s
  beta_reduce
  rw [y1, m1]
  beta_reduce
  rw [y2, m2]
  ring

theorem genP_smul (a b c d : ℝ) (F : ℝ → ℝ → ℝ) (s y m : ℝ) :
    genP a b c d (fun y m => s * F y m) y m = s * genP a b c d F y m := by
  unfold genP d1 d11 d2 d22
  simp only [deriv_const_mul_field']
  ring

theorem genP_zero (a b c d y m : ℝ) : genP a b c d (fun _ _ => 0) y m = 0 := by
  simp [genP, d1, d11, d2, d22]

end Aux_RiskPremia_SC

theorem solution (E : NoRPParams) (hE : E.Standing) (q : ℝ → ℝ)
    (J V W U w θ : ℝ → ℝ → ℝ)
    (hJ : ContDiff ℝ 2 (Function.uncurry J)) (hW : ContDiff ℝ 2 (Function.uncurry W))
    (hU : ContDiff ℝ 2 (Function.uncurry U))
    (h4a : ∀ y μ : ℝ, E.rf * J y μ
      = Real.exp y - w y μ + genP E.κy E.σy E.κμ E.σμ J y μ + E.s * (V y μ - J y μ))
    (h4b : ∀ y μ : ℝ, E.rf * V y μ
      = -E.c + genP E.κy E.σy E.κμ E.σμ V y μ + q (θ y μ) * (J y μ - V y μ))
    (h4c : ∀ y μ : ℝ, E.rf * W y μ
      = w y μ + genP E.κy E.σy E.κμ E.σμ W y μ + E.s * (U y μ - W y μ))
    (h4d : ∀ y μ : ℝ, E.rf * U y μ
      = E.z + genP E.κy E.σy E.κμ E.σμ U y μ + θ y μ * q (θ y μ) * (W y μ - U y μ))
    (hfree : ∀ y μ : ℝ, V y μ = 0)
    (hfirm : ∀ y μ : ℝ, J y μ - V y μ = (1 - E.β) * (J y μ - V y μ + W y μ - U y μ))
    (hworker : ∀ y μ : ℝ, W y μ - U y μ = E.β * (J y μ - V y μ + W y μ - U y μ)) :
    IsEquilibriumNoRP E q (fun y μ => J y μ - V y μ + W y μ - U y μ) θ ∧
      ∀ y μ : ℝ, w y μ = E.β * Real.exp y + (1 - E.β) * E.z + E.β * E.c * θ y μ := by
  open Aux_RiskPremia_SC in
  have hV : V = fun _ _ => 0 := by funext y μ; exact hfree y μ
  have hβ : (1 - E.β) ≠ 0 := by have := hE.2.2.2.2; intro h; linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → ℝ → ℝ, S = fun y μ => J y μ - V y μ + W y μ - U y μ := ⟨_, rfl⟩
  have hVc : ContDiff ℝ 2 (Function.uncurry V) := by rw [hV]; exact contDiff_const
  have hcd : ContDiff ℝ 2 (Function.uncurry S) := by
    rw [hSdef]; exact ((hJ.sub hVc).add hW).sub hU
  rw [← hSdef]
  have hSv : ∀ y μ, S y μ = J y μ + W y μ - U y μ := by
    intro y μ; rw [hSdef]; beta_reduce; rw [hfree]; ring
  have hJS : J = fun y μ => (1 - E.β) * S y μ := by
    funext y μ; have := hfirm y μ; rw [hfree] at this; rw [hSv]; linarith
  have hWU : (fun y μ => W y μ + (-1) * U y μ) = fun y μ => E.β * S y μ := by
    funext y μ; have := hworker y μ; rw [hfree] at this; rw [hSv]; linarith
  have gJ : ∀ y μ, genP E.κy E.σy E.κμ E.σμ J y μ = (1 - E.β) * genP E.κy E.σy E.κμ E.σμ S y μ := by
    intro y μ
    have := congrArg (fun F => genP E.κy E.σy E.κμ E.σμ F y μ) hJS
    beta_reduce at this
    rw [this, genP_smul]
  have gWU : ∀ y μ, genP E.κy E.σy E.κμ E.σμ W y μ - genP E.κy E.σy E.κμ E.σμ U y μ
      = E.β * genP E.κy E.σy E.κμ E.σμ S y μ := by
    intro y μ
    have := congrArg (fun F => genP E.κy E.σy E.κμ E.σμ F y μ) hWU
    beta_reduce at this
    rw [genP_lin _ _ _ _ W U hW hU, genP_smul] at this
    linarith
  have gV : ∀ y μ, genP E.κy E.σy E.κμ E.σμ V y μ = 0 := by
    intro y μ; rw [hV]; exact genP_zero _ _ _ _ _ _
  have hc : ∀ y μ, E.c = (1 - E.β) * q (θ y μ) * S y μ := by
    intro y μ
    have h := h4b y μ
    rw [gV, hfree] at h
    have hj : J y μ = (1 - E.β) * S y μ := by rw [hJS]
    rw [hj] at h
    linarith
  refine ⟨⟨hcd, fun y μ => ⟨?_, hc y μ⟩⟩, fun y μ => ?_⟩
  · have hcθ : E.β * E.c / (1 - E.β) * θ y μ = E.β * q (θ y μ) * S y μ * θ y μ := by
      rw [hc y μ]; field_simp
    have hS1 := hSv y μ
    have hwu := hworker y μ
    rw [hfree] at hwu
    have e1 := gJ y μ
    have e2 := gWU y μ
    have a := h4a y μ
    have c4 := h4c y μ
    have d := h4d y μ
    rw [hfree] at a
    rw [hcθ]
    linear_combination a + c4 - d + (E.rf + E.s + q (θ y μ) * θ y μ * E.β) * hS1 - q (θ y μ) * θ y μ * hwu + e1 + e2
  · have hS1 := hSv y μ
    have hwu := hworker y μ
    rw [hfree] at hwu
    have hj : J y μ = (1 - E.β) * S y μ := by rw [hJS]
    have e1 := gJ y μ
    have e2 := gWU y μ
    have a := h4a y μ
    have c4 := h4c y μ
    have d := h4d y μ
    have hcc := hc y μ
    rw [hfree] at a
    have hW' : W y μ = U y μ + E.β * S y μ := by
      have : J y μ - 0 + W y μ - U y μ = S y μ := by rw [hS1]; ring
      rw [this] at hwu; linarith
    have gW' : genP E.κy E.σy E.κμ E.σμ W y μ = genP E.κy E.σy E.κμ E.σμ U y μ + E.β * genP E.κy E.σy E.κμ E.σμ S y μ := by
      linarith
    rw [hj, e1] at a
    rw [hW', gW'] at c4
    rw [hW'] at d
    rw [hcc]
    linear_combination E.β * a - (1 - E.β) * c4 + (1 - E.β) * d
