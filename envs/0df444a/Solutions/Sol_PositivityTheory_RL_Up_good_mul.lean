-- Prove2me | solution 1 for PositivityTheory.RL.Up.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:38.916571+00:00
-- url     : https://prove2.me/submissions/91238230-3538-4f13-834c-2277b05226e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.RL.Up
theorem _root_.solution {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (U : ℝ → (Sch l →L[ℂ] Sch l))
    (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1) (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ))
    (hc0 : ∀ w, c 0 w = w) (hc : ∀ w a, HasDerivAt (fun t => c t w a) (-(X *ᵥ w) a) 0)
    (hD : ∀ t w, dRho w * U t = U t * dRho (c t w))
    (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (X *ᵥ w)) {j : Sch l →L[ℂ] B} (hj : Good U Q j) (w : l ⊕ l → ℝ) :
    Good U Q (j ∘L dRho w) := by
  intro f
  have e : (fun t => (j ∘L dRho w) (U t f)) = fun t => ∑ a, ((c t w a : ℝ) : ℂ) • j (U t (dRho (Pi.single a 1) f)) := by
    funext t
    show j ((dRho w * U t) f) = _
    rw [hD, ContinuousLinearMap.mul_apply, dRho_eq_sum]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  rw [e]
  have := HasDerivAt.fun_sum (u := Finset.univ) fun a _ => ((hc w a).ofReal_comp).smul (hj (dRho (Pi.single a 1) f))
  refine this.congr_deriv ?_
  simp only [h0, hc0, ContinuousLinearMap.one_apply, Finset.sum_add_distrib]
  have e1 : dRho w * Q = Q * dRho w - dRho (X *ᵥ w) := by rw [← hQ]; abel
  show _ = j ((dRho w * Q) f)
  rw [e1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub, dRho_eq_sum w, dRho_eq_sum (X *ᵥ w)]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul, ofReal_neg, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]
end PositivityTheory.RL.Up
