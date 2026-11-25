-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_DerivSpanTrdeg_derivation_eq_zero_of_isSeparable_d3b7ef088867
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:51.075063+00:00
-- url     : https://prove2.me/submissions/f7cea46b-ad7f-4370-bf04-084045c9bb7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsDerivSpanTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PDerivSpanTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.Vertical
namespace DerivSpanTrdeg
theorem _root_.solution {k K M : Type*} [Field k] [Field K]
    [Algebra k K] [AddCommGroup M] [Module K M] [Module k M] [IsScalarTower k K M] (s : Set K)
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] (D : Derivation k K M)
    (hs : ∀ x ∈ s, D x = 0) : D = 0 := by
  have hE : ∀ x ∈ IntermediateField.adjoin k s, D x = 0 := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap x => exact D.map_algebraMap x
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | inv x _ hx => rw [Derivation.leibniz_inv, hx, smul_zero]
    | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  ext α
  set E := IntermediateField.adjoin k s
  have hsep : IsSeparable E α := Algebra.IsSeparable.isSeparable E α
  set g : Polynomial K := (minpoly E α).map (algebraMap E K)
  have h0 : D (g.eval α) = 0 := by
    rw [Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  have hc : D.mapCoeffs g = 0 := by
    ext i
    simp only [Derivation.mapCoeffs_apply, g, Polynomial.coeff_map]
    exact (hE _ ((minpoly E α).coeff i).2).trans (by simp)
  rw [Derivation.apply_eval_eq, hc, map_zero, zero_add] at h0
  have hne : g.derivative.eval α ≠ 0 := by
    simp only [g]
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval E α)
  simpa [hne] using h0
end DerivSpanTrdeg
end GroundTheory.Heights₂.Heights.Vertical
