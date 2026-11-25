-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalYT_eq_zero_a0591a1126ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:32:15.143985+00:00
-- url     : https://prove2.me/submissions/a0a36f02-3dd3-4cb8-9271-fc291526e9ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_evalAt_comp_toRingHom_ccc700392e82

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    {F : Polynomial (MvPolynomial (Fin d) ℂ)} {s : MvPolynomial (Fin n) ℂ ⧸ J}
    (hs : Polynomial.eval₂ ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom s F = 0)
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    evalYT F (fun i => eval z (p i)) (evalAt J hz s) = 0 := by
  have h := congrArg (evalAt J hz : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ) hs
  rw [map_zero, Polynomial.hom_eval₂, evalAt_comp_toRingHom] at h
  rw [evalYT, Polynomial.eval_map]
  exact h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
