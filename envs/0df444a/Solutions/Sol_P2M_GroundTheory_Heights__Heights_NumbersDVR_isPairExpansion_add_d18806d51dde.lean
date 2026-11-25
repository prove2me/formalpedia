-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_add_d18806d51dde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:17.100455+00:00
-- url     : https://prove2.me/submissions/79b209f9-24ce-4550-9d62-2808823dc1cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {n m : ℕ} {A B : MvPolynomial (Fin n) ℤ}
    {As Bs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ} (hA : IsPairExpansion m A As)
    (hB : IsPairExpansion m B Bs) : IsPairExpansion m (A + B) (As + Bs) := by
  refine ⟨?_, fun i => (hA.homogeneous i).add (hB.homogeneous i)⟩
  simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hA.expansion,
    ← hB.expansion]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR
