-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_eval_linearFormPoly_edaf060fc944
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:41.253303+00:00
-- url     : https://prove2.me/submissions/871321da-90f8-4db0-b53b-7fd927bee058

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) (c : Fin n → k) :
    eval c (linearFormPoly φ) = φ c := by
  have hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → k) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]
  simp [linearFormPoly, map_sum, mul_comm]
end GroundTheory.Heights₂.Heights.ComplexSets
