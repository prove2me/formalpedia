-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ringKrullDim_graphIdeal_a824ae9cd5f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:49.591844+00:00
-- url     : https://prove2.me/submissions/115a8474-6f43-41cb-a47d-b4540c597bab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := by
  let g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (Ideal.Quotient.mk J).comp (graphHom p).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)
  have hker : RingHom.ker g = graphIdeal J p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg))
end GroundTheory.Heights₂.Heights.Targets
