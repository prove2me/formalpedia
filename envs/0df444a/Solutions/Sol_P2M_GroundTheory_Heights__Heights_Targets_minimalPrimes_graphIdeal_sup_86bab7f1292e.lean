-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_minimalPrimes_graphIdeal_sup_86bab7f1292e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:30.093409+00:00
-- url     : https://prove2.me/submissions/bd618101-6f08-48e6-b6a4-f4f62f111328

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_sup_span_187dce0f4183

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
    (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).minimalPrimes =
      (fun W => graphIdeal W p) '' (J ⊔ Ideal.span {p}).minimalPrimes := by
  rw [graphIdeal_sup_span, graphIdeal]
  exact Ideal.comap_minimalPrimes_eq_of_surjective (graphHom_surjective p) _
end GroundTheory.Heights₂.Heights.Targets
