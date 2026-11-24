-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isClosed_zeroSetIn_of_ideal_803675c815b8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:10.02863+00:00
-- url     : https://prove2.me/submissions/e19a21f1-2463-4b72-bf4c-b2fcaf0538a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace

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
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (zeroSetIn I) := by
  have h : zeroSetIn I = ⋂ q ∈ I, {z : σ → ℂ | eval z q = 0} := by
    ext z; simp [zeroSetIn]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
