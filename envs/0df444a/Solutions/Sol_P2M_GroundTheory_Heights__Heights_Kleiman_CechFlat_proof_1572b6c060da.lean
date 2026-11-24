-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechFlat_proof_1572b6c060da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:37.657577+00:00
-- url     : https://prove2.me/submissions/90096b06-36ff-4b5f-b908-e999af7d0669

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open TensorProduct MvPolynomial
noncomputable section
universe u v
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CechFlat
theorem _root_.solution : CechFlat.Statement.{u, v} := by
  intro S _ _ N S' _ _ _ M M' _ _ _ _ _ _ _ _ _ _ 𝓜 𝓜' f hf hX hdeg i c
  exact ⟨FlatBC.cohomBC f hX hf 𝓜 𝓜' hdeg c i⟩
end CechFlat
end GroundTheory.Heights₂.Heights.Kleiman
