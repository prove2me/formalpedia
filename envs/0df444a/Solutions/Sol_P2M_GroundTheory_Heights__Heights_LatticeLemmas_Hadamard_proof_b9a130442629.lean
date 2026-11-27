-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_Hadamard_proof_b9a130442629
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:13.244336+00:00
-- url     : https://prove2.me/submissions/206de4d7-1b74-42ec-8d73-9072743a9018

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_Hadamard_intersectionNumber_baseChange_fb4e5d913042

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace
universe u v w
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace Hadamard
theorem _root_.solution (_h1 : Sublattice.Statement.{u, v}) : Hadamard.Statement.{u, v, w} :=
  Hadamard.intersectionNumber_baseChange
end Hadamard
end GroundTheory.Heights₂.Heights.LatticeLemmas
