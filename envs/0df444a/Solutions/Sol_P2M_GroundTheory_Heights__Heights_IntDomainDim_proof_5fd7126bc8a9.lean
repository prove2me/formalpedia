-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntDomainDim_proof_5fd7126bc8a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:16.932574+00:00
-- url     : https://prove2.me/submissions/1ac59d59-89a5-4444-b1c1-af892d56881c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_ringKrullDim_int_af7f3029f4b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_le_trdeg_add_one_int_10c3d154db15


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra
namespace GroundTheory.Heights₂.Heights
namespace IntDomainDim
theorem _root_.solution : IntDomainDim.Statement := by
  intro A _ inst _ _ hinj
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  have hfin : trdeg ℤ A < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp hfin
  rw [ht, Cardinal.toENat_nat]
  have h1 := ringKrullDim_le_trdeg_add_one_int t A hinj ht
  have h2 := le_ringKrullDim_int A hinj t ht
  push_cast at h1 h2
  exact le_antisymm h1 h2
end IntDomainDim
end GroundTheory.Heights₂.Heights
