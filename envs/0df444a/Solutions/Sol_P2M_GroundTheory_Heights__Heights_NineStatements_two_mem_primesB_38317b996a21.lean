-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_two_mem_primesB_38317b996a21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:48.060247+00:00
-- url     : https://prove2.me/submissions/43ec6cb2-a55b-44db-aed2-05474722ff3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {B : ℕ} (hB : 2 ≤ B) (bad : Finset ℕ) : 2 ∈ primesB B bad := by
  rw [primesB]
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, hB⟩, Nat.prime_two⟩)
end GroundTheory.Heights₂.Heights.NineStatements
