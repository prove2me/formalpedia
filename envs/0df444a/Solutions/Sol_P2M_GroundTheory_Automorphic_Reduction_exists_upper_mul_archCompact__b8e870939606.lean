-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact__b8e870939606
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:55.494033+00:00
-- url     : https://prove2.me/submissions/ebd5e6fd-f740-411c-858f-31bfdbbf49c2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}
variable [NumberField K]
omit [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (w : InfinitePlace K) (h : GL (Fin n) w.Completion) :
    ∃ p : GL (Fin n) w.Completion × GL (Fin n) w.Completion,
      (p.1 : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular ∧ p.2 ∈ archCompact w ∧
        h = p.1 * p.2 := by
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_upper_mul_archCompact w h
  exact ⟨(b, k), hb, hk, rfl⟩
end GroundTheory.Automorphic.Reduction
