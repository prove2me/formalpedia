-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:04.887908+00:00
-- url     : https://prove2.me/submissions/7f604786-efa9-4c29-a74b-4d91451af3e8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_sum_E
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (X : gl n) :
    UniversalEnvelopingAlgebra.ι ℂ X = ∑ a : Fin n × Fin n, X a.1 a.2 • e (n := n) a := by
  conv_lhs => rw [eq_sum_E X]
  simp [e, map_sum, map_smul]
end GroundTheory.Automorphic.HarishChandra
