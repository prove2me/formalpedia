-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_mem_center_of_forall___commute_47468f82d060
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:30.705048+00:00
-- url     : https://prove2.me/submissions/ed3d1cb1-69d6-4845-9042-e8942bdcfc0d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
namespace GroundTheory.Automorphic
theorem _root_.solution {z : UniversalEnvelopingAlgebra ℝ L}
    (hz : ∀ x : L, UniversalEnvelopingAlgebra.ι ℝ x * z = z * UniversalEnvelopingAlgebra.ι ℝ x) :
    z ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ L) := by
  rw [Subalgebra.mem_center_iff]
  intro u
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ L t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ L) u
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r z
  | ι x => exact hz x
  | mul a b ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]
end GroundTheory.Automorphic
