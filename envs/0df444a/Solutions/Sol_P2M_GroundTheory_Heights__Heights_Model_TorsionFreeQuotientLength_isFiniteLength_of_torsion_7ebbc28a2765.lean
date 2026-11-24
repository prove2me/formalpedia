-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_isFiniteLength_of_torsion_7ebbc28a2765
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:00.514799+00:00
-- url     : https://prove2.me/submissions/0d0c47d0-a25a-47e8-9aeb-845c66c22b57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_pi_quot_smul_top_69b4b0f38899

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
theorem _root_.solution [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (Q : Type*) [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (hQ : ∀ q : Q, ∃ c : R, c ≠ 0 ∧ c • q = 0) : IsFiniteLength R Q := by
  have htors : Module.IsTorsion R Q := fun q => by
    obtain ⟨c, hc, hcq⟩ := hQ q
    exact ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, hcq⟩
  obtain ⟨c, hc1, hc2⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htors
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R Q
  have hle : (c • ⊤ : Submodule R (Fin n → R)) ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [LinearMap.mem_ker, map_smul]
    exact (Submodule.mem_annihilator.mp hc1) _ Submodule.mem_top
  have hs : Function.Surjective ((c • ⊤ : Submodule R (Fin n → R)).liftQ f hle) := by
    intro q
    obtain ⟨x, rfl⟩ := hf q
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  rw [← Module.length_ne_top_iff]
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hs)
  rw [length_pi_quot_smul_top]
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _)
    (Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton R hc2))
end GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
