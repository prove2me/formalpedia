-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_eq_add_mul_of_map_residue_mem_e22e557433f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:11.316841+00:00
-- url     : https://prove2.me/submissions/c5e818cc-a15d-4b8a-bb70-cd5c82742bda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialPieceRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_weightedHomogeneousComponent_b0c16ffbf749
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_mem_weightedHomogeneousSubmodule_88a694c8725e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    (hP : IsMultiHomogIdeal P) {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m)
    (hfP : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal P) :
    ∃ p ∈ P, ∃ g ∈ weightedHomogeneousSubmodule O (blockWeight ι) m, f = p + C ϖ * g := by
  have hfh := (mem_weightedHomogeneousSubmodule _ _ _ _).1 hf
  obtain ⟨p, hp, hpf⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hfP
  have hpm : weightedHomogeneousComponent (blockWeight ι) m p ∈ P := hP p hp m
  have hker : f - weightedHomogeneousComponent (blockWeight ι) m p ∈
      RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* _) := by
    rw [RingHom.mem_ker, map_sub, map_residue_weightedHomogeneousComponent, hpf,
      weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1
        (map_residue_mem_weightedHomogeneousSubmodule hf)), sub_self]
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton'] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨_, hpm, weightedHomogeneousComponent (blockWeight ι) m g, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · have h2 : C ϖ * weightedHomogeneousComponent (blockWeight ι) m g =
        f - weightedHomogeneousComponent (blockWeight ι) m p := by
      rw [C_mul', ← map_smul, ← C_mul', mul_comm, hg, map_sub, weightedHomogeneousComponent_eq_self hfh,
        weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
    rw [h2]
    ring
end GroundTheory.Heights₂.Heights.NumbersDVR
