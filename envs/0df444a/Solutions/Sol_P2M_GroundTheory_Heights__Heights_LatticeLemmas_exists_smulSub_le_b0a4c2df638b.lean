-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_smulSub_le_b0a4c2df638b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:22.665214+00:00
-- url     : https://prove2.me/submissions/9418ca61-3cd2-4f5f-acf1-847ea0fefeec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_smul_mem_f84cdc00b338

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
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (M₁ M₂ : FullLattice K V) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ smulSub b M₂.carrier ≤ M₁.carrier := by
  classical
  obtain ⟨S, hS⟩ := M₂.fg
  choose f hf0 hf using exists_smul_mem M₁
  refine ⟨∏ s ∈ S, f s, Finset.prod_ne_zero_iff.mpr fun s _ ↦ hf0 s, ?_⟩
  rw [smulSub, Submodule.map_le_iff_le_comap, ← hS, Submodule.span_le]
  intro s hs
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_coe.mp hs), mul_smul]
  exact M₁.carrier.smul_mem _ (hf s)
end GroundTheory.Heights₂.Heights.LatticeLemmas
