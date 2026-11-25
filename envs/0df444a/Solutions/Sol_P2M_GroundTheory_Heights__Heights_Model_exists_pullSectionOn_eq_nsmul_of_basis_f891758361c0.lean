-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_pullSectionOn_eq_nsmul_of_basis_f891758361c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:24.414231+00:00
-- url     : https://prove2.me/submissions/5562eaf5-5b05-4897-90b4-80247591aafb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable (hPB : PullbackBasis.Statement.{0}) (hRL : RatLocalAffine.Statement)
  {X : Scheme.{0}} (f : X ⟶ SpecZ) [Flat f] (L : X.Modules)
  {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} {t : Fin n → Γ(L, W)} (ht : IsBasisOn L W t)
include hPB hRL hW ht
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution
    (σ : Γ((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L, baseChangeMap f ℚ ⁻¹ᵁ W)) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : Γ(L, W), pullSectionOn (baseChangeMap f ℚ) L W τ = N • σ := by
  have hb := (hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self
  obtain ⟨b, rfl⟩ := hb.2 σ
  choose N hN a ha using fun i => (hRL X f W hW).2 (b i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i,
    ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • a i) • t i, ?_⟩
  rw [pullSectionOn_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ha i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]
end GroundTheory.Heights₂.Heights.Model
