-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldOrbit_proof_05a8d999f3c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:02.621373+00:00
-- url     : https://prove2.me/submissions/f9838994-9b6a-4daf-a07f-4aba2dbeb1cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldOrbit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldOrbit_bijective_mul_out_inv_b2a5c02b809d
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal Pointwise
variable (G : Type*) [Group G]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace UnfoldOrbit
theorem _root_.solution [MeasurableSpace G] [MeasurableMul G] : UnfoldOrbit.Statement G := by
  intro μ _ Γ Γ₀ _ hle FD FD₀ hFD hFD₀ φ hφ hinv
  have : Countable Γ₀ := (Subgroup.inclusion_injective hle).countable
  have : Countable (Γ ⧸ Γ₀.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  rw [lintegral_tsum (f := fun (q : Γ ⧸ Γ₀.subgroupOf Γ) g => φ (((Quotient.out q : Γ) : G)⁻¹ * g))
      fun q => (hφ.comp (measurable_const_mul _)).aemeasurable,
    hFD.setLIntegral_eq_tsum φ FD₀,
    ← (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle)).tsum_eq,
    ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  have h1 : ∫⁻ g in FD, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ x in ((Quotient.out q : Γ) : G)⁻¹ • FD, φ x ∂μ := by
    rw [← Set.image_smul]
    exact (measurePreserving_mul_left μ _).setLIntegral_comp_emb (measurableEmbedding_mulLeft _) φ FD
  rw [h1, hFD₀.setLIntegral_eq_tsum' φ]
  refine tsum_congr fun h => ?_
  have hset : h • ((Quotient.out q : Γ) : G)⁻¹ • FD ∩ FD₀ =
      FD₀ ∩ (Equiv.ofBijective _ (UnfoldOrbit.bijective_mul_out_inv G hle) (q, h)) • FD := by
    rw [Set.inter_comm]
    congr 1
    show (h : G) • ((Quotient.out q : Γ) : G)⁻¹ • FD = ((h : G) * ((Quotient.out q : Γ) : G)⁻¹) • FD
    rw [smul_smul]
  rw [hset]
  exact lintegral_congr fun x => hinv _ (h⁻¹).2 x
end UnfoldOrbit
end GroundTheory.Heights₂.Heights.FiniteCovolume
