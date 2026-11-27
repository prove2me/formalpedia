-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DedekindFibreRank_proof_a236dd3c4119
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:26.834711+00:00
-- url     : https://prove2.me/submissions/6fde5ef0-2e88-439e-a1ce-ce3e0d0d2221

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDedekindFibreRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDedekindFibreRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Module TensorProduct
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace DedekindFibreRank
theorem _root_.solution : DedekindFibreRank.Statement := by
  intro S _ _ G _ _ hfin htf 𝔪 h𝔪
  have : Module.Flat S G := inferInstance
  let e₁ : (S ⧸ 𝔪) ≃ₐ[S] 𝔪.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom S (S ⧸ 𝔪) 𝔪.ResidueField)
      𝔪.bijective_algebraMap_quotient_residueField
  let e : (G ⧸ 𝔪 • (⊤ : Submodule S G)) ≃ₗ[S] 𝔪.Fiber G :=
    (TensorProduct.quotTensorEquivQuotSMul G 𝔪).symm ≪≫ₗ
      TensorProduct.congr e₁.toLinearEquiv (LinearEquiv.refl S G)
  rw [e.length_eq, Module.length_eq_of_surjective (R := 𝔪.ResidueField)
    𝔪.algebraMap_residueField_surjective, Module.length_eq_finrank, Ideal.finrank_fiber_eq_finrank]
end DedekindFibreRank
end GroundTheory.Heights₂.Heights.Kleiman
