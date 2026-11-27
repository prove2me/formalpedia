-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_OrthProjection_hyps_96e56183e03b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:19.888255+00:00
-- url     : https://prove2.me/submissions/f38f63ca-691e-4ab4-9a5e-762581f5c4f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_finrank_b2407f5ee816
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_conj_ne_one_e84154cc7c34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_invol_b290ae2f2fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm__a969c2c0434a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0e0_6b9fc7c10d02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_f0f0_a1dde18274c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0f0_88b2973874db

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic
attribute [local instance] topAE
attribute [local instance] isModuleTopology_AE
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace OrthProjection
theorem _root_.solution :
    (∀ x, (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x) ∧
      hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) :=
  ⟨gauss_invol, hypPlane_herm', hf_e0e0, hf_f0f0, hf_e0f0, gauss_finrank, gauss_conj_ne_one,
    isModuleTopology_AE⟩
end OrthProjection
end GroundTheory.Heights₂.Heights.StrongApprox
