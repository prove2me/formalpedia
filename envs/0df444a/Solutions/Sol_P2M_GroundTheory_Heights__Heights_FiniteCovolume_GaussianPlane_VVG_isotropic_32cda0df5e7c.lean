-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_VVG_isotropic_32cda0df5e7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:10:42.007012+00:00
-- url     : https://prove2.me/submissions/50fa5892-bb0c-4b48-aa7d-96180af88bd2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_isotropicVector_ne_zero_3e8a12d81f0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_hermitian_isotropicVector_f0a977af7739
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
theorem _root_.solution : ∀ x ∈ VVG, x ≠ 0 ∧ hG.toSesq x x = 0 := by
  rintro _ ⟨γ, -, rfl⟩
  refine ⟨fun h => isotropicVector_ne_zero ((smul_eq_zero_iff_eq γ).1 h), ?_⟩
  rw [← hermitian_isotropicVector]
  exact HermitianForm.mem_unitaryGroup.1 γ.2 v0 v0
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
