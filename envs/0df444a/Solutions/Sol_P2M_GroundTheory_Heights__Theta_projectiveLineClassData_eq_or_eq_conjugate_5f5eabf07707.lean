-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_or_eq_conjugate_5f5eabf07707
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:43.408039+00:00
-- url     : https://prove2.me/submissions/eb57df24-dac6-4209-af1e-e8877a7a7bd9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (φ : K →+* ℂ) : φ = σ ∨ φ = conjugate σ := by
  classical
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [NumberField.Embeddings.card K ℂ, hK]
  have h2 : ({σ, conjugate σ} : Finset (K →+* ℂ)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (conjugate_ne σ hσ).symm, hcard]
  have : φ ∈ ({σ, conjugate σ} : Finset (K →+* ℂ)) := h2 ▸ Finset.mem_univ φ
  simpa using this
end GroundTheory.Heights₂.Theta.projectiveLineClassData
