-- Prove2me | solution 1 for PIW.HCFdeg.adjoint_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:07.500578+00:00
-- url     : https://prove2.me/submissions/66a82ec1-a32a-415e-8a27-ecb46717f3d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_CommuteStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open scoped InnerProductSpace ComplexStarModule
open ContinuousLinearMap
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : G →* (H →L[ℂ] H))
namespace PIW.HCFdeg
theorem _root_.solution (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) : adjoint (π g) = π g⁻¹ := by
  have hinner : ∀ (h : G) (x y : H), ⟪π h x, π h y⟫_ℂ = ⟪x, y⟫_ℂ := fun h x y =>
    (⟨(π h).toLinearMap, hπ h⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
  have hinv : ∀ x, π g (π g⁻¹ x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    simp
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  conv_rhs => rw [← hinv x]
  rw [hinner]
end PIW.HCFdeg
