-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_eq_mul_of_valAt__eq_continuous_mul_9681dd359b4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:26.636908+00:00
-- url     : https://prove2.me/submissions/37d4e1ba-7dff-4b8b-9274-57bd856940bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqMulOfContinuousOnQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqMulOfContinuousOnQuotientStatement
import Theorems.Thm_GlobalTheory_exists_eq_mul_of_continuousOn_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (u : HolUnif P.A L P.g) (U : P.A.left.Opens) (a b : Γ(P.A.left, U)) (φ : (Fin P.g → ℂ) → ℂ), Out.Laws → IsAffineOpen U → b ≠ 0 → ContinuousOn φ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} → (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U a = φ z * valAt' (u.ex z).left U b) → ∃ c : Γ(P.A.left, U), a = c * b := by
  first | exact @GlobalTheory.exists_eq_mul_of_continuousOn_quotient | exact GlobalTheory.exists_eq_mul_of_continuousOn_quotient | (intros; apply GlobalTheory.exists_eq_mul_of_continuousOn_quotient <;> assumption)
end _root_.GlobalTheory.T
