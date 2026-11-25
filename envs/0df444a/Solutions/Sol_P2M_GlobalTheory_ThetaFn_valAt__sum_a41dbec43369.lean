-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaFn_valAt__sum_a41dbec43369
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:34.449546+00:00
-- url     : https://prove2.me/submissions/1711f0c6-7806-473a-9bc8-a57c0868b734

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.ThetaFn
theorem _root_.solution {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {I : Type*} (t : Finset I) (f : I → Γ(X, U)) :
    valAt' x U (∑ i ∈ t, f i) = ∑ i ∈ t, valAt' x U (f i) := by
  simp only [valAt'_eq_valHom x h, map_sum]
end GlobalTheory.ThetaFn
