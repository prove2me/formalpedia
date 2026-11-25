-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_compound_injective_e33b2c31042c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:49.215721+00:00
-- url     : https://prove2.me/submissions/86f175c2-3a2e-4ce4-ae5e-bf97d203e47f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_eq_one_1c79c4c51027
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_compound_mul_eq_7a2fc1706bba

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {F : Type} [Field F] {N1 n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {m : ℕ} (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B.row) :
    Function.Injective (Matrix.of fun (S : {S : Finset (Fin N1) // S.card = m})
      (S' : {S : Finset (Fin n) // S.card = m}) =>
        (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det).mulVec := by
  obtain ⟨C, hBC⟩ := exists_mul_eq_one B hB
  let D : Matrix {S : Finset (Fin n) // S.card = m} {S : Finset (Fin N1) // S.card = m} F :=
    Matrix.of fun S'' S => (C.submatrix (S.1.orderEmbOfFin S.2) (S''.1.orderEmbOfFin S''.2)).det
  have hD : D * (Matrix.of fun (S : {S : Finset (Fin N1) // S.card = m})
      (S' : {S : Finset (Fin n) // S.card = m}) =>
        (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det) = 1 := by
    ext S'' S'
    have hc : (if S'' = S' then (1 : F) else 0) = if S' = S'' then 1 else 0 := if_congr eq_comm rfl rfl
    rw [Matrix.mul_apply, Matrix.one_apply, hc, ← compound_mul_eq B C hBC S' S'']
    rfl
  intro x y hxy
  have := congrArg D.mulVec hxy
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD, Matrix.one_mulVec, Matrix.one_mulVec] at this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
