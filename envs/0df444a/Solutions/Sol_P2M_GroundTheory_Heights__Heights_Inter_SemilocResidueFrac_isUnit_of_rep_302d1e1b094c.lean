-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_isUnit_of_rep_302d1e1b094c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:43.366308+00:00
-- url     : https://prove2.me/submissions/2dd0b3e3-7d1f-452a-a7bf-34ae9afd19e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_eq_zero_iff_cc85a26563f0


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
theorem _root_.solution (P W : Ideal (MRing ι)) [P.IsPrime] (hPW : P ≤ W) {z : locRing P W} {u w : MRing ι}
    {a : K → ℕ} (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) (huW : u ∉ W)
    (e : (z : FractionRing (MRing ι ⧸ P)) * regularityLocalResidue_holds.frHom P w = regularityLocalResidue_holds.frHom P u) : IsUnit z := by
  have hu0 : regularityLocalResidue_holds.frHom P u ≠ 0 := fun h => huW (hPW (regularityLocalResidue_holds.frHom_eq_zero_iff.1 h))
  refine IsUnit.of_mul_eq_one (⟨_, regularityLocalResidue_holds.mem_locRing_of_form hPW hw hu huW⟩ : locRing P W) (Subtype.ext ?_)
  show (z : FractionRing (MRing ι ⧸ P)) * (regularityLocalResidue_holds.frHom P w * (regularityLocalResidue_holds.frHom P u)⁻¹) = 1
  rw [← mul_assoc, e, mul_inv_cancel₀ hu0]
end GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
