-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaFn_IsFnAt_valAt__ptSecT_57da73e55bb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:38.296268+00:00
-- url     : https://prove2.me/submissions/0036f434-3184-4a19-9bb4-467c8fe48744

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c
import Theorems.Thm_GlobalTheory_ThetaFn_comp_ptSecT
import Theorems.Thm_GlobalTheory_ThetaFn_mem_ptChart_iff

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
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)
variable {u p}
namespace GlobalTheory.ThetaFn
namespace IsFnAt
theorem _root_.solution {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z) (j : Fin 1 → L.ι)
    (hj : ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => x.left) j) :
    valAt' p.left (LB.wchart L (fun _ : Fin 1 => x.left) j)
      ((T.left.presheaf.map (homOfLE (val_le A L x j)).op).hom
        (((ptSecT A x).left.app _).hom (s.f j))) = θ z * u.fr (j 0) z ^ k := by
  refine (valAt'_appLE' p.left (ptSecT A x).left (val_le A L x j) hj _).trans ?_
  rw [comp_ptSecT u p hx]
  exact h j z ((exAt_mem_chart_iff u p k j z).2 ((mem_ptChart_iff hx j).1 hj))
end IsFnAt
end GlobalTheory.ThetaFn
