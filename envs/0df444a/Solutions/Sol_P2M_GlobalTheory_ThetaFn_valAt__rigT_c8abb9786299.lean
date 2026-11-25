-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaFn_valAt__rigT_c8abb9786299
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:13.636803+00:00
-- url     : https://prove2.me/submissions/05440964-17a8-4955-9167-8069eb388d82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__unit_zpow_a99706afe68e
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c
import Theorems.Thm_GlobalTheory_ThetaFn_mem_ptChart_iff
import Theorems.Thm_GlobalTheory_ThetaFn_comp_one_eq_ex_zero
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero


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
variable (p)
namespace GlobalTheory.ThetaFn
theorem _root_.solution {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) (k : ℤ)
    (j : Fin 1 → L.ι) (hj : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U (j 0)) :
    valAt' p.left (LB.wchart L (fun _ : Fin 1 => (1 : T ⟶ A).left) j)
      ((rigT A L rig T k).s j).val = u.fr (j 0) 0 ^ k := by
  have hj' := (mem_ptChart_iff (comp_one_eq_ex_zero u p) j).2 hj
  have hp : p.left ≫ T.hom = 𝟙 (Sp ℂ) := Over.w p
  have h0 : ⊤ ≤ (L.pull (eSec A)).U (fun _ => j 0) := by
    rw [ex_zero] at hj
    exact fun _ hy => Set.mem_iInter.2 fun _ => hj hy
  refine (valAt'_unit_zpow p.left hj' _ k).trans (congrArg (· ^ k) ?_)
  refine (valAt'_appLE' p.left T.hom (rigT_le A L j) hj' _).trans ?_
  rw [hp]
  exact (hrig (fun _ => j 0) h0).symm
end GlobalTheory.ThetaFn
