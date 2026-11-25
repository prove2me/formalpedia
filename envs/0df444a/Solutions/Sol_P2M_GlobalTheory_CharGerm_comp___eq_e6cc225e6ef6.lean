-- Prove2me | solution 1 for P2M_GlobalTheory_CharGerm_comp___eq_e6cc225e6ef6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:48:33.949804+00:00
-- url     : https://prove2.me/submissions/7164d353-a34f-4d58-920e-efe871960f42

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_P2M_GlobalTheory_CharGerm_comp___of_le_7862f78d989c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints
variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)
namespace GlobalTheory.CharGerm
theorem _root_.solution {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ}
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  rcases le_total m n with h | h
  · exact comp_χ_of_le χ h u v huv
  · exact (comp_χ_of_le χ h v u huv.symm).symm
end GlobalTheory.CharGerm
