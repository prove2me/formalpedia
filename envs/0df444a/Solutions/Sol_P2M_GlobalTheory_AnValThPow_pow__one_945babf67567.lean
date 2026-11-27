-- Prove2me | solution 1 for P2M_GlobalTheory_AnValThPow_pow__one_945babf67567
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:18.441137+00:00
-- url     : https://prove2.me/submissions/0250623b-2d7b-462d-bbf6-54537d66b2d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ThetaConstantPowEqOneOfPowerTrivial
import Theorems.Thm_GlobalTheory_AnValThPow_translT_translPt

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
open GlobalTheory GlobalTheory.AnValThPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}
namespace GlobalTheory.AnValThPow
theorem _root_.solution [IsCommMonObj A] (x : T ⟶ A) (n : ℕ) (i : Fin n) :
    powφ A x n (i, 1) = (translPt A (x ^ ((i : ℕ) + 1))).left := by
  unfold powφ
  dsimp only
  rw [Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, translT_translPt, ← pow_succ']
end GlobalTheory.AnValThPow
