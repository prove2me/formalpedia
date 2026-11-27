-- Prove2me | solution 1 for P2M_GlobalTheory_AdjRead_one_ad__554dde3ddb02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:58:21.347066+00:00
-- url     : https://prove2.me/submissions/801d7e05-a86b-48fd-931d-96f3a9ae6e90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjReadingOne
import Theorems.Thm_GlobalTheory_AdjRead_psum_one
import Theorems.Thm_P2M_GlobalTheory_AdjRead_comp_ad__1f5d75380be3

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.AdjRead
theorem _root_.solution {T : Over S} (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f'] (k) :
    (lift (1 : T ⟶ A) (1 : T ⟶ A)).left ≫ adφ f f' k = (1 : T ⟶ A).left := by
  rw [comp_adφ]
  have h1 : (![(1 : T ⟶ A), 1 ≫ f'] : Fin 2 → (T ⟶ A)) = fun _ => 1 := by
    funext i; fin_cases i <;> simp
  have h2 : (![(1 : T ⟶ A) ≫ f, 1] : Fin 2 → (T ⟶ A)) = fun _ => 1 := by
    funext i; fin_cases i <;> simp
  rcases k with I | I <;> simp only [Sum.elim_inl, Sum.elim_inr, cub, h1, h2, psum_one]
end GlobalTheory.AdjRead
