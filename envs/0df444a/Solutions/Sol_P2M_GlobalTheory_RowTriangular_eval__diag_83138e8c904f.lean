-- Prove2me | solution 1 for P2M_GlobalTheory_RowTriangular_eval__diag_83138e8c904f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:43.110302+00:00
-- url     : https://prove2.me/submissions/7b3b7e6d-bde4-4603-90a4-3b4dc96a064b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RowTriangular
open MvPolynomial
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k T : Type} [Field k] [CommRing T]
namespace GlobalTheory.RowTriangular
theorem _root_.solution [Fintype Ty] (φ : k →+* T) {a : Ty → ℕ → ℕ} {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowDeg r n k a P) (c : ∀ σ, Fin (r σ) → T) (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => c ℓ.1 ℓ.2.1 * y ℓ) P =
      (∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 ^ a p.1 p.2) * eval₂Hom φ y P := by
  classical
  simp only [coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ ℓ : Letter Ty r n, c ℓ.1 ℓ.2.1 ^ m ℓ = ∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 ^ a p.1 p.2 := by
    rw [Fintype.prod_sigma, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hP m hm σ i]
  rw [hc]
  ring
end GlobalTheory.RowTriangular
