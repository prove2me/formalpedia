-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaModelGroup_valAt__eval__5710659469e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:32:35.649138+00:00
-- url     : https://prove2.me/submissions/7db080f4-47b6-4b07-821f-99c8590a90a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b
import Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
namespace GlobalTheory.ThetaModelGroup
theorem _root_.solution {κ : Type} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) (U : X.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ U)
    (r : κ → Γ(X.left, U)) (F : MvPolynomial κ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun c => valAt' x.left U (r c)) F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact valAt'_constFn x.left X.hom (Over.w x) U a h
  | add p q hp hq => rw [MvPolynomial.eval₂_add, valAt'_add, hp, hq, map_add]
  | mul_X p c hp => rw [MvPolynomial.eval₂_mul, valAt'_mul, hp, MvPolynomial.eval₂_X, map_mul, MvPolynomial.eval_X]
end GlobalTheory.ThetaModelGroup
