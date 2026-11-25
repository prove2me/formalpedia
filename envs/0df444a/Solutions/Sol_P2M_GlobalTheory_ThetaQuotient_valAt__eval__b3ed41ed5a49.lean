-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaQuotient_valAt__eval__b3ed41ed5a49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:40.867931+00:00
-- url     : https://prove2.me/submissions/ac600f67-6fe6-437e-ad4d-849750c8b3c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous
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
open GlobalTheory.ThetaQuotient
namespace GlobalTheory.ThetaQuotient
theorem _root_.solution {σ : Type*} {X : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) {U : X.left.Opens}
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (r : σ → Γ(X.left, U)) (F : MvPolynomial σ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun i => valAt' x.left U (r i)) F := by
  have hx : x.left ≫ X.hom = 𝟙 _ := Over.w x
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact valAt'_constFn x.left X.hom hx U a h
  | add p q hp hq => rw [MvPolynomial.eval₂_add, map_add, valAt'_add, hp, hq]
  | mul_X p i hp => rw [MvPolynomial.eval₂_mul, map_mul, valAt'_mul, hp, MvPolynomial.eval₂_X, MvPolynomial.eval_X]
end GlobalTheory.ThetaQuotient
