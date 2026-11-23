-- Prove2me | solution 1 for P2M_GlobalTheory_LamBiext_prod_law__e869053602e8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:31.522127+00:00
-- url     : https://prove2.me/submissions/f22c9ab0-c9d1-4f6d-bc02-b67794bbba6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.LamBiext
theorem _root_.solution {T : Over S} (a b c : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 G).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift (a * b) c).left * (h (lift a c).left)⁻¹ * (h (lift b c).left)⁻¹ := by
  have r₀ : lift a (lift b c) ≫ x3 G 0 = a := by simp [x3]
  have r₁ : lift a (lift b c) ≫ x3 G 1 = b := by simp [x3]
  have r₂ : lift a (lift b c) ≫ x3 G 2 = c := by simp [x3]
  have s : lift a (lift b c) ≫ padd G (x3 G 0) (x3 G 1) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  refine (Fintype.prod_equiv Equiv.ulift _ (fun i : Fin 3 => h ((lift a (lift b c)).left ≫
    law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift a (lift b c) ≫ lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, s, r₀, r₁, r₂]
  simp only [zpow_neg, zpow_one]
end GlobalTheory.LamBiext
