-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.genHasVal_powGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:26:14.634282+00:00
-- url     : https://prove2.me/submissions/fdb23b97-7cb9-4a88-9918-6df43947d6f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsValGenHasVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) (k : ℕ) :
    GenHasVal ϖ L φ φ' hφ (fun i => (k : ℤ) * ε i) (GeneratorPullback.powGen L φ' ε t k) (k * n) := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  refine ⟨GeneratorPullback.powGen L φ ε e k, ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen L φ ε e he k, c ^ k, ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := hc
    refine ⟨u ^ k, ?_⟩
    rw [mul_pow, ← zpow_natCast (_ ^ n), ← zpow_mul, mul_comm n, Units.val_pow_eq_pow_val, map_pow]
  · intro j
    have h1 : (GeneratorPullback.powGen L φ' ε t k).s j = t.s j ^ k := rfl
    have h2 : (GeneratorPullback.powGen L φ ε e k).s j = e.s j ^ k := rfl
    rw [h1, h2, Units.val_pow_eq_pow_val, hte j]
    erw [mul_pow, map_pow, map_pow, Units.val_pow_eq_pow_val]
    congr 1
    simp only [scal, resTop, map_pow]
    rfl
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
