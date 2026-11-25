-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.germ_eq_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:26.338285+00:00
-- url     : https://prove2.me/submissions/584eb935-a3bf-4139-96a9-b11e4b4cf0f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (y : Y)
    {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (j : K → L.ι) (hy : y ∈ LB.wchart L φ j) :
    (Y.presheaf.germ (LB.wchart L φ j) y hy).hom (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J := by
  have h1 := sec_trans s (𝟙 Y) y (j' := fun k => J (𝟙 Y ≫ φ k)) hy (hJ.mem φ (𝟙 Y))
  erw [gs_eq (𝟙 Y) y _ hy] at h1
  unfold sval
  rw [← h1]
  first | rfl | simp
end ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
