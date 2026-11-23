-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.sval_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:03.071573+00:00
-- url     : https://prove2.me/submissions/a7447bb6-9646-487c-a054-504a8c07c031

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_gs_sum

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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ j : K → L.ι, s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = ∑ i, gs r z ⊤ (b i) * sval (t i) r z J := by
  have hmem : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((φ k).base ⁻¹' (L.U (J (r ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
  show gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k))) = _
  rw [hs, gs_sum r z _ hmem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hmem]
  congr 1
  exact gs_res r z le_top hmem (b i)
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
