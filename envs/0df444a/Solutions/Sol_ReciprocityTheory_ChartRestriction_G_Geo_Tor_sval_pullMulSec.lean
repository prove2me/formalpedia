-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.sval_pullMulSec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:48.106833+00:00
-- url     : https://prove2.me/submissions/f791b937-19d8-46ce-bf3f-5193b4e47b6f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
variable {L} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (r : Z ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullMulSec s h u hu) r z J = sval s (r ≫ h) z J * (val u r z J).val := by
  have hm := hJ.mem (Sum.elim (fun k => h ≫ φ k) φ₃) r
  have hm1 : h (r z) ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  have hm3 : r z ∈ LB.wchart L φ₃ (fun k => J (r ≫ φ₃ k)) := hJ.mem φ₃ r
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z _ hm _).trans (gs_pull r h z _ hm1 _))
    ((gs_res r z _ hm _).trans (gs_unit r z _ hm3 _)))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
