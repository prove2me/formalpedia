-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.foldr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:25.097418+00:00
-- url     : https://prove2.me/submissions/fc89ebca-bc2d-47fe-8105-a4bf4588a3a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_iter_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
section lin
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
private theorem Dof_add' (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f + g) = Dof F v f + Dof F v g := by
  first
  | simp only [Dof, map_add, mul_add, Finset.sum_add_distrib]
  | simp [Dof, mul_add, Finset.sum_add_distrib]
end lin
section deg
variable {ι : Type} [Fintype ι]
end deg
section wick
variable [Algebra ℚ k]
end wick
end ReciprocityTheory.ChartRestriction.G.TB.GE
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (L : List ι) (m : ι →₀ ℕ) (f g : PS k 1 d) :
    L.foldr (fun l h => (Dof F (u l))^[m l] h) (f + g) =
      L.foldr (fun l h => (Dof F (u l))^[m l] h) f + L.foldr (fun l h => (Dof F (u l))^[m l] h) g := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons, ih]
    exact iter_add _ (fun f g => Dof_add' F (u l) f g) _ _ _
end ReciprocityTheory.ChartRestriction.G.TB.GE
