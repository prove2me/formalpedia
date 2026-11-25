-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.foldr_Cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:23.699291+00:00
-- url     : https://prove2.me/submissions/6d5d18e5-3d92-45c1-8108-371fe85bb8f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_iter_Cmul
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
private theorem Dof_C_mul (v : Fin d → k) (r : k) (f : PS k 1 d) :
    Dof F v (C r * f) = C r * Dof F v f := by
  first
  | (simp only [Dof, ← MvPowerSeries.smul_eq_C_mul, map_smul, mul_smul_comm, Finset.smul_sum]; done)
  | (simp only [Dof, ← MvPowerSeries.smul_eq_C_mul, Derivation.map_smul, mul_smul_comm, Finset.smul_sum]; done)
  | (simp only [Dof, Finset.mul_sum, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib]; done)
  | (have hp := (pderiv : Unit))
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
theorem _root_.solution (L : List ι) (m : ι →₀ ℕ) (r : k) (f : PS k 1 d) :
    L.foldr (fun l h => (Dof F (u l))^[m l] h) (C r * f) =
      C r * L.foldr (fun l h => (Dof F (u l))^[m l] h) f := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons, ih]
    exact iter_Cmul _ (fun r f => Dof_C_mul F (u l) r f) _ _ _
end ReciprocityTheory.ChartRestriction.G.TB.GE
