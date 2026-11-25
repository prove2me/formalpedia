-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dof_Cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:40:23.570716+00:00
-- url     : https://prove2.me/submissions/441a43a4-0da9-463d-be95-a0b71daaa812

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (F : Fin d → PS k 2 d) (u : Fin d → k) (a : k) (g : PS k 1 d) :
    Dof F u (C a * g) = C a * Dof F u g := by
  have hD : ∀ j, pderiv k ((0 : Fin 1), j) (C a * g) = C a * pderiv k ((0 : Fin 1), j) g := by
    intro j
    rw [Derivation.leibniz]
    have h0 : pderiv k ((0 : Fin 1), j) (C a : PS k 1 d) = 0 := by
      rw [show (C a : PS k 1 d) = algebraMap k (PS k 1 d) a from rfl]
      exact Derivation.map_algebraMap _ _
    rw [h0, smul_zero, add_zero, smul_eq_mul]
  simp only [Dof, hD]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
