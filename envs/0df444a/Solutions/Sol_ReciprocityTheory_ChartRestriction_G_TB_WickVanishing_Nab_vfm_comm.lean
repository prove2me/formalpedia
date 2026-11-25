-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.vfm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:13.329558+00:00
-- url     : https://prove2.me/submissions/5a6b4fa8-b712-4f92-9d4f-3e4c5f38a98e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vf_comm
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
section VF
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]
private theorem vf_sub' {k : Type} [CommRing k] {τ : Type} [Fintype τ] (c : τ → MvPowerSeries τ k)
    (a b : MvPowerSeries τ k) : vf c (a - b) = vf c a - vf c b := by
  simp only [vf, map_sub, mul_sub, Finset.sum_sub_distrib]
private theorem vf_mul' {k : Type} [CommRing k] {τ : Type} [Fintype τ] (c : τ → MvPowerSeries τ k)
    (a b : MvPowerSeries τ k) : vf c (a * b) = a * vf c b + b * vf c a := by
  simp only [vf, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
end VF
section Law
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
end Law
section Transfer
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
end Transfer
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (c c' : τ → MvPowerSeries τ k) (f f' G : MvPowerSeries τ k) :
    (vf c (vf c' G - f' * G) - f * (vf c' G - f' * G)) - (vf c' (vf c G - f * G) - f' * (vf c G - f * G)) =
      vf (fun t => vf c (c' t) - vf c' (c t)) G - (vf c f' - vf c' f) * G := by
  rw [vf_sub', vf_sub', vf_mul', vf_mul', ← vf_comm]
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
