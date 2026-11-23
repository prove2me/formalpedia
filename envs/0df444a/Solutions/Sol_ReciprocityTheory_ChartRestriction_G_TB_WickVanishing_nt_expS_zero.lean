-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.nt_expS_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:33.563085+00:00
-- url     : https://prove2.me/submissions/066e2efb-9106-4a66-ac40-d71fea7a56bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  have hdvd : (PowerSeries.X : PowerSeries k) ^ 1 ∣ PowerSeries.exp k - 1 := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    first
    | (simp [PowerSeries.coeff_exp]; done)
    | (simp only [map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_one, if_true, Nat.factorial_zero,
        Nat.cast_one, div_one, map_one, sub_self]; done)
  obtain ⟨R, hR⟩ := hdvd
  have hexp : PowerSeries.exp k = 1 + PowerSeries.X ^ 1 * R := by
    rw [← hR]
    ring
  have hc : constantCoeff (0 : PS k n d) = 0 := map_zero _
  have hs : PowerSeries.HasSubst (0 : PS k n d) := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hc
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hc
    | (show IsNilpotent _; rw [hc]; exact IsNilpotent.zero)
  have key : ∀ f : PowerSeries k, PowerSeries.subst (0 : PS k n d) f = PowerSeries.substAlgHom hs f := by
    intro f
    first
    | rw [PowerSeries.coe_substAlgHom]
    | rfl
  have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries k) = 0 := by
    first
    | exact PowerSeries.substAlgHom_X hs
    | (rw [← key]; exact PowerSeries.subst_X hs)
  unfold FB.expS
  rw [hexp, key]
  simp [hX]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
