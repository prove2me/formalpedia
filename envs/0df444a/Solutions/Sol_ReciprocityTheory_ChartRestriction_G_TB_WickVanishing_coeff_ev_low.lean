-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:56.367429+00:00
-- url     : https://prove2.me/submissions/46da3ac0-7a33-4c07-9f4f-94ea6e7966ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_one_le_iInf_order
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_axes


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
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a' : Fin 2 → Pt k 2 d)
    (ha' : ∀ j i, constantCoeff (a' j i) = 0) (e : Fin 2 × Fin d →₀ ℕ) (he : e.degree < 2) :
    coeff e (ev (n := 2) a' h) = 0 := by
  apply coeff_of_lt_order
  unfold ev
  refine lt_of_lt_of_le ?_ (le_order_subst (hasSubst_of_constantCoeff_zero (a := fun p : Fin 2 × Fin d => a' p.1 p.2)
    (fun p => ha' p.1 p.2)) h)
  have h2 : (2 : ℕ∞) ≤ h.order := nat_le_order (coeff_eq_zero_of_axes h hc.ax0 hc.ax1)
  calc (e.degree : ℕ∞) < 2 := by exact_mod_cast he
    _ = 1 * 2 := (one_mul _).symm
    _ ≤ _ := mul_le_mul' (one_le_iInf_order _ (fun p => ha' p.1 p.2)) h2
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
