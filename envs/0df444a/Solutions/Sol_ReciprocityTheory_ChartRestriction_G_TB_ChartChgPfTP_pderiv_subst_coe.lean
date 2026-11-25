-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:43.667022+00:00
-- url     : https://prove2.me/submissions/f640ffbc-64f8-44d7-9328-8f8dc1255811

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ τ : Type} [Fintype σ] [DecidableEq σ] {a : σ → MvPowerSeries τ k} (hs : HasSubst a)
    (i : τ) (p : MvPolynomial σ k) :
    pderiv k i (substAlgHom hs (p : MvPowerSeries σ k)) =
      ∑ s, substAlgHom hs (pderiv k s (p : MvPowerSeries σ k)) * pderiv k i (a s) := by
  classical
  have h1 : subst a (1 : MvPowerSeries σ k) = 1 := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact map_one _
  have h0 : subst a (0 : MvPowerSeries σ k) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact map_zero _
  rw [MvPowerSeries.coe_substAlgHom]
  induction p using MvPolynomial.induction_on
  next c =>
    have hc : ((MvPolynomial.C c : MvPolynomial σ k) : MvPowerSeries σ k) = c • (1 : MvPowerSeries σ k) := by
      first
      | rw [MvPolynomial.coe_C, MvPowerSeries.smul_eq_C_mul, mul_one]
      | simp [MvPowerSeries.smul_eq_C_mul]
    rw [hc]
    simp [map_smul, Derivation.map_one_eq_zero, h1, h0, MvPowerSeries.subst_smul hs]
  next p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, MvPowerSeries.subst_add hs, hp, hq, add_mul, Finset.sum_add_distrib]
  next p s hp =>
    have hpX : ((p * MvPolynomial.X s : MvPolynomial σ k) : MvPowerSeries σ k) = (p : MvPowerSeries σ k) * X s := by
      first
      | rw [MvPolynomial.coe_mul, MvPolynomial.coe_X]
      | simp
    have hδ : ∑ s', subst a (p : MvPowerSeries σ k) * subst a (pderiv k s' (X s : MvPowerSeries σ k)) *
        pderiv k i (a s') = subst a (p : MvPowerSeries σ k) * pderiv k i (a s) := by
      rw [Finset.sum_eq_single s]
      · simp [MvPowerSeries.pderiv_X, Pi.single_apply, h1]
      · intro b _ hb
        simp [MvPowerSeries.pderiv_X, Pi.single_apply, hb, Ne.symm hb, h0]
      · simp
    rw [hpX, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_X hs, Derivation.leibniz, hp]
    simp only [Derivation.leibniz, smul_eq_mul, MvPowerSeries.subst_add hs, MvPowerSeries.subst_mul hs,
      MvPowerSeries.subst_X hs, add_mul, Finset.sum_add_distrib, hδ]
    first
    | (simp only [Finset.mul_sum, mul_assoc])
    | (rw [Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun _ _ => by ring)
    | ring
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
