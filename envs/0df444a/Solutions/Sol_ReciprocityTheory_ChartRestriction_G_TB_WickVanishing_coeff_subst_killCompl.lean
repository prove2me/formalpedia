-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_killCompl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:43.273795+00:00
-- url     : https://prove2.me/submissions/8fef2bd8-47e0-45a0-bbaf-73ff3cdec3b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum

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
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {σ τ R : Type*} [CommRing R] [Finite τ] (e : σ ↪ τ) (f : MvPowerSeries τ R)
    (a : τ → MvPowerSeries σ R) (ha : ∀ t, a t = killCompl e (X t)) (x : σ →₀ ℕ) :
    coeff x (subst a f) = coeff (embDomain e x) f := by
  classical
  have haS : HasSubst a := by
    apply hasSubst_of_constantCoeff_zero
    intro t
    rw [ha, ← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  have hterm : ∀ n : τ →₀ ℕ, coeff n f • coeff x (n.prod fun s m => a s ^ m) =
      if n = embDomain e x then coeff n f else 0 := by
    intro n
    have hprod : (n.prod fun s m => a s ^ m) = killCompl e (monomial n (1 : R)) := by
      have h1 := monomial_eq (R := R) n (fun _ => 1)
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [h1, map_prod]
      simp only [map_pow, ha, Finsupp.prod]
    rw [hprod, coeff_killCompl, coeff_monomial]
    by_cases hn : n = embDomain e x
    · subst hn
      simp
    · rw [if_neg (Ne.symm hn), if_neg hn, smul_zero]
  rw [coeff_subst haS, finsum_eq_single _ (embDomain e x)]
  · rw [hterm, if_pos rfl]
  · intro n hn
    rw [hterm, if_neg hn]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
