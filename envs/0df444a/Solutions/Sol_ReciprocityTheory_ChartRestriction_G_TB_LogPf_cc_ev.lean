-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:48.280107+00:00
-- url     : https://prove2.me/submissions/2f46d8e4-eade-4fdc-9adc-6691d67b87f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
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
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
private theorem cc_subst_lemma {σ τ : Type} [Fintype σ] {L : σ → MvPowerSeries τ k}
    (hL0 : ∀ p, constantCoeff (L p) = 0) (F : MvPowerSeries σ k) :
    constantCoeff (MvPowerSeries.subst L F) = constantCoeff F := by
  classical
  have hL : MvPowerSeries.HasSubst L := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hL0
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hL, finsum_eq_single _ 0]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact he (Finsupp.ext hn)
    have hz : constantCoeff (e.prod fun s n => L s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
      rw [map_pow, hL0, zero_pow hp]
    rw [hz, smul_zero]
variable (G : FGLaw k d)
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  exact cc_subst_lemma (σ := Fin m × Fin d) (τ := Fin n × Fin d) (L := fun p => a p.1 p.2) (fun p => ha p.1 p.2) f
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
