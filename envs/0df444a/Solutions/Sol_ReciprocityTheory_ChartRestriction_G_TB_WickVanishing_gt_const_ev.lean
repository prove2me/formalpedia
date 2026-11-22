-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:29:27.393076+00:00
-- url     : https://prove2.me/submissions/33896431-31df-4700-a183-3c21964c1ca5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Exp2
variable (A : Type) [CommRing A] [Algebra ℚ A]
end Exp2
section Ev
variable {k : Type} [CommRing k] {d : ℕ}
private theorem gt_cc_lemma {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ k) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact he (Finsupp.ext hne)
    have h0 : constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, ha s, zero_pow hs])
    rw [h0, smul_zero]
end Ev
section Calc
variable {k : Type} [CommRing k] {d : ℕ}
end Calc
section Calc2
variable {k : Type} [CommRing k] {d : ℕ}
end Calc2
section Main
end Main
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (f : PS k m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  exact (gt_cc_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f).trans hf
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
