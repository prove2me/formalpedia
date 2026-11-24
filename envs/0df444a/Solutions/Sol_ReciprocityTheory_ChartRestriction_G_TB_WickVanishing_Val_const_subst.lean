-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:57.875545+00:00
-- url     : https://prove2.me/submissions/e4db745f-736d-4a8c-8de9-2ef415335822

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionSecondOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
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
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
private theorem hasSubst_lemma {σ τ k : Type} [CommRing k] [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact ⟨fun s => by simp [ha s], fun d => Set.toFinite _⟩
private theorem mvPowerSeries_subst_C {σ τ k : Type} [CommRing k] {a : σ → MvPowerSeries τ k} (hs : HasSubst a) (c : k) :
    subst a (C c : MvPowerSeries σ k) = (C c : MvPowerSeries τ k) := by
  have e : ∀ (ρ : Type), (C c : MvPowerSeries ρ k) = c • (1 : MvPowerSeries ρ k) := fun ρ => by
    first
    | rw [MvPowerSeries.smul_eq_C_mul, mul_one]
    | simp [MvPowerSeries.smul_eq_C_mul]
  rw [e σ, e τ, ← coe_substAlgHom hs, map_smul, map_one]
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
section Inter
variable {k}
end Inter
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
theorem _root_.solution {σ τ k : Type} [CommRing k] [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (G : MvPowerSeries σ k) : constantCoeff (subst a G) = constantCoeff G := by
  have hs : HasSubst a := hasSubst_lemma ha
  have h0 : constantCoeff (G - C (constantCoeff G)) = 0 := by simp
  have h1 : constantCoeff (subst a (G - C (constantCoeff G))) = 0 := by
    first
    | exact constantCoeff_subst_eq_zero hs _ h0
    | exact constantCoeff_subst_eq_zero hs h0
    | (apply constantCoeff_subst_eq_zero <;> assumption)
  have e : subst a (G - C (constantCoeff G)) = subst a G - C (constantCoeff G) := by
    rw [← coe_substAlgHom hs, map_sub, coe_substAlgHom hs, mvPowerSeries_subst_C hs]
  rw [e, map_sub, constantCoeff_C, sub_eq_zero] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
