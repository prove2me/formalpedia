-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.E_nablaPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:45.766728+00:00
-- url     : https://prove2.me/submissions/b209a95e-1f3f-48f6-afe6-696406c5c1a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionSecondOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_bE_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_E_foldr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {k}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
    subst (bE k h) (nablaPoly k B h m u P G) = DpolyOf (B.FK k) u P (subst (bE k h) G) := by
  have hb : HasSubst (bE k h) := hasSubst_lemma (bE_const k h hax)
  unfold nablaPoly DpolyOf DmonOf
  rw [← coe_substAlgHom hb, map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_mul, coe_substAlgHom hb, mvPowerSeries_subst_C hb, E_foldr B h hax m u n]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
