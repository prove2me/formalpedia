-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.E_liftX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:48.901134+00:00
-- url     : https://prove2.me/submissions/2332d831-137b-403c-aabb-4dbef657d3c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionSecondOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_bE_const
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
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
theorem _root_.solution (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (f : PS k 1 d) :
    subst (bE k h) (liftX k f) = f := by
  have hb : HasSubst (bE k h) := hasSubst_lemma (bE_const k h hax)
  have hl : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) := hasSubst_lemma (fun p => by simp)
  unfold liftX
  first
  | rw [subst_comp_subst_apply hl hb]
  | rw [subst_comp_subst_apply hb hl]
  have e : (fun p : Fin 1 × Fin d => subst (bE k h) (X (Sum.inl p.2) : AA k d)) =
      (X : Fin 1 × Fin d → PS k 1 d) := by
    funext p
    rw [subst_X hb]
    rcases p with ⟨q, j⟩
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    rfl
  rw [e]
  first
  | (rw [subst_self]; rfl)
  | exact congrFun subst_self f
  | simp [subst_self]
  | (rw [← map_algebraMap_eq_subst_X]; simp)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
