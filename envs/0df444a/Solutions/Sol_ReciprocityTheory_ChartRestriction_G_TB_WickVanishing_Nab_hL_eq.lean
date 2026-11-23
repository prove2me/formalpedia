-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.hL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:31.828484+00:00
-- url     : https://prove2.me/submissions/4466eeae-68f6-4764-b8d4-cdd44c38a25f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (w0 : O) :
    B.hL k h w0 = ev (n := 1) ![pt k d 0, B.actK k w0] h := by
  have hc : comp1 (B.actK k w0) (pt k d 0) = B.actK k w0 := by
    funext i
    unfold comp1 ev
    have hX : (fun p : Fin 1 × Fin d => (![pt k d 0] : Fin 1 → Pt k 1 d) p.1 p.2) = MvPowerSeries.X := by
      funext p
      obtain ⟨a, b⟩ := p
      fin_cases a
      rfl
    rw [hX, MvPowerSeries.subst_self]
    rfl
  unfold FB.hL
  rw [hc]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
