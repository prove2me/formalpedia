-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.homK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:43.782531+00:00
-- url     : https://prove2.me/submissions/db466045-b751-4e64-bca0-1b5cf5e8c587

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_zero_constant_first_point


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
theorem _root_.solution (B : FB R d O) (a : O) (c : Fin d) :
    ev (n := 2) ![(lawK k B).F] (B.actK k a c) =
      ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] (B.FK k c) := by
  have h := congrArg (fun P : Pt R 2 d => MvPowerSeries.map (algebraMap R k) (P c)) (B.A.hom a)
  simp only [comp1, FGLaw.add, addOf] at h
  have c01 : CZ (![pt R (n := 2) d 0, pt R d 1] : Fin 2 → Pt R 2 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) CZ.nil)
  have cL : CZ (![addOf B.G.F (pt R (n := 2) d 0) (pt R d 1)] : Fin 1 → Pt R 2 d) :=
    CZ.cons (fun i => constantCoeff_ev c01 (B.G.const i)) CZ.nil
  have cR : CZ (![comp1 (B.A.act a) (pt R (n := 2) d 0), comp1 (B.A.act a) (pt R (n := 2) d 1)] : Fin 2 → Pt R 2 d) :=
    CZ.cons (fun i => constantCoeff_ev zero_constant_first_point (B.A.const a i)) (CZ.cons (fun i => constantCoeff_ev czY (B.A.const a i)) CZ.nil)
  rw [map_ev _ cL, map_ev _ cR] at h
  have m1 : ∀ i, MvPowerSeries.map (algebraMap R k) (addOf B.G.F (pt R (n := 2) d 0) (pt R d 1) i) = B.FK k i := by
    intro i
    show MvPowerSeries.map (algebraMap R k) (ev (n := 2) ![pt R d 0, pt R d 1] (B.G.F i)) = _
    rw [map_ev _ c01]
    have : (fun j c => MvPowerSeries.map (algebraMap R k) ((![pt R (n := 2) d 0, pt R d 1] : Fin 2 → Pt R 2 d) j c)) =
        fun j => pt k (n := 2) d j := by
      funext j c; fin_cases j <;> simp [pt_apply]
    rw [this, ev_pt]
    rfl
  have m2 : ∀ (l : Fin 2) (i : Fin d), MvPowerSeries.map (algebraMap R k) (comp1 (B.A.act a) (pt R (n := 2) d l) i) =
      comp1 (B.actK k a) (pt k (n := 2) d l) i := by
    intro l i
    show MvPowerSeries.map (algebraMap R k) (ev (n := 2) ![pt R d l] (B.A.act a i)) = ev (n := 2) ![pt k d l] (B.actK k a i)
    rw [map_ev _ (CZ.cons (cc_pt l) CZ.nil)]
    congr 1
    funext j c; fin_cases j; simp [pt_apply]
  have fL : (fun j i => MvPowerSeries.map (algebraMap R k)
      ((![addOf B.G.F (pt R (n := 2) d 0) (pt R d 1)] : Fin 1 → Pt R 2 d) j i)) = ![(lawK k B).F] := by
    funext j i; fin_cases j; exact m1 i
  have fR : (fun j i => MvPowerSeries.map (algebraMap R k)
      ((![comp1 (B.A.act a) (pt R (n := 2) d 0), comp1 (B.A.act a) (pt R (n := 2) d 1)] : Fin 2 → Pt R 2 d) j i)) =
      ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] := by
    funext j i; fin_cases j
    · exact m2 0 i
    · exact m2 1 i
  rw [fL, fR] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
