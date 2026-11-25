-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_contAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:30.979706+00:00
-- url     : https://prove2.me/submissions/16067ced-2bfa-44ac-9885-1159df628191

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Mt_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ag_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ag_Nid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
theorem _root_.solution (p0 : ℕ) (hp : p0 ≤ r) (v0 : Fin r → ℂ) :
    ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ms p0 hp p.1 p.2) (Nid r, v0) := by
  have hinv : ContinuousAt (fun M : Matrix (Fin p0) (Fin p0) ℂ => M⁻¹) (Ag p0 hp (Nid r)) := by
    rw [Ag_Nid]
    apply continuousAt_matrix_inv
    rw [Matrix.det_one]
    have := NormedRing.inverse_continuousAt (1 : ℂˣ)
    rwa [Units.val_one] at this
  have hAg : ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ag p0 hp p.1) (Nid r, v0) :=
    ((Ag_cont p0 hp).comp continuous_fst).continuousAt
  have h1 : ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) =>
      ((p.2, p.1, (Ag p0 hp p.1)⁻¹) : (Fin r → ℂ) × (Fin r → Fin r → ℂ) × Matrix (Fin p0) (Fin p0) ℂ))
      (Nid r, v0) :=
    continuous_snd.continuousAt.prodMk
      (continuous_fst.continuousAt.prodMk (ContinuousAt.comp_of_eq hinv hAg rfl))
  have heq : (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ms p0 hp p.1 p.2) =
      fun p => Mt p0 hp (p.2, p.1, (Ag p0 hp p.1)⁻¹) := by
    funext p
    simp only [Ms, Mt]
  rw [heq]
  exact (Mt_cont p0 hp).continuousAt.comp h1
end ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
