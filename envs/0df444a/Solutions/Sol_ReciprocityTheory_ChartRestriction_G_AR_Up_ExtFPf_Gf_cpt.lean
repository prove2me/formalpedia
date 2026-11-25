-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.Gf_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:45.806259+00:00
-- url     : https://prove2.me/submissions/d4607b61-f648-48aa-b915-eeac84f4754c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
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


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
private lemma one_mem_bor_upper_bounds {Ψ : Finset (E →+* ℂ)} :
    (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame Ψ r) ∈ Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne hca.ne'
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Gf D la F (cpt X x0 z) = ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) := by
  have hzd : cpt X x0 z ∈ X.dom := hz
  have hne : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hzd τ).2 i
    rw [h0] at h1
    simp at h1
  have hpos : 0 < X.nfac la (cpt X x0 z) := by
    unfold Data.nfac
    apply Finset.prod_pos
    intro τ _
    apply Finset.prod_pos
    intro i _
    apply Real.rpow_pos_of_pos
    exact norm_pos_iff.2 (div_ne_zero (hne τ i.succ) (hne τ i.castSucc))
  have hr1 : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = cpt X x0 z := by
    funext τ
    exact Matrix.mul_one (mat (cpt X x0 z) τ)
  obtain ⟨hΔ, hzo, hbo⟩ := D.uniq z hz _ one_mem_bor_upper_bounds
  rw [hr1] at hΔ hzo hbo
  have hP : P0 D la F (cpt X x0 z) = F z := by
    unfold P0
    rw [if_pos (show cpt X x0 z ∈ X.dom ∧ D.Δ (cpt X x0 z) ≠ 0 from ⟨hzd, hΔ⟩), hzo, hbo]
    simp [bchar]
  unfold Gf
  have hp : X.pnorm la (P0 D la F) (cpt X x0 z) =
      ‖P0 D la F (cpt X x0 z)‖ * X.nfac la (cpt X x0 z) := rfl
  rw [hp, hP]
  congr 1
  unfold phla
  have hl : -(-2 * Real.log (X.nfac la (cpt X x0 z))) = Real.log (X.nfac la (cpt X x0 z) ^ 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hl, Real.exp_log (pow_pos hpos 2), mul_pow]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
