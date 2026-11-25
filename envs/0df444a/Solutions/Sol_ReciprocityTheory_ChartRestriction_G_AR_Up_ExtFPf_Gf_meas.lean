-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.Gf_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:48.037369+00:00
-- url     : https://prove2.me/submissions/8ce60594-689a-48cd-b671-3a52c91abebc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_cont_dmin
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
private lemma dom_isOpen : IsOpen X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => cont_dmin X τ i
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := by
    intro τ
    first
      | exact Continuous.matrix_det (continuous_apply τ)
      | (unfold mat; fun_prop)
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => ?_
  refine (isOpen_ne_fun (hdet τ) continuous_const).inter (isOpen_iInter_of_finite fun i => ?_)
  exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hd τ i)))
private lemma bor_diag_ne_zero {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ)
    (i : Fin r) : b τ i i ≠ 0 := by
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular (by intro a c hca; exact (hb τ).2 a c hca)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ _)
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
theorem _root_.solution (hF : DifferentiableOn ℂ F (OmF X x0)) : Measurable (Gf D la F) := by
  classical
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => cont_dmin X τ i
  have hcellO : IsOpen (cell D) := by
    have hc : cell D = X.dom ∩ {x | D.Δ x ≠ 0} := rfl
    rw [hc]
    exact dom_isOpen.inter (isOpen_ne_fun D.hΔ.continuous continuous_const)
  have hfc : ContinuousOn (fun x => bchar la (D.bOf x) * F (D.zOf x)) (cell D) := by
    have hzc : ContinuousOn D.zOf (cell D) := D.hz.continuousOn
    have hbc : ContinuousOn D.bOf (cell D) := D.hb.continuousOn
    have hsplit : ∀ x ∈ cell D, D.zOf x ∈ OmF X x0 ∧ D.bOf x ∈ Bor X.Ψ r :=
      fun x hx => ⟨(D.split x hx.1 hx.2).1, (D.split x hx.1 hx.2).2.1⟩
    refine ContinuousOn.mul ?_ (hF.continuousOn.comp hzc fun x hx => (hsplit x hx).1)
    unfold bchar
    apply continuousOn_finset_prod
    intro τ _
    apply continuousOn_finset_prod
    intro i _
    apply ContinuousOn.zpow₀
    · have hent : Continuous fun y : Frame X.Ψ r => y τ i i := by
        first
          | fun_prop
          | continuity
      exact hent.comp_continuousOn hbc
    · intro x hx
      left
      exact bor_diag_ne_zero (hsplit x hx).2 τ i
  have hP : P0 D la F = (cell D).piecewise (fun x => bchar la (D.bOf x) * F (D.zOf x)) 0 := by
    funext x
    by_cases h : x ∈ cell D
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact if_pos h
    · first
        | rw [Set.piecewise_eq_of_notMem _ _ _ h]
        | rw [Set.piecewise_eq_of_not_mem _ _ _ h]
      exact if_neg h
  have hPm : Measurable (P0 D la F) := by
    rw [hP]
    exact hfc.measurable_piecewise continuous_zero.continuousOn hcellO.measurableSet
  have hnf : Measurable fun x => X.nfac la x := by
    unfold Data.nfac
    apply Finset.measurable_prod
    intro τ _
    apply Finset.measurable_prod
    intro i _
    exact (((hd τ i.succ).measurable.div (hd τ i.castSucc).measurable).norm).pow_const _
  have hp : ∀ x, X.pnorm la (P0 D la F) x = ‖P0 D la F x‖ * X.nfac la x := fun x => rfl
  unfold Gf
  simp only [hp]
  first
    | exact ((hPm.norm.mul hnf).pow_const 2).ennreal_ofReal
    | exact ENNReal.measurable_ofReal.comp ((hPm.norm.mul hnf).pow_const 2)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
