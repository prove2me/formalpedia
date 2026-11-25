-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.diffOn_param_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:08.112611+00:00
-- url     : https://prove2.me/submissions/95a7e515-4255-42f3-8fed-746d259219d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
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
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
section Param
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type} [Fintype ι]
private theorem norm_fderiv_le_of_differentiableOn_ball_of_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : F → ℂ} {x0 x : F} {ρ C : ℝ} (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (ball x0 ρ))
    (hC : ∀ z ∈ ball x0 ρ, ‖f z‖ ≤ C) (hx : x ∈ ball x0 (ρ / 2)) :
    ‖fderiv ℂ f x‖ ≤ C / (ρ / 2) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x0 (mem_ball_self hρ))
  have hx1 : ‖x - x0‖ < ρ / 2 := mem_ball_iff_norm.mp hx
  have hxd : DifferentiableAt ℂ f x :=
    hf.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set R := ρ / 2 / ‖v‖ with hRdef
  have hR : 0 < R := by positivity
  have hRv : R * ‖v‖ = ρ / 2 := div_mul_cancel₀ _ hvpos.ne'
  have hmem : ∀ w : ℂ, ‖w‖ ≤ R → x + w • v ∈ ball x0 ρ := by
    intro w hw
    rw [mem_ball_iff_norm]
    have h2 : ‖w • v‖ ≤ ρ / 2 := by
      rw [norm_smul, ← hRv]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg v)
    have h3 : x + w • v - x0 = (x - x0) + w • v := by abel
    rw [h3]
    calc _ ≤ ‖x - x0‖ + ‖w • v‖ := norm_add_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add_of_lt_of_le hx1 h2
      _ = ρ := by ring
  have hgd : DifferentiableOn ℂ (fun w : ℂ => f (x + w • v)) (closedBall 0 R) := by
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    have hfa : DifferentiableAt ℂ f (x + w • v) :=
      hf.differentiableAt (isOpen_ball.mem_nhds (hmem w hw'))
    exact (hfa.comp w ((differentiableAt_id.smul_const v).const_add x)).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun w : ℂ => f (x + w • v)) (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    exact hgd
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (le_of_eq (mem_sphere_zero_iff_norm.mp hz))))
  have hline : HasDerivAt (fun w : ℂ => x + w • v) ((1 : ℂ) • v) 0 :=
    ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hfd : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact hxd.hasFDerivAt
  have hg := hfd.comp_hasDerivAt (0 : ℂ) hline
  rw [one_smul] at hg
  have hder : deriv (fun w : ℂ => f (x + w • v)) 0 = fderiv ℂ f x v := hg.deriv
  rw [hder] at hcau
  calc ‖fderiv ℂ f x v‖ ≤ C / R := hcau
    _ = C / (ρ / 2) * ‖v‖ := by
      rw [hRdef]
      field_simp
end Param
section Frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
end Frame
end
end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
theorem _root_.solution {K : Set (ι → ℝ)} (hKv : volume K < ⊤)
    (A : (ι → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (ι → ℝ) → ℂ) (he : Continuous e) (he1 : ∀ t, ‖e t‖ ≤ 1)
    (hbd : ∀ x0 ∈ U, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ U ∧
      ∀ t, ∀ z ∈ closedBall x0 ρ, ‖G (A t z)‖ ≤ C) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  obtain ⟨ρ, hρ, C, hsub, hC⟩ := hbd x0 hx0
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hKv.ne
  have hballU : ball x0 ρ ⊆ U := ball_subset_closedBall.trans hsub
  have hslice : ∀ t, DifferentiableOn ℂ (fun z => G (A t z)) U := fun t =>
    hG.comp (A t).differentiable.differentiableOn (fun z hz => hAU t z hz)
  have hAx : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  have hcont : ∀ x ∈ U, Continuous fun t => G (A t x) * e t := fun x hx =>
    (hG.continuousOn.comp_continuous (hAx x) (fun t => hAU t x hx)).mul he
  have hfd : ∀ t, ∀ x ∈ U, HasFDerivAt (fun z => G (A t z) * e t)
      (e t • fderiv ℂ (fun z => G (A t z)) x) x := fun t x hx =>
    ((hslice t).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.mul_const (e t)
  have hF'eq : (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0) =
      fun t => e t • (fderiv ℂ G (A t x0)).comp (A t) := by
    funext t
    congr 1
    have hGd : DifferentiableAt ℂ G (A t x0) := hG.differentiableAt (hU.mem_nhds (hAU t x0 hx0))
    exact fderiv_comp x0 hGd (A t).differentiableAt |>.trans (by rw [(A t).fderiv])
  have hmeasF' : AEStronglyMeasurable (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0)
      (volume.restrict K) := by
    rw [hF'eq]
    refine he.aestronglyMeasurable.smul ?_
    letI : MeasurableSpace (F →L[ℂ] ℂ) := borel _
    haveI : BorelSpace (F →L[ℂ] ℂ) := ⟨rfl⟩
    have hm : Measurable (fderiv ℂ G) := measurable_fderiv ℂ G
    have h1 : AEStronglyMeasurable (fun t => fderiv ℂ G (A t x0)) (volume.restrict K) :=
      (hm.comp (hAx x0).measurable).aestronglyMeasurable
    exact (ContinuousLinearMap.compL ℂ F F ℂ).aestronglyMeasurable_comp₂ h1 hA.aestronglyMeasurable
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t) (F' := fun x t => e t • fderiv ℂ (fun z => G (A t z)) x)
    (bound := fun _ => C / (ρ / 2)) (x₀ := x0) (ball_mem_nhds x0 (half_pos hρ))
    (Filter.eventually_of_mem (hU.mem_nhds hx0) fun x hx => (hcont x hx).aestronglyMeasurable)
    ((integrable_const C).mono' (hcont x0 hx0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        calc ‖G (A t x0)‖ * ‖e t‖ ≤ C * 1 :=
              mul_le_mul (hC t x0 (mem_closedBall_self hρ.le)) (he1 t) (norm_nonneg _)
                ((norm_nonneg _).trans (hC t x0 (mem_closedBall_self hρ.le)))
          _ = C := mul_one C))
    hmeasF'
    (Filter.Eventually.of_forall fun t x hx => by
      rw [norm_smul]
      have hb := norm_fderiv_le_of_differentiableOn_ball_of_norm_le hρ ((hslice t).mono hballU)
        (fun z hz => hC t z (ball_subset_closedBall hz)) hx
      have hC0 : 0 ≤ C / (ρ / 2) := (norm_nonneg _).trans hb
      calc ‖e t‖ * ‖fderiv ℂ (fun z => G (A t z)) x‖ ≤ 1 * (C / (ρ / 2)) :=
            mul_le_mul (he1 t) hb (norm_nonneg _) zero_le_one
        _ = C / (ρ / 2) := one_mul _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun t x hx =>
      hfd t x (hballU (ball_subset_ball (by linarith) hx)))
  exact key.differentiableAt.differentiableWithinAt
end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
