-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:33:14.470086+00:00
-- url     : https://prove2.me/submissions/ec702f2d-99fd-473d-99e3-ed4ad6cca469

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_fund
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_bdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_ne_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_per_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_continuous_pointNormSq_quotient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointwiseNormSq_add_period


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution : StepPos := by
  intro E _ _ X q n F hF hF0
  have hc : Continuous (X.ptN2 q F) := continuous_pointNormSq_quotient X q hF.1.continuous
  have hnn : ∀ v, 0 ≤ X.ptN2 q F v := by
    intro v
    unfold PT.ptN2
    positivity
  have hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, X.ptN2 q F (v + γ) = X.ptN2 q F v :=
    fun γ hγ v => pointwiseNormSq_add_period X hF hγ v
  set U : Set (Fin n → Vsp X.dim) := {v | 0 < X.ptN2 q F v} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const hc
  have hUne : U.Nonempty := by
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hF0
    refine ⟨v, ?_⟩
    show 0 < X.ptN2 q F v
    unfold PT.ptN2
    exact mul_pos (pow_pos (norm_pos_iff.mpr hv) 2) (Real.exp_pos _)
  have hUpos : 0 < volume U := hUopen.measure_pos volume hUne
  have hUfd : 0 < volume (U ∩ X.fd n) := by
    open Pointwise in (
      have hinv : ∀ g : (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup, g +ᵥ U = U := by
        intro g
        ext v
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        show 0 < X.ptN2 q F (-g +ᵥ v) ↔ 0 < X.ptN2 q F v
        rw [per_span X n (X.ptN2 q F) hper (-g) v]
      have hfd := (fd_fund X n).measure_eq_tsum U
      simp only [hinv, tsum_const] at hfd
      rw [pos_iff_ne_zero]
      intro h0
      rw [h0] at hfd
      simp at hfd
      exact hUpos.ne' hfd)
  have hint : IntegrableOn (X.ptN2 q F) (X.fd n) volume :=
    (hc.continuousOn.integrableOn_compact (fd_bdd X n).isCompact_closure).mono_set subset_closure
  have hpos : 0 < ∫ v in X.fd n, X.ptN2 q F v := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint]
    refine lt_of_lt_of_le hUfd (measure_mono (Set.inter_subset_inter_left _ ?_))
    intro v hv
    exact ne_of_gt hv
  rw [PT.l2, setAverage_eq, smul_eq_mul]
  refine mul_pos (inv_pos.mpr ?_) hpos
  first
    | (rw [measureReal_def]; exact ENNReal.toReal_pos (fd_ne_zero X n) (fd_ne_top X n))
    | exact ENNReal.toReal_pos (fd_ne_zero X n) (fd_ne_top X n)
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
