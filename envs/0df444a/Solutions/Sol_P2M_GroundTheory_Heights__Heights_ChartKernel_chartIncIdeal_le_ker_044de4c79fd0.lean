-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_chartIncIdeal_le_ker_044de4c79fd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:10.277799+00:00
-- url     : https://prove2.me/submissions/0985117e-3b5e-43a7-9ec2-4d35e3a73921

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inl_3d0d3333bcc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartX_eq_zero_bb52bd00c10d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution : chartIncIdeal I t e ≤ RingHom.ker (chartSubst I t e) := by
  have h1 : ∑ m, chartX I t e (C (t m)) * chartX I t e (X m) = 1 := by
    have := chartX_eq_zero I t e (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (linForm t - 1)))
    rw [map_sub, map_one, sub_eq_zero] at this
    simpa [linForm, map_sum] using this
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    rw [chartSubst_inl, chartX_eq_zero I t e hg, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hC : ∑ l, C (chartX I t e (C (t l))) * C (chartX I t e (X l)) =
        (1 : MvPolynomial (Fin e × Fin n) (ChartInc I t e)) := by
      rw [← C_1, ← h1, map_sum]
      simp only [C_mul]
    simp only [chartSubst, map_sum, map_mul, eval₂Hom_X', Sum.elim_inr, Sum.elim_inl]
    simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one, sub_self]
end GroundTheory.Heights₂.Heights.ChartKernel
