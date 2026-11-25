-- Prove2me | solution 1 for PositivityTheory.CW.functional_calculus_of_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:40.733208+00:00
-- url     : https://prove2.me/submissions/b0c11421-8282-47b2-9891-0576a13aa677

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_fc_basis
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_repr_fc
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_inner_eq_sum
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_fc_id
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_re_inner_fc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open FunctionalCalculusInner
namespace PositivityTheory.CW
theorem _root_.solution : A0 → FunctionalCalculusLaws := by
  intro _ n ε V _ _ E _ ι b μ hb
  have hid := fc_id ε E b μ hb.eig
  refine ⟨fun φ ν v hv => ?_, fun φ x y => ?_, fun φ ψ hφψ w => ?_, fun φ ψ => ?_, fun φ ψ => ?_,
    fun c => ?_, hid⟩
  · refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h1 : b.repr (casimirK ε E v) i = b.repr ((ν : ℂ) • v) i := by rw [show casimirK ε E v = (ν : ℂ) • v from hv]
    rw [← hid, repr_fc] at h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    rw [repr_fc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases h0 : b.repr v i = 0
    · simp [h0]
    · have : μ i = ν := by
        have := mul_right_cancel₀ h0 h1
        exact_mod_cast this
      rw [this]
  · have hs : (b.repr (fc b μ φ x)).support ⊆ (b.repr x).support := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi ⊢
      rw [repr_fc] at hi
      exact right_ne_zero_of_mul hi
    rw [inner_eq_sum b hb.on _ _ _ hs, inner_eq_sum b hb.on _ _ _ subset_rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_fc, repr_fc, map_mul, Complex.conj_ofReal]
    ring
  · rw [re_inner_fc b hb.on, re_inner_fc b hb.on]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hφψ _ (hb.nonneg i)) (sq_nonneg _)
  · refine b.ext fun i => ?_
    simp only [fc_basis, LinearMap.add_apply, Complex.ofReal_add, add_smul]
  · refine b.ext fun i => ?_
    simp only [fc_basis, Module.End.mul_apply, map_smul, smul_smul, Complex.ofReal_mul, mul_comm]
  · refine b.ext fun i => ?_
    simp [fc_basis]
end PositivityTheory.CW
