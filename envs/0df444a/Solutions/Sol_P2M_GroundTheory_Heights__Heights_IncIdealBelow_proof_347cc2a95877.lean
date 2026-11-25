-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncIdealBelow_proof_347cc2a95877
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:29.421567+00:00
-- url     : https://prove2.me/submissions/5c44305f-2e37-4bf1-8177-4b19161812c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncIdealBelow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
private theorem shiftGroup_injective {e n : ℕ} : Function.Injective (shiftGroup (e := e) (n := n)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shiftGroup, Prod.mk.injEq, Fin.succ_inj] at h
  rw [h.1, h.2]
private theorem aeval_killFirst_eq_zero {F : Type*} [Field F] {e n δ : ℕ} (hδ : 1 ≤ δ)
    {f : MvPolynomial (Fin (e + 1) × Fin n) F} (hf : IsMultiHomog δ f) :
    aeval (killFirst (F := F)) f = 0 := by
  classical
  rw [aeval_def, eval₂_eq]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := congrFun (hf (mem_support_iff.mp hd)) 0
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
  have hne : (∑ c ∈ d.support, (d c • groupWeight (e + 1) n c) 0) ≠ 0 := by rw [hw]; omega
  obtain ⟨ij, hij, hij0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h1 : ij.1 = 0 := by
    by_contra h
    apply hij0
    simp [groupWeight, Ne.symm h]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hij ?_)
  rw [killFirst, if_pos h1]
  exact zero_pow (Finsupp.mem_support_iff.mp hij)
end
end GroundTheory.Heights₂.Heights
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace IncIdealBelow
theorem _root_.solution (h₁ : ChowFormMultiHomog.Statement) : IncIdealBelow.Statement := by
  intro F _ n e I f hI hf
  classical
  obtain ⟨δ, hδ, hmh⟩ := h₁ F n (e + 1) I f hI hf
  rw [eq_bot_iff]
  intro g hg
  rw [Ideal.mem_bot]
  set g' : MvPolynomial (Fin (e + 1) × Fin n) F := rename shiftGroup g with hg'
  have hvan : ∀ v ∈ incidence I (e + 1), aeval v g' = 0 := by
    rintro v ⟨x, hx0, hxI, hxv⟩
    rw [hg', aeval_rename]
    exact (mem_incIdeal_iff.mp hg) (v ∘ shiftGroup) ⟨x, hx0, hxI, fun i => hxv i.succ⟩
  obtain ⟨h, hh⟩ := (hf.2 g').mp hvan
  have hfix : aeval (killFirst (F := F)) g' = g' := by
    rw [hg', aeval_rename]
    conv_rhs => rw [← aeval_X_left_apply (rename shiftGroup g), aeval_rename]
    congr 1
  have hzero : g' = 0 := by
    rw [← hfix, hh, map_mul, aeval_killFirst_eq_zero hδ hmh, zero_mul]
  exact rename_injective _ shiftGroup_injective (by rw [← hg', hzero, map_zero])
end IncIdealBelow
end GroundTheory.Heights₂.Heights
