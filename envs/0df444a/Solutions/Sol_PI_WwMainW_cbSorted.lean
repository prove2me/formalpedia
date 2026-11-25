-- Prove2me | solution 1 for PI.WwMainW.cbSorted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:15.586833+00:00
-- url     : https://prove2.me/submissions/b3a73911-9a8f-4887-b9a9-b13bba37e973

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_SumInjEqSumPairs
import Theorems.Thm_PI_WwMainW_sum_inj_eq_sum_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
noncomputable section
open PI PI.WwMainW
namespace PI.WwMainW
theorem _root_.solution : CBSorted := by
  unfold CBSorted
  intro R _ p n A B
  classical
  have step1 : (A * B).det = ∑ f : Fin p → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    simp only [Matrix.det_apply', Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
      Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  have step2 : ∑ f : Fin p → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det =
      ∑ x : (Fin p ↪o Fin n) × Perm (Fin p),
        (∏ i, B ((⇑x.1 ∘ ⇑x.2) i) i) * (A.submatrix id (⇑x.1 ∘ ⇑x.2)).det := by
    rw [sum_inj_eq_sum_pairs (fun f : Fin p → Fin n => (∏ i, B (f i) i) * (A.submatrix id f).det),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · rfl
    · have hf' : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        apply hf
        intro i j hij
        by_contra hne
        exact hc ⟨i, j, hij, hne⟩
      obtain ⟨i, j, hij, hne⟩ := hf'
      rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij]), mul_zero]
  rw [step1, step2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hsub : ∀ τ : Perm (Fin p),
      (A.submatrix id (⇑J ∘ ⇑τ)).det = Perm.sign τ * (A.submatrix id J).det := by
    intro τ
    have hm : A.submatrix id (⇑J ∘ ⇑τ) = (A.submatrix id J).submatrix id τ := by
      rw [Matrix.submatrix_submatrix]; rfl
    rw [hm, Matrix.det_permute']
  simp only [hsub]
  rw [Matrix.det_apply' (B.submatrix J id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Function.comp_apply]
  ring
end PI.WwMainW
