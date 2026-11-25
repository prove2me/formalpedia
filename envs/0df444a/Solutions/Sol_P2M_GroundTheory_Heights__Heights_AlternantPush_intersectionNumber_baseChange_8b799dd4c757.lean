-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AlternantPush_intersectionNumber_baseChange_8b799dd4c757
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:56.636805+00:00
-- url     : https://prove2.me/submissions/c3b68017-8f42-459b-a989-a4561812fb83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_rename_mul_rename_356f52824e82

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace AlternantPush
theorem _root_.solution : AlternantPush.Statement := by
  intro r s
  refine ⟨1, Or.inl rfl, fun la hla => ?_⟩
  rw [KAlt.antisym_rename_mul_rename]
  split_ifs with h
  · rw [one_mul]
  · simp only [not_forall, not_le] at h
    obtain ⟨a, ha⟩ := h
    have hr : 0 < r := Fin.pos a
    set a0 : Fin r := ⟨r - 1, by omega⟩ with ha0
    have hle : la a0 ≤ la a := hla (show a ≤ a0 from by
      rw [Fin.le_def]; simp only [ha0]; have := a.isLt; omega)
    have hlt : la a0 < s := lt_of_le_of_lt hle ha
    set b0 : Fin s := ⟨s - 1 - la a0, by omega⟩ with hb0
    have hdet : alternant (Sum.elim (fun a : Fin r => la a + (r - 1 - (a : ℕ)))
        fun b : Fin s => s - 1 - (b : ℕ)) = 0 := by
      unfold alternant
      refine Matrix.det_zero_of_column_eq (i := Sum.inl a0) (j := Sum.inr b0) Sum.inl_ne_inr ?_
      intro k
      simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
      congr 1
      show la a0 + (r - 1 - (r - 1)) = s - 1 - (s - 1 - la a0)
      omega
    rw [hdet, smul_zero]
end AlternantPush
end GroundTheory.Heights₂.Heights
