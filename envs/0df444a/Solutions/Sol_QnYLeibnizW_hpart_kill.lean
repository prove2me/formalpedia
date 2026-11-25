-- Prove2me | solution 1 for QnYLeibnizW.hpart_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:21.248882+00:00
-- url     : https://prove2.me/submissions/f5e15001-37d5-409e-ab2f-3e32600543ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
import Theorems.Thm_QnYLeibnizW_single_mulVec_bvec
import Theorems.Thm_QnYLeibnizW_single_conjTranspose
import Theorems.Thm_QnYLeibnizW_posL_val
import Theorems.Thm_QnYLeibnizW_out_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)}
namespace QnYLeibnizW
theorem _root_.solution (a b : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : q.val < i.val ∨ 2 * r + k < q.val + i.val) :
    hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec q = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) *ᵥ bvec q = 0 := by
  obtain ⟨hqa, _⟩ := out_ne a q hq
  obtain ⟨hqb, _⟩ := out_ne b q hq
  have h1 : Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) *ᵥ bvec q = 0 := by
    rw [single_mulVec_bvec, if_neg hqb]
  have hw : (Hpk k r *ᵥ bvec q) (posL k r i a) = 0 := by
    have ha := a.isLt
    have hi := i.isLt
    unfold mdim at ha
    have hv := posL_val (k := k) (r := r) (i := i) a
    have he : (Hpk k r *ᵥ bvec q) (posL k r i a) = Hpk k r (posL k r i a) q := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [he]
    unfold Hpk
    try beta_reduce
    split_ifs <;> first | rfl | (exfalso; omega) | (exfalso; rw [Fin.ext_iff] at *; omega)
  have h2 : (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ *ᵥ (Hpk k r *ᵥ bvec q) = 0 := by
    rw [single_conjTranspose]
    generalize Hpk k r *ᵥ bvec q = w at hw ⊢
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with hl
    · rw [← hl.2, hw, mul_zero]
    · rw [zero_mul]
  constructor
  · unfold hpart1
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero,
      h1, sub_zero, smul_zero]
  · unfold hpart2
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero,
      h1, add_zero, smul_zero]
end QnYLeibnizW
