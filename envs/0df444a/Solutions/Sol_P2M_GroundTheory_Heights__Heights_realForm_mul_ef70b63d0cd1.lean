-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_realForm_mul_ef70b63d0cd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:08.381225+00:00
-- url     : https://prove2.me/submissions/47268a98-67a9-42de-a6e8-2509daddcc08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PComplexJacobian

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ) :
    realForm (A * B) = realForm A * realForm B := by
  ext ⟨i, a⟩ ⟨k, c⟩
  simp only [realForm, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.re_sum, Complex.im_sum]
  fin_cases a <;> fin_cases c <;>
    simp only [Complex.mul_re, Complex.mul_im, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    refine Finset.sum_congr rfl fun j _ => by ring
end GroundTheory.Heights₂.Heights
