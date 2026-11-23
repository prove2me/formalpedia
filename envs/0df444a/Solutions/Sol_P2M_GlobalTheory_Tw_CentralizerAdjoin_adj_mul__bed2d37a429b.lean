-- Prove2me | solution 1 for P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_mul__bed2d37a429b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:06.507207+00:00
-- url     : https://prove2.me/submissions/a80cd460-6e84-40a0-b824-182078077830

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_Model_transpose_mul_Phi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (g * h) = adj δ h * adj δ g := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  simp only [adj, conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd, ← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R),
    transpose_mul_Phi, Matrix.one_mul]
end GlobalTheory.Tw.CentralizerAdjoin
