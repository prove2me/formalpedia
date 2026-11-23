-- Prove2me | solution 1 for P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_one__bd9885609913
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:31.525957+00:00
-- url     : https://prove2.me/submissions/47116420-a1b1-4303-9bd4-c363b6fd617c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_Model_Phi_mul_transpose


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
theorem _root_.solution {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ 1 = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  rw [adj, conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc δ, Phi_mul_transpose, Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hd]
end GlobalTheory.Tw.CentralizerAdjoin
