-- Prove2me | solution 1 for PI.FrameInd.CountsW.blockA_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:45.084955+00:00
-- url     : https://prove2.me/submissions/9738c1c2-845e-4b77-82b3-e10d4973971d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
import Theorems.Thm_Formalism_QuantumDeterminants_ggBlockA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd
namespace PI.FrameInd.CountsW
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hz : inWb k r z)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (herm (gramM k r z z' γ) c c).re =
      (herm (Hpk k r) z z).re * Complex.normSq (c (Sum.inl (Fin.last r))) := by
  have hb : ∀ a b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = (herm (Hpk k r) z z • ggLastU r) a b :=
    fun a b => ggBlockA k r z hz a b
  simp only [herm, dotProduct, mulVec, Fintype.sum_sum_type, hc, star_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, hb, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last r) (fun a _ ha => by simp [ggLastU, ha]) (by simp)]
  rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [ggLastU, hb]) (by simp)]
  simp [ggLastU, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring
end PI.FrameInd.CountsW
