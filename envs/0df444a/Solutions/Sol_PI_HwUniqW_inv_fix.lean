-- Prove2me | solution 1 for PI.HwUniqW.inv_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:41:30.458193+00:00
-- url     : https://prove2.me/submissions/40818014-7ac9-4871-9dd4-5f373b125a88

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
private lemma Hpk_mul_self_eq_one : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  obtain ⟨p, hp⟩ : ∃ p : Fin (2 * r + k + 1),
      (p : ℕ) = if (i : ℕ) < r ∨ r + k < (i : ℕ) then 2 * r + k - i else i :=
    ⟨⟨if (i : ℕ) < r ∨ r + k < (i : ℕ) then 2 * r + k - i else i, by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single p]
  · unfold Hpk
    simp only [Fin.ext_iff]
    split_ifs at hp ⊢ <;> first | omega | (norm_num; done) | (simp; done)
  · intro l _ hl
    rw [Ne, Fin.ext_iff] at hl
    unfold Hpk
    simp only [Fin.ext_iff]
    split_ifs at hp ⊢ <;> first | omega | (simp; done) | (norm_num; done)
  · intro h
    exact absurd (Finset.mem_univ p) h
private lemma Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
  have h : aᴴ * Hpk k r * a = Hpk k r := hU
  calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hpk_mul_self_eq_one]
private lemma isUnit_det_of_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) : IsUnit a.det :=
  Matrix.isUnit_det_of_left_inverse (Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_UH hU)
end PI.HwUniqW
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) : a⁻¹ *ᵥ v = v := by
  calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a (isUnit_det_of_mem_UH hU), Matrix.one_mulVec]
end PI.HwUniqW
