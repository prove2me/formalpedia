-- Prove2me | solution 1 for PI.HwUniqW.conj_UH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:53.757034+00:00
-- url     : https://prove2.me/submissions/f78cc95c-40d1-4784-9e2e-429fdc77e957

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
private lemma mul_mem_UH_highest_weight_uniqueness {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']
private lemma inv_mem_UH_highest_weight_uniqueness {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv a (isUnit_det_of_mem_UH ha), Matrix.conjTranspose_one, Matrix.one_mul,
          Matrix.mul_one]
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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) : g⁻¹ * x * g ∈ UH (Hpk k r) := by
  obtain ⟨hxU, -, -⟩ := hx
  obtain ⟨hgU, -, -⟩ := hg
  exact mul_mem_UH_highest_weight_uniqueness (mul_mem_UH_highest_weight_uniqueness (inv_mem_UH_highest_weight_uniqueness hgU) hxU) hgU
end PI.HwUniqW
