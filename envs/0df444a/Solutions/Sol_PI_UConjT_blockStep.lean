-- Prove2me | solution 1 for PI.UConjT.blockStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:22.818426+00:00
-- url     : https://prove2.me/submissions/7adb326d-ad01-4ae1-b74b-fc75e0fba393

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup
import Theorems.Thm_PI_UConjT_star_eq_self_of_im_eq_zero
import Theorems.Thm_PI_UConjT_eq_blk_of_last
import Theorems.Thm_PI_UConjT_submatrix_mem_unitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix
namespace PI.UConjT
theorem _root_.solution : BlockStep := by
  intro hS n g hg
  obtain ⟨u, hu, d, hgu, hreal⟩ := hS n g hg
  have hu1 : u * uᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hu
  have hu2 : uᴴ * u = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hu
  have hgeq : g = u * diagonal d * uᴴ := by
    rw [← hgu, Matrix.mul_assoc, hu1, Matrix.mul_one]
  set k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (uᴴ)ᵀ * uᴴ with hkdef
  have hkH : kᴴ = u * uᵀ := by
    rw [hkdef, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
    ext i j
    simp [conjTranspose_apply]
  have hkk : k * kᴴ = 1 := by
    rw [hkH, hkdef, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hu2, Matrix.one_mul,
      ← transpose_mul, hu1, transpose_one]
  have hkU : k ∈ unitaryGroup (Fin (n + 1)) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; exact hkk
  have hconj : k * g * kᴴ = gᵀ := by
    rw [hkH, hgeq, hkdef, transpose_mul, transpose_mul, diagonal_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc uᴴ u, hu2, Matrix.one_mul, ← Matrix.mul_assoc uᴴ u, hu2,
      Matrix.one_mul]

  have hkent : ∀ i j, k i j = ∑ l, star (u i l) * star (u j l) := by
    intro i j; simp [hkdef, mul_apply, conjTranspose_apply]
  have hu1e : ∀ i j, ∑ l, u i l * star (u j l) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hu1 i) j
    simpa [mul_apply, conjTranspose_apply, one_apply] using this
  have hcol : ∀ i, k i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
    intro i
    rw [hkent]
    have : ∑ l, star (u i l) * star (u (Fin.last n) l) = star (∑ l, u i l * star (u (Fin.last n) l)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_mul', star_star, star_eq_self_of_im_eq_zero (hreal l)]
    rw [this, hu1e]
    split_ifs <;> simp
  have hrow : ∀ j, k (Fin.last n) j = if Fin.last n = j then 1 else 0 := by
    intro j
    rw [hkent, ← hu1e]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_eq_self_of_im_eq_zero (hreal l)]
  have hcol' : ∀ i : Fin n, k (Fin.castSucc i) (Fin.last n) = 0 := by
    intro i; rw [hcol]; simp [Fin.castSucc_ne_last]
  have hrow' : ∀ j : Fin n, k (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j; rw [hrow]; simp [(Fin.castSucc_ne_last j).symm]
  have hll : k (Fin.last n) (Fin.last n) = 1 := by rw [hcol]; simp
  refine ⟨k.submatrix Fin.castSucc Fin.castSucc, submatrix_mem_unitaryGroup k hkU hcol', ?_⟩
  rw [eq_blk_of_last k hcol' hrow' hll]
  exact hconj
end PI.UConjT
