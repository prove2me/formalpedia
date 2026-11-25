-- Prove2me | solution 1 for PI.NRL.exists_mul_eq_one_add_smul_of_rows_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:15.707798+00:00
-- url     : https://prove2.me/submissions/6c4f471d-a1ee-4264-b387-91d610a7a951

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormRepresentationLift_ExistsMulEqOneAddSmulOfRowsGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.NRL
open Matrix
variable {R : Type*} [CommRing R] {r : ℕ}
namespace PI.NRL
theorem _root_.solution (g : R) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R → Prop)
    (h1 : P 1) (hmul : ∀ M N, P M → P N → P (M * N))
    (hrow : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → R, ∃ w : Fin (r + 1) → R,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧ P (1 + rowMat a w)) :
    ∀ k : ℕ, k ≤ r → ∀ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R, UniUp ξ →
      (∀ d c : Fin (r + 1), k ≤ d.val → ξ d c = if d = c then 1 else 0) →
      ∃ M, P M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  intro k
  induction k with
  | zero =>
    intro _ ξ _ hid
    refine ⟨1, h1, 0, ?_⟩
    rw [Matrix.one_mul, smul_zero, add_zero]
    ext d c
    rw [hid d c (Nat.zero_le _), Matrix.one_apply]
  | succ k ih =>
    intro hk ξ hξ hid
    let a : Fin (r + 1) := ⟨k, by omega⟩
    have hak : a.val < r := by show k < r; omega
    obtain ⟨w, hw0, hw1, hP⟩ := hrow a hak (fun c => -ξ a c)
    choose! q hq using hw1
    let ξ₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
      fun d c => if d = a then (if d = c then 1 else 0) else ξ d c
    let Q₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
      fun d c => if d = a then (if a < c then q c else 0) else 0
    have hsum : ∀ c, ∑ e, w e * ξ e c = w c := by
      intro c
      have he' : ∀ e, w e * ξ e c = w e * (if e = c then 1 else 0) := by
        intro e
        by_cases he : e ≤ a
        · rw [hw0 e he, zero_mul, zero_mul]
        · rw [hid e c (Fin.lt_iff_val_lt_val.mp (not_le.mp he))]
      rw [Finset.sum_congr rfl (fun e _ => he' e)]
      simp
    have hE : (1 + rowMat a w) * ξ = ξ₀ + g • Q₁ := by
      ext d c
      have hrm : ∑ e, rowMat a w d e * ξ e c = if d = a then w c else 0 := by
        simp only [rowMat]
        split_ifs with hd
        · exact hsum c
        · simp
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, hrm]
      show ξ d c + (if d = a then w c else 0) =
        (if d = a then (if d = c then 1 else 0) else ξ d c) + g * (if d = a then (if a < c then q c else 0) else 0)
      by_cases hd : d = a
      · rw [hd, if_pos rfl, if_pos rfl, if_pos rfl]
        rcases lt_trichotomy c a with hca | hca | hca
        · rw [hξ.1 a c hca, hw0 c hca.le, if_neg (ne_of_lt hca).symm, if_neg (not_lt.mpr hca.le)]
          simp
        · rw [hca, hξ.2 a, hw0 a le_rfl, if_pos rfl, if_neg (lt_irrefl a)]
          simp
        · rw [hq c hca, if_neg (ne_of_lt hca), if_pos hca]
          ring
      · rw [if_neg hd, if_neg hd, if_neg hd]
        simp
    have hξ₀ : UniUp ξ₀ := by
      refine ⟨fun d c hcd => ?_, fun d => ?_⟩
      · show (if d = a then (if d = c then 1 else 0) else ξ d c) = 0
        by_cases h1' : d = a
        · rw [if_pos h1', if_neg (ne_of_lt hcd).symm]
        · rw [if_neg h1']
          exact hξ.1 d c hcd
      · show (if d = a then (if d = d then 1 else 0) else ξ d d) = 1
        by_cases h1' : d = a
        · rw [if_pos h1', if_pos rfl]
        · rw [if_neg h1']
          exact hξ.2 d
    have hid₀ : ∀ d c : Fin (r + 1), k ≤ d.val → ξ₀ d c = if d = c then 1 else 0 := by
      intro d c hdk
      show (if d = a then (if d = c then 1 else 0) else ξ d c) = _
      by_cases h1' : d = a
      · rw [if_pos h1']
      · rw [if_neg h1']
        apply hid d c
        have hne : d.val ≠ k := fun h' => h1' (Fin.ext h')
        omega
    obtain ⟨M, hM, Q, hMQ⟩ := ih (by omega) ξ₀ hξ₀ hid₀
    refine ⟨M * (1 + rowMat a w), hmul _ _ hM hP, Q + M * Q₁, ?_⟩
    rw [Matrix.mul_assoc, hE, Matrix.mul_add, hMQ, Matrix.mul_smul, smul_add, add_assoc]
end PI.NRL
