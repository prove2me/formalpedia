-- Prove2me | solution 1 for PermPartialTranspose.CommonSolutions.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:27:16.023692+00:00
-- url     : https://prove2.me/submissions/8b3dfd39-91ac-4003-ae72-7c280c37230c

import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops
import Theorems.Thm_PermPartialTranspose_CommonSolutions_eq_70
import Theorems.Thm_PermPartialTranspose_CommonSolutions_eq_74
import Theorems.Thm_PermPartialTranspose_CommonSolutions_appendix_b_high_dim

open PermPartialTranspose.CommonSolutions

private lemma rcheck_neg_eq (a w : ℂ) :
    Rcheck 2 a w (-a) = a • pBar 2 + w • swapOp 2 := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Rcheck, pBar, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma entry_d2 (a b x y z : ℂ)
    (h : onFirst (Rcheck 2 a x b) * onLast (Rcheck 2 a z b) * onFirst (Rcheck 2 a y b) =
        onLast (Rcheck 2 a y b) * onFirst (Rcheck 2 a z b) * onLast (Rcheck 2 a x b)) :
    a ^ 2 * (x + y - z) + a * b * (x - z) - b ^ 2 * y = 0 ∧
    b * (a + b) * (a + b + y + z) = 0 ∧
    b * (a + b) * (x - y) = 0 := by
  have e1 := congrFun (congrFun h ((0 : Fin 2), (1 : Fin 2), (0 : Fin 2)))
    ((1 : Fin 2), (0 : Fin 2), (0 : Fin 2))
  have e2 := congrFun (congrFun h ((0 : Fin 2), (0 : Fin 2), (1 : Fin 2)))
    ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2))
  have e3 := congrFun (congrFun h ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)))
    ((1 : Fin 2), (0 : Fin 2), (1 : Fin 2))
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, onFirst, onLast, Rcheck,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, swapOp, pStar, partialTranspose2,
    smul_eq_mul, Prod.mk.injEq] at e1 e2 e3
  simp at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e1
  · linear_combination e2
  · linear_combination -e3

theorem solution (d : ℕ) (hd : 2 ≤ d) (a b : ℂ) (ha : a ≠ 0) :
    (∀ u : ℂ, u ≠ 0 →
      (BraidRel (Rcheck d a u b) ↔
        d = 2 ∧ (a = -b ∨ (a = b ∧ b = -u)))) ∧
    (b ≠ 0 → (AdditiveYBE d a b ↔ d = 2 ∧ a = -b)) ∧
    (MultiplicativeYBE d a b ↔ d = 2 ∧ a = -b) := by
  rcases eq_or_lt_of_le hd with rfl | hd3
  · refine ⟨?_, ?_, ?_⟩
    · intro u hu
      constructor
      · intro hB
        obtain ⟨h1, h2, -⟩ := entry_d2 a b u u u hB
        have h1' : (a + b) * (a - b) * u = 0 := by linear_combination h1
        rcases mul_eq_zero.mp h1' with hab | hu0
        · rcases mul_eq_zero.mp hab with hplus | hminus
          · exact ⟨rfl, Or.inl (by linear_combination hplus)⟩
          · have hab_eq : a = b := by linear_combination hminus
            subst hab_eq
            have h2' : 4 * a ^ 2 * (a + u) = 0 := by linear_combination h2
            rcases mul_eq_zero.mp h2' with ha0 | hau
            · exfalso
              rcases mul_eq_zero.mp ha0 with h4 | ha2
              · norm_num at h4
              · exact pow_ne_zero 2 ha ha2
            · exact ⟨rfl, Or.inr ⟨rfl, by linear_combination hau⟩⟩
        · exact absurd hu0 hu
      · rintro ⟨-, hab | ⟨rfl, rfl⟩⟩
        · have hb : b = -a := by linear_combination hab
          subst hb
          unfold BraidRel
          rw [rcheck_neg_eq]
          exact eq_74 a u u u
        · have hneg : Rcheck 2 (-u) u (-u) = Rcheck 2 (-u) (-(-u)) (-u) := by
            rw [neg_neg]
          rw [hneg]
          exact eq_70 (-u) ha
    · intro hb
      constructor
      · intro hA
        obtain ⟨-, -, h3⟩ := entry_d2 a b 1 0 (1 + 0) (hA 1 0)
        have h3' : b * (a + b) = 0 := by linear_combination h3
        rcases mul_eq_zero.mp h3' with hb0 | hab
        · exact absurd hb0 hb
        · exact ⟨rfl, by linear_combination hab⟩
      · rintro ⟨-, hab⟩ u v
        have hb' : b = -a := by linear_combination hab
        subst hb'
        rw [rcheck_neg_eq, rcheck_neg_eq, rcheck_neg_eq]
        exact eq_74 a u v (u + v)
    · constructor
      · intro hM
        obtain ⟨h1, -, -⟩ := entry_d2 a b 1 0 (1 * 0) (hM 1 0)
        have h1' : a * (a + b) = 0 := by linear_combination h1
        rcases mul_eq_zero.mp h1' with ha0 | hab
        · exact absurd ha0 ha
        · exact ⟨rfl, by linear_combination hab⟩
      · rintro ⟨-, hab⟩ x y
        have hb' : b = -a := by linear_combination hab
        subst hb'
        rw [rcheck_neg_eq, rcheck_neg_eq, rcheck_neg_eq]
        exact eq_74 a x y (x * y)
  · obtain ⟨hB, hM, hA⟩ := appendix_b_high_dim d hd3 a b ha
    have hd2 : d ≠ 2 := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      exact ⟨fun h => False.elim (hB u hu h), fun ⟨h, _⟩ => False.elim (hd2 h)⟩
    · intro hb
      exact ⟨fun h => False.elim (hA hb h), fun ⟨h, _⟩ => False.elim (hd2 h)⟩
    · exact ⟨fun h => False.elim (hM h), fun ⟨h, _⟩ => False.elim (hd2 h)⟩
