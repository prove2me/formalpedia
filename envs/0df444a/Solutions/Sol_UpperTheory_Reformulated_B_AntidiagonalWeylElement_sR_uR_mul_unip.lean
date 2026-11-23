-- Prove2me | solution 1 for UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR_uR_mul_unip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:01.918929+00:00
-- url     : https://prove2.me/submissions/c342017f-5e30-4cbf-ae20-fe1b7191c214

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryRootEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
private theorem mul_J {L : Type} [Field L] {n : ℕ} {p : Type} (M : Matrix p (Fin n) L) (i : p) (j : Fin n) :
    (M * antiJ L n) i j = M i (Fin.rev j) := by
  simp [Matrix.mul_apply, antiJ_apply']
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
private theorem up_mul {n : ℕ} {L : Type} [Field L] {M N : Matrix (Fin n) (Fin n) L}
    (hM : Up M) (hN : Up N) : Up (M * N) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k i with hk | hk
    · rw [hM.1 i k hk, zero_mul]
    · rw [hN.1 k j (lt_of_lt_of_le hij hk), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.2, hN.2, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM.1 i k h, zero_mul]
      · rw [hN.1 k i h, mul_zero]
    · simp
private theorem pm_cases {n : ℕ} (A A1 B B1 k : Fin n) :
    ((k : ℕ) = A ∧ (pm A A1 B B1 k : ℕ) = A1) ∨ ((k : ℕ) = A1 ∧ (pm A A1 B B1 k : ℕ) = A) ∨
      ((k : ℕ) = B ∧ (pm A A1 B B1 k : ℕ) = B1) ∨ ((k : ℕ) = B1 ∧ (pm A A1 B B1 k : ℕ) = B) ∨
      ((k : ℕ) ≠ A ∧ (k : ℕ) ≠ A1 ∧ (k : ℕ) ≠ B ∧ (k : ℕ) ≠ B1 ∧ (pm A A1 B B1 k : ℕ) = k) := by
  unfold pm
  by_cases h1 : k = A
  · simp [h1]
  by_cases h2 : k = A1
  · subst h2
    simp [h1]
  by_cases h3 : k = B
  · subst h3
    simp [h1, h2, Fin.ext_iff]
  by_cases h4 : k = B1
  · subst h4
    simp [h1, h2, h3, Fin.ext_iff]
  · simp [h1, h2, h3, h4, Fin.ext_iff]
    omega
private theorem pm_invol {n : ℕ} {A A1 B B1 : Fin n} (hA : (A : ℕ) + 1 = A1) (hB : (B : ℕ) + 1 = B1)
    (hAB : (A1 : ℕ) < B) (k : Fin n) : pm A A1 B B1 (pm A A1 B B1 k) = k := by
  have c1 := pm_cases A A1 B B1 k
  have c2 := pm_cases A A1 B B1 (pm A A1 B B1 k)
  rw [Fin.ext_iff]
  omega
private theorem pm_lt {n : ℕ} {A A1 B B1 : Fin n} (hA : (A : ℕ) + 1 = A1) (hB : (B : ℕ) + 1 = B1)
    (hAB : (A1 : ℕ) < B) {i j : Fin n} (hij : j < i) :
    pm A A1 B B1 j < pm A A1 B B1 i ∨ (pm A A1 B B1 i = A ∧ pm A A1 B B1 j = A1) ∨
      (pm A A1 B B1 i = B ∧ pm A A1 B B1 j = B1) := by
  have c1 := pm_cases A A1 B B1 i
  have c2 := pm_cases A A1 B B1 j
  simp only [Fin.lt_def, Fin.ext_iff] at hij ⊢
  omega
private theorem S_abs {n : ℕ} {L : Type} [Field L] {A A1 B B1 : Fin n} (hA : (A : ℕ) + 1 = A1)
    (hB : (B : ℕ) + 1 = B1) (hAB : (A1 : ℕ) < B) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) L) i j +
      ((if i = A then (1 : L) else 0) * (-1) * (if j = A then 1 else 0) +
        (if i = A then (1 : L) else 0) * 1 * (if j = A1 then 1 else 0) +
        ((if i = A1 then (1 : L) else 0) * 1 * (if j = A then 1 else 0) +
          (if i = A1 then (1 : L) else 0) * (-1) * (if j = A1 then 1 else 0))) +
      ((if i = B then (1 : L) else 0) * (-1) * (if j = B then 1 else 0) +
        (if i = B then (1 : L) else 0) * 1 * (if j = B1 then 1 else 0) +
        ((if i = B1 then (1 : L) else 0) * 1 * (if j = B then 1 else 0) +
          (if i = B1 then (1 : L) else 0) * (-1) * (if j = B1 then 1 else 0))) =
      if pm A A1 B B1 i = j then 1 else 0 := by
  have d1 : A ≠ A1 := by simp only [ne_eq, Fin.ext_iff]; omega
  have d2 : A ≠ B := by simp only [ne_eq, Fin.ext_iff]; omega
  have d3 : A ≠ B1 := by simp only [ne_eq, Fin.ext_iff]; omega
  have d4 : A1 ≠ B := by simp only [ne_eq, Fin.ext_iff]; omega
  have d5 : A1 ≠ B1 := by simp only [ne_eq, Fin.ext_iff]; omega
  have d6 : B ≠ B1 := by simp only [ne_eq, Fin.ext_iff]; omega
  have e1 := d1.symm
  have e2 := d2.symm
  have e3 := d3.symm
  have e4 := d4.symm
  have e5 := d5.symm
  have e6 := d6.symm
  clear hA hB hAB
  have cases' : ∀ k : Fin n, k = A ∨ k = A1 ∨ k = B ∨ k = B1 ∨
      (k ≠ A ∧ A ≠ k ∧ k ≠ A1 ∧ A1 ≠ k ∧ k ≠ B ∧ B ≠ k ∧ k ≠ B1 ∧ B1 ≠ k) := by
    intro k
    by_cases h1 : k = A
    · exact Or.inl h1
    by_cases h2 : k = A1
    · exact Or.inr (Or.inl h2)
    by_cases h3 : k = B
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : k = B1
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h1, Ne.symm h1, h2, Ne.symm h2, h3, Ne.symm h3, h4, Ne.symm h4⟩)))
  rcases cases' i with rfl | rfl | rfl | rfl | ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ <;>
    rcases cases' j with rfl | rfl | rfl | rfl | ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ <;>
    clear cases' <;>
    simp [pm, Matrix.one_apply, *]
private theorem conj_apply {n : ℕ} {L : Type} [Field L] (c : Fin 2 → Fin n)
    (Z : Matrix (Fin 2) (Fin 2) L) (i j : Fin n) :
    (cM L c * Z * (cM L c).transpose) i j =
      ∑ p, ∑ q, (if i = c p then (1 : L) else 0) * Z p q * (if j = c q then 1 else 0) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cM, Finset.sum_mul]
  exact Finset.sum_comm
private theorem block_apply {L : Type} [Field L] {n a : ℕ} (h : 2 * (a + 2) ≤ n)
    (X Y : Matrix (Fin 2) (Fin 2) L) (i j : Fin n) :
    blockM a h X Y i j = (1 : Matrix (Fin n) (Fin n) L) i j +
      (∑ p, ∑ q, (if i = cI n a h p then (1 : L) else 0) * (X - 1) p q * (if j = cI n a h q then 1 else 0)) +
      (∑ p, ∑ q, (if i = cJ n a h p then (1 : L) else 0) * (Y - 1) p q * (if j = cJ n a h q then 1 else 0)) := by
  simp only [blockM, Matrix.add_apply, conj_apply]
private theorem vals {n a : ℕ} (h : 2 * (a + 2) ≤ n) :
    (cI n a h 0 : ℕ) + 1 = cI n a h 1 ∧ (cJ n a h 0 : ℕ) + 1 = cJ n a h 1 ∧
      (cI n a h 1 : ℕ) < cJ n a h 0 ∧ (cI n a h 1 : ℕ) + cJ n a h 0 + 1 = n ∧
      (cI n a h 0 : ℕ) + cJ n a h 1 + 1 = n := by
  have c0 : (cI n a h 0 : ℕ) = a := rfl
  have c1 : (cI n a h 1 : ℕ) = a + 1 := rfl
  have d0 : (cJ n a h 0 : ℕ) = n - 2 - a := rfl
  have d1 : (cJ n a h 1 : ℕ) = n - 2 - a + 1 := rfl
  omega
private theorem partner_wU {L : Type} [Field L] (σ : L →+* L) : partner σ (wU L) = w2 L := by
  have e : (((wU L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = w2 L := rfl
  simp only [partner]
  rw [e, conj_transpose_antidiag_fixed, weyl_mul_weyl, Matrix.one_mul]
private theorem partner_nU {L : Type} [Field L] (σ : L →+* L) (z : L) :
    partner σ (nU z) = !![1, -σ z; 0, 1] := by
  have e : (((nU z)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -z; 0, 1] := rfl
  have e2 : cT σ !![(1 : L), -z; 0, 1] = !![1, 0; -σ z, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cT]
  simp only [partner]
  rw [e, e2]
  simp [w2, Matrix.mul_fin_two]
private theorem S_apply {L : Type} [Field L] {n a : ℕ} (σ : L →+* L)
    (hσ : ∀ x : L, σ (σ x) = x) (h : 2 * (a + 2) ≤ n) (i j : Fin n) :
    (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      if pm (cI n a h 0) (cI n a h 1) (cJ n a h 0) (cJ n a h 1) i = j then 1 else 0 := by
  have e : (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (w2 L) (partner σ (wU L)) := rfl
  obtain ⟨v1, v2, v3, -, -⟩ := vals h
  have z00 : (w2 L - 1) 0 0 = -1 := by simp [w2]
  have z01 : (w2 L - 1) 0 1 = 1 := by simp [w2]
  have z10 : (w2 L - 1) 1 0 = 1 := by simp [w2]
  have z11 : (w2 L - 1) 1 1 = -1 := by simp [w2]
  rw [e, partner_wU, block_apply]
  simp only [Fin.sum_univ_two, z00, z01, z10, z11]
  exact S_abs v1 v2 v3 i j
private theorem U_apply {L : Type} [Field L] {n a : ℕ} (σ : L →+* L)
    (hσ : ∀ x : L, σ (σ x) = x) (h : 2 * (a + 2) ≤ n) (z : L) (i j : Fin n) :
    (((uR σ hσ a h z : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      (1 : Matrix (Fin n) (Fin n) L) i j + (if i = cI n a h 0 ∧ j = cI n a h 1 then z else 0) +
        (if i = cJ n a h 0 ∧ j = cJ n a h 1 then -σ z else 0) := by
  have e : (((uR σ hσ a h z : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h !![1, z; 0, 1] (partner σ (nU z)) := rfl
  have x00 : (!![(1 : L), z; 0, 1] - 1) 0 0 = 0 := by simp
  have x01 : (!![(1 : L), z; 0, 1] - 1) 0 1 = z := by simp
  have x10 : (!![(1 : L), z; 0, 1] - 1) 1 0 = 0 := by simp
  have x11 : (!![(1 : L), z; 0, 1] - 1) 1 1 = 0 := by simp
  have y00 : (!![(1 : L), -σ z; 0, 1] - 1) 0 0 = 0 := by simp
  have y01 : (!![(1 : L), -σ z; 0, 1] - 1) 0 1 = -σ z := by simp
  have y10 : (!![(1 : L), -σ z; 0, 1] - 1) 1 0 = 0 := by simp
  have y11 : (!![(1 : L), -σ z; 0, 1] - 1) 1 1 = 0 := by simp
  have k : ∀ (P Q : Prop) [Decidable P] [Decidable Q] (t : L),
      (if P then (1 : L) else 0) * t * (if Q then 1 else 0) = if P ∧ Q then t else 0 := by
    intro P Q _ _ t
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  rw [e, partner_nU, block_apply]
  simp only [Fin.sum_univ_two, x00, x01, x10, x11, y00, y01, y10, y11, mul_zero, zero_mul, add_zero, zero_add]
  rw [k, k]
private theorem up_U {n : ℕ} {L : Type} [Field L] {A A1 B B1 : Fin n} (hA : (A : ℕ) + 1 = A1)
    (hB : (B : ℕ) + 1 = B1) {x t : L} {U : Matrix (Fin n) (Fin n) L}
    (hU : ∀ i j, U i j = (1 : Matrix (Fin n) (Fin n) L) i j + (if i = A ∧ j = A1 then x else 0) +
      (if i = B ∧ j = B1 then t else 0)) : Up U := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have n0 : i ≠ j := ne_of_gt hij
    have n1 : ¬ (i = A ∧ j = A1) := by
      rintro ⟨rfl, rfl⟩
      simp only [Fin.lt_def] at hij
      omega
    have n2 : ¬ (i = B ∧ j = B1) := by
      rintro ⟨rfl, rfl⟩
      simp only [Fin.lt_def] at hij
      omega
    rw [hU, Matrix.one_apply_ne n0, if_neg n1, if_neg n2]
    simp
  · have n1 : ¬ (i = A ∧ i = A1) := by
      rintro ⟨rfl, e⟩
      rw [← e] at hA
      omega
    have n2 : ¬ (i = B ∧ i = B1) := by
      rintro ⟨rfl, e⟩
      rw [← e] at hB
      omega
    rw [hU, Matrix.one_apply_eq, if_neg n1, if_neg n2]
    simp
private theorem row_U {n : ℕ} {L : Type} [Field L] {A A1 B B1 : Fin n} (hAB : A ≠ B)
    {x t : L} {U : Matrix (Fin n) (Fin n) L}
    (hU : ∀ i j, U i j = (1 : Matrix (Fin n) (Fin n) L) i j + (if i = A ∧ j = A1 then x else 0) +
      (if i = B ∧ j = B1 then t else 0)) (V : Matrix (Fin n) (Fin n) L) (l : Fin n) :
    (U * V) A l = V A l + x * V A1 l := by
  rw [Matrix.mul_apply]
  simp only [hU]
  simp [add_mul, Finset.sum_add_distrib, Matrix.one_apply, hAB]
private theorem col_U {n : ℕ} {L : Type} [Field L] {A A1 B B1 : Fin n} (hAB : A1 ≠ B1)
    {x t : L} {U : Matrix (Fin n) (Fin n) L}
    (hU : ∀ i j, U i j = (1 : Matrix (Fin n) (Fin n) L) i j + (if i = A ∧ j = A1 then x else 0) +
      (if i = B ∧ j = B1 then t else 0)) (M : Matrix (Fin n) (Fin n) L) (k : Fin n) :
    (M * U) k A1 = M k A1 + M k A * x := by
  rw [Matrix.mul_apply]
  simp only [hU]
  simp [mul_add, Finset.sum_add_distrib, Matrix.one_apply, hAB]
private theorem unit_entry {n : ℕ} {L : Type} [Field L] (σ : L →+* L) {A A1 B B1 : Fin n}
    (hA : (A : ℕ) + 1 = A1) (hB : (B : ℕ) + 1 = B1) (hAB : (A1 : ℕ) < B)
    (hs1 : (A1 : ℕ) + B + 1 = n) (hs2 : (A : ℕ) + B1 + 1 = n)
    {W : Matrix (Fin n) (Fin n) L} (hW : cT σ W * antiJ L n * W = antiJ L n) (hu : Up W) :
    σ (W A A1) + W B B1 = 0 := by
  have e := congrFun (congrFun hW A1) B1
  have r0 : antiJ L n A1 B1 = 0 := by
    show (if (A1 : ℕ) + B1 + 1 = n then (1 : L) else 0) = 0
    rw [if_neg]
    omega
  rw [r0, Matrix.mul_apply] at e
  simp only [mul_J] at e
  have ne : B ≠ B1 := by simp only [ne_eq, Fin.ext_iff]; omega
  have hz : ∀ l : Fin n, l ≠ B ∧ l ≠ B1 → cT σ W A1 (Fin.rev l) * W l B1 = 0 := by
    rintro l ⟨l1, l2⟩
    simp only [ne_eq, Fin.ext_iff] at l1 l2
    have := l.isLt
    by_cases c : (l : ℕ) < B
    · have : W (Fin.rev l) A1 = 0 := hu.1 _ _ (by
        rw [Fin.lt_def, Fin.val_rev]
        omega)
      show σ (W (Fin.rev l) A1) * W l B1 = 0
      rw [this, map_zero, zero_mul]
    · rw [hu.1 l B1 (by rw [Fin.lt_def]; omega), mul_zero]
  rw [Fintype.sum_eq_add B B1 ne hz] at e
  have rB : Fin.rev B = A1 := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  have rB1 : Fin.rev B1 = A := by
    rw [Fin.ext_iff, Fin.val_rev]
    omega
  rw [rB, rB1] at e
  have e' : σ (W A1 A1) * W B B1 + σ (W A A1) * W B1 B1 = 0 := e
  rw [hu.2 A1, hu.2 B1, map_one, one_mul, mul_one] at e'
  rw [add_comm]
  exact e'
private theorem conj_up {n : ℕ} {L : Type} [Field L] {A A1 B B1 : Fin n} (hA : (A : ℕ) + 1 = A1)
    (hB : (B : ℕ) + 1 = B1) (hAB : (A1 : ℕ) < B) {S W : Matrix (Fin n) (Fin n) L}
    (hS : ∀ i j, S i j = if pm A A1 B B1 i = j then 1 else 0) (hu : Up W)
    (w1 : W A A1 = 0) (w2' : W B B1 = 0) : Up (S * W * S) := by
  have key : ∀ i j, (S * W * S) i j = W (pm A A1 B B1 i) (pm A A1 B B1 j) := by
    intro i j
    have r1 : ∀ k, (S * W) i k = W (pm A A1 B B1 i) k := by
      intro k
      rw [Matrix.mul_apply]
      simp [hS]
    rw [Matrix.mul_apply]
    simp only [r1, hS]
    rw [Finset.sum_eq_single (pm A A1 B B1 j)]
    · rw [pm_invol hA hB hAB, if_pos rfl, mul_one]
    · intro k _ hk
      rw [if_neg, mul_zero]
      intro e
      apply hk
      rw [← e, pm_invol hA hB hAB]
    · simp
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    rcases pm_lt hA hB hAB hij with c | ⟨c1, c2⟩ | ⟨c1, c2⟩
    · exact hu.1 _ _ c
    · rw [c1, c2, w1]
    · rw [c1, c2, w2']
  · rw [key, hu.2]
private theorem unip_core {n : ℕ} {L : Type} [Field L] (σ : L →+* L) {A A1 B B1 : Fin n}
    (hA : (A : ℕ) + 1 = A1) (hB : (B : ℕ) + 1 = B1) (hAB : (A1 : ℕ) < B)
    (hs1 : (A1 : ℕ) + B + 1 = n) (hs2 : (A : ℕ) + B1 + 1 = n)
    {U1 U2 V S : Matrix (Fin n) (Fin n) L} {x z t1 t2 : L}
    (hU1 : ∀ i j, U1 i j = (1 : Matrix (Fin n) (Fin n) L) i j + (if i = A ∧ j = A1 then x else 0) +
      (if i = B ∧ j = B1 then t1 else 0))
    (hU2 : ∀ i j, U2 i j = (1 : Matrix (Fin n) (Fin n) L) i j + (if i = A ∧ j = A1 then z else 0) +
      (if i = B ∧ j = B1 then t2 else 0))
    (hV : Up V) (hz : V A A1 + x + z = 0)
    (hS : ∀ i j, S i j = if pm A A1 B B1 i = j then 1 else 0)
    (hW : cT σ (U1 * V * U2) * antiJ L n * (U1 * V * U2) = antiJ L n) :
    Up (S * (U1 * V * U2) * S) := by
  have dAB : A ≠ B := by simp only [ne_eq, Fin.ext_iff]; omega
  have dAB1 : A1 ≠ B1 := by simp only [ne_eq, Fin.ext_iff]; omega
  have wup : Up (U1 * V * U2) := up_mul (up_mul (up_U hA hB hU1) hV) (up_U hA hB hU2)
  have w1 : (U1 * V * U2) A A1 = 0 := by
    have ltA : A < A1 := by rw [Fin.lt_def]; omega
    rw [col_U dAB1 hU2, row_U dAB hU1, row_U dAB hU1, hV.2 A, hV.2 A1, hV.1 A1 A ltA]
    linear_combination hz
  have w2' : (U1 * V * U2) B B1 = 0 := by
    have := unit_entry σ hA hB hAB hs1 hs2 hW wup
    rwa [w1, map_zero, zero_add] at this
  exact conj_up hA hB hAB hS wup w1 w2'
private theorem sR_sq {L : Type} [Field L] {n a : ℕ} (σ : L →+* L)
    (hσ : ∀ x : L, σ (σ x) = x) (h : 2 * (a + 2) ≤ n) :
    sR σ hσ a h * sR σ hσ a h = 1 := by
  have e : wU L * wU L = 1 := Units.ext (weyl_mul_weyl L)
  show rootHom σ hσ a h (wU L) * rootHom σ hσ a h (wU L) = 1
  rw [← map_mul, e, map_one]
private theorem uR_neg {L : Type} [Field L] {n a : ℕ} (σ : L →+* L)
    (hσ : ∀ x : L, σ (σ x) = x) (h : 2 * (a + 2) ≤ n) (t : L) :
    uR σ hσ a h (-t) * uR σ hσ a h t = 1 := by
  have e : nU (-t) * nU t = 1 := by
    apply Units.ext
    show !![(1 : L), -t; 0, 1] * !![(1 : L), t; 0, 1] = 1
    exact neg_unipotent_mul t
  show rootHom σ hσ a h (nU (-t)) * rootHom σ hσ a h (nU t) = 1
  rw [← map_mul, e, map_one]
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
theorem _root_.solution :
    ∀ (L : Type) [inst : Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
      (hσ : ∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) (a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n)
      (v : ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)),
      UpperTheory.Reformulated.B.AntidiagonalWeylElement.IsUnipU v →
        ∃ (y : L),
          ∀ (x : L),
            ∃ (b : ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)),
              UpperTheory.Reformulated.B.AntidiagonalWeylElement.IsUnipU b ∧
                UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR σ hσ a h * UpperTheory.Reformulated.B.AntidiagonalWeylElement.uR σ hσ a h x * v =
                  b * (UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR σ hσ a h * UpperTheory.Reformulated.B.AntidiagonalWeylElement.uR σ hσ a h (x + y)) := by
  intro L _ _ σ n hσ a h v hv
  refine ⟨((v : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (cI n a h 0) (cI n a h 1), fun x => ?_⟩
  obtain ⟨v1, v2, v3, v4, v5⟩ := vals h
  generalize hy : ((v : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (cI n a h 0) (cI n a h 1) = y
  refine ⟨sR σ hσ a h * (uR σ hσ a h x * v * uR σ hσ a h (-(x + y))) * sR σ hσ a h, ?_, ?_⟩
  · have hw := (uR σ hσ a h x * v * uR σ hσ a h (-(x + y))).2
    exact unip_core σ v1 v2 v3 v4 v5 (U_apply σ hσ h x) (U_apply σ hσ h (-(x + y)))
      (V := ((v : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) hv (by rw [hy]; ring)
      (S_apply σ hσ h) hw
  · have hss := sR_sq σ hσ h
    have hnp := uR_neg σ hσ h (x + y)
    calc _ = sR σ hσ a h * uR σ hσ a h x * v * (uR σ hσ a h (-(x + y)) * uR σ hσ a h (x + y)) := by
          rw [hnp, mul_one]
      _ = sR σ hσ a h * (uR σ hσ a h x * v * uR σ hσ a h (-(x + y))) * 1 * uR σ hσ a h (x + y) := by
          simp only [mul_assoc, one_mul]
      _ = _ := by
          rw [← hss]
          simp only [mul_assoc]
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
