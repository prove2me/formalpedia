-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.remarkC4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:34:43.681369+00:00
-- url     : https://prove2.me/submissions/ccc7cb26-1ac8-42b5-a8a7-4f29a925def8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

lemma g52a_word_append {d p n k : ℕ} (K : Fin p → Operator d) (w : Fin n → Fin p)
    (w' : Fin k → Fin p) :
    (List.ofFn fun i => K (w i)).prod * (List.ofFn fun i => K (w' i)).prod =
      (List.ofFn fun i => K (Fin.append w w' i)).prod := by
  have e : ∀ {m : ℕ} (u : Fin m → Fin p), (List.ofFn fun i => K (u i)) = (List.ofFn u).map K := by
    intro m u; rw [List.map_ofFn]; rfl
  rw [e, e, e, List.ofFn_fin_append, List.map_append, List.prod_append]

lemma g52a_word_norm {d p : ℕ} (K : Fin p → Operator d) (hK : QAlgorithms.IsKrausFamily K) :
    ∀ k : ℕ, ∑ w : Fin k → Fin p,
      ((List.ofFn fun i => K (w i)).prod)ᴴ * (List.ofFn fun i => K (w i)).prod = 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ : Fin (k+1) => Fin p).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.prod_cons, Matrix.conjTranspose_mul]
    rw [Finset.sum_comm]
    have : ∀ w : Fin k → Fin p, ∑ i : Fin p, ((List.ofFn fun j => K (w j)).prod)ᴴ * (K i)ᴴ *
        (K i * (List.ofFn fun j => K (w j)).prod) =
        ((List.ofFn fun j => K (w j)).prod)ᴴ * (List.ofFn fun j => K (w j)).prod := by
      intro w
      simp only [Matrix.mul_assoc]
      rw [← Finset.mul_sum]
      simp only [← Matrix.mul_assoc]
      unfold QAlgorithms.IsKrausFamily at hK
      rw [← Finset.sum_mul, hK, Matrix.one_mul]
    simp only [this, ih]

/-- Remark C.4, PDF p.22: propagation of full left-multiplied Kraus span,
in the actual least invariant support context of C.3. -/
theorem solution {d p : ℕ} (hd : 0 < d) (K : Fin p → Operator d)
    (hK : IsKrausFamily K) (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) (P : Operator d)
    (hS : LeastInvariantSubspace (krausApply K) S) (hP : OrthogonalProjectorOnto P S)
    (n : ℕ) (hn : 0 < n)
    (hfull : leftMultiplySpace P (krausWordSpace K n) = leftMultiplySpace P ⊤) :
    ∀ m : ℕ, n ≤ m →
      leftMultiplySpace P (krausWordSpace K m) = leftMultiplySpace P ⊤ := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hR : ∀ (w' : Fin k → Fin p) X, X ∈ leftMultiplySpace P (krausWordSpace K n) →
      X * (List.ofFn fun i => K (w' i)).prod ∈ leftMultiplySpace P (krausWordSpace K (n+k)) := by
    intro w' X hX
    have hW : krausWordSpace K n ≤ (krausWordSpace K (n+k)).comap
        (LinearMap.mulRight ℂ (List.ofFn fun i => K (w' i)).prod) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
      rw [g52a_word_append]
      exact Submodule.subset_span ⟨_, rfl⟩
    have : leftMultiplySpace P (krausWordSpace K n) ≤ (leftMultiplySpace P
        (krausWordSpace K (n+k))).comap
        (LinearMap.mulRight ℂ (List.ofFn fun i => K (w' i)).prod) := by
      apply Submodule.span_le.mpr
      rintro A ⟨B, hB, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
      rw [Matrix.mul_assoc]
      exact Submodule.subset_span ⟨_, hW hB, rfl⟩
    exact this hX
  apply le_antisymm
  · exact Submodule.span_mono fun A ⟨B, _, h⟩ => ⟨B, Submodule.mem_top, h⟩
  · apply Submodule.span_le.mpr
    rintro A ⟨B, -, rfl⟩
    have hB : B = ∑ w' : Fin k → Fin p, (B * ((List.ofFn fun i => K (w' i)).prod)ᴴ) *
        (List.ofFn fun i => K (w' i)).prod := by
      simp only [Matrix.mul_assoc]
      rw [← Finset.mul_sum, g52a_word_norm K hK k, Matrix.mul_one]
    simp only [SetLike.mem_coe]
    rw [hB, Finset.mul_sum]
    apply Submodule.sum_mem
    intro w' _
    rw [← Matrix.mul_assoc]
    apply hR
    rw [hfull]
    exact Submodule.subset_span ⟨_, Submodule.mem_top, rfl⟩


end

