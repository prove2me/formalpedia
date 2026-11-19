-- Prove2me | solution 1 for QMCTriFree.Circuit.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:06:14.741142+00:00
-- url     : https://prove2.me/submissions/cb0e8ed9-86be-46e8-bddc-ee1478948961

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Lasserre

open QMCTriFree.Circuit QMCProduct.HalfApprox Matrix

private lemma pauli1_herm (a : Fin 4) : (pauli1 a).IsHermitian := by
  fin_cases a <;> ext i j <;> cases i <;> cases j <;>
    simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ]

private lemma pauli1_sq (a : Fin 4) : pauli1 a * pauli1 a = 1 := by
  fin_cases a <;> ext i j <;> cases i <;> cases j <;>
    simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.mul_apply]

private lemma pauliOp_herm {n : ℕ} (s : PauliString n) : (pauliOp s).IsHermitian := by
  ext x y
  simp only [pauliOp, QAlgorithms.kronAll, Matrix.conjTranspose_apply, Matrix.of_apply,
    Complex.star_def, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  have h := congr_fun (congr_fun (pauli1_herm (s q)) (x q)) (y q)
  simpa [Matrix.conjTranspose_apply] using h

private lemma kronAll_mul {n : ℕ} (f g : Fin n → Matrix Bool Bool ℂ) :
    QAlgorithms.kronAll f * QAlgorithms.kronAll g = QAlgorithms.kronAll (fun q => f q * g q) := by
  ext x z
  simp only [QAlgorithms.kronAll, Matrix.mul_apply, Matrix.of_apply]
  have hterm : ∀ y : QAlgorithms.Qubits n,
      (∏ q : Fin n, f q (x q) (y q)) * (∏ q : Fin n, g q (y q) (z q)) =
      ∏ q : Fin n, (f q (x q) (y q) * g q (y q) (z q)) :=
    fun y => (Finset.prod_mul_distrib).symm
  simp_rw [hterm]
  symm
  exact Fintype.prod_sum fun q b => f q (x q) b * g q b (z q)

private lemma pauliOp_mul {n : ℕ} (s t : PauliString n) :
    pauliOp s * pauliOp t = QAlgorithms.kronAll (fun q => pauli1 (s q) * pauli1 (t q)) := by
  unfold pauliOp
  exact kronAll_mul _ _

private lemma idStr_deg {n : ℕ} : pauliDegree (idStr n) ≤ 2 := by
  simp [pauliDegree, idStr]

private lemma pairStr_deg {n : ℕ} (a : Fin 4) (i j : Fin n) : pauliDegree (pairStr a i j) ≤ 2 := by
  unfold pauliDegree pairStr
  have hsub : (Finset.univ.filter fun t : Fin n => (if t = i ∨ t = j then a else 0) ≠ 0) ⊆
      ({i, j} : Finset (Fin n)) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    simp [h.1, h.2] at ht
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

private def idP2 (n : ℕ) : P2 n := ⟨idStr n, idStr_deg⟩
private def pairP2 {n : ℕ} (a : Fin 4) (i j : Fin n) : P2 n := ⟨pairStr a i j, pairStr_deg a i j⟩

private lemma entry_id_pair {n : ℕ} (M : Matrix (P2 n) (P2 n) ℝ) (a : Fin 4) (i j : Fin n) :
    entry M (idStr n) (pairStr a i j) = M (idP2 n) (pairP2 a i j) := by
  simp [entry, idP2, pairP2, idStr_deg, pairStr_deg]

private lemma pauliOp_id {n : ℕ} : pauliOp (idStr n) = 1 := by
  ext x y
  simp only [pauliOp, idStr, QAlgorithms.kronAll, Matrix.of_apply, pauli1, ↓reduceIte,
    Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · simp only [if_neg h]
    obtain ⟨q, hq⟩ : ∃ q : Fin n, x q ≠ y q := by
      by_contra hall; push Not at hall; exact h (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

private lemma pauliOp_pair_mul_same {n : ℕ} (a : Fin 4) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (pauliOp (pairStr a i j))ᴴ * pauliOp (pairStr a i k) =
      (pauliOp (idStr n))ᴴ * pauliOp (pairStr a j k) := by
  have h0 : pauli1 0 = 1 := by ext x y; simp [pauli1]
  rw [(pauliOp_herm _).eq, (pauliOp_herm _).eq, pauliOp_id, one_mul, pauliOp_mul]
  congr 1
  funext q
  simp only [pairStr]
  by_cases hqi : q = i
  · subst hqi
    simp [pauli1_sq, hij, hik, h0]
  · by_cases hqj : q = j
    · subst hqj; simp [hqi, hjk, h0]
    · by_cases hqk : q = k
      · subst hqk; simp [hqi, hqj, h0]
      · simp [hqi, hqj, hqk, h0]

private lemma pauli1_offdiag_mul (a b c : Fin 4)
    (h : (a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 2 ∧ b = 1 ∧ c = 3) ∨
         (a = 2 ∧ b = 3 ∧ c = 1) ∨ (a = 3 ∧ b = 2 ∧ c = 1) ∨
         (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 3 ∧ c = 2)) :
    ∃ s : ℂ, (s = Complex.I ∨ s = -Complex.I) ∧ pauli1 a * pauli1 b = s • pauli1 c := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨Complex.I, Or.inl rfl, ?_⟩
    ext x y; cases x <;> cases y <;> simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.mul_apply]
  · refine ⟨-Complex.I, Or.inr rfl, ?_⟩
    ext x y; cases x <;> cases y <;> simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.mul_apply]
  · refine ⟨Complex.I, Or.inl rfl, ?_⟩
    ext x y; cases x <;> cases y <;> simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.mul_apply]
  · refine ⟨-Complex.I, Or.inr rfl, ?_⟩
    ext x y; cases x <;> cases y <;> simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.mul_apply]
  · refine ⟨Complex.I, Or.inl rfl, ?_⟩
    ext x y; cases x <;> cases y <;> simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.mul_apply]
  · refine ⟨-Complex.I, Or.inr rfl, ?_⟩
    ext x y; cases x <;> cases y <;> simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.mul_apply]

private lemma pauliOp_pair_mul_diff_same_edge {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a b c : Fin 4)
    (h : (a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 2 ∧ b = 1 ∧ c = 3) ∨
         (a = 2 ∧ b = 3 ∧ c = 1) ∨ (a = 3 ∧ b = 2 ∧ c = 1) ∨
         (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 3 ∧ c = 2)) :
    (pauliOp (pairStr a i j))ᴴ * pauliOp (pairStr b i j) =
      -((pauliOp (idStr n))ᴴ * pauliOp (pairStr c i j)) := by
  obtain ⟨s, hs, hmul⟩ := pauli1_offdiag_mul a b c h
  rw [(pauliOp_herm _).eq, (pauliOp_herm _).eq, pauliOp_id, one_mul, pauliOp_mul]
  ext x z
  simp only [QAlgorithms.kronAll, pauliOp, Matrix.of_apply, Matrix.neg_apply]
  have hterm : ∀ q : Fin n,
      (pauli1 (pairStr a i j q) * pauli1 (pairStr b i j q)) (x q) (z q) =
      (if q = i ∨ q = j then s else 1) * pauli1 (pairStr c i j q) (x q) (z q) := by
    intro q
    simp only [pairStr]
    by_cases hq : q = i ∨ q = j
    · simp [hq, hmul]
    · simp [hq, pauli1]
  simp_rw [hterm, Finset.prod_mul_distrib]
  have hprod : (∏ q : Fin n, if q = i ∨ q = j then s else 1) = -1 := by
    have hfilt : (Finset.univ.filter fun q : Fin n => q = i ∨ q = j) = {i, j} := by
      ext q; simp
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, hfilt, Finset.prod_pair hij]
    rcases hs with rfl | rfl <;> simp [Complex.I_sq]
  rw [hprod, neg_one_mul]

private lemma pauliOp_pair_mul_diff_not_herm {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : Fin 4) (ha : a = 1 ∨ a = 2 ∨ a = 3) (hb : b = 1 ∨ b = 2 ∨ b = 3) (hab : a ≠ b) :
    ¬ ((pauliOp (pairStr a i j))ᴴ * pauliOp (pairStr b i k)).IsHermitian := by
  have hc : ∃ c : Fin 4,
      (a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 2 ∧ b = 1 ∧ c = 3) ∨
      (a = 2 ∧ b = 3 ∧ c = 1) ∨ (a = 3 ∧ b = 2 ∧ c = 1) ∨
      (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 3 ∧ c = 2) := by
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
  obtain ⟨c, hc⟩ := hc
  obtain ⟨s, hs, hmul⟩ := pauli1_offdiag_mul a b c hc
  rw [(pauliOp_herm _).eq, pauliOp_mul]
  let t : PauliString n := fun q => if q = i then c else if q = j then a else if q = k then b else 0
  have heq : QAlgorithms.kronAll (fun q => pauli1 (pairStr a i j q) * pauli1 (pairStr b i k q)) =
      s • pauliOp t := by
    ext x z
    simp only [QAlgorithms.kronAll, pauliOp, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have hterm : ∀ q : Fin n,
        (pauli1 (pairStr a i j q) * pauli1 (pairStr b i k q)) (x q) (z q) =
        (if q = i then s else 1) * pauli1 (t q) (x q) (z q) := by
      intro q
      simp only [pairStr, t]
      by_cases hqi : q = i
      · subst hqi; simp [hij.symm, hik.symm, hmul]
      · by_cases hqj : q = j
        · subst hqj; simp [hqi, hjk, pauli1]
        · by_cases hqk : q = k
          · subst hqk; simp [hqi, hqj, pauli1]
          · simp [hqi, hqj, hqk, pauli1]
    simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [heq]
  intro hherm
  have hneg : (s • pauliOp t)ᴴ = (-s) • pauliOp t := by
    rw [Matrix.conjTranspose_smul, (pauliOp_herm t).eq]
    congr 1
    rcases hs with rfl | rfl <;> simp
  rw [hherm.eq] at hneg
  have h0 : (2 * s) • pauliOp t = 0 := by
    ext x z
    have h1 := congr_fun (congr_fun hneg x) z
    simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at h1 ⊢
    linear_combination h1
  have h2s : (2 * s) ≠ 0 := by rcases hs with rfl | rfl <;> simp [Complex.I_ne_zero]
  have hpauli_ne : pauliOp t ≠ 0 := by
    have hsq : pauliOp t * pauliOp t = 1 := by
      rw [pauliOp_mul]
      ext x z
      simp only [QAlgorithms.kronAll, Matrix.of_apply, Matrix.one_apply]
      have h1 : ∀ q, (pauli1 (t q) * pauli1 (t q)) (x q) (z q) = if x q = z q then 1 else 0 := by
        intro q; rw [pauli1_sq, Matrix.one_apply]
      simp_rw [h1]
      by_cases hxz : x = z
      · subst hxz; simp
      · simp only [if_neg hxz]
        obtain ⟨q, hq⟩ : ∃ q, x q ≠ z q := by by_contra hall; push Not at hall; exact hxz (funext hall)
        exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)
    intro h0t
    rw [h0t, Matrix.zero_mul] at hsq
    have h01 := congr_fun (congr_fun hsq (fun _ => false)) (fun _ => false)
    simp at h01
  exact hpauli_ne ((smul_eq_zero.mp h0).resolve_left h2s)

private lemma sum_pair_le_one {n : ℕ} (M : Matrix (P2 n) (P2 n) ℝ) (hM : IsFeasible M)
    {j k : Fin n} (hjk : j ≠ k) :
    M (idP2 n) (pairP2 1 j k) + M (idP2 n) (pairP2 2 j k) + M (idP2 n) (pairP2 3 j k) ≤ 1 := by
  let u : P2 n → ℝ := fun A =>
    (if A = idP2 n then 1 else 0) -
    (if A = pairP2 1 j k then 1 else 0) -
    (if A = pairP2 2 j k then 1 else 0) -
    (if A = pairP2 3 j k then 1 else 0)
  let u_fs : P2 n →₀ ℝ := Finsupp.onFinset Finset.univ u (fun _ _ => Finset.mem_univ _)
  have hnn : 0 ≤ star u ⬝ᵥ (M *ᵥ u) := by
    have h := hM.1.2 u_fs
    simpa [u_fs, Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using h
  have h12 : pairP2 1 j k ≠ pairP2 2 j k := by
    intro h; have := congr_fun (congrArg Subtype.val h) j; simp [pairP2, pairStr] at this
  have h13 : pairP2 1 j k ≠ pairP2 3 j k := by
    intro h; have := congr_fun (congrArg Subtype.val h) j; simp [pairP2, pairStr] at this
  have h23 : pairP2 2 j k ≠ pairP2 3 j k := by
    intro h; have := congr_fun (congrArg Subtype.val h) j; simp [pairP2, pairStr] at this
  have h01 : idP2 n ≠ pairP2 1 j k := by
    intro h; have := congr_fun (congrArg Subtype.val h) j; simp [idP2, pairP2, idStr, pairStr] at this
  have h02 : idP2 n ≠ pairP2 2 j k := by
    intro h; have := congr_fun (congrArg Subtype.val h) j; simp [idP2, pairP2, idStr, pairStr] at this
  have h03 : idP2 n ≠ pairP2 3 j k := by
    intro h; have := congr_fun (congrArg Subtype.val h) j; simp [idP2, pairP2, idStr, pairStr] at this
  have hsym : ∀ A B : P2 n, M A B = M B A := fun A B => by
    have := congr_fun (congr_fun hM.1.1.eq B) A
    simpa [Matrix.conjTranspose_apply] using this
  have hdiag : ∀ A : P2 n, M A A = 1 := hM.2.2.2.2
  have hoff : ∀ a b c : Fin 4,
      ((a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 2 ∧ b = 1 ∧ c = 3) ∨
       (a = 2 ∧ b = 3 ∧ c = 1) ∨ (a = 3 ∧ b = 2 ∧ c = 1) ∨
       (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 3 ∧ c = 2)) →
      M (pairP2 a j k) (pairP2 b j k) = -M (idP2 n) (pairP2 c j k) :=
    fun a b c h => hM.2.2.1 _ _ _ _ (pauliOp_pair_mul_diff_same_edge hjk a b c h)
  have hexp : star u ⬝ᵥ (M *ᵥ u) =
      4 - 4 * (M (idP2 n) (pairP2 1 j k) + M (idP2 n) (pairP2 2 j k) + M (idP2 n) (pairP2 3 j k)) := by
    simp only [dotProduct, Matrix.mulVec, star_trivial, u]
    have hS : ∀ f : P2 n → ℝ,
        (∑ A : P2 n, ((if A = idP2 n then 1 else 0) - (if A = pairP2 1 j k then 1 else 0) -
          (if A = pairP2 2 j k then 1 else 0) - (if A = pairP2 3 j k then 1 else 0)) * f A) =
        f (idP2 n) - f (pairP2 1 j k) - f (pairP2 2 j k) - f (pairP2 3 j k) := by
      intro f
      simp only [sub_mul, one_mul, zero_mul, ite_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    have hS' : ∀ f : P2 n → ℝ,
        (∑ A : P2 n, f A * ((if A = idP2 n then 1 else 0) - (if A = pairP2 1 j k then 1 else 0) -
          (if A = pairP2 2 j k then 1 else 0) - (if A = pairP2 3 j k then 1 else 0))) =
        f (idP2 n) - f (pairP2 1 j k) - f (pairP2 2 j k) - f (pairP2 3 j k) := by
      intro f
      simp_rw [mul_comm (f _)]
      exact hS f
    rw [hS]
    simp_rw [hS', hdiag]
    rw [hsym (pairP2 1 j k) (idP2 n), hsym (pairP2 2 j k) (idP2 n),
      hsym (pairP2 3 j k) (idP2 n),
      hoff 1 2 3 (Or.inl ⟨rfl, rfl, rfl⟩),
      hoff 2 1 3 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
      hoff 2 3 1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))),
      hoff 3 2 1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))),
      hoff 3 1 2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))),
      hoff 1 3 2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))]
    ring
  linarith

theorem solution {n : ℕ} (w : Fin n → Fin n → ℝ) (M : Matrix (P2 n) (P2 n) ℝ)
    (hM : IsFeasible M) (i : Fin n) (S : Finset (Fin n)) (hS : S ⊆ nbrs w i) :
    ∑ j ∈ S, xval M i j ≤ 1 := by
  have hiS : i ∉ S := by
    intro hi
    have := Finset.mem_filter.mp (hS hi)
    exact this.2.1 rfl
  by_cases hSne : S.Nonempty
  · let A_M : ℝ := -∑ j ∈ S, (M (idP2 n) (pairP2 1 i j) + M (idP2 n) (pairP2 2 i j) +
      M (idP2 n) (pairP2 3 i j))
    let a3 : Fin 3 → Fin 4 := fun a => a.succ
    let v : P2 n → ℝ := fun B =>
      (if B = idP2 n then A_M else 0) +
      ∑ j ∈ S, ∑ a : Fin 3, if B = pairP2 (a3 a) i j then 1 else 0
    let v_fs : P2 n →₀ ℝ := Finsupp.onFinset Finset.univ v (fun _ _ => Finset.mem_univ _)
    have hnn : 0 ≤ star v ⬝ᵥ (M *ᵥ v) := by
      have h := hM.1.2 v_fs
      simpa [v_fs, Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using h
    have hsym : ∀ A B : P2 n, M A B = M B A := fun A B => by
      have := congr_fun (congr_fun hM.1.1.eq B) A
      simpa [Matrix.conjTranspose_apply] using this
    have hdiag : ∀ A : P2 n, M A A = 1 := hM.2.2.2.2
    have hv_sum : ∀ f : P2 n → ℝ,
        (∑ B : P2 n, v B * f B) =
        A_M * f (idP2 n) + ∑ j ∈ S, ∑ a : Fin 3, f (pairP2 (a3 a) i j) := by
      intro f
      simp only [v, add_mul, Finset.sum_add_distrib]
      congr 1
      · simp
      · simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => by simp
    have hv_sum' : ∀ f : P2 n → ℝ,
        (∑ B : P2 n, f B * v B) =
        A_M * f (idP2 n) + ∑ j ∈ S, ∑ a : Fin 3, f (pairP2 (a3 a) i j) := by
      intro f
      simp_rw [mul_comm (f _)]
      exact hv_sum f
    have ha3_0 : a3 0 = 1 := rfl
    have ha3_1 : a3 1 = 2 := rfl
    have ha3_2 : a3 2 = 3 := rfl
    have hexp : star v ⬝ᵥ (M *ᵥ v) =
        A_M ^ 2 - 2 * A_M ^ 2 +
        ∑ j ∈ S, ∑ a : Fin 3, ∑ k ∈ S, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k) := by
      simp only [dotProduct, Matrix.mulVec, star_trivial]
      rw [hv_sum]
      simp_rw [hv_sum']
      have h1 : (∑ j ∈ S, ∑ a : Fin 3, M (idP2 n) (pairP2 (a3 a) i j)) = -A_M := by
        dsimp only [A_M]
        simp only [Fin.sum_univ_three, ha3_0, ha3_1, ha3_2]
        ring
      have h2 : (∑ j ∈ S, ∑ a : Fin 3, M (pairP2 (a3 a) i j) (idP2 n)) = -A_M := by
        simp_rw [hsym _ (idP2 n)]
        exact h1
      rw [mul_add, h1, hdiag]
      have h3 : (∑ j ∈ S, (∑ a : Fin 3, (A_M * M (pairP2 (a3 a) i j) (idP2 n) +
          ∑ k ∈ S, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k)))) =
          A_M * (-A_M) + ∑ j ∈ S, ∑ a : Fin 3, ∑ k ∈ S, ∑ b : Fin 3,
            M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, h2]
      rw [h3]
      ring
    have hoff_same : ∀ j ∈ S,
        (∑ a : Fin 3, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i j)) =
        3 - 2 * (M (idP2 n) (pairP2 1 i j) + M (idP2 n) (pairP2 2 i j) + M (idP2 n) (pairP2 3 i j)) := by
      intro j hj
      have hij : i ≠ j := fun h => hiS (h ▸ hj)
      have hoff : ∀ a b c : Fin 4,
          ((a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 2 ∧ b = 1 ∧ c = 3) ∨
           (a = 2 ∧ b = 3 ∧ c = 1) ∨ (a = 3 ∧ b = 2 ∧ c = 1) ∨
           (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 3 ∧ c = 2)) →
          M (pairP2 a i j) (pairP2 b i j) = -M (idP2 n) (pairP2 c i j) :=
        fun a b c h => hM.2.2.1 _ _ _ _ (pauliOp_pair_mul_diff_same_edge hij a b c h)
      simp only [Fin.sum_univ_three, ha3_0, ha3_1, ha3_2, hdiag,
        hoff 1 2 3 (Or.inl ⟨rfl, rfl, rfl⟩),
        hoff 2 1 3 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
        hoff 2 3 1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))),
        hoff 3 2 1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))),
        hoff 3 1 2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))),
        hoff 1 3 2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))]
      ring
    have hoff_diff : ∀ j ∈ S, ∀ k ∈ S, j ≠ k →
        (∑ a : Fin 3, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k)) ≤ 1 := by
      intro j hj k hk hjk
      have hij : i ≠ j := fun h => hiS (h ▸ hj)
      have hik : i ≠ k := fun h => hiS (h ▸ hk)
      have ha3 : ∀ a : Fin 3, a3 a = 1 ∨ a3 a = 2 ∨ a3 a = 3 := by
        intro a; fin_cases a <;> simp [a3]
      have h0 : ∀ a b : Fin 3, a ≠ b →
          M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k) = 0 := by
        intro a b hab
        apply hM.2.2.2.1
        refine pauliOp_pair_mul_diff_not_herm hij hik hjk (a3 a) (a3 b) (ha3 a) (ha3 b) ?_
        intro h; apply hab; fin_cases a <;> fin_cases b <;> simp_all [a3]
      have hsame : ∀ a : Fin 3,
          M (pairP2 (a3 a) i j) (pairP2 (a3 a) i k) = M (idP2 n) (pairP2 (a3 a) j k) :=
        fun a => hM.2.1 _ _ _ _ (pauliOp_pair_mul_same (a3 a) hij hik hjk)
      simp only [Fin.sum_univ_three]
      rw [h0 0 1 (by decide), h0 0 2 (by decide), h0 1 0 (by decide), h0 1 2 (by decide),
          h0 2 0 (by decide), h0 2 1 (by decide), hsame 0, hsame 1, hsame 2, ha3_0, ha3_1, ha3_2]
      simp only [add_zero, zero_add]
      exact sum_pair_le_one M hM hjk
    have hquad_le :
        (∑ j ∈ S, ∑ a : Fin 3, ∑ k ∈ S, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k)) ≤
        3 * (S.card : ℝ) + 2 * A_M + (S.card : ℝ) * ((S.card : ℝ) - 1) := by
      have hcomm : (∑ j ∈ S, ∑ a : Fin 3, ∑ k ∈ S, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k)) =
          ∑ j ∈ S, ∑ k ∈ S, ∑ a : Fin 3, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
      rw [hcomm]
      have hrow : ∀ j ∈ S,
          (∑ k ∈ S, ∑ a : Fin 3, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k)) ≤
          3 - 2 * (M (idP2 n) (pairP2 1 i j) + M (idP2 n) (pairP2 2 i j) + M (idP2 n) (pairP2 3 i j)) +
          ((S.card : ℝ) - 1) := by
        intro j hj
        rw [← Finset.add_sum_erase S _ hj, hoff_same j hj]
        have hrest : (∑ k ∈ S.erase j, ∑ a : Fin 3, ∑ b : Fin 3,
            M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k)) ≤ (S.card : ℝ) - 1 := by
          calc (∑ k ∈ S.erase j, ∑ a : Fin 3, ∑ b : Fin 3,
                M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k))
              ≤ ∑ _k ∈ S.erase j, (1 : ℝ) := by
                refine Finset.sum_le_sum fun k hk => ?_
                exact hoff_diff j hj k (Finset.mem_erase.mp hk).2 (Finset.mem_erase.mp hk).1.symm
            _ = (S.card : ℝ) - 1 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul, mul_one,
                    Nat.cast_sub (Finset.card_pos.mpr hSne), Nat.cast_one]
        linarith
      calc (∑ j ∈ S, ∑ k ∈ S, ∑ a : Fin 3, ∑ b : Fin 3, M (pairP2 (a3 a) i j) (pairP2 (a3 b) i k))
          ≤ ∑ j ∈ S, (3 - 2 * (M (idP2 n) (pairP2 1 i j) + M (idP2 n) (pairP2 2 i j) +
              M (idP2 n) (pairP2 3 i j)) + ((S.card : ℝ) - 1)) := Finset.sum_le_sum hrow
        _ = 3 * (S.card : ℝ) + 2 * A_M + (S.card : ℝ) * ((S.card : ℝ) - 1) := by
            have hsum_add : (∑ j ∈ S, (3 - 2 * (M (idP2 n) (pairP2 1 i j) + M (idP2 n) (pairP2 2 i j) +
                M (idP2 n) (pairP2 3 i j)) + ((S.card : ℝ) - 1))) =
                (S.card : ℝ) * (3 + ((S.card : ℝ) - 1)) - 2 * (-A_M) := by
              have h1 : ∀ j ∈ S, (3 - 2 * (M (idP2 n) (pairP2 1 i j) + M (idP2 n) (pairP2 2 i j) +
                  M (idP2 n) (pairP2 3 i j)) + ((S.card : ℝ) - 1)) =
                  (3 + ((S.card : ℝ) - 1)) - 2 * (M (idP2 n) (pairP2 1 i j) +
                    M (idP2 n) (pairP2 2 i j) + M (idP2 n) (pairP2 3 i j)) := fun _ _ => by ring
              rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
                  ← Finset.mul_sum]
              dsimp only [A_M]; ring
            rw [hsum_add]; ring
    have hA_le : A_M ≤ (S.card : ℝ) + 2 := by
      have hkR : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg (A_M - ((S.card : ℝ) + 2))]
    have hxval : ∑ j ∈ S, xval M i j = (A_M - (S.card : ℝ)) / 2 := by
      have hpt : ∀ j ∈ S, xval M i j = -(1 / 2 : ℝ) * (1 + M (idP2 n) (pairP2 1 i j) +
          M (idP2 n) (pairP2 2 i j) + M (idP2 n) (pairP2 3 i j)) := by
        intro j _
        simp only [xval, entry_id_pair]
      rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
      have hsum_add : (∑ x ∈ S, (1 + M (idP2 n) (pairP2 1 i x) + M (idP2 n) (pairP2 2 i x) +
          M (idP2 n) (pairP2 3 i x))) = (S.card : ℝ) - A_M := by
        have h1 : ∀ x ∈ S, (1 + M (idP2 n) (pairP2 1 i x) + M (idP2 n) (pairP2 2 i x) +
            M (idP2 n) (pairP2 3 i x)) =
            1 + (M (idP2 n) (pairP2 1 i x) + M (idP2 n) (pairP2 2 i x) +
              M (idP2 n) (pairP2 3 i x)) := fun _ _ => by ring
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            mul_one]
        dsimp only [A_M]; ring
      rw [hsum_add]; ring
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hSne, Finset.sum_empty]
    norm_num
