-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.separated_orthogonal_projectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:13:18.147497+00:00
-- url     : https://prove2.me/submissions/6d8afec0-d2c6-4aac-a3da-ed461afce7b0

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section StageH
variable {H : Type*} [Ring H]

theorem g67d_fP {d : ℕ} (f : Fin d → H) (k : ℕ) (hk : k < d) (hstage : OrthogonalStage f k)
    (i : Fin d) (hi : k < i.val) :
    f i * ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), f j = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hstage
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rcases lt_or_eq_of_le hj with hj | hj
  · exact (h4 j i hj hi.le).2
  · exact h3 j i (by omega) (by rw [Fin.lt_def]; omega)

theorem g67d_Pf {d : ℕ} (f : Fin d → H) (k : ℕ) (hstage : OrthogonalStage f k)
    (i : Fin d) (hi : i.val ≤ k) :
    f i * ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), f j = f i := by
  obtain ⟨h1, h2, h3, h4⟩ := hstage
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact h1 i
  · intro j hj hji
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases lt_or_eq_of_le hi with hi' | hi'
    · rcases lt_or_eq_of_le hj with hj' | hj'
      · exact h2 i j hi' hj' (Ne.symm hji)
      · exact (h4 i j hi' (by omega)).1
    · have : j.val < k := by
        rcases lt_or_eq_of_le hj with hj' | hj'
        · exact hj'
        · exact absurd (Fin.ext (by omega)) hji
      exact (h4 j i this (by omega)).2
  · intro h; exact absurd (by simpa using hi) h

theorem g67d_stage {d : ℕ} (f : Fin d → H) (k : ℕ)
    (hk : k < d) (hstage : OrthogonalStage f k) :
    OrthogonalStage (orthogonalStep f k) (k + 1) := by
  have hfP := g67d_fP f k hk hstage
  have hPf := g67d_Pf f k hstage
  obtain ⟨h1, h2, h3, h4⟩ := hstage
  set P := ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), f j with hPdef
  have hstep : ∀ i : Fin d, orthogonalStep f k i = if i.val ≤ k then f i else (1 - P) * f i := by
    intro i; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hstep]
    split_ifs with hi
    · exact h1 i
    · have := hfP i (by omega)
      calc (1 - P) * f i * ((1 - P) * f i) = (1 - P) * (f i * (1 - P) * f i) := by noncomm_ring
        _ = (1 - P) * f i := by rw [mul_sub, mul_one, this, sub_zero, h1]
  · intro i j hi hj hij
    rw [hstep, hstep, if_pos (by omega), if_pos (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi' <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact h2 i j hi' hj' hij
    · exact (h4 i j hi' (by omega)).1
    · exact (h4 j i hj' (by omega)).2
    · exact absurd (Fin.ext (by omega)) hij
  · intro i j hi hij
    have hij' : i.val < j.val := hij
    rw [hstep, hstep, if_neg (by omega), if_neg (by omega)]
    have := hfP j (by omega)
    have h3' := h3 i j (by omega) hij
    calc (1 - P) * f j * ((1 - P) * f i) = (1 - P) * (f j * f i - f j * P * f i) := by noncomm_ring
      _ = 0 := by rw [h3', this]; simp
  · intro i j hi hj
    rw [hstep, hstep, if_pos (by omega), if_neg (by omega)]
    have hfi := hPf i (by omega)
    have hji : f j * f i = 0 := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
      · exact (h4 i j hi' (by omega)).2
      · exact h3 i j (by omega) (by rw [Fin.lt_def]; omega)
    constructor
    · calc f i * ((1 - P) * f j) = f i * f j - f i * P * f j := by noncomm_ring
        _ = 0 := by rw [hfi]; simp
    · calc (1 - P) * f j * f i = (1 - P) * (f j * f i) := by noncomm_ring
        _ = 0 := by rw [hji, mul_zero]

end StageH

section AppendixDefinitions

variable {R : Type*} [CommRing R]

theorem g67d_diag_mul {d : ℕ} {M N : Matrix (Fin d) (Fin d) R}
    (hM : M.BlockTriangular id) (hN : N.BlockTriangular id) (a : Fin d) :
    (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

theorem g67d_window {d : ℕ} (p q : Fin d) :
    ∀ (l : List (Matrix (Fin d) (Fin d) R)),
      (∀ M ∈ l, M.BlockTriangular id ∧ ∀ c : Fin d, p ≤ c → c ≤ q → M c c = 0) →
      ∀ a b : Fin d, p ≤ a → b ≤ q → b.val < a.val + l.length → l.prod a b = 0 := by
  intro l
  induction l with
  | nil =>
    intro _ a b _ _ h
    simp only [List.prod_nil, List.length_nil, add_zero] at h ⊢
    exact Matrix.one_apply_ne (fun hab => by rw [hab] at h; exact lt_irrefl _ h)
  | cons M l ih =>
    intro hl a b hpa hbq hlen
    have hM := hl M (by simp)
    have hl' : ∀ N ∈ l, N.BlockTriangular id ∧ ∀ c : Fin d, p ≤ c → c ≤ q → N c c = 0 :=
      fun N hN => hl N (by simp [hN])
    have hP : l.prod.BlockTriangular id := by
      have := list_prod_mem (S := Matrix.blockTriangularSubalgebra R R (id : Fin d → Fin d)) (l := l)
        (fun N hN => (hl' N hN).1)
      exact this
    rw [List.prod_cons, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    by_cases hca : c < a
    · rw [hM.1 hca, zero_mul]
    by_cases hcb : b < c
    · rw [hP hcb, mul_zero]
    push_neg at hca hcb
    rcases eq_or_lt_of_le hca with h | h
    · rw [← h, hM.2 a hpa (le_trans (le_trans hca hcb) hbq), zero_mul]
    · rw [ih hl' c b (le_trans hpa hca) hbq (by
        simp only [List.length_cons] at hlen
        have : a.val < c.val := h
        omega), mul_zero]

theorem g67d_pow_window {d : ℕ} (M : Matrix (Fin d) (Fin d) R) (hM : M.BlockTriangular id)
    (p q : Fin d) (hz : ∀ c : Fin d, p ≤ c → c ≤ q → M c c = 0) (m : ℕ)
    (a b : Fin d) (hpa : p ≤ a) (hbq : b ≤ q) (hlen : b.val < a.val + m) : (M ^ m) a b = 0 := by
  rw [← List.prod_replicate]
  exact g67d_window p q _ (fun N hN => by rw [List.eq_of_mem_replicate hN]; exact ⟨hM, hz⟩) a b
    hpa hbq (by simpa using hlen)

theorem g67d_nilp {d : ℕ} (M : Matrix (Fin d) (Fin d) R) (hM : M.BlockTriangular id)
    (hz : ∀ c : Fin d, M c c = 0) (m : ℕ) (hm : d ≤ m) : M ^ m = 0 := by
  ext a b
  by_cases hab : b < a
  · exact (hM.pow m) hab
  push_neg at hab
  exact g67d_pow_window M hM a b (fun c _ _ => hz c) m a b le_rfl le_rfl (by omega)

theorem g67d_diag_list {d : ℕ} (a : Fin d) : ∀ (l : List (Matrix (Fin d) (Fin d) R)),
    (∀ M ∈ l, M.BlockTriangular id) → l.prod a a = (l.map (fun M => M a a)).prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons M l ih =>
    intro hl
    have hP : l.prod.BlockTriangular id :=
      list_prod_mem (S := Matrix.blockTriangularSubalgebra R R (id : Fin d → Fin d)) (l := l)
        (fun N hN => hl N (by simp [hN]))
    rw [List.prod_cons, g67d_diag_mul (hl M (by simp)) hP, ih (fun N hN => hl N (by simp [hN]))]
    simp

theorem g67d_diag_pow {d : ℕ} (M : Matrix (Fin d) (Fin d) R) (hM : M.BlockTriangular id)
    (a : Fin d) (m : ℕ) : (M ^ m) a a = (M a a) ^ m := by
  rw [← List.prod_replicate, g67d_diag_list a _ (fun N hN => by
    rw [List.eq_of_mem_replicate hN]; exact hM)]
  simp

/-- support condition of shape {i} -/
def g67d_Supp {d : ℕ} (i : Fin d) (M : Matrix (Fin d) (Fin d) R) : Prop :=
  ∀ a b, M a b ≠ 0 → a ≤ i ∧ i ≤ b

theorem g67d_supp_upper {d : ℕ} {i : Fin d} {M : Matrix (Fin d) (Fin d) R}
    (h : g67d_Supp i M) : M.BlockTriangular id := by
  intro a b hab
  by_contra hne
  obtain ⟨h1, h2⟩ := h a b hne
  exact absurd (lt_of_lt_of_le hab (le_trans h1 h2)) (lt_irrefl _)

theorem g67d_supp_mul_right {d : ℕ} {i : Fin d} {M Y : Matrix (Fin d) (Fin d) R}
    (h : g67d_Supp i M) (hY : Y.BlockTriangular id) : g67d_Supp i (M * Y) := by
  intro a b hab
  by_contra hn
  apply hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  by_cases hM : M a c = 0
  · rw [hM, zero_mul]
  obtain ⟨h1, h2⟩ := h a c hM
  have hbi : b < i := by
    by_contra hb; push_neg at hb; exact hn ⟨h1, hb⟩
  rw [hY (lt_of_lt_of_le hbi h2), mul_zero]

theorem g67d_supp_mul_left {d : ℕ} {i : Fin d} {M Y : Matrix (Fin d) (Fin d) R}
    (h : g67d_Supp i M) (hY : Y.BlockTriangular id) : g67d_Supp i (Y * M) := by
  intro a b hab
  by_contra hn
  apply hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  by_cases hM : M c b = 0
  · rw [hM, mul_zero]
  obtain ⟨h1, h2⟩ := h c b hM
  have hbi : i < a := by
    by_contra hb; push_neg at hb; exact hn ⟨hb, h2⟩
  rw [hY (lt_of_le_of_lt h1 hbi), zero_mul]

theorem g67d_supp_orth {d : ℕ} {i j : Fin d} {M N : Matrix (Fin d) (Fin d) R}
    (hM : g67d_Supp j M) (hN : g67d_Supp i N) (hij : i < j) : M * N = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  by_cases h1 : M a c = 0
  · rw [h1, zero_mul]
  by_cases h2 : N c b = 0
  · rw [h2, mul_zero]
  exact absurd (lt_of_lt_of_le hij (le_trans (hM a c h1).2 (hN c b h2).1)) (lt_irrefl _)

/-! ### epsilon polynomial facts -/

theorem g67d_eps_sum {C : Type*} [CommRing C] (N : ℕ) (hN : 1 ≤ N) (y : C) :
    epsilon N y + epsilon N (1 - y) = 1 := by
  have h1 : ((1 - y) + y) ^ (2 * N - 1) = 1 := by simp
  rw [add_pow] at h1
  have hn : 2 * N - 1 + 1 = N + N := by omega
  rw [hn, Finset.sum_range_add] at h1
  have hA : epsilon N y = ∑ x ∈ Finset.range N,
      (1 - y) ^ x * y ^ (2 * N - 1 - x) * ((2 * N - 1).choose x : C) := by
    unfold epsilon
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  have hB : epsilon N (1 - y) = ∑ x ∈ Finset.range N,
      (1 - y) ^ (N + x) * y ^ (2 * N - 1 - (N + x)) * ((2 * N - 1).choose (N + x) : C) := by
    unfold epsilon
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < N := Finset.mem_range.mp hj
    have e1 : 2 * N - 1 - (N - 1 - j) = N + j := by omega
    have e2 : 2 * N - 1 - (N + j) = N - 1 - j := by omega
    rw [e1, e2, sub_sub_cancel]
    have : Nat.choose (2 * N - 1) (N - 1 - j) = Nat.choose (2 * N - 1) (N + j) := by
      rw [← Nat.choose_symm (by omega : N - 1 - j ≤ 2 * N - 1), e1]
    rw [this]
    ring
  rw [hA, hB]
  exact h1

theorem g67d_eps_dvd {C : Type*} [CommRing C] (N : ℕ) (y : C) :
    y ^ N ∣ epsilon N y := by
  unfold epsilon
  refine Finset.dvd_sum (fun i hi => ?_)
  have hi' : i < N := Finset.mem_range.mp hi
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow y (by omega)) _) _

theorem g67d_aeval_eps {H : Type*} [Ring H] [Algebra R H] (N : ℕ) (x : H) (p : Polynomial R) :
    Polynomial.aeval x (epsilon N p) = epsilon N (Polynomial.aeval x p) := by
  simp [epsilon, map_sum, map_mul, map_pow, map_natCast, map_sub, map_one]

/-- Idempotent lifting for an upper triangular matrix with 0/1 diagonal and
support of shape {i}. -/
theorem g67d_lift {d : ℕ} (i : Fin d) (x : Matrix (Fin d) (Fin d) R)
    (hx : g67d_Supp i x) (hdiag : ∀ a, x a a = if a = i then 1 else 0) :
    ∃ e : Matrix (Fin d) (Fin d) R, e ∈ Algebra.adjoin R {x} ∧ e * e = e ∧ g67d_Supp i e ∧
      ∀ a, e a a = if a = i then 1 else 0 := by
  have hxU := g67d_supp_upper hx
  set N := d + 1 with hNdef
  set φ := Polynomial.aeval (R := R) x with hφ
  have hU : ∀ p : Polynomial R, (φ p).BlockTriangular id := by
    intro p
    have hmem : φ p ∈ Algebra.adjoin R {x} := Polynomial.aeval_mem_adjoin_singleton R x
    have hle : Algebra.adjoin R {x} ≤ Matrix.blockTriangularSubalgebra R R (id : Fin d → Fin d) :=
      Algebra.adjoin_le (by simpa using hxU)
    exact hle hmem
  have hX : φ Polynomial.X = x := by simp [hφ]
  have he : epsilon N x = φ (epsilon N Polynomial.X) := by rw [g67d_aeval_eps, hX]
  have he' : epsilon N (1 - x) = φ (epsilon N (1 - Polynomial.X)) := by
    rw [g67d_aeval_eps]; simp [hφ]
  obtain ⟨a, ha⟩ := g67d_eps_dvd N (Polynomial.X : Polynomial R)
  obtain ⟨b, hb⟩ := g67d_eps_dvd N (1 - Polynomial.X : Polynomial R)
  have hsum := g67d_eps_sum N (by omega) (Polynomial.X : Polynomial R)
  have hsumH : epsilon N x + epsilon N (1 - x) = 1 := by
    rw [he, he', ← map_add, hsum, map_one]
  have hmap : φ (Polynomial.X * (1 - Polynomial.X)) = x * (1 - x) := by simp [hφ]
  have hyU : (x * (1 - x)).BlockTriangular id := by rw [← hmap]; exact hU _
  have hydiag : ∀ c, (x * (1 - x)) c c = 0 := by
    intro c
    rw [g67d_diag_mul hxU ((Matrix.blockTriangular_one).sub hxU), Matrix.sub_apply,
      Matrix.one_apply_eq, hdiag]
    split_ifs <;> simp
  have hzero : (x * (1 - x)) ^ N = 0 := g67d_nilp _ hyU hydiag N (by omega)
  refine ⟨epsilon N x, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact Polynomial.aeval_mem_adjoin_singleton R x
  · have hprod : epsilon N x * epsilon N (1 - x) = 0 := by
      rw [he, he', ← map_mul, ha, hb]
      have : Polynomial.X ^ N * a * ((1 - Polynomial.X) ^ N * b) =
          (Polynomial.X * (1 - Polynomial.X)) ^ N * (a * b) := by rw [mul_pow]; ring
      rw [this, map_mul, map_pow, hmap, hzero, zero_mul]
    have : epsilon N x = epsilon N x * (epsilon N x + epsilon N (1 - x)) := by
      rw [hsumH, mul_one]
    calc epsilon N x * epsilon N x
        = epsilon N x * (epsilon N x + epsilon N (1 - x)) - epsilon N x * epsilon N (1 - x) := by
          noncomm_ring
      _ = epsilon N x := by rw [hprod, sub_zero, ← this]
  · have : epsilon N x = x * φ (Polynomial.X ^ (N - 1) * a) := by
      rw [he, ha, ← hX, ← map_mul]
      congr 1
      have hN1 : N = (N - 1) + 1 := by omega
      conv_lhs => rw [hN1]
      ring
    rw [this]
    exact g67d_supp_mul_right hx (hU _)
  · have hpoly : epsilon N (Polynomial.X : Polynomial R) - Polynomial.X =
        (Polynomial.X * (1 - Polynomial.X)) *
          (Polynomial.X ^ (N - 1) * a - (1 - Polynomial.X) ^ (N - 1) * b) := by
      have hN1 : N = (N - 1) + 1 := by omega
      have h2 : epsilon N (Polynomial.X : Polynomial R) - Polynomial.X =
          epsilon N (Polynomial.X : Polynomial R) * (1 - Polynomial.X) -
            Polynomial.X * epsilon N (1 - Polynomial.X) := by
        linear_combination (Polynomial.X : Polynomial R) * hsum
      rw [h2]
      conv_lhs => rw [ha, hb, hN1]
      ring
    have hdiff : epsilon N x - x = (x * (1 - x)) *
        φ (Polynomial.X ^ (N - 1) * a - (1 - Polynomial.X) ^ (N - 1) * b) := by
      rw [he, ← hX, ← map_sub, hpoly, map_mul, hmap, hX]
    intro c
    have h3 : (epsilon N x - x) c c = 0 := by
      rw [hdiff, g67d_diag_mul hyU (hU _), hydiag, zero_mul]
    rw [Matrix.sub_apply, sub_eq_zero] at h3
    rw [h3, hdiag]


theorem g67d_repU {d n : ℕ} (S : TriangularSystem R d n) :
    ∀ M ∈ representedAlgebra S, M.BlockTriangular id := by
  intro M hM
  have hle : representedAlgebra S ≤ Matrix.blockTriangularSubalgebra R R (id : Fin d → Fin d) := by
    apply Algebra.adjoin_le
    rintro _ ⟨k, rfl⟩
    exact fun a b h => S.upper k a b h
  exact hle hM

theorem solution [IsDomain R] {d n : ℕ}
    (S : TriangularSystem R d n) (hsep : UnitSeparating S) :
    ∃ e : Fin d → Matrix (Fin d) (Fin d) R,
      QAlgorithms.Papers.Independent.Support21.P08.CompleteOrthogonalIdempotents e ∧ ∀ i, HasShape (e i) {i} ∧ e i ∈ representedAlgebra S := by
  have hU := g67d_repU S
  have hLmem : ∀ k, S.L k ∈ representedAlgebra S := fun k => Algebra.subset_adjoin ⟨k, rfl⟩
  -- interpolation factors
  let kk : ∀ i j : Fin d, i ≠ j → Fin n := fun i j h => Classical.choose (hsep i j h)
  have hkk : ∀ i j (h : i ≠ j), IsUnit (S.L (kk i j h) i i - S.L (kk i j h) j j) :=
    fun i j h => Classical.choose_spec (hsep i j h)
  let F : Fin d → Fin d → Matrix (Fin d) (Fin d) R := fun i j =>
    if h : i = j then 1 else
      Ring.inverse (S.L (kk i j h) i i - S.L (kk i j h) j j) •
        (S.L (kk i j h) - algebraMap R _ (S.L (kk i j h) j j))
  have hFmem : ∀ i j, F i j ∈ representedAlgebra S := by
    intro i j
    simp only [F]
    split_ifs with h
    · exact Subalgebra.one_mem _
    · exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hLmem _) (Subalgebra.algebraMap_mem _ _)) _
  have hFdiag : ∀ i j a, i ≠ j → (a = i → F i j a a = 1) ∧ (a = j → F i j a a = 0) := by
    intro i j a h
    simp only [F, dif_neg h, Matrix.smul_apply, Matrix.sub_apply, Matrix.algebraMap_matrix_apply,
      if_pos rfl, smul_eq_mul]
    constructor
    · rintro rfl
      exact Ring.inverse_mul_cancel _ (hkk a j h)
    · rintro rfl
      simp
  let Z : Fin d → Matrix (Fin d) (Fin d) R := fun i => ((List.finRange d).map (F i)).prod
  have hZmem : ∀ i, Z i ∈ representedAlgebra S := fun i =>
    list_prod_mem (fun M hM => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hM
      exact hFmem i j)
  have hZdiag : ∀ i a, Z i a a = if a = i then 1 else 0 := by
    intro i a
    simp only [Z]
    rw [g67d_diag_list a _ (fun M hM => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hM
      exact hU _ (hFmem i j)), List.map_map]
    split_ifs with hai
    · subst hai
      refine List.prod_eq_one (fun r hr => ?_)
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
      simp only [Function.comp_apply]
      by_cases hj : a = j
      · subst hj; simp [F]
      · exact (hFdiag a j a hj).1 rfl
    · refine List.prod_eq_zero (List.mem_map.mpr ⟨a, List.mem_finRange a, ?_⟩)
      simp only [Function.comp_apply]
      exact (hFdiag i a a (Ne.symm hai)).2 rfl
  -- powers have the right support
  have hdpos : ∀ i : Fin d, d ≠ 0 := fun i => by have := i.isLt; omega
  let x : Fin d → Matrix (Fin d) (Fin d) R := fun i => Z i ^ d
  have hxmem : ∀ i, x i ∈ representedAlgebra S := fun i => Subalgebra.pow_mem _ (hZmem i) _
  have hxdiag : ∀ i a, x i a a = if a = i then 1 else 0 := by
    intro i a
    simp only [x]
    rw [g67d_diag_pow _ (hU _ (hZmem i)), hZdiag]
    split_ifs
    · simp
    · exact zero_pow (hdpos i)
  have hxsupp : ∀ i, g67d_Supp i (x i) := by
    intro i a b hab
    by_contra hn
    apply hab
    by_cases hba : b < a
    · exact (hU _ (hxmem i)) hba
    push_neg at hba
    refine g67d_pow_window _ (hU _ (hZmem i)) a b (fun c hc1 hc2 => ?_) d a b le_rfl le_rfl
      (by have := b.isLt; omega)
    rw [hZdiag, if_neg]
    rintro rfl
    exact hn ⟨hc1, hc2⟩
  -- lift to idempotents
  have hlift := fun i => g67d_lift i (x i) (hxsupp i) (hxdiag i)
  choose e0 he0mem he0idem he0supp he0diag using hlift
  have he0mem' : ∀ i, e0 i ∈ representedAlgebra S := by
    intro i
    have : Algebra.adjoin R {x i} ≤ representedAlgebra S :=
      Algebra.adjoin_le (by simpa using hxmem i)
    exact this (he0mem i)
  -- orthogonalization
  let g : ℕ → Fin d → Matrix (Fin d) (Fin d) R := fun k => Nat.rec e0 (fun k gk => orthogonalStep gk k) k
  have hg0 : g 0 = e0 := rfl
  have hgs : ∀ k, g (k + 1) = orthogonalStep (g k) k := fun k => rfl
  have inv : ∀ k, k ≤ d → OrthogonalStage (g k) k ∧ ∀ i, g k i ∈ representedAlgebra S ∧
      g67d_Supp i (g k i) ∧ ∀ a, g k i a a = if a = i then 1 else 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⟨fun i => he0idem i, fun i j hi => absurd hi (Nat.not_lt_zero _),
        fun i j _ hij => g67d_supp_orth (he0supp j) (he0supp i) hij,
        fun i j hi => absurd hi (Nat.not_lt_zero _)⟩, fun i => ⟨he0mem' i, he0supp i, he0diag i⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨hst, hprop⟩ := ih (by omega)
      refine ⟨hgs k ▸ g67d_stage (g k) k (by omega) hst, fun i => ?_⟩
      rw [hgs k]
      set P := ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), g k j with hP
      have hPmem : P ∈ representedAlgebra S := Subalgebra.sum_mem _ (fun j _ => (hprop j).1)
      have h1P : (1 - P) ∈ representedAlgebra S := Subalgebra.sub_mem _ (Subalgebra.one_mem _) hPmem
      have hstep : orthogonalStep (g k) k i = if i.val ≤ k then g k i else (1 - P) * g k i := rfl
      rw [hstep]
      split_ifs with hik
      · exact hprop i
      · obtain ⟨hm, hs, hd⟩ := hprop i
        refine ⟨Subalgebra.mul_mem _ h1P hm, g67d_supp_mul_left hs (hU _ h1P), fun a => ?_⟩
        rw [g67d_diag_mul (hU _ h1P) (g67d_supp_upper hs), hd]
        split_ifs with hai
        · subst hai
          rw [Matrix.sub_apply, Matrix.one_apply_eq, hP, Matrix.sum_apply,
            Finset.sum_eq_zero (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              rw [(hprop j).2.2 a, if_neg (fun h => by subst h; exact hik hj)])]
          simp
        · simp
  obtain ⟨hst, hprop⟩ := inv d le_rfl
  obtain ⟨hidem, horth, -, -⟩ := hst
  refine ⟨g d, ⟨hidem, fun i j hij => horth i j i.isLt j.isLt hij, ?_⟩, fun i => ?_⟩
  · -- completeness
    set u := ∑ i, g d i with hu
    have huu : u * u = u := by
      rw [hu, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_eq_single i (fun j _ hji => horth i j i.isLt j.isLt (Ne.symm hji))
        (fun h => absurd (Finset.mem_univ i) h), hidem]
    set v := 1 - u with hv
    have hvv : IsIdempotentElem v := by
      show v * v = v
      rw [hv]
      calc (1 - u) * (1 - u) = 1 - u - u + u * u := by noncomm_ring
        _ = 1 - u := by rw [huu]; abel
    have huU : u ∈ representedAlgebra S := Subalgebra.sum_mem _ (fun j _ => (hprop j).1)
    have hvU : v.BlockTriangular id := hU _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) huU)
    have hvdiag : ∀ c, v c c = 0 := by
      intro c
      rw [hv, Matrix.sub_apply, Matrix.one_apply_eq, hu, Matrix.sum_apply]
      simp_rw [fun j => (hprop j).2.2 c]
      simp
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      ext a; exact a.elim0
    · have h0 : v ^ d = 0 := g67d_nilp v hvU hvdiag d le_rfl
      rw [hvv.pow_eq (by omega)] at h0
      rw [hv] at h0
      exact (sub_eq_zero.mp h0).symm
  · obtain ⟨hm, hs, hd⟩ := hprop i
    refine ⟨⟨⟨i, Finset.mem_singleton_self i⟩, fun a b h => ⟨i, Finset.mem_singleton_self i, hs a b h⟩,
      fun a => by rw [hd]; simp [Finset.mem_singleton]⟩, hm⟩

end AppendixDefinitions

end
