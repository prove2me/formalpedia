-- Prove2me | solution 1 for PolySwap.KMS.proposition_5_14
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T03:56:08.122248+00:00
-- url     : https://prove2.me/submissions/2deb0380-3af4-4ab9-a88d-15705b63f6a2

import Mathlib
import Definitions.Def_PolySwap_KMS_Unip

open Classical Matrix

namespace PolySwap.KMS.Sol514

variable {n : ℕ} {R : Type*} [CommRing R]

lemma umat_mul (g h : Unip n R) : umat n R (g * h) = umat n R g * umat n R h := rfl

lemma umat_one : umat n R (1 : Unip n R) = 1 := rfl

lemma umat_inj {g h : Unip n R} (e : umat n R g = umat n R h) : g = h :=
  Subtype.ext (Subtype.ext e)

lemma umat_unitri (g : Unip n R) : IsUnitriangular n R (umat n R g) := g.2

noncomputable def mkU (M : Matrix (Fin n) (Fin n) R) (hM : IsUnitriangular n R M) : Unip n R :=
  ⟨⟨M, by rw [Matrix.det_of_isUpperTriangular (fun i j h => hM.1 i j h)]; simp [hM.2]⟩, hM⟩

@[simp] lemma umat_mkU (M : Matrix (Fin n) (Fin n) R) (hM : IsUnitriangular n R M) :
    umat n R (mkU M hM) = M := rfl

lemma unitri_one_add (N : Matrix (Fin n) (Fin n) R) (h : ∀ a b, N a b ≠ 0 → a < b) :
    IsUnitriangular n R (1 + N) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have h1 : N i j = 0 := by
      by_contra hne; exact absurd (h i j hne) (not_lt.2 hij.le)
    simp [h1, (ne_of_lt hij).symm]
  · have h1 : N i i = 0 := by
      by_contra hne; exact absurd (h i i hne) (lt_irrefl _)
    simp [h1]

/-- The elementary matrix `e_{ab}(c)` (as the off-identity part of a transvection). -/
def el (a b : Fin n) (c : R) : Matrix (Fin n) (Fin n) R := fun i j => if i = a ∧ j = b then c else 0

lemma el_strict (a b : Fin n) (hab : a < b) (c : R) : ∀ i j, el a b c i j ≠ 0 → i < j := by
  intro i j h
  unfold el at h
  split_ifs at h with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact hab
  · exact absurd rfl h

/-- A subgroup containing the transvections `1 + e_{ab}(c)` with `a < b` and `P a b` contains
every element whose off-diagonal support lies in `P`. -/
theorem mem_of_pattern (K : Subgroup (Unip n R)) (P : Fin n → Fin n → Prop)
    (hK : ∀ (a b : Fin n) (c : R) (t : Unip n R), a < b → P a b →
      umat n R t = 1 + el a b c → t ∈ K) :
    ∀ g : Unip n R, (∀ a b, a ≠ b → umat n R g a b ≠ 0 → P a b) → g ∈ K := by
  intro g
  generalize hN : (Finset.univ.filter
    (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ umat n R g p.1 p.2 ≠ 0)).card = N
  induction N using Nat.strong_induction_on generalizing g with
  | _ N ih =>
    intro hg
    set S := Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ umat n R g p.1 p.2 ≠ 0) with hS
    by_cases hne : S.Nonempty
    · obtain ⟨⟨a, b⟩, hp, hmin⟩ := S.exists_min_image (fun p => p.2) hne
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hab : a < b := by
        rcases lt_or_gt_of_ne hp.1 with h | h
        · exact h
        · exact absurd ((umat_unitri g).1 a b h) hp.2
      set c := umat n R g a b with hc
      have hcol : ∀ i, i ≠ a → umat n R g i a = 0 := by
        intro i hi
        by_contra h
        have := hmin (i, a) (by simp [hS, hi, h])
        exact absurd hab (not_lt.2 this)
      have haa : umat n R g a a = 1 := (umat_unitri g).2 a
      let t := mkU (1 + el a b (-c)) (unitri_one_add _ (el_strict a b hab _))
      let ti := mkU (1 + el a b c) (unitri_one_add _ (el_strict a b hab _))
      have hgt_mat : ∀ i j, umat n R (g * t) i j =
          if i = a ∧ j = b then 0 else umat n R g i j := by
        intro i j
        rw [umat_mul]
        simp only [t, umat_mkU]
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
        simp only [el, mul_ite, mul_zero]
        rw [Finset.sum_eq_single a]
        · by_cases hj : j = b
          · subst hj
            by_cases hi : i = a
            · subst hi; simp [haa, hc]
            · simp [hcol i hi, hi]
          · simp [hj]
        · intro k _ hk; simp [hk]
        · simp
      have htti : t * ti = 1 := by
        apply umat_inj
        rw [umat_mul, umat_one]
        simp only [t, ti, umat_mkU]
        have : el a b (-c) * el a b c = (0 : Matrix (Fin n) (Fin n) R) := by
          ext i j
          simp only [Matrix.mul_apply, el, Matrix.zero_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          by_cases h1 : i = a ∧ k = b
          · have : ¬ (k = a ∧ j = b) := fun h2 => absurd (h1.2 ▸ h2.1) (ne_of_gt hab)
            simp [this]
          · simp [h1]
        have e2 : el a b (-c) + el a b c = (0 : Matrix (Fin n) (Fin n) R) := by
          ext i j; simp only [el, Matrix.add_apply, Matrix.zero_apply]; split_ifs <;> simp
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, this, Matrix.one_mul,
          Matrix.mul_one, Matrix.one_mul, add_zero, add_assoc, add_comm (el a b c), e2, add_zero]
      have hg_eq : g = (g * t) * ti := by rw [mul_assoc, htti, mul_one]
      have hPab : P a b := hg a b hp.1 hp.2
      rw [hg_eq]
      refine K.mul_mem ?_ (hK a b c ti hab hPab rfl)
      have hS' : Finset.univ.filter
          (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ umat n R (g * t) p.1 p.2 ≠ 0) = S.erase (a, b) := by
        ext ⟨i, j⟩
        simp only [hgt_mat i j, hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
          ne_eq, Prod.mk.injEq]
        by_cases h : i = a ∧ j = b
        · simp [h]
        · simp [h]
      refine ih _ ?_ (g * t) rfl ?_
      · rw [hS', ← hN]
        exact Finset.card_erase_lt_of_mem (by simp [hS, hp.1, hp.2, ← hc])
      · intro i j hij hne'
        rw [hgt_mat] at hne'
        split_ifs at hne' with h
        · exact absurd rfl hne'
        · exact hg i j hij hne'
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : g = 1 := by
        apply umat_inj
        ext i j
        rw [umat_one, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp [(umat_unitri g).2 i]
        · simp only [hij, if_false]
          by_contra h
          have : (i, j) ∈ S := by simp [hS, hij, h]
          rw [hne] at this
          simp at this
      rw [this]; exact K.one_mem

section Blocks

variable (n : ℕ)

lemma blk_ge1 (a : Fin n) : 1 ≤ blockOf n a := by unfold blockOf; split_ifs <;> omega
lemma blk_le5 (a : Fin n) : blockOf n a ≤ 5 := by unfold blockOf; split_ifs <;> omega
lemma blk_le4 (a : Fin n) : blockOf n a ≤ 4 ↔ (a : ℕ) < n - n / 5 := by
  unfold blockOf; split_ifs <;> omega
lemma blk_ge2 (a : Fin n) : 2 ≤ blockOf n a ↔ n / 5 ≤ (a : ℕ) := by
  unfold blockOf; split_ifs <;> omega
lemma blk_eq1 (a : Fin n) : blockOf n a = 1 ↔ (a : ℕ) < n / 5 := by
  unfold blockOf; split_ifs <;> omega
lemma blk_eq2 (a : Fin n) : blockOf n a = 2 ↔ n / 5 ≤ (a : ℕ) ∧ (a : ℕ) < 2 * (n / 5) := by
  unfold blockOf; split_ifs <;> omega
lemma blk_eq5 (a : Fin n) : blockOf n a = 5 ↔ n - n / 5 ≤ (a : ℕ) := by
  unfold blockOf; split_ifs <;> omega
lemma blk_mono {a b : Fin n} (h : a ≤ b) : blockOf n a ≤ blockOf n b := by
  have : (a : ℕ) ≤ b := h
  unfold blockOf; split_ifs <;> omega

end Blocks

/-- A transvection `1 + e_{ab}(c)`, `a < b`, is a block generator `E_{i,j}(A)` with
`i = blockOf a`, `j = blockOf b`. -/
lemma tv_gen (a b : Fin n) (hab : a < b) (c : R) (t : Unip n R)
    (ht : umat n R t = 1 + el a b c) :
    ∃ A, Admissible n R (blockOf n a) (blockOf n b) A ∧
      umat n R t = E n R (blockOf n a) (blockOf n b) A := by
  rcases lt_or_eq_of_le (blk_mono n hab.le) with hlt | heq
  · refine ⟨el a b c, Or.inl ⟨hlt, fun x y hxy => ?_⟩, by simp [E, hlt, ht]⟩
    simp only [el]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact absurd ⟨rfl, rfl⟩ hxy
    · rfl
  · refine ⟨1 + el a b c, Or.inr ⟨heq, unitri_one_add _ (el_strict a b hab c), ?_⟩,
      by simp [E, heq, ht]⟩
    intro x y hxy
    simp only [Matrix.add_apply, Matrix.one_apply, el]
    split_ifs with h1 h2 h2
    · obtain ⟨rfl, rfl⟩ := h2; exact absurd ⟨rfl, heq.symm⟩ hxy
    · simp
    · obtain ⟨rfl, rfl⟩ := h2; exact absurd ⟨rfl, heq.symm⟩ hxy
    · simp

/-- Matrices whose nonzero off-diagonal part is strictly upper triangular (as a support
condition) give unitriangular `1 + N`. -/
lemma unitri_of_supp (N : Matrix (Fin n) (Fin n) R) (Q : Fin n → Fin n → Prop)
    (hQ : ∀ a b, Q a b → a < b) (h : ∀ a b, N a b ≠ 0 → Q a b) :
    IsUnitriangular n R (1 + N) :=
  unitri_one_add N fun a b hab => hQ a b (h a b hab)

end PolySwap.KMS.Sol514

open PolySwap.KMS PolySwap.KMS.Sol514 Matrix

theorem solution (n : ℕ) (R : Type*) [CommRing R] (hn : 5 ≤ n)
    (H₁ H₂ : Subgroup (Unip n R))
    (hH₁ : H₁ = Subgroup.closure {g | ∃ i j A, 1 ≤ i ∧ i ≤ j ∧ j ≤ 4 ∧ Admissible n R i j A ∧
      umat n R g = E n R i j A})
    (hH₂ : H₂ = Subgroup.closure {g | ∃ i A, 2 ≤ i ∧ i ≤ 5 ∧ Admissible n R i 5 A ∧
      umat n R g = E n R i 5 A}) :
    ∀ g : Unip n R, ∃ l : List (Unip n R), l.length ≤ 6 ∧ (∀ x ∈ l, x ∈ H₁ ∨ x ∈ H₂) ∧
      l.prod = g := by
  intro g
  have hk : 1 ≤ n / 5 := by omega
  have hk5 : 5 * (n / 5) ≤ n := Nat.mul_div_le n 5
  set k := n / 5 with hkdef
  -- `h₁`: `g` on blocks 1–4, the identity elsewhere.
  let Pm : Matrix (Fin n) (Fin n) R := fun a b =>
    if (a : ℕ) < n - k ∧ (b : ℕ) < n - k then umat n R g a b else if a = b then 1 else 0
  have hPm : IsUnitriangular n R Pm := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [Pm]; split_ifs with h1 h2
      · exact (umat_unitri g).1 i j hij
      · exact absurd h2 (ne_of_lt hij).symm
      · rfl
    · simp only [Pm]; split_ifs <;> simp [(umat_unitri g).2 i]
  let h1 := mkU Pm hPm
  have eh1 : umat n R h1 = Pm := rfl
  have h1mem : h1 ∈ H₁ := by
    subst hH₁
    refine mem_of_pattern _ (fun a b => (a : ℕ) < n - k ∧ (b : ℕ) < n - k) ?_ h1 ?_
    · intro a b c t hab hP ht
      obtain ⟨A, hA, hE⟩ := tv_gen a b hab c t ht
      exact Subgroup.subset_closure ⟨_, _, A, blk_ge1 n a, blk_mono n hab.le,
        (blk_le4 n b).2 hP.2, hA, hE⟩
    · intro a b hab hne
      rw [eh1] at hne
      simp only [Pm] at hne
      split_ifs at hne with h
      · exact h
      · simp at hne
  -- `Y = h₁⁻¹ g` fixes the first `n - k` coordinate vectors.
  let Y := h1⁻¹ * g
  have hcolg : ∀ a b : Fin n, (b : ℕ) < n - k → umat n R g a b = umat n R h1 a b := by
    intro a b hb
    rw [eh1]
    simp only [Pm]
    split_ifs with h1' h2
    · rfl
    · subst h2; exact absurd hb (by simpa using fun h => h1' ⟨h, h⟩)
    · have : b < a := by
        have : ¬ (a : ℕ) < n - k := fun ha => h1' ⟨ha, hb⟩
        exact Fin.lt_def.2 (by omega)
      exact (umat_unitri g).1 a b this
  have hY : ∀ a b : Fin n, (b : ℕ) < n - k → umat n R Y a b = if a = b then 1 else 0 := by
    intro a b hb
    have : umat n R Y a b = umat n R (h1⁻¹ * h1) a b := by
      simp only [Y, umat_mul, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun c _ => by rw [hcolg c b hb]
    rw [this, inv_mul_cancel, umat_one, Matrix.one_apply]
  -- The (1,5) corner of `Y`.
  let C : Matrix (Fin n) (Fin n) R := fun a b =>
    if (a : ℕ) < k ∧ n - k ≤ (b : ℕ) then umat n R Y a b else 0
  have hCs : ∀ a b, C a b ≠ 0 → (a : ℕ) < k ∧ n - k ≤ (b : ℕ) := by
    intro a b h; simp only [C] at h; split_ifs at h with h'; exact h'; exact absurd rfl h
  have hQ : ∀ a b : Fin n, ((a : ℕ) < k ∧ n - k ≤ (b : ℕ)) → a < b := fun a b h =>
    Fin.lt_def.2 (by omega)
  have hCneg : ∀ a b, (-C) a b ≠ 0 → (a : ℕ) < k ∧ n - k ≤ (b : ℕ) := fun a b h =>
    hCs a b (by simpa using h)
  have hCC : C * C = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1' : C a c = 0
    · simp [h1']
    · have := hCs a c h1'
      have : C c b = 0 := by
        by_contra h2; have := hCs c b h2; omega
      simp [this]
  have hYC : umat n R Y * C = C := by
    ext a b
    simp only [Matrix.mul_apply]
    have : ∀ c, umat n R Y a c * C c b = if a = c then C c b else 0 := by
      intro c
      by_cases h' : C c b = 0
      · simp [h']
      · have := hCs c b h'
        rw [hY a c (by omega)]; split_ifs <;> simp
    simp_rw [this]
    simp
  let Z := mkU (1 + C) (unitri_of_supp C _ hQ hCs)
  let Zi := mkU (1 + -C) (unitri_of_supp (-C) _ hQ hCneg)
  have hZiZ : Zi * Z = 1 := by
    apply umat_inj
    simp only [umat_mul, umat_one, Zi, Z, umat_mkU]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.neg_mul, hCC]
    abel
  -- `h₂ = Y Z⁻¹`: supported on rows of blocks 2–5 and columns of block 5.
  let h2 := Y * Zi
  have h2mat : ∀ a b, umat n R h2 a b = umat n R Y a b - C a b := by
    intro a b
    have : umat n R h2 = umat n R Y - C := by
      simp only [h2, umat_mul, Zi, umat_mkU]
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, hYC, sub_eq_add_neg]
    rw [this, Matrix.sub_apply]
  have h2mem : h2 ∈ H₂ := by
    subst hH₂
    refine mem_of_pattern _ (fun a b => k ≤ (a : ℕ) ∧ n - k ≤ (b : ℕ)) ?_ h2 ?_
    · intro a b c t hab hP ht
      obtain ⟨A, hA, hE⟩ := tv_gen a b hab c t ht
      have hb5 : blockOf n b = 5 := (blk_eq5 n b).2 hP.2
      rw [hb5] at hA hE
      exact Subgroup.subset_closure ⟨_, A, (blk_ge2 n a).2 hP.1, blk_le5 n a, hA, hE⟩
    · intro a b hab hne
      rw [h2mat] at hne
      by_cases hb : (b : ℕ) < n - k
      · have : C a b = 0 := by by_contra h; have := hCs a b h; omega
        rw [hY a b hb, this] at hne; simp [hab] at hne
      · by_cases ha : (a : ℕ) < k
        · have hb' : n - k ≤ (b : ℕ) := by omega
          have hC : C a b = umat n R Y a b := by simp only [C]; rw [if_pos ⟨ha, hb'⟩]
          rw [hC, sub_self] at hne; exact absurd rfl hne
        · exact ⟨by omega, by omega⟩
  -- The corner `Z = [x, y]` with `x = E₁₂(A)`, `y = E₂₅(B)`.
  let A : Matrix (Fin n) (Fin n) R := fun a c => if (a : ℕ) < k ∧ (c : ℕ) = a + k then 1 else 0
  let B : Matrix (Fin n) (Fin n) R := fun c b =>
    if k ≤ (c : ℕ) ∧ (c : ℕ) < 2 * k ∧ n - k ≤ (b : ℕ) then umat n R Y ⟨c - k, by omega⟩ b else 0
  have hAs : ∀ a c, A a c ≠ 0 → (a : ℕ) < k ∧ (c : ℕ) = a + k := by
    intro a c h; simp only [A] at h; split_ifs at h with h'; exact h'; exact absurd rfl h
  have hBs : ∀ c b, B c b ≠ 0 → k ≤ (c : ℕ) ∧ (c : ℕ) < 2 * k ∧ n - k ≤ (b : ℕ) := by
    intro c b h; simp only [B] at h; split_ifs at h with h'; exact h'; exact absurd rfl h
  have hQA : ∀ a c : Fin n, ((a : ℕ) < k ∧ (c : ℕ) = a + k) → a < c := fun a c h =>
    Fin.lt_def.2 (by omega)
  have hQB : ∀ c b : Fin n, (k ≤ (c : ℕ) ∧ (c : ℕ) < 2 * k ∧ n - k ≤ (b : ℕ)) → c < b :=
    fun c b h => Fin.lt_def.2 (by omega)
  have hAn : ∀ a c, (-A) a c ≠ 0 → (a : ℕ) < k ∧ (c : ℕ) = a + k := fun a c h =>
    hAs a c (by simpa using h)
  have hBn : ∀ c b, (-B) c b ≠ 0 → k ≤ (c : ℕ) ∧ (c : ℕ) < 2 * k ∧ n - k ≤ (b : ℕ) :=
    fun c b h => hBs c b (by simpa using h)
  have zero_of : ∀ (X W : Matrix (Fin n) (Fin n) R),
      (∀ a c b, X a c ≠ 0 → W c b ≠ 0 → False) → X * W = 0 := by
    intro X W h
    ext a b
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1' : X a c = 0
    · simp [h1']
    · by_cases h2' : W c b = 0
      · simp [h2']
      · exact (h a c b h1' h2').elim
  have hAA : A * A = 0 := zero_of A A fun a c b h1' h2' => by
    have := hAs a c h1'; have := hAs c b h2'; omega
  have hBB : B * B = 0 := zero_of B B fun a c b h1' h2' => by
    have := hBs a c h1'; have := hBs c b h2'; omega
  have hBA : B * A = 0 := zero_of B A fun a c b h1' h2' => by
    have := hBs a c h1'; have := hAs c b h2'; omega
  have hAB : A * B = C := by
    ext a b
    simp only [Matrix.mul_apply]
    by_cases ha : (a : ℕ) < k
    · rw [Finset.sum_eq_single ⟨a + k, by omega⟩]
      · simp only [A, B, C, ha, true_and, if_true, one_mul]
        by_cases hb : n - k ≤ (b : ℕ)
        · have : (⟨(a : ℕ) + k - k, by omega⟩ : Fin n) = a := Fin.ext (by simp)
          have h2k : ¬ 2 * k ≤ (a : ℕ) + k := by omega
          simp [hb, h2k]
        · simp [hb]
      · intro c _ hc
        have : A a c = 0 := by
          by_contra h; exact hc (Fin.ext (hAs a c h).2)
        simp [this]
      · simp
    · have : ∀ c, A a c = 0 := fun c => by by_contra h; exact ha (hAs a c h).1
      simp [this, C, ha]
  let x := mkU (1 + A) (unitri_of_supp A _ hQA hAs)
  let xi := mkU (1 + -A) (unitri_of_supp (-A) _ hQA hAn)
  let y := mkU (1 + B) (unitri_of_supp B _ hQB hBs)
  let yi := mkU (1 + -B) (unitri_of_supp (-B) _ hQB hBn)
  have hAadm : ∀ A' : Matrix (Fin n) (Fin n) R,
      (∀ a c, A' a c ≠ 0 → (a : ℕ) < k ∧ (c : ℕ) = a + k) → Admissible n R 1 2 A' := by
    intro A' h
    refine Or.inl ⟨by norm_num, fun a c hac => ?_⟩
    by_contra hne
    obtain ⟨h1', h2'⟩ := h a c hne
    exact hac ⟨(blk_eq1 n a).2 h1', (blk_eq2 n c).2 ⟨by omega, by omega⟩⟩
  have hBadm : ∀ B' : Matrix (Fin n) (Fin n) R,
      (∀ c b, B' c b ≠ 0 → k ≤ (c : ℕ) ∧ (c : ℕ) < 2 * k ∧ n - k ≤ (b : ℕ)) →
      Admissible n R 2 5 B' := by
    intro B' h
    refine Or.inl ⟨by norm_num, fun c b hcb => ?_⟩
    by_contra hne
    obtain ⟨h1', h2', h3'⟩ := h c b hne
    exact hcb ⟨(blk_eq2 n c).2 ⟨h1', h2'⟩, (blk_eq5 n b).2 h3'⟩
  have xmem : ∀ (A' : Matrix (Fin n) (Fin n) R) (hA' : ∀ a c : Fin n, A' a c ≠ 0 → (a : ℕ) < k ∧ (c : ℕ) = a + k),
      mkU (1 + A') (unitri_of_supp A' _ hQA hA') ∈ H₁ := by
    intro A' hA'
    subst hH₁
    exact Subgroup.subset_closure ⟨1, 2, A', le_rfl, by norm_num, by norm_num, hAadm A' hA',
      by simp [E]⟩
  have ymem : ∀ (B' : Matrix (Fin n) (Fin n) R) (hB' : ∀ c b : Fin n, B' c b ≠ 0 → k ≤ (c : ℕ) ∧ (c : ℕ) < 2 * k ∧ n - k ≤ (b : ℕ)),
      mkU (1 + B') (unitri_of_supp B' _ hQB hB') ∈ H₂ := by
    intro B' hB'
    subst hH₂
    exact Subgroup.subset_closure ⟨2, B', le_rfl, by norm_num, hBadm B' hB', by simp [E]⟩
  have hcomm : xi * yi * x * y = Z := by
    apply umat_inj
    simp only [umat_mul, xi, yi, x, y, Z, umat_mkU]
    rw [← hAB]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.mul_assoc, hAA, hBB, hBA, Matrix.mul_zero, neg_zero, add_zero]
    abel
  refine ⟨[h1, h2, xi, yi, x, y], by simp, ?_, ?_⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl h1mem
    · exact Or.inr h2mem
    · exact Or.inl (xmem _ hAn)
    · exact Or.inr (ymem _ hBn)
    · exact Or.inl (xmem _ hAs)
    · exact Or.inr (ymem _ hBs)
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    have : xi * (yi * (x * y)) = Z := by rw [← hcomm]; group
    rw [this]
    simp only [h2, mul_assoc, hZiZ, mul_one, Y, mul_inv_cancel_left]
