-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.example_6_16
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:44:25.413908+00:00
-- url     : https://prove2.me/submissions/7e636baf-8fc5-409e-a65d-76246486022b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_6_15

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8C6

variable {d : ℕ}

lemma dep_apply (p q : Fin d × Fin d) :
    depolarizing d p q = if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0 := rfl

lemma ad_apply (B : Mat d) (p q : Fin d × Fin d) : ad B p q = B p.1 q.1 * conj (B p.2 q.2) := rfl

lemma applyMap_apply (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ q : Fin d × Fin d, t (i, j) q * X q.1 q.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

lemma am_mul (s r : Map d) (X : Mat d) :
    applyMap (s * r) X = applyMap s (applyMap r X) := by
  ext i j
  simp only [applyMap_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  ring

lemma am_ad (B : Mat d) (X : Mat d) : applyMap (ad B) X = B * X * Bᴴ := by
  ext i j
  rw [applyMap_apply]
  simp only [ad, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma am_sum {K : Type*} [Fintype K] (M : K → Map d) (X : Mat d) :
    applyMap (∑ k, M k) X = ∑ k, applyMap (M k) X := by
  ext i j
  simp only [applyMap_apply, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ent_single' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (r s i j : n) :
    (A * Matrix.single r s (1 : ℂ) * Aᴴ) i j = A i r * conj (A j s) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.sum_eq_single r]
    · simp [Complex.star_def]
    · intro b _ hb; simp only [Matrix.single_apply]; rw [if_neg (fun h => hb h.1.symm)]; simp
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _; simp [Matrix.single_apply, Ne.symm hb]
  · simp

lemma kraus_form {t : Map d} (ht : UnitalChannel t) :
    ∃ m : ℕ, ∃ E : Fin m → Mat d, (∑ j, (E j)ᴴ * E j = 1) ∧ t = ∑ j, ad (E j) := by
  obtain ⟨m, E, hK, hE⟩ := ht.1
  refine ⟨m, E, hK, ?_⟩
  ext p q
  have h := congrFun (congrFun (hE (Matrix.single q.1 q.2 1)) p.1) p.2
  rw [applyMap_apply, Finset.sum_eq_single q] at h
  · rw [Matrix.sum_apply]
    simp only [Matrix.single_apply, and_self, if_true, mul_one] at h
    rw [h]
    simp only [QAlgorithms.krausApply, Matrix.sum_apply, ent_single']
    rfl
  · intro b _ hb
    rw [Matrix.single_apply, if_neg (fun c => hb (Prod.ext c.1.symm c.2.symm)), mul_zero]
  · simp

lemma isChannel_of_kraus {K ι : Type*} [Fintype K] [Fintype ι] [DecidableEq ι]
    (E : K → Matrix ι ι ℂ) (hE : QAlgorithms.IsKrausFamily E) (Φ : QAlgorithms.Superop ι ι)
    (hΦ : ∀ ρ, Φ ρ = QAlgorithms.krausApply E ρ) : QAlgorithms.IsChannel Φ := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (e.symm j), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily at hE ⊢
    rw [← hE]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · intro ρ
    rw [hΦ]
    unfold QAlgorithms.krausApply
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

lemma ad_mul (A B : Mat d) : ad A * ad B = ad (A * B) := by
  ext p q
  simp only [Matrix.mul_apply, ad_apply, Fintype.sum_prod_type, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma uc_mul {s r : Map d} (hs : UnitalChannel s) (hr : UnitalChannel r) :
    UnitalChannel (s * r) := by
  obtain ⟨m, E, hE, rfl⟩ := kraus_form hs
  obtain ⟨m', F, hF, rfl⟩ := kraus_form hr
  have hunit : applyMap ((∑ j, ad (E j)) * ∑ j, ad (F j)) 1 = 1 := by
    rw [am_mul, hr.2, hs.2]
  refine ⟨?_, hunit⟩
  let G : Fin m × Fin m' → Mat d := fun k => E k.1 * F k.2
  refine isChannel_of_kraus G ?_ _ ?_
  · unfold QAlgorithms.IsKrausFamily
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [G, Matrix.conjTranspose_mul]
    have : ∀ y : Fin m', ∑ x : Fin m, (F y)ᴴ * (E x)ᴴ * (E x * F y) = (F y)ᴴ * F y := by
      intro y
      calc ∑ x : Fin m, (F y)ᴴ * (E x)ᴴ * (E x * F y)
          = (F y)ᴴ * (∑ x, (E x)ᴴ * E x) * F y := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ => by noncomm_ring
        _ = (F y)ᴴ * F y := by rw [hE, Matrix.mul_one]
    simp only [this]
    exact hF
  · intro ρ
    rw [am_mul, am_sum, am_sum]
    simp only [am_ad, QAlgorithms.krausApply, G, Fintype.sum_prod_type, Finset.mul_sum,
      Finset.sum_mul, Matrix.conjTranspose_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    noncomm_ring

lemma uc_pow {t : Map d} (ht : UnitalChannel t) (n : ℕ) (hn : 1 ≤ n) :
    UnitalChannel (t ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => rwa [pow_one]
  | succ n _ ih => rw [pow_succ]; exact uc_mul ih ht

lemma col_le {m : ℕ} (E : Fin m → Mat d) (hE : ∑ j, (E j)ᴴ * E j = 1) (a b : Fin d) :
    ∑ j, Complex.normSq (E j a b) ≤ 1 := by
  have h := congrFun (congrFun hE b) b
  rw [Matrix.sum_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def] at h
  have h' : ∑ j, ∑ i, Complex.normSq (E j i b) = 1 := by
    have := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    generalize E j i b = z
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]; ring
  rw [← h']
  refine Finset.sum_le_sum fun j _ => ?_
  exact Finset.single_le_sum (f := fun i => Complex.normSq (E j i b))
    (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

lemma entry_le {t : Map d} (ht : UnitalChannel t) (p q : Fin d × Fin d) : ‖t p q‖ ≤ 1 := by
  obtain ⟨m, E, hE, rfl⟩ := kraus_form ht
  rw [Matrix.sum_apply]
  calc ‖∑ j, ad (E j) p q‖ ≤ ∑ j, ‖ad (E j) p q‖ := norm_sum_le _ _
    _ ≤ ∑ j, (Complex.normSq (E j p.1 q.1) + Complex.normSq (E j p.2 q.2)) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [ad_apply, norm_mul, Complex.norm_conj, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg (‖E j p.1 q.1‖ - ‖E j p.2 q.2‖)]
    _ = (∑ j, Complex.normSq (E j p.1 q.1) + ∑ j, Complex.normSq (E j p.2 q.2)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ 1 := by linarith [col_le E hE p.1 q.1, col_le E hE p.2 q.2]

end X8C6

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8BS

variable {m n : ℕ}

abbrev φ : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv

/-- block entries on the sum type -/
def BS (s : Map m) (t : Map n) : Fin m ⊕ Fin n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℂ
  | .inl i, .inl j, .inl a, .inl c => s (i, j) (a, c)
  | .inr i, .inr j, .inr a, .inr c => t (i, j) (a, c)
  | _, _, _, _ => 0

lemma sum4_one {k : ℕ} (f : Fin k → Fin k → Fin k → Fin k → ℂ) (i0 j0 a0 c0 : Fin k) :
    (∑ i : Fin k, ∑ j : Fin k, ∑ a : Fin k, ∑ c : Fin k,
      if i0 = i ∧ j0 = j ∧ a0 = a ∧ c0 = c then f i j a c else 0) = f i0 j0 a0 c0 := by
  simp only [ite_and]
  simp [Finset.sum_ite_eq]

lemma sum4_zero {k : ℕ} (f : Fin k → Fin k → Fin k → Fin k → ℂ) (P : Fin k → Fin k → Fin k → Fin k → Prop)
    (h : ∀ i j a c, ¬ P i j a c) :
    (∑ i : Fin k, ∑ j : Fin k, ∑ a : Fin k, ∑ c : Fin k,
      if P i j a c then f i j a c else 0) = 0 := by
  simp [h]

lemma bs_entry (s : Map m) (t : Map n) (x y z w : Fin m ⊕ Fin n) :
    binarySum s t (φ x, φ y) (φ z, φ w) = BS s t x y z w := by
  have L : ∀ (i i' : Fin m), ((Fin.castAdd n i : Fin (m + n)) : ℕ) = (i' : ℕ) ↔ i = i' := by
    intro i i'; simp [Fin.ext_iff]
  have R : ∀ (i i' : Fin n), ((Fin.natAdd m i : Fin (m + n)) : ℕ) = m + (i' : ℕ) ↔ i = i' := by
    intro i i'; simp [Fin.ext_iff]
  have L0 : ∀ (i : Fin m) (i' : Fin n), ((Fin.castAdd n i : Fin (m + n)) : ℕ) = m + (i' : ℕ) ↔ False := by
    intro i i'; simp only [Fin.coe_castAdd, iff_false]; omega
  have R0 : ∀ (i : Fin n) (i' : Fin m), ((Fin.natAdd m i : Fin (m + n)) : ℕ) = (i' : ℕ) ↔ False := by
    intro i i'; simp only [Fin.coe_natAdd, iff_false]; omega
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rcases w with w | w <;>
    simp only [binarySum, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, L, R, L0, R0,
      false_and, and_false, if_false, Finset.sum_const_zero, add_zero, zero_add, BS, sum4_one]

end X8BS

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8BS

variable {m n : ℕ}

lemma sum_pair (f : Fin (m + n) × Fin (m + n) → ℂ) :
    ∑ r, f r = ∑ u : Fin m ⊕ Fin n, ∑ v : Fin m ⊕ Fin n, f (φ u, φ v) := by
  rw [Fintype.sum_prod_type, ← (φ (m := m) (n := n)).sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← (φ (m := m) (n := n)).sum_comp]

lemma bs_ext {M N : Map (m + n)}
    (h : ∀ x y z w : Fin m ⊕ Fin n, M (φ x, φ y) (φ z, φ w) = N (φ x, φ y) (φ z, φ w)) :
    M = N := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  obtain ⟨x, rfl⟩ := (φ (m := m) (n := n)).surjective p1
  obtain ⟨y, rfl⟩ := (φ (m := m) (n := n)).surjective p2
  obtain ⟨z, rfl⟩ := (φ (m := m) (n := n)).surjective q1
  obtain ⟨w, rfl⟩ := (φ (m := m) (n := n)).surjective q2
  exact h x y z w

lemma bs_mul (s s' : Map m) (t t' : Map n) :
    binarySum s t * binarySum s' t' = binarySum (s * s') (t * t') := by
  apply bs_ext
  intro x y z w
  rw [Matrix.mul_apply, sum_pair]
  simp only [bs_entry]
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rcases w with w | w <;>
    simp [BS, Fintype.sum_sum_type, Matrix.mul_apply, Fintype.sum_prod_type]

@[simp] lemma cn_ne (x : Fin m) (z : Fin n) : (Fin.castAdd n x = Fin.natAdd m z) ↔ False := by
  simp only [Fin.ext_iff, Fin.coe_castAdd, Fin.coe_natAdd, iff_false]; omega

@[simp] lemma nc_ne (x : Fin m) (z : Fin n) : (Fin.natAdd m z = Fin.castAdd n x) ↔ False := by
  simp only [Fin.ext_iff, Fin.coe_castAdd, Fin.coe_natAdd, iff_false]; omega

lemma bs_pow (s : Map m) (t : Map n) (k : ℕ) (hk : 1 ≤ k) :
    binarySum s t ^ k = binarySum (s ^ k) (t ^ k) := by
  induction k, hk using Nat.le_induction with
  | base => simp only [pow_one]
  | succ k _ ih => rw [pow_succ, ih, bs_mul, pow_succ, pow_succ]

lemma bs_comb {J K : Type*} [Fintype J] [Fintype K] (p : J → ℝ) (q : K → ℝ)
    (hp : ∑ j, p j = 1) (hq : ∑ k, q k = 1) (A : J → Map m) (B : K → Map n) :
    binarySum (∑ j, p j • A j) (∑ k, q k • B k) =
      ∑ x : J × K, (p x.1 * q x.2) • binarySum (A x.1) (B x.2) := by
  apply bs_ext
  intro x y z w
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, bs_entry]
  have hp' : ∑ j, (p j : ℂ) = 1 := by exact_mod_cast hp
  have hq' : ∑ k, (q k : ℂ) = 1 := by exact_mod_cast hq
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rcases w with w | w <;>
    simp only [BS, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, smul_zero,
      Finset.sum_const_zero, Fintype.sum_prod_type, Complex.ofReal_mul]
  · rw [← mul_one (∑ j, _), ← hq', Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  · rw [← one_mul (∑ k, _), ← hp', Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-! block-diagonal embedding -/

def emb (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) : Mat (m + n) :=
  Matrix.reindexAlgEquiv ℂ ℂ φ A

lemma emb_apply (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) (x y : Fin m ⊕ Fin n) :
    emb A (φ x) (φ y) = A x y := by
  simp [emb, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

lemma emb_ct (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) : (emb A)ᴴ = emb Aᴴ := by
  simp only [emb, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex]

lemma emb_mul (A B : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) : emb A * emb B = emb (A * B) := by
  simp only [emb, map_mul]

lemma emb_one : emb (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) = 1 := by
  simp only [emb, map_one]

lemma emb_sum {K : Type*} [Fintype K] (A : K → Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) :
    emb (∑ k, A k) = ∑ k, emb (A k) := by
  simp only [emb, map_sum]

def W (U : Unitary m) (U' : Unitary n) : Unitary (m + n) :=
  ⟨emb (Matrix.fromBlocks (U : Mat m) 0 0 (U' : Mat n)), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, emb_ct, emb_mul,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    have h1 : (U : Mat m) * (U : Mat m)ᴴ = 1 := by
      have := U.2; rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
      exact this
    have h2 : (U' : Mat n) * (U' : Mat n)ᴴ = 1 := by
      have := U'.2; rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
      exact this
    simp only [h1, h2, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.fromBlocks_one, emb_one]⟩

lemma W_apply (U : Unitary m) (U' : Unitary n) (x y : Fin m ⊕ Fin n) :
    ((W U U' : Unitary (m + n)) : Mat (m + n)) (φ x) (φ y) =
      Matrix.fromBlocks (U : Mat m) 0 0 (U' : Mat n) x y := emb_apply _ x y

lemma beta_apply {d : ℕ} (U V : Unitary d) (p q : Fin d × Fin d) :
    beta U V p q = ∑ m : Fin d, (U : Mat d) p.1 m * conj ((U : Mat d) p.2 m) *
      conj ((V : Mat d) q.1 m) * (V : Mat d) q.2 m := by
  have h1 : ∀ j : Fin d × Fin d, (∑ r : Fin d × Fin d, ad (U : Mat d) p r * dephasing d r j) =
      if j.1 = j.2 then ad (U : Mat d) p j else 0 := by
    intro j
    simp only [dephasing]
    rw [Finset.sum_eq_single j]
    · by_cases h : j.1 = j.2 <;> simp [h]
    · intro b _ hb; simp [hb]
    · simp
  simp only [beta, Matrix.mul_apply, h1, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m]
  · simp [ad, Matrix.conjTranspose_apply]; ring
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma bs_beta (U V : Unitary m) (U' V' : Unitary n) :
    binarySum (beta U V) (beta U' V') = beta (W U U') (W V V') := by
  apply bs_ext
  intro x y z w
  rw [bs_entry, beta_apply, ← (φ (m := m) (n := n)).sum_comp]
  simp only [W_apply]
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rcases w with w | w <;>
    simp [BS, Fintype.sum_sum_type, beta_apply]

lemma mtd_of {d : ℕ} {K : Type*} [Fintype K] (p : K → ℝ) (U V : K → Unitary d)
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (t : Map d) (ht : t = ∑ j, p j • beta (U j) (V j)) :
    MTD t := by
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => p (e.symm j), fun j => U (e.symm j), fun j => V (e.symm j),
    fun j => hp _, ?_, ?_⟩
  · rw [← hs]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · rw [ht]; exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

lemma bs_mtd {s : Map m} {t : Map n} (hs : MTD s) (ht : MTD t) : MTD (binarySum s t) := by
  obtain ⟨a, p, U, V, hp0, hp1, rfl⟩ := hs
  obtain ⟨b, q, U', V', hq0, hq1, rfl⟩ := ht
  refine mtd_of (fun x : Fin a × Fin b => p x.1 * q x.2) (fun x => W (U x.1) (U' x.2))
    (fun x => W (V x.1) (V' x.2)) (fun x => mul_nonneg (hp0 _) (hq0 _)) ?_ _ ?_
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hq1, mul_one, hp1]
  · rw [bs_comb p q hp1 hq1]
    simp only [bs_beta]

end X8BS

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8BS

open X8C6

variable {m n : ℕ}

lemma uc_of {d : ℕ} {K : Type*} [Fintype K] (G : K → Mat d) (h1 : ∑ k, (G k)ᴴ * G k = 1)
    (h2 : ∑ k, G k * (G k)ᴴ = 1) : UnitalChannel (∑ k, ad (G k)) := by
  refine ⟨isChannel_of_kraus G h1 _ fun ρ => ?_, ?_⟩
  · rw [am_sum]; simp only [am_ad, QAlgorithms.krausApply]
  · rw [am_sum]; simp only [am_ad, Matrix.mul_one]; exact h2

lemma unital_sum {d a : ℕ} (E : Fin a → Mat d) (h : UnitalChannel (∑ j, ad (E j))) :
    ∑ j, E j * (E j)ᴴ = 1 := by
  have := h.2
  rw [am_sum] at this
  simpa only [am_ad, Matrix.mul_one] using this

lemma emb_add (A B : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) : emb (A + B) = emb A + emb B := by
  simp only [emb, map_add]

def Gk {a b : ℕ} (E : Fin a → Mat m) (F : Fin b → Mat n) : Fin a ⊕ Fin b → Mat (m + n)
  | .inl i => emb (Matrix.fromBlocks (E i) 0 0 0)
  | .inr j => emb (Matrix.fromBlocks 0 0 0 (F j))

lemma bs_repr {a b : ℕ} (E : Fin a → Mat m) (F : Fin b → Mat n) :
    binarySum (∑ i, ad (E i)) (∑ j, ad (F j)) = ∑ k, ad (Gk E F k) := by
  apply bs_ext
  intro x y z w
  rw [bs_entry, Matrix.sum_apply, Fintype.sum_sum_type]
  simp only [Gk, ad_apply, emb_apply]
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rcases w with w | w <;>
    simp [BS, Matrix.sum_apply, ad_apply]

lemma sumG1 {a b : ℕ} (E : Fin a → Mat m) (F : Fin b → Mat n)
    (hE : ∑ i, (E i)ᴴ * E i = 1) (hF : ∑ j, (F j)ᴴ * F j = 1) :
    ∑ k, (Gk E F k)ᴴ * Gk E F k = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [Gk, emb_ct, emb_mul, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  rw [← emb_sum, ← emb_sum, ← emb_add, ← emb_one]
  congr 1
  ext u v
  rcases u with u | u <;> rcases v with v | v <;>
    simp [Matrix.sum_apply, Matrix.one_apply] <;>
    first
      | rw [← Matrix.sum_apply, hE, Matrix.one_apply]
      | rw [← Matrix.sum_apply, hF, Matrix.one_apply]

lemma sumG2 {a b : ℕ} (E : Fin a → Mat m) (F : Fin b → Mat n)
    (hE : ∑ i, E i * (E i)ᴴ = 1) (hF : ∑ j, F j * (F j)ᴴ = 1) :
    ∑ k, Gk E F k * (Gk E F k)ᴴ = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [Gk, emb_ct, emb_mul, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  rw [← emb_sum, ← emb_sum, ← emb_add, ← emb_one]
  congr 1
  ext u v
  rcases u with u | u <;> rcases v with v | v <;>
    simp [Matrix.sum_apply, Matrix.one_apply] <;>
    first
      | rw [← Matrix.sum_apply, hE, Matrix.one_apply]
      | rw [← Matrix.sum_apply, hF, Matrix.one_apply]

lemma fixP {a b : ℕ} (E : Fin a → Mat m) (F : Fin b → Mat n) (hE : ∑ i, E i * (E i)ᴴ = 1) :
    applyMap (∑ k, ad (Gk E F k)) (emb (Matrix.fromBlocks 1 0 0 0)) =
      emb (Matrix.fromBlocks 1 0 0 0) := by
  rw [am_sum, Fintype.sum_sum_type]
  simp only [am_ad, Gk, emb_ct, emb_mul, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one]
  rw [← emb_sum, ← emb_sum, ← emb_add]
  congr 1
  ext u v
  rcases u with u | u <;> rcases v with v | v <;>
    simp [Matrix.sum_apply, ← hE]

theorem x8_616 (hm : 0 < m) (hn : 0 < n)
    (t : Map m) (s : Map n) (ht : UnitalChannel t) (hs : UnitalChannel s)
    (hpt : Primitive t) (hps : Primitive s) :
    UnitalChannel (binarySum t s) ∧ Eventually MTD (binarySum t s) ∧
      ¬ Primitive (binarySum t s) := by
  obtain ⟨a, E, hE, rfl⟩ := kraus_form ht
  obtain ⟨b, F, hF, rfl⟩ := kraus_form hs
  have hE2 := unital_sum E ht
  have hF2 := unital_sum F hs
  have huc : UnitalChannel (binarySum (∑ i, ad (E i)) (∑ j, ad (F j))) := by
    rw [bs_repr]; exact uc_of _ (sumG1 E F hE hF) (sumG2 E F hE2 hF2)
  refine ⟨huc, ?_, ?_⟩
  · obtain ⟨n1, hn1, h1⟩ := corollary_6_15 hm _ ht hpt
    obtain ⟨n2, hn2, h2⟩ := corollary_6_15 hn _ hs hps
    refine ⟨max n1 n2, le_max_of_le_left hn1, fun k hk => ?_⟩
    rw [bs_pow _ _ k (le_trans hn1 (le_of_max_le_left hk))]
    exact bs_mtd (h1 k (le_of_max_le_left hk)) (h2 k (le_of_max_le_right hk))
  · intro hprim
    set P := emb (Matrix.fromBlocks (1 : Mat m) 0 0 (0 : Mat n))
    have hP : P ∈ peripheral (binarySum (∑ i, ad (E i)) (∑ j, ad (F j))) := by
      refine Submodule.subset_span ⟨1, by simp, ?_⟩
      rw [one_smul, bs_repr]
      exact fixP E F hE2
    rw [hprim, scalars, Submodule.mem_span_singleton] at hP
    obtain ⟨c, hc⟩ := hP
    have e1 := congrFun (congrFun hc (φ (Sum.inl ⟨0, hm⟩))) (φ (Sum.inl ⟨0, hm⟩))
    have e2 := congrFun (congrFun hc (φ (Sum.inr ⟨0, hn⟩))) (φ (Sum.inr ⟨0, hn⟩))
    simp only [P, emb_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] at e1 e2
    rw [e1] at e2
    exact one_ne_zero e2

end X8BS

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (t : Map m) (s : Map n) (ht : UnitalChannel t) (hs : UnitalChannel s)
    (hpt : Primitive t) (hps : Primitive s) :
    UnitalChannel (binarySum t s) ∧ Eventually MTD (binarySum t s) ∧
      ¬ Primitive (binarySum t s) :=
  QAlgorithms.Papers.Independent.Information100.P26.X8BS.x8_616 hm hn t s ht hs hpt hps
