-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.graph_encoding_covariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:19:58.716998+00:00
-- url     : https://prove2.me/submissions/0b41c79b-940f-446f-86a3-6092baa0e215

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms

open scoped Matrix

lemma p50h_natToBits (n : ℕ) (x : Qubits n) : QAlgorithms.natToBits n (bitsEquivFin n x) = x := by
  unfold QAlgorithms.natToBits
  have : (⟨(bitsEquivFin n x : ℕ) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ : Fin (2 ^ n)) = bitsEquivFin n x := by
    ext; simp [Nat.mod_eq_of_lt (bitsEquivFin n x).isLt]
  rw [this, Equiv.symm_apply_apply]

lemma p50h_emb_apply {n : ℕ} (i : Fin n) (A : Mat Bool) (x y : Qubits n) :
    siteEmbedding i A x y = if (∀ l, l ≠ i → x l = y l) then A (x i) (y i) else 0 := by
  simp only [siteEmbedding, QAlgorithms.Papers.Independent.Renew46.P24.siteOperator, p50h_natToBits]
  split_ifs with h
  · rw [Finset.prod_eq_one, mul_one]
    intro l _
    by_cases hl : l = i
    · simp [hl]
    · simp [hl, h l hl]
  · push_neg at h
    obtain ⟨l, hl, hxy⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl, hxy]), mul_zero]

lemma p50h_conj_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (M : Mat (Qubits n)) (y y' : Qubits n) :
    conjSuperop (sitePermutation p) M y y' = M (y ∘ p) (y' ∘ p) := by
  have hiff : ∀ y x : Qubits n, (y = x ∘ p.symm) ↔ (x = y ∘ p) := by
    intro y x
    constructor
    · rintro rfl; funext l; simp
    · rintro rfl; funext l; simp
  simp only [conjSuperop, Matrix.mul_apply, sitePermutation, Matrix.conjTranspose_apply]
  simp only [hiff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma p50h_conjT {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (sitePermutation p)ᴴ = sitePermutation p.symm := by
  ext y x
  simp only [sitePermutation, Matrix.conjTranspose_apply, apply_ite star, star_one, star_zero]
  apply if_congr _ rfl rfl
  constructor
  · rintro rfl; funext l; simp
  · rintro rfl; funext l; simp

lemma p50h_unit1 {n : ℕ} (p : Equiv.Perm (Fin n)) :
    sitePermutation p * (sitePermutation p)ᴴ = 1 := by
  have := p50h_conj_apply p 1
  ext y y'
  have h2 := this y y'
  simp only [conjSuperop, Matrix.mul_one] at h2
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  apply if_congr _ rfl rfl
  constructor
  · intro h; funext l; simpa using congrFun h (p.symm l)
  · rintro rfl; rfl

lemma p50h_unit2 {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (sitePermutation p)ᴴ * sitePermutation p = 1 := by
  have := p50h_unit1 p.symm
  rw [p50h_conjT, Equiv.symm_symm] at this
  rw [p50h_conjT]; exact this

lemma p50h_conj_mul {n : ℕ} (p : Equiv.Perm (Fin n)) (A B : Mat (Qubits n)) :
    conjSuperop (sitePermutation p) (A * B) =
      conjSuperop (sitePermutation p) A * conjSuperop (sitePermutation p) B := by
  simp only [conjSuperop]
  calc sitePermutation p * (A * B) * (sitePermutation p)ᴴ
      = sitePermutation p * A * ((sitePermutation p)ᴴ * sitePermutation p) * B * (sitePermutation p)ᴴ := by
        rw [p50h_unit2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma p50h_conj_add {n : ℕ} (p : Equiv.Perm (Fin n)) (A B : Mat (Qubits n)) :
    conjSuperop (sitePermutation p) (A + B) =
      conjSuperop (sitePermutation p) A + conjSuperop (sitePermutation p) B := by
  simp only [conjSuperop, Matrix.mul_add, Matrix.add_mul]

lemma p50h_conj_smul {n : ℕ} (p : Equiv.Perm (Fin n)) (c : ℂ) (A : Mat (Qubits n)) :
    conjSuperop (sitePermutation p) (c • A) = c • conjSuperop (sitePermutation p) A := by
  simp only [conjSuperop, Matrix.mul_smul, Matrix.smul_mul]

lemma p50h_conj_sum {n : ℕ} (p : Equiv.Perm (Fin n)) {ι : Type*} (s : Finset ι) (f : ι → Mat (Qubits n)) :
    conjSuperop (sitePermutation p) (∑ i ∈ s, f i) = ∑ i ∈ s, conjSuperop (sitePermutation p) (f i) := by
  simp only [conjSuperop, Matrix.mul_sum, Matrix.sum_mul]

lemma p50h_conj_ite {n : ℕ} (p : Equiv.Perm (Fin n)) (c : Prop) [Decidable c] (A : Mat (Qubits n)) :
    conjSuperop (sitePermutation p) (if c then A else 0) = if c then conjSuperop (sitePermutation p) A else 0 := by
  split_ifs <;> simp [conjSuperop]

lemma p50h_conj_emb {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) (A : Mat Bool) :
    conjSuperop (sitePermutation p) (siteEmbedding i A) = siteEmbedding (p i) A := by
  ext y y'
  rw [p50h_conj_apply, p50h_emb_apply, p50h_emb_apply]
  simp only [Function.comp_apply]
  apply if_congr _ rfl rfl
  constructor
  · intro h m hm
    have := h (p.symm m) (by intro h'; apply hm; rw [← h']; simp)
    simpa using this
  · intro h l hl
    exact h (p l) (by intro h'; exact hl (p.injective h'))

lemma p50h_emb_mul {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B : Mat Bool) (x y : Qubits n) :
    (siteEmbedding i A * siteEmbedding j B) x y =
      if (∀ l, l ≠ i → l ≠ j → x l = y l) then A (x i) (y i) * B (x j) (y j) else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Function.update x i (y i))]
  · rw [p50h_emb_apply, p50h_emb_apply]
    simp only [Function.update_self, Function.update_of_ne hij.symm]
    by_cases h : ∀ l, l ≠ i → l ≠ j → x l = y l
    · rw [if_pos h, if_pos, if_pos]
      · intro l hl
        by_cases hli : l = i
        · subst hli; simp
        · rw [Function.update_of_ne hli]; exact h l hli hl
      · intro l hl; rw [Function.update_of_ne hl]
    · rw [if_neg h]
      by_cases h1 : ∀ l, l ≠ j → Function.update x i (y i) l = y l
      · exfalso; apply h; intro l hli hlj
        have := h1 l hlj; rwa [Function.update_of_ne hli] at this
      · rw [if_neg h1, mul_zero]
  · intro z _ hz
    rw [p50h_emb_apply, p50h_emb_apply]
    by_cases h1 : ∀ l, l ≠ i → x l = z l
    · by_cases h2 : ∀ l, l ≠ j → z l = y l
      · exfalso; apply hz; funext l
        by_cases hli : l = i
        · subst hli; simp; exact h2 l hij
        · rw [Function.update_of_ne hli]; exact (h1 l hli).symm
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma p50h_emb_comm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B : Mat Bool) :
    siteEmbedding i A * siteEmbedding j B = siteEmbedding j B * siteEmbedding i A := by
  ext x y
  rw [p50h_emb_mul i j hij, p50h_emb_mul j i hij.symm]
  apply if_congr _ (mul_comm _ _) rfl
  constructor
  · intro h l h1 h2; exact h l h2 h1
  · intro h l h1 h2; exact h l h2 h1

lemma p50h_two_sum {n : ℕ} {M : Type*} [AddCommGroup M] (σ : Equiv.Perm (Fin n))
    (R : Fin n → Fin n → Prop) (hR : ∀ i j, R i j → R j i) (hirr : ∀ i, ¬ R i i)
    (g : Fin n → Fin n → M) (hg : ∀ i j, R i j → g i j = g j i)
    (c : Fin n → Fin n → Prop) [∀ i j, Decidable (c i j)] [∀ i j, Decidable (R i j)]
    (hc : ∀ i j, c i j ↔ σ i < σ j ∧ R i j) :
    (∑ i, ∑ j, if c i j then g i j else 0) + (∑ i, ∑ j, if c i j then g i j else 0) =
      ∑ i, ∑ j, if R i j then g i j else 0 := by
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hij : R i j
  · have hne : σ i ≠ σ j := by
      intro h; have := σ.injective h; subst this; exact hirr _ hij
    rw [if_pos hij]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [if_pos ((hc i j).2 ⟨hlt, hij⟩), if_neg (fun h => absurd ((hc j i).1 h).1 (not_lt.2 hlt.le)), add_zero]
    · rw [if_neg (fun h => absurd ((hc i j).1 h).1 (not_lt.2 hlt.le)), if_pos ((hc j i).2 ⟨hlt, hR i j hij⟩),
        zero_add, hg i j hij]
  · rw [if_neg hij, if_neg (fun h => hij ((hc i j).1 h).2),
      if_neg (fun h => hij (hR j i ((hc j i).1 h).2)), add_zero]

lemma p50h_sum_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    (R : Fin n → Fin n → Prop) (hR : ∀ i j, R i j → R j i) (hirr : ∀ i, ¬ R i i)
    (g : Fin n → Fin n → Mat (Qubits n)) (hg : ∀ i j, R i j → g i j = g j i)
    (c d : Fin n → Fin n → Prop) [∀ i j, Decidable (c i j)] [∀ i j, Decidable (d i j)]
    (hc : ∀ i j, c i j ↔ σ i < σ j ∧ R i j) (hd : ∀ i j, d i j ↔ i < j ∧ R i j) :
    (∑ i, ∑ j, if c i j then g i j else 0) = ∑ i, ∑ j, if d i j then g i j else 0 := by
  classical
  have h1 := p50h_two_sum σ R hR hirr g hg c hc
  have h2 := p50h_two_sum 1 R hR hirr g hg d (by simpa using hd)
  rw [← h2, ← two_smul ℂ, ← two_smul ℂ] at h1
  exact smul_right_injective _ (two_ne_zero) h1

end QAlgorithms.Papers.Independent.Advance50.P50

end

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50 in
open QAlgorithms.Papers.Independent.Information100.P63 (Mat) in
open scoped Matrix in
theorem solution {n : ℕ} (G H : SimpleGraph (Fin n))
    (p : Equiv.Perm (Fin n)) (hiso : ∀ i j, H.Adj (p i) (p j) ↔ G.Adj i j)
    (t : ℝ) (ht : 0 < t) (rho : Mat (Qubits n)) (hrho : IsDensityMatrix rho)
    (hfixed : ∀ q : Equiv.Perm (Fin n), conjSuperop (sitePermutation q) rho = rho) :
    graphHamiltonian H = conjSuperop (sitePermutation p) (graphHamiltonian G) ∧
    graphEvolution H t = conjSuperop (sitePermutation p) (graphEvolution G t) ∧
    graphEncoding H t rho = conjSuperop (sitePermutation p) (graphEncoding G t rho) := by
  classical
  have hHam : graphHamiltonian H = conjSuperop (sitePermutation p) (graphHamiltonian G) := by
    unfold graphHamiltonian
    simp only [p50h_conj_add, p50h_conj_sum, p50h_conj_ite, p50h_conj_mul,
      p50h_conj_emb]
    congr 1
    · rw [← Equiv.sum_comp p]
      refine (Finset.sum_congr rfl fun i _ => (Equiv.sum_comp p _).symm).trans ?_
      exact p50h_sum_eq p G.Adj (fun i j h => h.symm) (fun i => G.irrefl)
        (fun i j => siteEmbedding (p i) pauliZ * siteEmbedding (p j) pauliZ)
        (fun i j h => p50h_emb_comm _ _ (fun h' => G.ne_of_adj h (p.injective h')) _ _)
        _ _ (fun i j => by rw [hiso]) (fun i j => Iff.rfl)
    · exact (Equiv.sum_comp p (fun i => siteEmbedding i pauliX)).symm
  set P := sitePermutation p with hP
  have u1 := p50h_unit1 p
  have u2 := p50h_unit2 p
  let u : (Mat (Qubits n))ˣ := ⟨P, Pᴴ, u1, u2⟩
  have hEv : graphEvolution H t = conjSuperop P (graphEvolution G t) := by
    simp only [graphEvolution, hHam, conjSuperop]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    exact Matrix.exp_units_conj u _
  refine ⟨hHam, hEv, ?_⟩
  have hr : Pᴴ * rho * P = rho := by
    have := hfixed p
    simp only [conjSuperop] at this
    calc Pᴴ * rho * P = Pᴴ * (P * rho * Pᴴ) * P := by rw [this]
      _ = (Pᴴ * P) * rho * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = rho := by rw [u2]; simp
  simp only [graphEncoding, hEv, conjSuperop, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc P * graphEvolution G t * Pᴴ * rho * (P * ((graphEvolution G t)ᴴ * Pᴴ))
      = P * graphEvolution G t * (Pᴴ * rho * P) * (graphEvolution G t)ᴴ * Pᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hr]; simp only [Matrix.mul_assoc]
