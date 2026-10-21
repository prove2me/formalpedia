-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P16.canonical_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:29:28.127027+00:00
-- url     : https://prove2.me/submissions/af62d6d4-3ef5-40aa-a3d5-688746b1fde9

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16
noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

open scoped ComplexConjugate


lemma g66j_pvc {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (x : Word n d) :
    coherentTensor n phi x = ∏ k, phi (x k) := rfl

lemma g66j_PD {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    boseProjector d n * pureDensity (coherentTensor n phi) = pureDensity (coherentTensor n phi) := by
  have hp : ∀ p : Equiv.Perm (Fin n),
      Schur.tensorPermutation d n p * pureDensity (coherentTensor n phi) =
        pureDensity (coherentTensor n phi) := by
    intro p
    ext y z
    simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, pureDensity, ite_mul,
      one_mul, zero_mul]
    rw [Finset.sum_eq_single (y ∘ p)]
    · rw [if_pos (by ext k; simp)]
      congr 1
      simp only [g66j_pvc, Function.comp_apply]
      exact Equiv.prod_comp p (fun k => phi (y k))
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [h]; ext k; simp
    · simp
  rw [boseProjector, Matrix.smul_mul, Finset.sum_mul]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

lemma g66j_DP {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    pureDensity (coherentTensor n phi) * boseProjector d n = pureDensity (coherentTensor n phi) := by
  have hp : ∀ p : Equiv.Perm (Fin n),
      pureDensity (coherentTensor n phi) * Schur.tensorPermutation d n p =
        pureDensity (coherentTensor n phi) := by
    intro p
    ext y z
    simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, pureDensity, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_eq_single (z ∘ p.symm)]
    · rw [if_pos rfl]
      congr 2
      simp only [g66j_pvc, Function.comp_apply]
      exact Equiv.prod_comp p.symm (fun k => phi (z k))
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [h]
    · simp
  rw [boseProjector, Matrix.mul_smul, Finset.mul_sum]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

def g66j_split {d N M : ℕ} (h : N ≤ M) : Word M d ≃ Word N d × Word (M - N) d where
  toFun x := (fun k => x ⟨k.val, by omega⟩, fun k => x ⟨N + k.val, by omega⟩)
  invFun z := fun j => if hj : j.val < N then z.1 ⟨j.val, hj⟩ else z.2 ⟨j.val - N, by omega⟩
  left_inv x := by
    funext j
    by_cases hj : j.val < N
    · simp [hj]
    · simp only [hj, dif_neg, not_false_eq_true]
      congr 1; ext; simp; omega
  right_inv z := by
    ext k
    · simp
    · simp

lemma g66j_pv_split {d N M : ℕ} (h : N ≤ M) (phi : EuclideanSpace ℂ (Fin d)) (x : Word M d) :
    coherentTensor M phi x = coherentTensor N phi (g66j_split h x).1 *
      coherentTensor (M - N) phi (g66j_split h x).2 := by
  simp only [g66j_pvc, g66j_split, Equiv.coe_fn_mk]
  have hM : N + (M - N) = M := by omega
  rw [← Fin.prod_congr' (fun j => phi (x j)) hM, Fin.prod_univ_add]
  rfl

lemma g66j_norm1 {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    ∑ u : Word n d, coherentTensor n phi u * conj (coherentTensor n phi u) = 1 := by
  simp only [g66j_pvc, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => phi a * conj (phi a))]
  have : ∑ a, phi a * conj (phi a) = 1 := by
    have h2 : ‖phi‖ ^ 2 = 1 := by rw [hphi]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simp only [Complex.mul_conj']
    exact_mod_cast h2
  simp [this]

lemma g66j_trW {d N M : ℕ} (h : N ≤ M) (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    (pureDensity (coherentTensor M phi) *
      tensorWithIdentity h (pureDensity (coherentTensor N phi))).trace = 1 := by
  set e := g66j_split (d := d) h
  set vN := coherentTensor N phi
  set vT := coherentTensor (M - N) phi
  let G : Word N d × Word (M - N) d → Word N d × Word (M - N) d → ℂ := fun z z' =>
    (vN z.1 * vT z.2) * conj (vN z'.1 * vT z'.2) * (vN z'.1 * conj (vN z.1)) *
      (if z'.2 = z.2 then 1 else 0)
  have key : ∀ x y : Word M d, pureDensity (coherentTensor M phi) x y *
      tensorWithIdentity h (pureDensity (coherentTensor N phi)) y x = G (e x) (e y) := by
    intro x y
    simp only [pureDensity, tensorWithIdentity, Matrix.of_apply, G]
    rw [g66j_pv_split h phi x, g66j_pv_split h phi y, Finset.prod_boole]
    have hc : (∀ k ∈ (Finset.univ : Finset (Fin (M - N))), y ⟨N + k.val, by omega⟩ = x ⟨N + k.val, by omega⟩) ↔ (e y).2 = (e x).2 := by
      simp only [Finset.mem_univ, true_implies, e, g66j_split, Equiv.coe_fn_mk, funext_iff]
    by_cases h1 : (e y).2 = (e x).2
    · rw [if_pos (hc.2 h1), if_pos h1]; simp only [e, vN, vT, g66j_split, Equiv.coe_fn_mk]; ring
    · rw [if_neg (fun h' => h1 (hc.1 h')), if_neg h1]; ring
  have ht : (pureDensity (coherentTensor M phi) *
      tensorWithIdentity h (pureDensity (coherentTensor N phi))).trace = ∑ x, ∑ y, G (e x) (e y) := by
    unfold Matrix.trace
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun y _ => key x y)
  rw [ht]
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  conv_lhs => arg 2; ext z; rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type, G, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hN := g66j_norm1 (n := N) phi hphi
  have hT := g66j_norm1 (n := M - N) phi hphi
  calc _ = ∑ u, ∑ w, ∑ u', (vN u * conj (vN u)) * ((vT w * conj (vT w)) * (vN u' * conj (vN u'))) := by
        refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun w _ =>
          Finset.sum_congr rfl (fun u' _ => ?_)))
        simp only [map_mul]; ring
    _ = 1 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        rw [hT, one_mul, hN, one_mul]

theorem solution (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    (∀ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 →
      cloningOverlap (canonicalCloner hNM.le) phi =
        (boseDimension d N : ℝ) / boseDimension d M) ∧
    cloningFidelity (canonicalCloner (d := d) hNM.le) =
      (boseDimension d N : ℝ) / boseDimension d M := by
  have hov : ∀ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 →
      cloningOverlap (canonicalCloner hNM.le) phi =
        (boseDimension d N : ℝ) / boseDimension d M := by
    intro phi hphi
    unfold cloningOverlap canonicalCloner
    rw [g66j_PD, g66j_DP, Matrix.mul_smul, Matrix.trace_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      g66j_DP, Matrix.trace_mul_cycle, g66j_PD, g66j_trW hNM.le phi hphi]
    rw [smul_eq_mul, mul_one, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div, Complex.ofReal_re]
  refine ⟨hov, ?_⟩
  have hS : {r : ℝ | ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧
      r = cloningOverlap (canonicalCloner (d := d) hNM.le) phi} =
      {(boseDimension d N : ℝ) / boseDimension d M} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨phi, hphi, rfl⟩; exact hov phi hphi
    · rintro rfl
      refine ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp, (hov _ (by simp)).symm⟩
  unfold cloningFidelity
  rw [hS, csInf_singleton]
