-- Prove2me | solution 1 for SuperRamanujan227.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:56:27.775838+00:00
-- url     : https://prove2.me/submissions/fd840eed-b38d-41b9-9fc9-139539bd407c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_Multigraph
import Definitions.Def_SuperRamanujan227_Main_Jacobi
import Definitions.Def_SuperRamanujan227_Main_FiniteFreeConvolution
import Theorems.Thm_SuperRamanujan227_Main_lemma_2_5
import Theorems.Thm_SuperRamanujan227_Main_lemma_5_4
import Theorems.Thm_SuperRamanujan227_Main_claim_5_3
import Theorems.Thm_SuperRamanujan227_Main_lemma_2_2
import Theorems.Thm_SuperRamanujan227_Main_claim_5_6

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Base
open SuperRamanujan227.Main

lemma alpha1_def (P : ℝ[X]) : kthLargestRoot P 1 = (P.roots.sort (· ≥ ·)).getD 0 0 := by
  simp [kthLargestRoot]

lemma sort_cons_form {P : ℝ[X]} (hne : P.roots ≠ 0) :
    ∃ a l, P.roots.sort (· ≥ ·) = a :: l := by
  have hlen : (P.roots.sort (· ≥ ·)).length ≠ 0 := by
    rw [Multiset.length_sort]; simpa using hne
  cases hl : P.roots.sort (· ≥ ·) with
  | nil => rw [hl] at hlen; simp at hlen
  | cons a l => exact ⟨a, l, rfl⟩

lemma alpha1_mem {P : ℝ[X]} (hne : P.roots ≠ 0) : kthLargestRoot P 1 ∈ P.roots := by
  rw [alpha1_def]
  obtain ⟨a, l, hl⟩ := sort_cons_form hne
  rw [hl]
  simp only [List.getD_cons_zero]
  rw [← Multiset.mem_sort (· ≥ ·), hl]
  simp

lemma le_alpha1 {P : ℝ[X]} (hne : P.roots ≠ 0) : ∀ r ∈ P.roots, r ≤ kthLargestRoot P 1 := by
  intro r hr
  rw [alpha1_def]
  obtain ⟨a, l, hl⟩ := sort_cons_form hne
  have hp := Multiset.pairwise_sort P.roots (· ≥ ·)
  rw [hl] at hp
  have hr' : r ∈ a :: l := by rw [← hl]; exact (Multiset.mem_sort (· ≥ ·)).mpr hr
  rw [hl]
  simp only [List.getD_cons_zero]
  rcases List.mem_cons.mp hr' with h | h
  · rw [h]
  · exact (List.pairwise_cons.mp hp).1 r h

lemma rr_roots_ne {P : ℝ[X]} (hP : RealRooted P) (h1 : 1 ≤ P.natDegree) : P.roots ≠ 0 := by
  intro h
  have := hP.2
  rw [h] at this
  simp at this
  omega

end SuperRamanujan227.Dev.Base
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Deriv
open SuperRamanujan227.Main SuperRamanujan227.Dev.Base

lemma natDeg_iter (P : ℝ[X]) (hP : P ≠ 0) (k : ℕ) (hk : k ≤ P.natDegree) :
    (derivative^[k] P).natDegree = P.natDegree - k ∧
    (derivative^[k] P).leadingCoeff = (P.natDegree.descFactorial k : ℝ) * P.leadingCoeff := by
  have hc : (derivative^[k] P).coeff (P.natDegree - k) =
      (P.natDegree.descFactorial k : ℝ) * P.leadingCoeff := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul]
    rfl
  have hne : (derivative^[k] P).coeff (P.natDegree - k) ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne')
      (leadingCoeff_ne_zero.mpr hP)
  have hdeg : (derivative^[k] P).natDegree = P.natDegree - k :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_iterate_derivative P k) hne
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hc]⟩

lemma rr_deriv {P : ℝ[X]} (hP : RealRooted P) (h1 : 1 ≤ P.natDegree) :
    RealRooted (derivative P) := by
  have hd0 : derivative P ≠ 0 := by
    intro h
    have := (derivative_eq_zero).mp h
    omega
  refine ⟨hd0, ?_⟩
  have h2 := card_roots_le_derivative P
  have h3 := hP.2
  have h4 := natDegree_derivative_le P
  have h5 := card_roots' (derivative P)
  omega

lemma rr_iter {P : ℝ[X]} (hP : RealRooted P) (k : ℕ) (hk : k ≤ P.natDegree) :
    RealRooted (derivative^[k] P) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    have ih' := ih (by omega)
    rw [Function.iterate_succ_apply']
    apply rr_deriv ih'
    rw [(natDeg_iter P hP.1 k (by omega)).1]
    omega

end SuperRamanujan227.Dev.Deriv
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Ord2
open SuperRamanujan227.Main

lemma list_kl (l : List ℝ) (hp : l.Pairwise (· ≥ ·)) (q : ℝ) (h2 : 2 ≤ l.length) :
    q < l.getD 1 0 ↔ 2 ≤ (l.filter (fun x => decide (q < x))).length := by
  match l, hp, h2 with
  | a :: b :: rest, hp, _ =>
    have hab : a ≥ b := (List.pairwise_cons.mp hp).1 b (by simp)
    have hrest : ∀ x ∈ rest, b ≥ x := (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).1
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    by_cases hq : q < b
    · have : q < a := lt_of_lt_of_le hq hab
      simp [List.filter_cons, hq, this]
    · push Not at hq
      have : (rest.filter (fun x => decide (q < x))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have := hrest x hx
        simp; linarith
      simp only [List.filter_cons, this]
      simp [not_lt.mpr hq]
      split_ifs <;> simp

noncomputable def sorted (S : Multiset ℝ) : List ℝ := S.sort (· ≥ ·)

lemma card_filter_eq (S : Multiset ℝ) (q : ℝ) :
    Multiset.card (S.filter (fun x => q < x)) = ((sorted S).filter (fun x => decide (q < x))).length := by
  have h : (↑(sorted S) : Multiset ℝ) = S := Multiset.sort_eq _ _
  conv_lhs => rw [← h]
  rw [Multiset.filter_coe, Multiset.coe_card]

lemma kl_multiset (S : Multiset ℝ) (q : ℝ) (h2 : 2 ≤ Multiset.card S) :
    q < (sorted S).getD 1 0 ↔ 2 ≤ Multiset.card (S.filter (fun x => q < x)) := by
  rw [card_filter_eq]
  have hlen : (sorted S).length = Multiset.card S := by unfold sorted; exact Multiset.length_sort _
  exact list_kl (sorted S) (by unfold sorted; exact Multiset.pairwise_sort S (· ≥ ·)) q (by omega)

lemma second_le_of_filter (S : Multiset ℝ) (q : ℝ) (h2 : 2 ≤ Multiset.card S)
    (h : Multiset.card (S.filter (fun x => q < x)) ≤ 1) : (sorted S).getD 1 0 ≤ q := by
  by_contra hc
  rw [not_le, kl_multiset S q h2] at hc
  omega

lemma second_mono (S S' : Multiset ℝ) (hle : S ≤ S') (h2 : 2 ≤ Multiset.card S) :
    (sorted S).getD 1 0 ≤ (sorted S').getD 1 0 := by
  have h2' : 2 ≤ Multiset.card S' := le_trans h2 (Multiset.card_le_card hle)
  by_contra hc
  rw [not_le] at hc
  set q := (sorted S').getD 1 0
  have h1 := (kl_multiset S q h2).mp hc
  have h3 : Multiset.card (S.filter (fun x => q < x)) ≤ Multiset.card (S'.filter (fun x => q < x)) :=
    Multiset.card_le_card (Multiset.monotone_filter_left _ hle)
  have h4 : ¬ (q < (sorted S').getD 1 0) := lt_irrefl _
  rw [kl_multiset S' q h2'] at h4
  omega

lemma kth2_def (P : ℝ[X]) : kthLargestRoot P 2 = (sorted P.roots).getD 1 0 := by
  simp [kthLargestRoot, sorted]

end SuperRamanujan227.Dev.Ord2
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Scale
open SuperRamanujan227.Main

lemma charpoly_smul {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (hc : c ≠ 0) :
    (c • A).charpoly = C (c ^ m) * A.charpoly.comp (C c⁻¹ * X) := by
  let φ : ℝ[X] →+* ℝ[X] := Polynomial.compRingHom (C c⁻¹ * X)
  have h1 : (c • A).charmatrix = C c • φ.mapMatrix A.charmatrix := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, φ, Polynomial.coe_compRingHom_apply, sub_comp, X_comp, C_comp,
        smul_eq_mul]
      rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul, ← C_mul]
    · simp only [Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.smul_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, φ, Polynomial.coe_compRingHom_apply, neg_comp, C_comp,
        smul_eq_mul, Matrix.smul_apply]
      rw [mul_neg, ← C_mul]
  unfold Matrix.charpoly
  rw [h1, Matrix.det_smul, ← RingHom.map_det φ, ← C_pow, Fintype.card_fin]
  rfl

lemma aux_prod (c : ℝ) (hc : c ≠ 0) (s : Multiset ℝ) :
    C (c ^ Multiset.card s) * (s.map (fun r => (X - C r : ℝ[X]))).prod.comp (C c⁻¹ * X) =
      (s.map (fun r => (X - C (c * r) : ℝ[X]))).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, mul_comp, sub_comp, X_comp,
      C_comp]
    have h1 : (C c⁻¹ * X - C a : ℝ[X]) = C c⁻¹ * (X - C (c * a)) := by
      have : c⁻¹ * (c * a) = a := by field_simp
      rw [mul_sub, ← C_mul, this]
    have hcc : C (c ^ (Multiset.card s + 1)) * C c⁻¹ = C (c ^ Multiset.card s) := by
      rw [← C_mul]; congr 1; rw [pow_succ]; field_simp
    rw [h1]
    generalize (Multiset.map (fun r => X - C r) s).prod.comp (C c⁻¹ * X) = Pc at ih ⊢
    generalize (Multiset.map (fun r => X - C (c * r)) s).prod = Pi at ih ⊢
    calc C (c ^ (Multiset.card s + 1)) * (C c⁻¹ * (X - C (c * a)) * Pc)
        = (C (c ^ (Multiset.card s + 1)) * C c⁻¹) * ((X - C (c * a)) * Pc) := by ring
      _ = (X - C (c * a)) * (C (c ^ Multiset.card s) * Pc) := by rw [hcc]; ring
      _ = _ := by rw [ih]

lemma charpoly_smul_roots {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (hc : 0 < c)
    (hA : Multiset.card A.charpoly.roots = m) :
    (c • A).charpoly.roots = A.charpoly.roots.map (fun r => c * r) := by
  have hmonic := A.charpoly_monic
  have hdeg : A.charpoly.natDegree = m := by simp
  have hsplit := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic (by rw [hdeg]; exact hA)
  rw [charpoly_smul A c hc.ne']
  conv_lhs => rw [← hsplit]
  have h2 := aux_prod c hc.ne' A.charpoly.roots
  rw [hA] at h2
  rw [h2, show (Multiset.map (fun r => (X - C (c * r) : ℝ[X])) A.charpoly.roots) =
    Multiset.map (fun a => (X - C a : ℝ[X])) (A.charpoly.roots.map (fun r => c * r)) by
      rw [Multiset.map_map]; rfl, roots_multiset_prod_X_sub_C]

end SuperRamanujan227.Dev.Scale
end

section
set_option autoImplicit false
open Polynomial Matrix

namespace SuperRamanujan227.Dev.Mat1
open SuperRamanujan227.Main

def eN (n d : ℕ) : Fin (n * d) ≃ Fin n × Fin d := finProdFinEquiv.symm

def blk {n d : ℕ} (i : Fin (n * d)) : Fin n := (eN n d i).1

noncomputable def Umat (n d : ℕ) : Matrix (Fin (n * d)) (Fin n) ℝ :=
  Matrix.of fun i v => if blk i = v then 1 else 0

lemma card_blk (n d : ℕ) (v : Fin n) :
    (Finset.univ.filter (fun i : Fin (n * d) => blk i = v)).card = d := by
  have : (Finset.univ.filter (fun i : Fin (n * d) => blk i = v)).card =
      (Finset.univ.filter (fun p : Fin n × Fin d => p.1 = v)).card := by
    apply Finset.card_bij (fun i _ => eN n d i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro a _ b _ h; exact (eN n d).injective h
    · intro p hp
      refine ⟨(eN n d).symm p, ?_, by simp⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have := (Finset.mem_filter.mp hp).2
      simpa [blk] using this
  rw [this]
  have : (Finset.univ.filter (fun p : Fin n × Fin d => p.1 = v)) = {v} ×ˢ Finset.univ := by
    ext p; simp [Prod.ext_iff, eq_comm]
  rw [this]; simp

lemma UtU (n d : ℕ) : (Umat n d)ᵀ * Umat n d = (d : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext v w
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Umat, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have h1 : ∀ i : Fin (n * d), (if blk i = v then (1:ℝ) else 0) * (if blk i = w then 1 else 0) =
      if blk i = v ∧ blk i = w then 1 else 0 := by
    intro i; by_cases a : blk i = v <;> by_cases b : blk i = w <;> simp [a, b]
  simp only [h1]
  rw [Finset.sum_boole]
  by_cases hvw : v = w
  · subst hvw
    simp only [and_self, if_true, mul_one]
    rw [card_blk]
  · have : (Finset.univ.filter (fun i : Fin (n * d) => blk i = v ∧ blk i = w)) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩; exact hvw (h1.symm.trans h2)
    rw [this]; simp [hvw]


noncomputable def Vmat (n d : ℕ) : Matrix (Fin (n * d)) (Fin (n * d)) ℝ :=
  (((1 : ℝ) / d) • Umat n d) * (Umat n d)ᵀ

lemma V_charpoly (n d : ℕ) (hd : 0 < d) :
    (Vmat n d).charpoly = X ^ (n * d - n) * (X - 1) ^ n := by
  have h := charpoly_mul_comm' (((1 : ℝ) / d) • Umat n d) (Umat n d)ᵀ
  have hBA : (Umat n d)ᵀ * (((1 : ℝ) / d) • Umat n d) = 1 := by
    rw [Matrix.mul_smul, UtU, smul_smul]
    have : (1 : ℝ) / d * d = 1 := by field_simp
    rw [this, one_smul]
  rw [hBA, charpoly_one] at h
  simp only [Fintype.card_fin] at h
  have hle : n ≤ n * d := Nat.le_mul_of_pos_right n hd
  have : (X : ℝ[X]) ^ (n * d) = X ^ n * X ^ (n * d - n) := by rw [← pow_add]; congr 1; omega
  rw [this, mul_assoc] at h
  unfold Vmat
  exact mul_left_cancel₀ (pow_ne_zero n X_ne_zero) (by rw [h])

lemma V_symm (n d : ℕ) : (Vmat n d).IsSymm := by
  unfold Vmat Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul]

lemma V_psd (n d : ℕ) : (Vmat n d).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (Umat n d)
  have h2 := h.smul (show (0 : ℝ) ≤ 1 / d by positivity)
  unfold Vmat
  rw [Matrix.smul_mul]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h2

lemma V_row (n d : ℕ) (hd : 0 < d) :
    Vmat n d *ᵥ (fun _ => (1 : ℝ)) = (1 : ℝ) • (fun _ => (1 : ℝ)) := by
  unfold Vmat
  rw [← Matrix.mulVec_mulVec]
  have h1 : (Umat n d)ᵀ *ᵥ (fun _ => (1 : ℝ)) = (fun _ => (d : ℝ)) := by
    ext v
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Umat, Matrix.of_apply, mul_one]
    rw [Finset.sum_boole, card_blk]
  have h2 : (Umat n d) *ᵥ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Umat, Matrix.of_apply, mul_one]
    simp
  rw [h1]
  have : (fun _ : Fin n => (d : ℝ)) = (d : ℝ) • (fun _ : Fin n => (1 : ℝ)) := by ext; simp
  rw [this, Matrix.mulVec_smul, Matrix.smul_mulVec, h2]
  ext i
  have hd' : (d : ℝ) ≠ 0 := by positivity
  simp [hd']

end SuperRamanujan227.Dev.Mat1
end

section
set_option autoImplicit false
open Polynomial Matrix

namespace SuperRamanujan227.Dev.Mat2
open SuperRamanujan227.Main

def e2 {N k : ℕ} (hN : N = 2 * k) : Fin N ≃ Fin 2 × Fin k :=
  (finCongr hN).trans finProdFinEquiv.symm

def tau0 {N k : ℕ} (hN : N = 2 * k) : Equiv.Perm (Fin N) :=
  (e2 hN).trans ((Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl (Fin k))).trans (e2 hN).symm)

lemma tau0_invol {N k : ℕ} (hN : N = 2 * k) (i : Fin N) : tau0 hN (tau0 hN i) = i := by
  have h : ∀ p : Fin 2 × Fin k, Prod.map (Equiv.swap (0 : Fin 2) 1) id
      (Prod.map (Equiv.swap (0 : Fin 2) 1) id p) = p := by
    rintro ⟨a, c⟩; fin_cases a <;> simp
  simp [tau0, h]

lemma tau0_ne {N k : ℕ} (hN : N = 2 * k) (i : Fin N) : tau0 hN i ≠ i := by
  intro h
  have := congrArg (e2 hN) h
  simp [tau0] at this
  revert this
  generalize (e2 hN i) = p
  obtain ⟨a, c⟩ := p
  fin_cases a <;> simp

/-- the perfect matching matrix of an involution -/
noncomputable def Minv {N : ℕ} (τ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => if j = τ i then 1 else 0

noncomputable def Mgen {N k : ℕ} (hN : N = 2 * k) : Matrix (Fin N) (Fin N) ℝ := Minv (tau0 hN)

noncomputable def J2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

lemma Mgen_eq {N k : ℕ} (hN : N = 2 * k) :
    Mgen hN = (Matrix.blockDiagonal (fun _ : Fin k => J2)).submatrix (e2 hN) (e2 hN) := by
  ext i j
  obtain ⟨p, rfl⟩ := (e2 hN).symm.surjective i
  obtain ⟨q, rfl⟩ := (e2 hN).symm.surjective j
  obtain ⟨a, c⟩ := p
  obtain ⟨b, c'⟩ := q
  simp only [Mgen, Minv, Matrix.of_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply,
    Matrix.blockDiagonal_apply, tau0, Equiv.trans_apply, Equiv.prodCongr_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.map_apply, Equiv.refl_apply, Prod.mk.injEq]
  fin_cases a <;> fin_cases b <;> simp [J2, eq_comm]


lemma J2_charpoly : J2.charpoly = X ^ 2 - 1 := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  simp [J2, Matrix.charmatrix_apply]
  ring

lemma charpoly_blockDiag (k : ℕ) :
    (Matrix.blockDiagonal (fun _ : Fin k => J2)).charpoly = (X ^ 2 - 1) ^ k := by
  have h : (Matrix.blockDiagonal (fun _ : Fin k => J2)).charmatrix =
      Matrix.blockDiagonal (fun _ : Fin k => J2.charmatrix) := by
    refine Matrix.ext fun ⟨a, c⟩ ⟨b, c'⟩ => ?_
    by_cases hc : c = c'
    · subst hc
      simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
    · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, hc]
  unfold Matrix.charpoly
  rw [h, Matrix.det_blockDiagonal]
  have h2 : J2.charmatrix.det = X ^ 2 - 1 := J2_charpoly
  simp [h2]

lemma Mgen_charpoly {N k : ℕ} (hN : N = 2 * k) : (Mgen hN).charpoly = (X ^ 2 - 1) ^ k := by
  rw [Mgen_eq]
  have := Matrix.charpoly_reindex (e2 hN).symm (Matrix.blockDiagonal (fun _ : Fin k => J2))
  rw [charpoly_blockDiag] at this
  rw [← this]
  rfl

end SuperRamanujan227.Dev.Mat2
end

section
set_option autoImplicit false
open Polynomial Matrix

namespace SuperRamanujan227.Dev.Mat3
open SuperRamanujan227.Main SuperRamanujan227.Dev.Mat2

lemma permMat_entry {m : ℕ} (σ : Equiv.Perm (Fin m)) (i a : Fin m) :
    permMat σ i a = if a = σ i then 1 else 0 := by
  simp [permMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

lemma conj_entry {m : ℕ} (σ : Equiv.Perm (Fin m)) (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    (permMat σ * A * (permMat σ).transpose) i j = A (σ i) (σ j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, permMat_entry]
  simp

lemma conj_Minv {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permMat σ * Minv τ * (permMat σ).transpose = Minv (σ⁻¹ * τ * σ) := by
  ext i j
  rw [conj_entry]
  simp only [Minv, Matrix.of_apply]
  have : (σ j = τ (σ i)) ↔ (j = (σ⁻¹ * τ * σ) i) := by
    simp only [Equiv.Perm.mul_apply]
    exact (Equiv.Perm.eq_inv_iff_eq).symm
  simp only [this]

lemma Minv_symm {m : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : ∀ i, τ (τ i) = i) : (Minv τ).IsSymm := by
  ext i j
  simp only [Minv, Matrix.transpose_apply, Matrix.of_apply]
  have : (i = τ j) ↔ (j = τ i) := by
    constructor
    · intro h; rw [h, hτ]
    · intro h; rw [h, hτ]
  simp only [this]

lemma Minv_row {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Minv τ *ᵥ (fun _ => (1 : ℝ)) = (1 : ℝ) • (fun _ => (1 : ℝ)) := by
  ext i
  simp [Minv, Matrix.mulVec, dotProduct]

end SuperRamanujan227.Dev.Mat3
end

section
set_option autoImplicit false
open Polynomial Matrix

namespace SuperRamanujan227.Dev.Mat4
open SuperRamanujan227.Main SuperRamanujan227.Dev.Mat1 SuperRamanujan227.Dev.Mat2

lemma entry_UMU (n d : ℕ) (τ : Equiv.Perm (Fin (n * d))) (u v : Fin n) :
    ((Umat n d)ᵀ * Minv τ * Umat n d) u v =
      ((Finset.univ.filter (fun i : Fin (n * d) => blk i = u ∧ blk (τ i) = v)).card : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Umat, Matrix.of_apply, Minv]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h : ∀ i : Fin (n * d), (∑ j : Fin (n * d),
      (if blk i = u then (1:ℝ) else 0) * (if j = τ i then 1 else 0) * (if blk j = v then 1 else 0)) =
      if blk i = u ∧ blk (τ i) = v then 1 else 0 := by
    intro i
    rw [Finset.sum_eq_single (τ i)]
    · by_cases a : blk i = u <;> by_cases b : blk (τ i) = v <;> simp [a, b]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [h]
  rw [Finset.sum_boole]


lemma cnt_even (n d : ℕ) (τ : Equiv.Perm (Fin (n * d))) (hinv : ∀ i, τ (τ i) = i)
    (hfix : ∀ i, τ i ≠ i) (u : Fin n) :
    Even (Finset.univ.filter (fun i : Fin (n * d) => blk i = u ∧ blk (τ i) = u)).card := by
  set S := Finset.univ.filter (fun i : Fin (n * d) => blk i = u ∧ blk (τ i) = u) with hS
  have hz : ∑ _i ∈ S, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun i _ => τ i) ?_ ?_ ?_ ?_
    · intro a ha; decide +revert
    · intro a ha _; exact hfix a
    · intro a ha
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hinv]; exact ⟨ha.2, ha.1⟩
    · intro a ha; exact hinv a
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hz
  exact (ZMod.natCast_eq_zero_iff_even).mp hz

lemma graph_exists (n d : ℕ) (τ : Equiv.Perm (Fin (n * d))) (hinv : ∀ i, τ (τ i) = i)
    (hfix : ∀ i, τ i ≠ i) :
    ∃ G : Multigraph n, G.IsRegular d ∧ G.adjReal = (Umat n d)ᵀ * Minv τ * Umat n d := by
  let cnt : Fin n → Fin n → ℕ := fun u v =>
    (Finset.univ.filter (fun i : Fin (n * d) => blk i = u ∧ blk (τ i) = v)).card
  have hsymm : (Matrix.of cnt).transpose = Matrix.of cnt := by
    ext u v
    simp only [Matrix.transpose_apply, Matrix.of_apply, cnt]
    apply Finset.card_nbij' τ τ
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hi ⊢
      rw [hinv]; exact ⟨hi.2, hi.1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hi ⊢
      rw [hinv]; exact ⟨hi.2, hi.1⟩
    · intro i _; exact hinv i
    · intro i _; exact hinv i
  refine ⟨⟨Matrix.of cnt, hsymm, fun v => cnt_even n d τ hinv hfix v⟩, ?_, ?_⟩
  · intro v
    show ∑ w, cnt v w = d
    simp only [cnt]
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun i : Fin (n * d) => blk i = v))
      (t := (Finset.univ : Finset (Fin n))) (f := fun i => blk (τ i)) (fun _ _ => Finset.mem_univ _)
    rw [card_blk] at h
    refine Eq.trans ?_ h.symm
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.filter_filter]
  · ext u v
    rw [entry_UMU]
    rfl

end SuperRamanujan227.Dev.Mat4
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Q1
open SuperRamanujan227.Main SuperRamanujan227.Dev.Base SuperRamanujan227.Dev.Deriv

lemma deriv_neg_comp (p : ℝ[X]) (s : ℝ) (h : p.comp (-X) = C s * p) :
    (derivative p).comp (-X) = C (-s) * derivative p := by
  have h1 := congrArg derivative h
  rw [derivative_comp, derivative_C_mul] at h1
  simp only [derivative_neg, derivative_X] at h1
  rw [C_neg]
  linear_combination (-1 : ℝ[X]) * h1

lemma iter_neg_comp (p : ℝ[X]) (hp : p.comp (-X) = p) (k : ℕ) :
    (derivative^[k] p).comp (-X) = C ((-1) ^ k) * derivative^[k] p := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := deriv_neg_comp _ _ ih
    rw [this]
    congr 2
    rw [pow_succ]; ring

lemma Q_nonneg_root (n d : ℕ) (hQ : RealRooted (Q n d)) (hne : (Q n d).roots ≠ 0) :
    0 ≤ kthLargestRoot (Q n d) 1 := by
  have hev : ((X ^ 2 - 1 : ℝ[X]) ^ (n * d / 2)).comp (-X) = (X ^ 2 - 1) ^ (n * d / 2) := by
    simp
  have h := iter_neg_comp _ hev (n * (d - 1))
  set r := kthLargestRoot (Q n d) 1 with hr
  have hmem := alpha1_mem hne
  have hroot : (Q n d).eval r = 0 := (mem_roots hQ.1).mp hmem
  have hneg : (Q n d).eval (-r) = 0 := by
    have h2 := congrArg (eval r) h
    simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at h2
    unfold Q
    rw [h2]
    unfold Q at hroot
    rw [hroot, mul_zero]
  have : -r ∈ (Q n d).roots := (mem_roots hQ.1).mpr hneg
  have := le_alpha1 hne _ this
  linarith

end SuperRamanujan227.Dev.Q1
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Q2
open SuperRamanujan227.Main SuperRamanujan227.Dev.Base SuperRamanujan227.Dev.Deriv

lemma rr_linprod (a b : ℝ) (i l : ℕ) : RealRooted ((X - C a) ^ i * (X - C b) ^ l) := by
  have h0 : ((X - C a) ^ i * (X - C b) ^ l : ℝ[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a)) (pow_ne_zero _ (X_sub_C_ne_zero b))
  refine ⟨h0, ?_⟩
  rw [roots_mul h0, roots_pow, roots_pow, roots_X_sub_C, roots_X_sub_C]
  simp [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) (pow_ne_zero _ (X_sub_C_ne_zero b))]

lemma natDeg_linprod (a b : ℝ) (i l : ℕ) : ((X - C a) ^ i * (X - C b) ^ l).natDegree = i + l := by
  rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) (pow_ne_zero _ (X_sub_C_ne_zero b))]
  simp

lemma f_eq (k : ℕ) : (X ^ 2 - 1 : ℝ[X]) ^ k = (X - C 1) ^ k * (X - C (-1)) ^ k := by
  rw [← mul_pow]
  congr 1
  simp only [map_one, map_neg]
  ring

lemma alpha1_f (k : ℕ) (hk : 1 ≤ k) : kthLargestRoot ((X - C 1) ^ k * (X - C (-1)) ^ k : ℝ[X]) 1 = 1 := by
  have hrr := rr_linprod (1 : ℝ) (-1) k k
  have hne := rr_roots_ne hrr (by rw [natDeg_linprod]; omega)
  have h1 : (1 : ℝ) ∈ ((X - C 1) ^ k * (X - C (-1)) ^ k : ℝ[X]).roots := by
    rw [mem_roots hrr.1]; simp [IsRoot, hk]; omega
  have h2 := le_alpha1 hne 1 h1
  have h3 := alpha1_mem hne
  rw [mem_roots hrr.1] at h3
  simp only [IsRoot, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h3
  set a := kthLargestRoot ((X - C 1) ^ k * (X - C (-1)) ^ k : ℝ[X]) 1
  have h4 : (a - 1) ^ k * (a - -1) ^ k = 0 := h3
  rcases mul_eq_zero.mp h4 with h | h
  · have := pow_eq_zero_iff (by omega) |>.mp h; linarith
  · have := pow_eq_zero_iff (by omega) |>.mp h; linarith

end SuperRamanujan227.Dev.Q2
end

section
set_option autoImplicit false
open Polynomial Matrix

namespace SuperRamanujan227.Dev.T11a
open SuperRamanujan227.Main SuperRamanujan227.Dev.Base SuperRamanujan227.Dev.Deriv
  SuperRamanujan227.Dev.Ord2 SuperRamanujan227.Dev.Mat1 SuperRamanujan227.Dev.Mat2
  SuperRamanujan227.Dev.Mat3 SuperRamanujan227.Dev.Q1 SuperRamanujan227.Dev.Q2

lemma ffMul_comm (D : ℕ) (p q : ℝ[X]) : ffMul D p q = ffMul D q p := by
  unfold ffMul
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_right_comm ((-1 : ℝ) ^ i)]

lemma Minv_tau0_symm {N k : ℕ} (hN : N = 2 * k) : (Mgen hN).IsSymm :=
  Minv_symm _ (tau0_invol hN)

lemma Q_eq (n d k : ℕ) (hN : n * d = 2 * k) :
    Q n d = derivative^[n * d - n] ((X - C 1) ^ k * (X - C (-1)) ^ k) := by
  unfold Q
  have h1 : n * d / 2 = k := by omega
  have h2 : n * (d - 1) = n * d - n := by rw [Nat.mul_sub, Nat.mul_one]
  rw [h1, h2, f_eq]


lemma alpha2_E_le (n d k : ℕ) (hN : n * d = 2 * k) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    kthLargestRoot (expCharpolyMul (Vmat n d) (Mgen hN)) 2 ≤ kthLargestRoot (Q n d) 1 := by
  have hd0 : 0 < d := by omega
  have hNn : 3 * n ≤ n * d := by nlinarith
  have hk1 : 1 ≤ k := by omega
  set j := n * d - n with hj
  set L := n * d - 1 with hL
  have hj1 : 1 ≤ j := by omega
  have hjL : j ≤ L := by omega
  set pV : ℝ[X] := X ^ j * (X - 1) ^ (n - 1) with hpVdef
  set pM : ℝ[X] := (X - C 1) ^ (k - 1) * (X - C (-1)) ^ k with hpMdef
  have hpV : (Vmat n d).charpoly = (X - C 1) * pV := by
    rw [V_charpoly n d hd0]
    have : (X - 1 : ℝ[X]) ^ n = (X - 1) * (X - 1) ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, hpVdef]
    simp only [map_one]
    ring
  have hpM : (Mgen hN).charpoly = (X - C 1) * pM := by
    rw [Mgen_charpoly hN, f_eq, hpMdef]
    have : (X - C 1 : ℝ[X]) ^ k = (X - C 1) * (X - C 1) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  have l25 := lemma_2_5 (Vmat n d) (Mgen hN) (V_symm n d) (Minv_tau0_symm hN) 1 1
    (V_row n d hd0) (Minv_row (tau0 hN)) pV pM hpV hpM
  have hE := l25.2.1
  have hpMdeg : pM.natDegree = L := by
    rw [hpMdef, natDeg_linprod]; omega
  have hpV' : pV = X ^ j * (X - 1) ^ (L - j) := by
    rw [hpVdef]; congr 2; omega
  rw [ffMul_comm, hpV', lemma_5_4 L j pM hpMdeg hj1 hjL] at hE
  set T := derivative^[j] pM with hT
  have hpMrr : RealRooted pM := rr_linprod 1 (-1) (k - 1) k
  have hTrr : RealRooted T := rr_iter hpMrr j (by omega)
  have hTdeg : T.natDegree = n - 1 := by
    rw [hT, (natDeg_iter pM hpMrr.1 j (by omega)).1, hpMdeg]; omega
  have hTne : T.roots ≠ 0 := rr_roots_ne hTrr (by omega)
  -- the polynomial f = chi(M) and Q
  set f : ℝ[X] := (X - C 1) ^ k * (X - C (-1)) ^ k with hf
  have hfrr : RealRooted f := rr_linprod 1 (-1) k k
  have hfdeg : f.natDegree = n * d := by rw [hf, natDeg_linprod]; omega
  have hQ : Q n d = derivative^[j] f := Q_eq n d k hN
  have hQrr : RealRooted (Q n d) := by rw [hQ]; exact rr_iter hfrr j (by omega)
  have hQdeg : (Q n d).natDegree = n := by
    rw [hQ, (natDeg_iter f hfrr.1 j (by omega)).1, hfdeg]; omega
  have hq0 : 0 ≤ kthLargestRoot (Q n d) 1 :=
    Q_nonneg_root n d hQrr (rr_roots_ne hQrr (by omega))
  have h53 := claim_5_3 f (n * d) hfrr hfdeg (by omega) j (by omega)
  have hα : kthLargestRoot f 1 = 1 := alpha1_f k hk1
  have hdiv : f /ₘ (X - C (kthLargestRoot f 1)) = pM := by
    rw [hα]
    have : f = (X - C 1) * pM := by rw [hf, hpMdef]; have : (X - C 1 : ℝ[X]) ^ k = (X - C 1) * (X - C 1) ^ (k - 1) := by
                                                        rw [← pow_succ']; congr 1; omega
                                    rw [this]; ring
    rw [this]
    exact mul_divByMonic_cancel_left _ (monic_X_sub_C 1)
  rw [hdiv, ← hT, ← hQ] at h53
  have hTle : ∀ x ∈ T.roots, x ≤ kthLargestRoot (Q n d) 1 :=
    fun x hx => le_trans (le_alpha1 hTne x hx) h53
  set q := kthLargestRoot (Q n d) 1 with hq
  have hc : (1 / (L.descFactorial j : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (L.descFactorial j : ℝ) := by exact_mod_cast Nat.descFactorial_pos.mpr hjL
    positivity
  have hCX : (C (1 / (L.descFactorial j : ℝ)) * X ^ j : ℝ[X]) ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ X_ne_zero)
  have hrootsE : (expCharpolyMul (Vmat n d) (Mgen hN)).roots =
      {(1 : ℝ) * 1} + (j • ({0} : Multiset ℝ) + T.roots) := by
    rw [hE]
    have h1 : (X - C (1 * 1) : ℝ[X]) ≠ 0 := X_sub_C_ne_zero _
    have h2 : (C (1 / (L.descFactorial j : ℝ)) * X ^ j * T) ≠ 0 := mul_ne_zero hCX hTrr.1
    rw [roots_mul (mul_ne_zero h1 h2), roots_X_sub_C, roots_mul h2, roots_C_mul _ hc, roots_X_pow]
  rw [kth2_def, hrootsE]
  apply second_le_of_filter
  · simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_nsmul]
    omega
  · rw [Multiset.filter_add, Multiset.filter_add]
    have h0 : Multiset.filter (fun x => q < x) (j • ({0} : Multiset ℝ)) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx
      have := Multiset.mem_nsmul.mp hx
      simp at this
      rw [this.2]; exact not_lt.mpr hq0
    have hT0 : Multiset.filter (fun x => q < x) T.roots = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx
      exact not_lt.mpr (hTle x hx)
    rw [h0, hT0]
    simp only [add_zero]
    have := Multiset.card_le_card (Multiset.filter_le (fun x => q < x) ({(1 : ℝ) * 1} : Multiset ℝ))
    simpa using this

end SuperRamanujan227.Dev.T11a
end

section
set_option autoImplicit false
open Polynomial Matrix

namespace SuperRamanujan227.Dev.T11b
open SuperRamanujan227.Main SuperRamanujan227.Dev.Base SuperRamanujan227.Dev.Deriv
  SuperRamanujan227.Dev.Ord2 SuperRamanujan227.Dev.Mat1 SuperRamanujan227.Dev.Mat2
  SuperRamanujan227.Dev.Mat3 SuperRamanujan227.Dev.Mat4 SuperRamanujan227.Dev.Q1
  SuperRamanujan227.Dev.Q2 SuperRamanujan227.Dev.T11a SuperRamanujan227.Dev.Scale

lemma tau_props (n d k : ℕ) (hN : n * d = 2 * k) (σ : Equiv.Perm (Fin (n * d))) :
    (∀ i, (σ⁻¹ * tau0 hN * σ) ((σ⁻¹ * tau0 hN * σ) i) = i) ∧
    (∀ i, (σ⁻¹ * tau0 hN * σ) i ≠ i) := by
  constructor
  · intro i
    simp [Equiv.Perm.mul_apply, tau0_invol]
  · intro i h
    simp only [Equiv.Perm.mul_apply] at h
    have h2 : tau0 hN (σ i) = σ i := by
      have := congrArg σ h
      simpa using this
    exact tau0_ne hN _ h2

lemma scaled_second (S : Multiset ℝ) (c : ℝ) (hc : 0 < c) (h2 : 2 ≤ Multiset.card S) :
    (sorted (S.map (fun r => c * r))).getD 1 0 ≤ c * (sorted S).getD 1 0 := by
  apply second_le_of_filter
  · simpa using h2
  · rw [Multiset.filter_map, Multiset.card_map]
    have : Multiset.filter ((fun x => c * (sorted S).getD 1 0 < x) ∘ fun r => c * r) S =
        Multiset.filter (fun x => (sorted S).getD 1 0 < x) S := by
      apply Multiset.filter_congr
      intro x _
      simp only [Function.comp]
      constructor
      · intro h; by_contra hh; rw [not_lt] at hh; nlinarith
      · intro h; nlinarith
    rw [this]
    by_contra hcon
    have h3 : 2 ≤ Multiset.card (Multiset.filter (fun x => (sorted S).getD 1 0 < x) S) := by omega
    have := (kl_multiset S ((sorted S).getD 1 0) h2).mpr h3
    exact lt_irrefl _ this


lemma main_graph (n d k : ℕ) (hN : n * d = 2 * k) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    ∃ G : Multigraph n, G.IsRegular d ∧ G.eig 2 ≤ (d : ℝ) * kthLargestRoot (Q n d) 1 := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hNn : 3 * n ≤ n * d := by nlinarith
  obtain ⟨hrrE, hk⟩ := lemma_2_2 (Vmat n d) (Mgen hN) (V_symm n d) (Minv_tau0_symm hN)
    (Or.inl (V_psd n d))
  obtain ⟨σ, hσrr, hσle⟩ := hk 2 (by omega) (by omega)
  obtain ⟨hinv, hfix⟩ := tau_props n d k hN σ
  obtain ⟨G, hreg, hadj⟩ := graph_exists n d _ hinv hfix
  refine ⟨G, hreg, ?_⟩
  have hW : permMat σ * Mgen hN * (permMat σ).transpose = Minv (σ⁻¹ * tau0 hN * σ) :=
    conj_Minv σ (tau0 hN)
  have hVW : Vmat n d * permMat σ * Mgen hN * (permMat σ).transpose =
      Vmat n d * Minv (σ⁻¹ * tau0 hN * σ) := by
    rw [← hW]
    simp only [Matrix.mul_assoc]
  rw [hVW] at hσrr hσle
  set Mt : Matrix (Fin (n * d)) (Fin (n * d)) ℝ := Minv (σ⁻¹ * tau0 hN * σ) with hMt
  set At : Matrix (Fin n) (Fin n) ℝ := ((1 : ℝ) / d) • G.adjReal with hAt
  -- charpoly relation
  have hcomm := charpoly_mul_comm' (((1 : ℝ) / d) • Umat n d) ((Umat n d)ᵀ * Mt)
  have hAB : (((1 : ℝ) / d) • Umat n d) * ((Umat n d)ᵀ * Mt) = Vmat n d * Mt := by
    unfold Vmat; rw [Matrix.mul_assoc]
  have hBA : ((Umat n d)ᵀ * Mt) * (((1 : ℝ) / d) • Umat n d) = At := by
    rw [hAt, hadj, Matrix.mul_smul, Matrix.mul_assoc]
  rw [hAB, hBA] at hcomm
  simp only [Fintype.card_fin] at hcomm
  have hcp : (Vmat n d * Mt).charpoly = X ^ (n * d - n) * At.charpoly := by
    have : (X : ℝ[X]) ^ (n * d) = X ^ n * X ^ (n * d - n) := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc] at hcomm
    exact mul_left_cancel₀ (pow_ne_zero n X_ne_zero) (by rw [hcomm])
  -- cardinality of roots of At.charpoly
  have hAtmonic := At.charpoly_monic
  have hcard : Multiset.card At.charpoly.roots = n := by
    have h1 := hσrr.2
    rw [hcp] at h1
    have h2 : (X ^ (n * d - n) * At.charpoly : ℝ[X]) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ X_ne_zero) hAtmonic.ne_zero
    rw [roots_mul h2, roots_X_pow, Multiset.card_add, Multiset.card_nsmul,
      natDegree_mul (pow_ne_zero _ X_ne_zero) hAtmonic.ne_zero] at h1
    simp only [Multiset.card_singleton, natDegree_X_pow, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin] at h1
    simp at h1
    omega
  have hAtne : (X ^ (n * d - n) * At.charpoly : ℝ[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hAtmonic.ne_zero
  have hle : At.charpoly.roots ≤ (Vmat n d * Mt).charpoly.roots := by
    rw [hcp, roots_mul hAtne, roots_X_pow]
    exact Multiset.le_add_left _ _
  have hmono := second_mono _ _ hle (by omega)
  have hadj_eq : G.adjReal = (d : ℝ) • At := by
    rw [hAt, smul_smul, mul_one_div_cancel hdR.ne', one_smul]
  have hscale := charpoly_smul_roots At d hdR hcard
  have hsc := scaled_second At.charpoly.roots d hdR (by omega)
  have hE := alpha2_E_le n d k hN hn2 hd
  unfold Multigraph.eig matrixEig
  rw [kth2_def, hadj_eq, hscale]
  have h3 : (sorted (Vmat n d * Mt).charpoly.roots).getD 1 0 ≤ kthLargestRoot (Q n d) 1 := by
    rw [← kth2_def]
    unfold matrixEig at hσle
    exact le_trans hσle hE
  calc _ ≤ (d : ℝ) * (sorted At.charpoly.roots).getD 1 0 := hsc
    _ ≤ (d : ℝ) * kthLargestRoot (Q n d) 1 := by
      apply mul_le_mul_of_nonneg_left (le_trans hmono h3) hdR.le

end SuperRamanujan227.Dev.T11b
end

section
set_option autoImplicit false

namespace SuperRamanujan227.Dev.Num

lemma rp (x : ℝ) (hx : 0 ≤ x) (c : ℝ) (m : ℕ) : (x ^ c) ^ m = x ^ (c * m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- the key inequality `Y ≤ X` -/
lemma YleX (n d : ℝ) (hn : 2 ≤ n) (hd : 3 ≤ d) :
    (1 - 2 / d) ^ ((5 : ℝ) / 3) * Real.sqrt d ≤
      d * ((d - 2 + 2 / n) ^ ((4 : ℝ) / 3) /
        ((d - 1 + 1 / n) ^ ((1 : ℝ) / 6) * (d ^ 2 + 4 * (d - 1) / n + 4 / n ^ 2) ^ ((5 : ℝ) / 6))) := by
  have hn0 : 0 < n := by linarith
  have hd0 : 0 < d := by linarith
  set a : ℝ := 1 - 2 / d with ha
  set u : ℝ := d - 2 + 2 / n with hu
  set v : ℝ := d - 1 + 1 / n with hv
  set w : ℝ := d ^ 2 + 4 * (d - 1) / n + 4 / n ^ 2 with hw
  have ha0 : 0 < a := by rw [ha]; rw [sub_pos, div_lt_one hd0]; linarith
  have hu0 : 0 < u := by
    rw [hu]; have : 0 < 2 / n := by positivity
    linarith
  have hv0 : 0 < v := by
    rw [hv]
    have : 0 < 1 / n := by positivity
    linarith
  have hw0 : 0 < w := by
    rw [hw]; have : 0 < 4 * (d - 1) / n := by apply div_pos <;> linarith
    positivity
  set ε : ℝ := 2 / (n * d) with hε
  have hε0 : 0 < ε := by positivity
  have hεle : ε ≤ 1 / d := by
    rw [hε, div_le_div_iff₀ (by positivity) hd0]; nlinarith
  have hu_eq : u = d * (a + ε) := by
    rw [hu, ha, hε]; field_simp
  have hvle : v ≤ d := by
    rw [hv]; have : 1 / n ≤ 1 := by rw [div_le_one hn0]; linarith
    linarith
  have hwle : w ≤ (d * (1 + ε)) ^ 2 := by
    have : d * (1 + ε) = d + 2 / n := by rw [hε]; field_simp
    rw [this, hw]
    have h1 : 0 ≤ 4 / n := by positivity
    have h2 : 4 * (d - 1) / n ≤ 4 * d / n := by
      apply div_le_div_of_nonneg_right _ hn0.le; linarith
    have h3 : 4 * d / n = 2 * d * (2 / n) := by field_simp; norm_num
    have h4 : (d + 2 / n) ^ 2 = d ^ 2 + 2 * d * (2 / n) + (2 / n) ^ 2 := by ring
    have h5 : (2 / n) ^ 2 = 4 / n ^ 2 := by field_simp; norm_num
    rw [h4, h5]; linarith
  set b : ℝ := a * (1 + ε) with hb
  have hb1 : b ≤ 1 := by
    have : a * (1 + ε) ≤ a * (1 + 1 / d) := by
      apply mul_le_mul_of_nonneg_left _ ha0.le; linarith
    have h2 : a * (1 + 1 / d) ≤ 1 := by
      rw [ha]
      have : (1 - 2 / d) * (1 + 1 / d) = 1 - 1 / d - 2 / d ^ 2 := by field_simp; ring
      rw [this]
      have : 0 < 1 / d := by positivity
      have : 0 < 2 / d ^ 2 := by positivity
      linarith
    linarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have hbab : b ≤ a + ε := by
    have ha1 : a ≤ 1 := by
      rw [ha]
      have : 0 < 2 / d := by positivity
      linarith
    rw [hb]; nlinarith [mul_pos ha0 hε0]
  have hmain : b ^ 10 ≤ (a + ε) ^ 8 := by
    calc b ^ 10 ≤ b ^ 8 := pow_le_pow_of_le_one hb0.le hb1 (by norm_num)
      _ ≤ (a + ε) ^ 8 := pow_le_pow_left₀ hb0.le hbab 8
  -- polynomial form
  have hpoly : a ^ 10 * d ^ 3 * (v * w ^ 5) ≤ d ^ 6 * u ^ 8 := by
    have h1 : v * w ^ 5 ≤ d * (d * (1 + ε)) ^ 10 := by
      calc v * w ^ 5 ≤ d * ((d * (1 + ε)) ^ 2) ^ 5 := by
            apply mul_le_mul hvle (pow_le_pow_left₀ hw0.le hwle 5) (by positivity) hd0.le
        _ = d * (d * (1 + ε)) ^ 10 := by rw [← pow_mul]
    calc a ^ 10 * d ^ 3 * (v * w ^ 5) ≤ a ^ 10 * d ^ 3 * (d * (d * (1 + ε)) ^ 10) := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = d ^ 14 * b ^ 10 := by rw [hb]; ring
      _ ≤ d ^ 14 * (a + ε) ^ 8 := by apply mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = d ^ 6 * u ^ 8 := by rw [hu_eq]; ring
  -- take sixth roots
  have hY0 : 0 < (1 - 2 / d) ^ ((5 : ℝ) / 3) * Real.sqrt d :=
    mul_pos (Real.rpow_pos_of_pos ha0 _) (Real.sqrt_pos.mpr hd0)
  have hX0 : 0 < d * (u ^ ((4 : ℝ) / 3) / (v ^ ((1 : ℝ) / 6) * w ^ ((5 : ℝ) / 6))) := by
    have := Real.rpow_pos_of_pos hu0 ((4 : ℝ) / 3)
    have := Real.rpow_pos_of_pos hv0 ((1 : ℝ) / 6)
    have := Real.rpow_pos_of_pos hw0 ((5 : ℝ) / 6)
    positivity
  by_contra hcon
  rw [not_le] at hcon
  have h6 := pow_lt_pow_left₀ hcon hX0.le (by norm_num : (6 : ℕ) ≠ 0)
  have eY : ((1 - 2 / d) ^ ((5 : ℝ) / 3) * Real.sqrt d) ^ 6 = a ^ 10 * d ^ 3 := by
    rw [mul_pow, rp a ha0.le, show (Real.sqrt d) ^ 6 = (Real.sqrt d ^ 2) ^ 3 by ring,
      Real.sq_sqrt hd0.le]
    have : ((5 : ℝ) / 3 * ((6 : ℕ) : ℝ)) = ((10 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  have eX : (d * (u ^ ((4 : ℝ) / 3) / (v ^ ((1 : ℝ) / 6) * w ^ ((5 : ℝ) / 6)))) ^ 6 =
      d ^ 6 * u ^ 8 / (v * w ^ 5) := by
    rw [mul_pow, div_pow, mul_pow, rp u hu0.le, rp v hv0.le, rp w hw0.le]
    have e1 : ((4 : ℝ) / 3 * ((6 : ℕ) : ℝ)) = ((8 : ℕ) : ℝ) := by norm_num
    have e2 : ((1 : ℝ) / 6 * ((6 : ℕ) : ℝ)) = 1 := by norm_num
    have e3 : ((5 : ℝ) / 6 * ((6 : ℕ) : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e1, e2, e3, Real.rpow_natCast, Real.rpow_one, Real.rpow_natCast]
    ring
  rw [eY, eX, div_lt_iff₀ (by positivity)] at h6
  linarith


lemma ge_quarter (d : ℝ) (hd : 3 ≤ d) :
    1 / 4 ≤ 3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (1 - 2 / d) ^ ((5 : ℝ) / 3) := by
  have hd0 : 0 < d := by linarith
  have ha : (1 : ℝ) / 3 ≤ 1 - 2 / d := by
    have : 2 / d ≤ 2 / 3 := by
      rw [div_le_div_iff₀ hd0 (by norm_num)]; linarith
    linarith
  have h1 : ((1 : ℝ) / 3) ^ ((5 : ℝ) / 3) ≤ (1 - 2 / d) ^ ((5 : ℝ) / 3) :=
    Real.rpow_le_rpow (by norm_num) ha (by norm_num)
  have p4 : 0 < (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have p3 : 0 < ((1 : ℝ) / 3) ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  set c : ℝ := 3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * ((1 : ℝ) / 3) ^ ((5 : ℝ) / 3) with hc
  have hc0 : 0 < c := by positivity
  have hc3 : c ^ 3 = 1 / 36 := by
    rw [hc, mul_pow, div_pow, rp 4 (by norm_num), rp (1 / 3) (by norm_num)]
    have e1 : ((1 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = 1 := by norm_num
    have e2 : ((5 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
    rw [e1, e2, Real.rpow_one, Real.rpow_natCast]
    norm_num
  have hq : (1 / 4 : ℝ) ≤ c := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h hc0.le (by norm_num : (3 : ℕ) ≠ 0)
    rw [hc3] at this
    norm_num at this
  calc (1 : ℝ) / 4 ≤ c := hq
    _ ≤ _ := by
      rw [hc]
      apply mul_le_mul_of_nonneg_left h1 (by positivity)

end SuperRamanujan227.Dev.Num
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Main
open SuperRamanujan227.Dev.T11b SuperRamanujan227.Dev.Num

theorem chk_theorem_1_1 (n d : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    ∃ G : Multigraph n, G.IsRegular d ∧
      G.eig 2 ≤ 2 * Real.sqrt ((d : ℝ) - 1) -
          3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (1 - 2 / (d : ℝ)) ^ ((5 : ℝ) / 3) * Real.sqrt (d : ℝ) /
            (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      2 * Real.sqrt ((d : ℝ) - 1) -
          3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (1 - 2 / (d : ℝ)) ^ ((5 : ℝ) / 3) * Real.sqrt (d : ℝ) /
            (n : ℝ) ^ ((2 : ℝ) / 3) ≤
        2 * Real.sqrt ((d : ℝ) - 1) - Real.sqrt (d : ℝ) / (4 * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
  obtain ⟨n', hn'⟩ := hn
  have hN : n * d = 2 * (n' * d) := by rw [hn']; ring
  obtain ⟨G, hreg, hG⟩ := main_graph n d (n' * d) hN hn2 hd
  have h56 := claim_5_6 n d hd hn2 ⟨n' * d, by omega⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hY := YleX (n : ℝ) (d : ℝ) hnR hdR
  have hq := ge_quarter (d : ℝ) hdR
  set a : ℝ := (1 - 2 / (d : ℝ)) ^ ((5 : ℝ) / 3) with ha
  set Z : ℝ := (((d : ℝ) - 2 + 2 / (n : ℝ)) ^ ((4 : ℝ) / 3) /
          (((d : ℝ) - 1 + 1 / (n : ℝ)) ^ ((1 : ℝ) / 6) *
            ((d : ℝ) ^ 2 + 4 * ((d : ℝ) - 1) / (n : ℝ) + 4 / (n : ℝ) ^ 2) ^ ((5 : ℝ) / 6))) with hZ
  have hn23 : 0 < (n : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hn0 _
  have hneg : (n : ℝ) ^ (-(2 : ℝ) / 3) = ((n : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := by
    rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring, Real.rpow_neg hn0.le]
  have hc3 : 0 < 3 / (4 : ℝ) ^ ((1 : ℝ) / 3) := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 4 by norm_num) ((1 : ℝ) / 3)
    positivity
  have hT1 : 3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * a * Real.sqrt (d : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3) =
      3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) * (a * Real.sqrt (d : ℝ)) := by
    rw [hneg]; field_simp
  have hK : (d : ℝ) * (3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) * Z) =
      3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) * ((d : ℝ) * Z) := by ring
  have hP : 0 ≤ 3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
    have := Real.rpow_pos_of_pos hn0 (-(2 : ℝ) / 3)
    positivity
  have hdK : 3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * a * Real.sqrt (d : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3) ≤
      (d : ℝ) * (3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) * Z) := by
    rw [hT1, hK]
    exact mul_le_mul_of_nonneg_left hY hP
  refine ⟨G, hreg, ?_, ?_⟩
  · have h1 : (d : ℝ) * (2 * Real.sqrt ((d : ℝ) - 1) / (d : ℝ) - kthLargestRoot (Q n d) 1) >
        (d : ℝ) * (3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) * Z) :=
      mul_lt_mul_of_pos_left h56 hd0
    have h2 : (d : ℝ) * (2 * Real.sqrt ((d : ℝ) - 1) / (d : ℝ)) = 2 * Real.sqrt ((d : ℝ) - 1) := by
      field_simp
    rw [mul_sub, h2] at h1
    linarith
  · have h1 : Real.sqrt (d : ℝ) / (4 * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
        3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * a * Real.sqrt (d : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [show 3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * a * Real.sqrt (d : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3) =
          (3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * a) * (Real.sqrt (d : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3)) by ring]
      rw [show Real.sqrt (d : ℝ) / (4 * (n : ℝ) ^ ((2 : ℝ) / 3)) =
          (1 / 4) * (Real.sqrt (d : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3)) by field_simp]
      apply mul_le_mul_of_nonneg_right hq
      positivity
    linarith

end SuperRamanujan227.Main
end

theorem solution : type_of% @SuperRamanujan227.Main.chk_theorem_1_1 := @SuperRamanujan227.Main.chk_theorem_1_1
