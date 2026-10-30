-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.realHilbertSchmidtProjection
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:24:39.750502+00:00
-- url     : https://prove2.me/submissions/d63f3cad-0db5-4961-a353-3b9d3116468d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

lemma pair_add_right {n : ℕ} (A B C : Mat n) :
    realHSPairing A (B + C) = realHSPairing A B + realHSPairing A C := by
  unfold realHSPairing; rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

lemma pair_smul_right {n : ℕ} (A B : Mat n) (r : ℝ) :
    realHSPairing A (r • B) = r * realHSPairing A B := by
  unfold realHSPairing; rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]; simp

lemma pair_sub_left {n : ℕ} (A B C : Mat n) :
    realHSPairing (A - B) C = realHSPairing A C - realHSPairing B C := by
  unfold realHSPairing; rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

lemma pair_comm {n : ℕ} (A B : Mat n) : realHSPairing A B = realHSPairing B A := by
  unfold realHSPairing
  have : (A.conjTranspose * B).conjTranspose = B.conjTranspose * A := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [← this, Matrix.trace_conjTranspose]; simp

lemma pair_self_eq {n : ℕ} (A : Mat n) : realHSPairing A A = frobSq A := by
  unfold realHSPairing
  have : Matrix.trace (A.conjTranspose * A) = (frobSq A : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, frobSq]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp
  rw [this]; simp

lemma frobSq_eq_zero' {n : ℕ} (A : Mat n) (h : frobSq A = 0) : A = 0 := by
  unfold frobSq at h
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun i => ∑ j, Complex.normSq (A i j))
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).mp h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun j => Complex.normSq (A i j)) (fun j _ => Complex.normSq_nonneg _)).mp
    (h' i (Finset.mem_univ i)) j (Finset.mem_univ j)
  simpa using h1

def Lf {n : ℕ} (A : Mat n) : Mat n →ₗ[ℝ] ℝ where
  toFun B := realHSPairing A B
  map_add' B C := pair_add_right A B C
  map_smul' r B := by simp only [RingHom.id_apply, smul_eq_mul]; exact pair_smul_right A B r

lemma pair_self_zero {n : ℕ} (A : Mat n) (h : realHSPairing A A = 0) : A = 0 := by
  rw [pair_self_eq] at h; exact frobSq_eq_zero' A h

lemma uniq {n : ℕ} (T : Set (Mat n)) (hsub : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ T) (g p q : Mat n)
    (hp : IsHSProjection T g p) (hq : IsHSProjection T g q) : p = q := by
  have h1 := hp.2 _ (hsub p hp.1 q hq.1)
  have h2 := hq.2 _ (hsub p hp.1 q hq.1)
  have : realHSPairing (p - q) (p - q) = 0 := by
    have e : p - q = (g - q) - (g - p) := by abel
    have h3 : realHSPairing (p - q) (p - q) = realHSPairing ((g - q) - (g - p)) (p - q) :=
      congrArg (fun x => realHSPairing x (p - q)) e
    rw [h3, pair_sub_left]
    linarith
  exact sub_eq_zero.mp (pair_self_zero _ this)


lemma key {n m : ℕ} (b : Fin m → Mat n)
    (horth : ∀ i j, realHSPairing (b i) (b j) = if i = j then 1 else 0) (g : Mat n) :
    ∀ h ∈ (Submodule.span ℝ (Set.range b) : Set (Mat n)),
      realHSPairing (g - basisProjection b g) h = 0 := by
  intro h hh
  have hh' : h ∈ Submodule.span ℝ (Set.range b) := hh
  rw [Submodule.mem_span_range_iff_exists_fun] at hh'
  obtain ⟨c, rfl⟩ := hh'
  have hb : ∀ i, realHSPairing (b i) (g - basisProjection b g) = 0 := by
    intro i
    have e1 : realHSPairing (b i) (g - basisProjection b g) =
        Lf (b i) g - Lf (b i) (basisProjection b g) := by
      show Lf (b i) (g - basisProjection b g) = _
      exact map_sub (Lf (b i)) g _
    have e2 : Lf (b i) (basisProjection b g) = realHSPairing (b i) g := by
      unfold basisProjection
      rw [map_sum]
      have : ∀ j, Lf (b i) (realHSPairing (b j) g • b j) =
          realHSPairing (b j) g * (if i = j then 1 else 0) := by
        intro j
        rw [map_smul, smul_eq_mul, show Lf (b i) (b j) = realHSPairing (b i) (b j) from rfl, horth]
      simp only [this]
      simp [Finset.sum_ite_eq]
    rw [e1, e2]; show realHSPairing (b i) g - realHSPairing (b i) g = 0; ring
  show Lf (g - basisProjection b g) (Finset.univ.sum fun i => c i • b i) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_eq_mul, show Lf (g - basisProjection b g) (b i) =
    realHSPairing (g - basisProjection b g) (b i) from rfl, pair_comm, hb i, mul_zero]


lemma proj_mem {n m : ℕ} (b : Fin m → Mat n) (g : Mat n) :
    basisProjection b g ∈ (Submodule.span ℝ (Set.range b) : Set (Mat n)) := by
  show basisProjection b g ∈ Submodule.span ℝ (Set.range b)
  unfold basisProjection
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38 in
theorem solution {n m : ℕ} (hn : 0 < n)
    (H : Subgroup ((Matrix (Fin n) (Fin n) ℂ))ˣ) (hH : IsClosed (H : Set ((Matrix (Fin n) (Fin n) ℂ))ˣ)) (b : Fin m → (Matrix (Fin n) (Fin n) ℂ))
    (hspan : (Submodule.span ℝ (Set.range b) : Set ((Matrix (Fin n) (Fin n) ℂ))) = matrixLieSet H)
    (horth : ∀ i j, realHSPairing (b i) (b j) = if i = j then 1 else 0) :
    ∀ g : (Matrix (Fin n) (Fin n) ℂ),
      (∃! p, IsHSProjection (matrixLieSet H) g p) ∧
      IsHSProjection (matrixLieSet H) g (basisProjection b g) ∧
      (∃! p, IsHSProjection (hsOrthogonal (matrixLieSet H)) g p) ∧
      IsHSProjection (hsOrthogonal (matrixLieSet H)) g (g - basisProjection b g) := by
  intro g
  rw [← hspan]
  have hS : IsHSProjection (Submodule.span ℝ (Set.range b) : Set (Mat n)) g (basisProjection b g) :=
    ⟨proj_mem b g, key b horth g⟩
  have hsubS : ∀ a ∈ (Submodule.span ℝ (Set.range b) : Set (Mat n)), ∀ c ∈
      (Submodule.span ℝ (Set.range b) : Set (Mat n)),
      a - c ∈ (Submodule.span ℝ (Set.range b) : Set (Mat n)) :=
    fun a ha c hc => Submodule.sub_mem _ ha hc
  have hT : IsHSProjection (hsOrthogonal (Submodule.span ℝ (Set.range b) : Set (Mat n))) g
      (g - basisProjection b g) := by
    refine ⟨key b horth g, ?_⟩
    intro h hh
    rw [sub_sub_cancel, pair_comm]
    exact hh _ (proj_mem b g)
  have hsubT : ∀ a ∈ hsOrthogonal (Submodule.span ℝ (Set.range b) : Set (Mat n)), ∀ c ∈
      hsOrthogonal (Submodule.span ℝ (Set.range b) : Set (Mat n)),
      a - c ∈ hsOrthogonal (Submodule.span ℝ (Set.range b) : Set (Mat n)) := by
    intro a ha c hc h hh
    rw [pair_sub_left, ha h hh, hc h hh, sub_zero]
  exact ⟨⟨_, hS, fun q hq => uniq _ hsubS g q _ hq hS⟩, hS,
    ⟨_, hT, fun q hq => uniq _ hsubT g q _ hq hT⟩, hT⟩
