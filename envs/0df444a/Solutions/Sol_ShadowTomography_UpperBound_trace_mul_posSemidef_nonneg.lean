-- Prove2me | solution 1 for ShadowTomography.UpperBound.trace_mul_posSemidef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:56:01.181824+00:00
-- url     : https://prove2.me/submissions/237e7e41-697a-41b5-bb51-67e4443d3c27

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound.Leaves

open Matrix

/-- PSD matrices are `star s * s` with `s = √A` self-adjoint. -/
lemma psd_sqrt {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A ∧ CFC.sqrt A * CFC.sqrt A = A := by
  have h0 : (0 : Matrix n n ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  refine ⟨?_, CFC.sqrt_mul_sqrt_self A h0⟩
  have := (CFC.sqrt_nonneg A).isSelfAdjoint
  simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using this

lemma trace_mul_psd {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨hs, hss⟩ := psd_sqrt B hB
  set s := CFC.sqrt B
  have h1 : (A * B).trace = (sᴴ * A * s).trace := by
    rw [← hss, hs, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 : (sᴴ * A * s).PosSemidef := hA.conjTranspose_mul_mul_same s
  rw [h1]
  exact (Complex.nonneg_iff.mp h2.trace_nonneg).1

/-- Product operator on `q` registers. -/
def prodOp {n : Type} {q : ℕ} (f : Fin q → Matrix n n ℂ) : Matrix (Fin q → n) (Fin q → n) ℂ :=
  fun x y => ∏ r, f r (x r) (y r)

lemma prodOp_mul {n : Type} [Fintype n] {q : ℕ} (f g : Fin q → Matrix n n ℂ) :
    prodOp f * prodOp g = prodOp (fun r => f r * g r) := by
  ext x y
  simp only [prodOp, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma prodOp_conjTranspose {n : Type} [Fintype n] {q : ℕ} (f : Fin q → Matrix n n ℂ) :
    (prodOp f)ᴴ = prodOp (fun r => (f r)ᴴ) := by
  ext x y
  simp [prodOp, Matrix.conjTranspose_apply]

lemma prodOp_psd {n : Type} [Fintype n] [DecidableEq n] {q : ℕ} (f : Fin q → Matrix n n ℂ)
    (hf : ∀ r, (f r).PosSemidef) : (prodOp f).PosSemidef := by
  have : prodOp f = (prodOp (fun r => CFC.sqrt (f r)))ᴴ * prodOp (fun r => CFC.sqrt (f r)) := by
    rw [prodOp_conjTranspose, prodOp_mul]
    congr 1; funext r
    rw [(psd_sqrt _ (hf r)).1, (psd_sqrt _ (hf r)).2]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma prodOp_trace {n : Type} [Fintype n] {q : ℕ} (f : Fin q → Matrix n n ℂ) :
    (prodOp f).trace = ∏ r, (f r).trace := by
  simp only [Matrix.trace, Matrix.diag, prodOp]
  rw [Fintype.prod_sum]

/-- A PSD matrix of trace one lies below the identity. -/
lemma one_sub_psd_of_trace_one {m : Type} [Fintype m] [DecidableEq m] (P : Matrix m m ℂ)
    (hP : P.PosSemidef) (ht : P.trace = 1) : (1 - P).PosSemidef := by
  have hH := hP.1
  set U := hH.eigenvectorUnitary
  have hspec : P = (U : Matrix m m ℂ) * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
      star (U : Matrix m m ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]
    rfl
  have hUU : (U : Matrix m m ℂ) * star (U : Matrix m m ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues; rw [ht] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hrw : 1 - P = (U : Matrix m m ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ (fun i => 1 - hH.eigenvalues i)) *
      (U : Matrix m m ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    conv_lhs => rw [hspec, ← hUU]
    have : Matrix.diagonal (RCLike.ofReal ∘ (fun i => 1 - hH.eigenvalues i)) =
        (1 : Matrix m m ℂ) - Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      ext i j; by_cases h : i = j <;> simp [h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [hrw]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply, Function.comp_apply]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hle i))

lemma sum_acceptPattern {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (q : ℕ) :
    ∑ S : Finset (Fin q), acceptPattern E q S = 1 := by
  classical
  ext x y
  rw [Matrix.sum_apply]
  have key : ∀ S : Finset (Fin q), acceptPattern E q S x y =
      (∏ r ∈ S, E (x r) (y r)) * ∏ r ∈ Finset.univ \ S, (1 - E) (x r) (y r) := by
    intro S
    have : acceptPattern E q S x y = ∏ r, (if r ∈ S then E (x r) (y r) else (1 - E) (x r) (y r)) := by
      simp only [acceptPattern]
      exact Finset.prod_congr rfl fun r _ => by split_ifs <;> rfl
    rw [this, Finset.prod_ite]
    congr 2
    · ext r; simp
    · ext r; simp
  simp_rw [key]
  rw [← Finset.powerset_univ, ← Finset.prod_add]
  simp only [Matrix.sub_apply, add_sub_cancel]
  by_cases hxy : x = y
  · subst hxy; simp [Matrix.one_apply]
  · obtain ⟨r, hr⟩ : ∃ r, x r ≠ y r := by
      by_contra h; push Not at h; exact hxy (funext h)
    rw [Matrix.one_apply_ne hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (Matrix.one_apply_ne hr)

lemma filter_sum_isEffect {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ)
    (hE : IsEffect E) (q : ℕ) (p : Finset (Fin q) → Prop) [DecidablePred p] :
    IsEffect (∑ S ∈ Finset.univ.filter p, acceptPattern E q S) := by
  have hAP : ∀ S, (acceptPattern E q S).PosSemidef := fun S => by
    have : acceptPattern E q S = prodOp (fun r => if r ∈ S then E else 1 - E) := by
      ext x y; simp [acceptPattern, prodOp]
    rw [this]; apply prodOp_psd; intro r; split_ifs
    · exact hE.1
    · exact hE.2
  refine ⟨Matrix.posSemidef_sum _ (fun S _ => hAP S), ?_⟩
  have : 1 - ∑ S ∈ Finset.univ.filter p, acceptPattern E q S =
      ∑ S ∈ Finset.univ.filter (fun S => ¬ p S), acceptPattern E q S := by
    rw [← sum_acceptPattern E q, ← Finset.sum_filter_add_sum_filter_not Finset.univ p]
    abel
  rw [this]; exact Matrix.posSemidef_sum _ (fun S _ => hAP S)

end ShadowTomography.UpperBound.Leaves

namespace ShadowTomography.UpperBound.Leaves
open Matrix

/-- Kraus-type operator picking the tuples that equal `z` off register `r`. -/
noncomputable def margK {n : Type} [Fintype n] [DecidableEq n] {q : ℕ} (r : Fin q)
    (z : {s // s ≠ r} → n) : Matrix (Fin q → n) n ℂ := by
  classical
  exact fun x a => if x r = a ∧ ∀ s : {s // s ≠ r}, x s = z s then 1 else 0

lemma restrict_sum {n : Type} [Fintype n] [DecidableEq n] {q : ℕ} (r : Fin q)
    (x y : Fin q → n) :
    (∑ z : ({s // s ≠ r} → n),
      (if ∀ s : {s // s ≠ r}, x s = z s then (1 : ℂ) else 0) *
      (if ∀ s : {s // s ≠ r}, y s = z s then (1 : ℂ) else 0)) =
    if ∀ s, s ≠ r → x s = y s then 1 else 0 := by
  classical
  have h1 : ∀ z : ({s // s ≠ r} → n), (∀ s : {s // s ≠ r}, x s = z s) ↔ (fun s => x s.1) = z :=
    fun z => ⟨fun h => funext h, fun h s => congrFun h s⟩
  simp_rw [h1, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : ∀ s, s ≠ r → x s = y s
  · rw [if_pos h, if_pos]; intro s; exact (h s.1 s.2).symm
  · rw [if_neg h, if_neg]; intro h'; exact h fun s hs => (h' ⟨s, hs⟩).symm

lemma marginal_eq_sum {n : Type} [Fintype n] [DecidableEq n] {q : ℕ}
    (σ : Matrix (Fin q → n) (Fin q → n) ℂ) (r : Fin q) :
    marginal σ r = ∑ z : ({s // s ≠ r} → n), (margK r z)ᴴ * σ * margK r z := by
  classical
  ext a b
  simp only [marginal, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, margK,
    Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hR := restrict_sum r i j
  have e : ∀ c : ({s // s ≠ r} → n),
      star (if i r = a ∧ ∀ s : {s // s ≠ r}, i s = c s then (1 : ℂ) else 0) * σ i j *
        (if j r = b ∧ ∀ s : {s // s ≠ r}, j s = c s then (1 : ℂ) else 0) =
      (if i r = a ∧ j r = b then σ i j else 0) *
        ((if ∀ s : {s // s ≠ r}, i s = c s then (1 : ℂ) else 0) *
         (if ∀ s : {s // s ≠ r}, j s = c s then (1 : ℂ) else 0)) := by
    intro c
    by_cases hi : i r = a <;> by_cases hj : j r = b <;> simp [hi, hj] <;> split_ifs <;> simp
  simp_rw [e]
  rw [← Finset.mul_sum, hR]
  by_cases hi : i r = a <;> by_cases hj : j r = b <;> simp [hi, hj]

lemma trace_marginal {n : Type} [Fintype n] [DecidableEq n] {q : ℕ}
    (σ : Matrix (Fin q → n) (Fin q → n) ℂ) (r : Fin q) :
    (marginal σ r).trace = σ.trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, marginal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single (x r)]
    · simp
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    apply hy; funext s
    by_cases hs : s = r
    · subst hs; rw [h1, h2]
    · exact (h3 s hs).symm
  · simp

end ShadowTomography.UpperBound.Leaves

open Matrix ShadowTomography.UpperBound ShadowTomography.UpperBound.Leaves

theorem solution {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := trace_mul_psd A B hA hB
