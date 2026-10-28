-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P43.alternative_pure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:43:17.22026+00:00
-- url     : https://prove2.me/submissions/2f98aea3-bd2a-4fe0-baad-294dfe0d2f42

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal trivialExtension)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma A3S54AP.h_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma A3S54AP.h_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma A3S54AP.h_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, A3S54AP.h_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma A3S54AP.h_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [A3S54AP.h_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (A3S54AP.h_trace_pow M)]


namespace A3S54AP

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

/-- complement-coordinates -/
abbrev Cs (D : Fin n → Type) (s : Finset (Fin n)) := (i : {i : Fin n // ¬ i ∈ s}) → D i.val

def split (s : Finset (Fin n)) : RegisterBasis D ≃ SubBasis D s × Cs D s :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) D

def Mat (psi : EuclideanSpace ℂ (RegisterBasis D)) (s : Finset (Fin n)) :
    Matrix (SubBasis D s × Unit) (Cs D s) ℂ :=
  fun a c => psi ((split s).symm (a.1, c))

lemma cond_iff (s : Finset (Fin n)) (p q : SubBasis D s) (c c' : Cs D s) (a b : SubBasis D s) :
    ((∀ i (hi : i ∈ s), (split s).symm (p, c) i = a ⟨i,hi⟩ ∧ (split s).symm (q, c') i = b ⟨i,hi⟩) ∧
      (∀ i, i ∉ s → (split s).symm (p, c) i = (split s).symm (q, c') i)) ↔
      (p = a ∧ q = b) ∧ c = c' := by
  simp only [split, Equiv.piEquivPiSubtypeProd_symm_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨funext fun i => ?_, funext fun i => ?_⟩, funext fun i => ?_⟩
    · have := (h1 i.1 i.2).1; rwa [dif_pos i.2] at this
    · have := (h1 i.1 i.2).2; rwa [dif_pos i.2] at this
    · have := h2 i.1 i.2; rwa [dif_neg i.2, dif_neg i.2] at this
  · rintro ⟨⟨rfl, rfl⟩, rfl⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simp [dif_pos hi]
    · simp [dif_neg hi]

lemma marginal_eq (psi : EuclideanSpace ℂ (RegisterBasis D)) (s : Finset (Fin n)) :
    registerMarginal (trivialExtension (pureDensity psi)) s = Mat psi s * (Mat psi s)ᴴ := by
  ext a b
  simp only [registerMarginal, trivialExtension, pureDensity, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Mat, RCLike.star_def]
  rw [← (split s).symm.sum_comp]
  simp_rw [← (split s).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [cond_iff]
  simp [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]


lemma trace_sub {X Y : Type*} [Fintype X] [Fintype Y] (A : Matrix X X ℂ) (e : Y ≃ X) :
    (A.submatrix e e).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun x => A x x)

lemma pow_sub {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (A : Matrix X X ℂ) (e : Y ≃ X) (k : ℕ) :
    (A.submatrix e e) ^ k = (A ^ k).submatrix e e := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]

def α (s : Finset (Fin n)) : Cs D s ≃ SubBasis D sᶜ × Unit where
  toFun c := (fun i => c ⟨i.1, Finset.mem_compl.1 i.2⟩, ())
  invFun z := fun i => z.1 ⟨i.1, Finset.mem_compl.2 i.2⟩
  left_inv c := rfl
  right_inv z := by ext <;> rfl

def β (s : Finset (Fin n)) : SubBasis D s × Unit ≃ Cs D sᶜ where
  toFun r := fun i => r.1 ⟨i.1, by simpa using i.2⟩
  invFun w := (fun i => w ⟨i.1, by simpa using i.2⟩, ())
  left_inv r := by ext <;> rfl
  right_inv w := rfl

lemma Mat_compl (psi : EuclideanSpace ℂ (RegisterBasis D)) (s : Finset (Fin n)) :
    Mat psi sᶜ = ((Mat psi s)ᵀ).submatrix (α s).symm (β s).symm := by
  ext z w
  simp only [Mat, Matrix.submatrix_apply, Matrix.transpose_apply]
  refine congrArg psi (funext fun i => ?_)
  simp only [split, Equiv.piEquivPiSubtypeProd_symm_apply, α, β, Equiv.coe_fn_symm_mk]
  by_cases h : i ∈ s
  · have h' : i ∉ sᶜ := by simpa using h
    rw [dif_neg h', dif_pos h]
  · have h' : i ∈ sᶜ := by simpa using h
    rw [dif_pos h', dif_neg h]

lemma ent_compl (psi : EuclideanSpace ℂ (RegisterBasis D)) (s : Finset (Fin n)) :
    vnEntropy (Mat psi s * (Mat psi s)ᴴ) = vnEntropy (Mat psi sᶜ * (Mat psi sᶜ)ᴴ) := by
  unfold vnEntropy
  rw [A3S54AP.h_trace_cfc_eq (Mat psi s * (Mat psi s)ᴴ) (Mat psi sᶜ * (Mat psi sᶜ)ᴴ)
    (Matrix.isHermitian_mul_conjTranspose_self _)
    (Matrix.isHermitian_mul_conjTranspose_self _) (fun x : ℝ => x * Real.logb 2 x) (by simp)]
  intro k
  rw [A3S54AP.h_trace_pow, Mat_compl, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    pow_sub, trace_sub]


lemma ent_empty (psi : EuclideanSpace ℂ (RegisterBasis D)) (hpsi : ‖psi‖ = 1) :
    vnEntropy (Mat psi (∅ : Finset (Fin n)) * (Mat psi ∅)ᴴ) = 0 := by
  have hsum : ∑ x, psi x * conj (psi x) = 1 := by
    have h2 : ‖psi‖ ^ 2 = ∑ x, ‖psi x‖ ^ 2 := EuclideanSpace.norm_sq_eq psi
    rw [hpsi, one_pow] at h2
    have : ∑ x, psi x * conj (psi x) = ((∑ x, ‖psi x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [RCLike.mul_conj]; norm_cast
    rw [this, ← h2]; simp
  have h1 : Mat psi (∅ : Finset (Fin n)) * (Mat psi ∅)ᴴ = 1 := by
    ext a b
    have hab : a = b := Subsingleton.elim a b
    subst hab
    rw [Matrix.one_apply_eq, Matrix.mul_apply, ← hsum]
    simp only [Mat, Matrix.conjTranspose_apply, RCLike.star_def]
    rw [← (split (∅ : Finset (Fin n))).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single a.1 (fun p hp => absurd (Subsingleton.elim p a.1) hp)]
  rw [h1]
  simp [vnEntropy, cfc_one]

end A3S54AP

open QAlgorithms.Papers.Independent.Support50.P43 in
theorem solution {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (psi : EuclideanSpace ℂ (RegisterBasis D)) (hpsi : ‖psi‖ = 1) :
    alternativeOn (pureDensity psi) Finset.univ =
      conventionalOn (pureDensity psi) Finset.univ := by
  have hS : ∀ s : Finset (Fin n), marginalEntropyBits (pureDensity psi) s =
      vnEntropy (A3S54AP.Mat psi s * (A3S54AP.Mat psi s)ᴴ) := by
    intro s
    simp only [marginalEntropyBits, QAlgorithms.Papers.Independent.Claimed50.P33.entropyAt]
    rw [A3S54AP.marginal_eq]
    congr 1
  have hc : ∀ s : Finset (Fin n), marginalEntropyBits (pureDensity psi) s =
      marginalEntropyBits (pureDensity psi) sᶜ := by
    intro s; rw [hS, hS]; exact A3S54AP.ent_compl psi s
  have huniv : marginalEntropyBits (pureDensity psi) Finset.univ = 0 := by
    rw [hc, Finset.compl_univ, hS]; exact A3S54AP.ent_empty psi hpsi
  have herase : ∀ i, marginalEntropyBits (pureDensity psi) (Finset.univ.erase i) =
      marginalEntropyBits (pureDensity psi) {i} := by
    intro i; rw [hc]; congr 1; ext j; simp
  simp only [alternativeOn, conventionalOn, huniv, herase, mul_zero, sub_zero]
