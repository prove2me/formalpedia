-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P10.two_route_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:43:41.934763+00:00
-- url     : https://prove2.me/submissions/45d4ea00-4886-43fb-b992-b0e65a614f66

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq
lemma g73d_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
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

lemma g73d_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g73d_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g73d_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g73d_entropy_swap {X Y : Type*} [Fintype X] {_ : DecidableEq X} [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g73d_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g73d_trace_pow M)]

lemma g73d_submatrix_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (A : Matrix X X ℂ) (σ : Y ≃ X) (k : ℕ) :
    (A.submatrix σ σ) ^ k = (A ^ k).submatrix σ σ := by
  induction k with
  | zero => simp [Matrix.submatrix_one_equiv]
  | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]

lemma g73d_trace_submatrix {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix X X ℂ) (σ : Y ≃ X) : (A.submatrix σ σ).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp σ (fun i => A i i)

lemma g73d_entropy_submatrix {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] {_ : DecidableEq Y}
    (A : Matrix X X ℂ) (hA : A.IsHermitian) (σ : Y ≃ X) :
    vnEntropy (A.submatrix σ σ) = vnEntropy A := by
  unfold vnEntropy
  rw [g73d_trace_cfc_eq _ _ (hA.submatrix σ) hA _ (by simp)
    (fun k => by rw [g73d_submatrix_pow, g73d_trace_submatrix])]

/-- the "cut" matrix of a pure vector along s -/
def g73d_cut {n : ℕ} {D : Fin n → Type} (ψ : EuclideanSpace ℂ (RegisterBasis D))
    (s : Finset (Fin n)) :
    Matrix (SubBasis D s × Unit) ((i : {x : Fin n // ¬ x ∈ s}) → D i.1) ℂ :=
  fun a q => ψ ((Equiv.piEquivPiSubtypeProd (· ∈ s) D).symm (a.1, q))

lemma g73d_marg_eq {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (ψ : EuclideanSpace ℂ (RegisterBasis D)) (s : Finset (Fin n)) :
    registerMarginal (trivialExtension (pureDensity ψ)) s =
      g73d_cut ψ s * (g73d_cut ψ s)ᴴ := by
  ext a b
  set e := Equiv.piEquivPiSubtypeProd (· ∈ s) D
  simp only [registerMarginal, trivialExtension, pureDensity, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, g73d_cut, RCLike.star_def]
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp (fun y => if _ then _ else _)]
  simp only [Fintype.sum_prod_type]
  have key : ∀ x y x1 y1, ((∀ (i : Fin n) (hi : i ∈ s), e.symm (x, y) i = a.1 ⟨i, hi⟩ ∧
      e.symm (x1, y1) i = b.1 ⟨i, hi⟩) ∧ ∀ i ∉ s, e.symm (x, y) i = e.symm (x1, y1) i) ↔
      (x = a.1 ∧ x1 = b.1 ∧ y = y1) := by
    intro x y x1 y1
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · funext i; have := (h1 i.1 i.2).1; simpa [i.2] using this
      · funext i; have := (h1 i.1 i.2).2; simpa [i.2] using this
      · funext i; have := h2 i.1 i.2; simpa [i.2] using this
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨fun i hi => by simp [hi], fun i hi => by simp [hi]⟩
  simp_rw [key, ite_and]
  simp [e]

lemma g73d_entropy_compl {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (ψ : EuclideanSpace ℂ (RegisterBasis D)) (s t : Finset (Fin n))
    (h : ∀ i, i ∈ t ↔ i ∉ s) :
    entropyAt (trivialExtension (pureDensity ψ)) s =
      entropyAt (trivialExtension (pureDensity ψ)) t := by
  unfold entropyAt
  rw [g73d_marg_eq, g73d_marg_eq, g73d_entropy_swap]
  let σ : (SubBasis D t × Unit) ≃ ((i : {x : Fin n // ¬ x ∈ s}) → D i.1) :=
    { toFun := fun a q => a.1 ⟨q.1, (h q.1).2 q.2⟩
      invFun := fun q => (fun i => q ⟨i.1, (h i.1).1 i.2⟩, ())
      left_inv := fun a => by ext; rfl
      right_inv := fun q => rfl }
  have hts : ∀ i, i ∉ t → i ∈ s := fun i hi => by
    by_contra hs; exact hi ((h i).2 hs)
  let τ : ((i : {x : Fin n // ¬ x ∈ t}) → D i.1) ≃ (SubBasis D s × Unit) :=
    { toFun := fun q => (fun i => q ⟨i.1, fun hi => (h i.1).1 hi i.2⟩, ())
      invFun := fun p i => p.1 ⟨i.1, hts i.1 i.2⟩
      left_inv := fun q => rfl
      right_inv := fun p => by ext; rfl }
  have hM : g73d_cut ψ t = ((g73d_cut ψ s)ᵀ).submatrix σ τ := by
    ext c q
    simp only [g73d_cut, Matrix.submatrix_apply, Matrix.transpose_apply]
    refine congrArg (fun x => ψ x) ?_
    funext i
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply]
    by_cases hi : i ∈ s
    · have hit : i ∉ t := fun hh => (h i).1 hh hi
      simp [hi, hit, σ, τ]
    · have hit : i ∈ t := (h i).2 hi
      simp [hi, hit, σ, τ]
  rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    g73d_entropy_submatrix _ (Matrix.isHermitian_mul_conjTranspose_self _)]

theorem solution {D : Fin 5 → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (psi : EuclideanSpace ℂ (RegisterBasis D))
    (hpsi : ‖psi‖ = 1) :
    routeI (pureDensity psi) = routeDifference (pureDensity psi) / 2 ∧
    routeII (pureDensity psi) = routeDifference (pureDensity psi) / 2 ∧
    routeI (pureDensity psi) = routeII (pureDensity psi) := by
  have C := g73d_entropy_compl psi
  unfold routeI routeII routeDifference info conditionalMultipartiteInformation allParties
  simp only [Fin.sum_univ_two]
  simp
  rw [C {2,3,4} {0,1} (by decide), C {4} {0,1,2,3} (by decide), C {4,1,0} {2,3} (by decide),
    C {4,2,0} {1,3} (by decide), C (insert 4 (Finset.univ.biUnion ![{2, 3}, {0}])) {1} (by decide),
    C (insert 4 (insert 0 (Finset.univ.biUnion ![{1}, {2}]))) {3} (by decide)]
  rw [show (Finset.univ.biUnion ![{0, 1}, {2, 3}] : Finset (Fin 5)) = {0,1,2,3} by decide,
    show (Finset.univ.biUnion ![{2, 3}, {0, 1}] : Finset (Fin 5)) = {0,1,2,3} by decide,
    show (Finset.univ.biUnion ![{1}, {3}] : Finset (Fin 5)) = {1,3} by decide,
    show ({4, 0} : Finset (Fin 5)) = {0, 4} by decide]
  refine ⟨by ring, by ring, by ring⟩
