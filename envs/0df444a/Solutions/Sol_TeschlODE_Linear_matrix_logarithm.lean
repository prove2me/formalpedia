-- Prove2me | solution 1 for TeschlODE.Linear.matrix_logarithm
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T01:56:15.841024+00:00
-- url     : https://prove2.me/submissions/022acf7a-46bd-4864-907f-90dce170d74d

import Mathlib

open Set
open scoped Matrix

namespace FloquetAux

lemma U_exp_eq_sum {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} {k : ℕ} (hX : X ^ k = 0) :
    NormedSpace.exp X = ∑ i ∈ Finset.range k, ((i.factorial : ℂ)⁻¹) • X ^ i := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine tsum_eq_sum (s := Finset.range k) fun i hi => ?_
  have : k ≤ i := by simpa using hi
  rw [pow_eq_zero_of_le this hX, smul_zero]

lemma U_exp_nilpotent {n : ℕ} {S : Subalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)}
    (y : S) (hy : IsNilpotent (y : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ e : S, NormedSpace.exp (y : Matrix (Fin n) (Fin n) ℂ) =
      (1 : Matrix (Fin n) (Fin n) ℂ) + (y : Matrix (Fin n) (Fin n) ℂ) +
        (y : Matrix (Fin n) (Fin n) ℂ) ^ 2 * (e : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨m, hm⟩ := hy
  refine ⟨∑ j ∈ Finset.range m, (((j + 2).factorial : ℂ)⁻¹) • y ^ j, ?_⟩
  have hm2 : (y : Matrix (Fin n) (Fin n) ℂ) ^ (m + 2) = 0 :=
    pow_eq_zero_of_le (by omega) hm
  have hcoe : ((∑ j ∈ Finset.range m, (((j + 2).factorial : ℂ)⁻¹) • y ^ j : S) :
      Matrix (Fin n) (Fin n) ℂ) =
      ∑ j ∈ Finset.range m, (((j + 2).factorial : ℂ)⁻¹) • (y : Matrix (Fin n) (Fin n) ℂ) ^ j := by
    simp
  rw [hcoe, U_exp_eq_sum hm2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have h1 : ∀ i ∈ Finset.range m,
      (((i + 1 + 1).factorial : ℂ)⁻¹) • (y : Matrix (Fin n) (Fin n) ℂ) ^ (i + 1 + 1) =
      (y : Matrix (Fin n) (Fin n) ℂ) ^ 2 *
        ((((i + 2).factorial : ℂ)⁻¹) • (y : Matrix (Fin n) (Fin n) ℂ) ^ i) := by
    intro i _
    rw [mul_smul_comm, ← pow_add, add_comm 2 i]
  rw [Finset.sum_congr rfl h1]
  simp only [zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    pow_zero, pow_one]
  abel


/-- The generator `N` viewed as an element of the commutative subalgebra `ℂ[N]`. -/
def U_gen {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) : Algebra.adjoin ℂ {N} :=
  ⟨N, Algebra.self_mem_adjoin_singleton ℂ N⟩

@[simp] lemma U_gen_coe {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) :
    ((U_gen N : Algebra.adjoin ℂ {N}) : Matrix (Fin n) (Fin n) ℂ) = N := rfl

lemma U_gen_pow_eq_zero {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : N ^ m = 0) :
    (U_gen N) ^ m = 0 := by
  apply Subtype.ext
  simpa using hm

/-- Newton lifting: for every `j` there is a nilpotent `x ∈ ℂ[N]` with
`exp x = 1 + N + N ^ (j + 1) * d` for some `d ∈ ℂ[N]`. -/
lemma U_lift {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : N ^ m = 0) (j : ℕ) :
    ∃ x d : Algebra.adjoin ℂ {N}, IsNilpotent x ∧
      NormedSpace.exp (x : Matrix (Fin n) (Fin n) ℂ) =
        ((1 + U_gen N + (U_gen N) ^ (j + 1) * d : Algebra.adjoin ℂ {N}) :
          Matrix (Fin n) (Fin n) ℂ) := by
  induction j with
  | zero =>
    refine ⟨0, -1, IsNilpotent.zero, ?_⟩
    have h : (1 + U_gen N + (U_gen N) ^ (0 + 1) * (-1) : Algebra.adjoin ℂ {N}) = 1 := by ring
    rw [h]
    simp
  | succ j ih =>
    obtain ⟨x, d, hx, hexp⟩ := ih
    set nR : Algebra.adjoin ℂ {N} := U_gen N with hnR
    have hnil : IsNilpotent nR := ⟨m, U_gen_pow_eq_zero N hm⟩
    set D : Algebra.adjoin ℂ {N} := nR ^ (j + 1) * d with hD
    have hDnil : IsNilpotent D := Commute.isNilpotent_mul_right (Commute.all _ _) (hnil.pow_succ j)
    have hnegDnil : IsNilpotent (-D) := hDnil.neg
    obtain ⟨e, he⟩ := U_exp_nilpotent (-D) (hnegDnil.map (Subalgebra.val _))
    refine ⟨x - D, -d - nR ^ j * d ^ 2 + (1 + nR + D) * nR ^ j * d ^ 2 * e,
      Commute.isNilpotent_sub (Commute.all _ _) hx hDnil, ?_⟩
    have hxD : ((x - D : Algebra.adjoin ℂ {N}) : Matrix (Fin n) (Fin n) ℂ) =
        (x : Matrix (Fin n) (Fin n) ℂ) + ((-D : Algebra.adjoin ℂ {N}) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_eq_add_neg]; rfl
    have hcomm : Commute (x : Matrix (Fin n) (Fin n) ℂ)
        ((-D : Algebra.adjoin ℂ {N}) : Matrix (Fin n) (Fin n) ℂ) :=
      (Commute.all x (-D)).map (Subalgebra.val _)
    rw [hxD, Matrix.exp_add_of_commute _ _ hcomm, hexp, he]
    have hring : ((1 + nR + D) * (1 + (-D) + (-D) ^ 2 * e) : Algebra.adjoin ℂ {N}) =
        1 + nR + nR ^ (j + 1 + 1) *
          (-d - nR ^ j * d ^ 2 + (1 + nR + D) * nR ^ j * d ^ 2 * e) := by
      rw [hD]; ring
    rw [← hring]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_pow,
      Subalgebra.coe_neg]

/-- (U) Logarithm of a unipotent matrix: `1 + N` with `N` nilpotent is an exponential of a nilpotent
polynomial in `N`. -/
theorem exists_exp_eq_one_add_of_isNilpotent {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ)
    (hN : IsNilpotent N) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X ∈ Algebra.adjoin ℂ {N} ∧ IsNilpotent X ∧
      NormedSpace.exp X = 1 + N := by
  obtain ⟨m, hm⟩ := hN
  obtain ⟨x, d, hx, hexp⟩ := U_lift N hm m
  refine ⟨x, x.2, hx.map (Subalgebra.val _), ?_⟩
  rw [hexp]
  have h0 : (U_gen N) ^ (m + 1) = 0 := by rw [pow_succ, U_gen_pow_eq_zero N hm, zero_mul]
  rw [h0, zero_mul, add_zero]
  simp

/-- A semisimple matrix over `ℂ` is diagonalizable: `S * P = P * diagonal d` with `P` invertible. -/
lemma exists_eigenbasis_matrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S)) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      IsUnit P ∧ S * P = P * Matrix.diagonal d := by
  set f : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' S with hf
  have htop : ⨆ μ, f.eigenspace μ = ⊤ := hS.iSup_eigenspace_eq_top
  have hind : iSupIndep fun μ => f.eigenspace μ := f.eigenspaces_iSupIndep
  have hint : DirectSum.IsInternal fun μ => f.eigenspace μ :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let v : ∀ μ, Module.Basis (Fin (Module.finrank ℂ (f.eigenspace μ))) ℂ (f.eigenspace μ) :=
    fun μ => Module.finBasis ℂ _
  let b := hint.collectedBasis v
  let e : (Σ μ, Fin (Module.finrank ℂ (f.eigenspace μ))) ≃ Fin n :=
    b.indexEquiv (Pi.basisFun ℂ (Fin n))
  let b' : Module.Basis (Fin n) ℂ (Fin n → ℂ) := b.reindex e
  have hb' : ∀ j, f (b' j) = (e.symm j).1 • b' j := by
    intro j
    have h1 : b (e.symm j) ∈ f.eigenspace (e.symm j).1 := hint.collectedBasis_mem v (e.symm j)
    have h2 : b' j = b (e.symm j) := by simp [b']
    rw [h2]
    exact Module.End.mem_eigenspace_iff.mp h1
  have hP : ∀ i j, ((Pi.basisFun ℂ (Fin n)).toMatrix b') i j = b' j i := by
    intro i j
    simp [Module.Basis.toMatrix_apply]
  refine ⟨(Pi.basisFun ℂ (Fin n)).toMatrix b', fun j => (e.symm j).1, ?_, ?_⟩
  · have := (Pi.basisFun ℂ (Fin n)).invertibleToMatrix b'
    exact isUnit_of_invertible _
  · ext i j
    rw [Matrix.mul_diagonal, hP]
    have h := congrFun (hb' j) i
    simp only [hf, Matrix.toLin'_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_comm, ← h, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP]

/-- Intertwining `S * P = P * D` extends to polynomials in `S` and `D`. -/
lemma aeval_mul_eq_of_intertwine {n : ℕ} (S P D : Matrix (Fin n) (Fin n) ℂ)
    (h : S * P = P * D) (q : Polynomial ℂ) :
    Polynomial.aeval S q * P = P * Polynomial.aeval D q := by
  have hpow : ∀ k : ℕ, S ^ k * P = P * D ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial]
    calc algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) a * S ^ k * P
        = algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) a * (P * D ^ k) := by rw [mul_assoc, hpow]
      _ = P * (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) a * D ^ k) := by
        rw [← mul_assoc, Algebra.commutes, mul_assoc]

/-- A polynomial in a diagonal matrix is the diagonal of the pointwise values. -/
lemma aeval_diagonal_eq {n : ℕ} (d : Fin n → ℂ) (q : Polynomial ℂ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  have h1 : Matrix.diagonal d = Matrix.diagonalAlgHom (n := Fin n) ℂ d := rfl
  rw [h1, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal (Polynomial.aeval d q) = _
  congr 1
  funext i
  have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : Fin n => ℂ) i) d q
  simp [Polynomial.coe_aeval_eq_eval] at this ⊢

/-- (S) Logarithm of an invertible semisimple (= diagonalizable over `ℂ`) matrix, as a polynomial
in the matrix. -/
theorem exists_exp_eq_of_isSemisimple {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S)) (hdet : S.det ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, B ∈ Algebra.adjoin ℂ {S} ∧ NormedSpace.exp B = S := by
  obtain ⟨P, d, hP, hSP⟩ := exists_eigenbasis_matrix S hS
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPdet' : P.det ≠ 0 := hPdet.ne_zero
  have hD : S = P * Matrix.diagonal d * P⁻¹ := by
    rw [← hSP]
    exact (Matrix.mul_nonsing_inv_cancel_right P S hPdet).symm
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    have h1 := congrArg Matrix.det hSP
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h1
    have h2 : ∏ j, d j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [h2, mul_zero] at h1
    exact hdet ((mul_eq_zero.mp h1).resolve_right hPdet')
  -- interpolating polynomial
  set q : Polynomial ℂ := Lagrange.interpolate (Finset.univ.image d) (id : ℂ → ℂ) Complex.log
    with hqdef
  have hq : ∀ i, q.eval (d i) = Complex.log (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := Finset.univ.image d) (v := (id : ℂ → ℂ))
      (r := Complex.log) (i := d i) Function.injective_id.injOn
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simpa [hqdef] using this
  set L : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => Complex.log (d i)) with hL
  have hAq : Polynomial.aeval (Matrix.diagonal d) q = L := by
    rw [aeval_diagonal_eq, hL]
    congr 1
    funext i
    exact hq i
  have hB : Polynomial.aeval S q = P * L * P⁻¹ := by
    have h := aeval_mul_eq_of_intertwine S P (Matrix.diagonal d) hSP q
    rw [hAq] at h
    rw [← h]
    exact (Matrix.mul_nonsing_inv_cancel_right P _ hPdet).symm
  refine ⟨P * L * P⁻¹, hB ▸ Polynomial.aeval_mem_adjoin_singleton ℂ S, ?_⟩
  rw [Matrix.exp_conj P L hP, hL, Matrix.exp_diagonal, Pi.exp_def]
  conv_rhs => rw [hD]
  congr 2
  congr 1
  funext i
  rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log (hd0 i)]

/-- (J) Every invertible complex matrix is an exponential (Jordan–Chevalley assembly of (U), (S)). -/
theorem exists_exp_eq_of_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp B = M := by
  classical
  -- Jordan–Chevalley decomposition of `toLin' M`
  obtain ⟨n₀, hn₀, s₀, hs₀, hnil, hss, hsum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := Matrix.toLin' M)
  set e : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ) := Matrix.toLinAlgEquiv'
  have he : ∀ A : Matrix (Fin n) (Fin n) ℂ, e A = Matrix.toLin' A := fun A => rfl
  -- the nilpotent part as a matrix
  set N : Matrix (Fin n) (Fin n) ℂ := e.symm n₀ with hNdef
  have hNe : e N = n₀ := e.apply_symm_apply n₀
  have hNnil : IsNilpotent N := by
    have := hnil.map (e.symm : Module.End ℂ (Fin n → ℂ) →+* Matrix (Fin n) (Fin n) ℂ)
    simpa using this
  have hcommMN : Commute M N := by
    have h1 : Commute (Matrix.toLin' M) n₀ := Algebra.commute_of_mem_adjoin_self hn₀
    have h2 : Commute (e M) (e N) := by rw [he, hNe]; exact h1
    exact e.injective (by simp only [map_mul]; exact h2.eq)
  -- the semisimple part `S = M - N`
  set S : Matrix (Fin n) (Fin n) ℂ := M - N with hSdef
  have hSss : Module.End.IsSemisimple (Matrix.toLin' S) := by
    have : Matrix.toLin' S = s₀ := by
      rw [← he, hSdef, map_sub, hNe, he]
      rw [eq_sub_of_add_eq' hsum.symm]
    rw [this]; exact hss
  have hcommSN : Commute S N := hcommMN.sub_left (Commute.refl N)
  -- `S` is a unit: `S = M * (1 - M⁻¹ N)`
  have hMunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hM
  have hSunit : IsUnit S := by
    obtain ⟨u, hu⟩ := id hMunit
    have hcu : Commute (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) N := by
      have : Commute (↑u : Matrix (Fin n) (Fin n) ℂ) N := by rw [hu]; exact hcommMN
      exact this.units_inv_left
    have hnil' : IsNilpotent ((↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * N) :=
      hcu.isNilpotent_mul_left hNnil
    have h1 : IsUnit (1 - (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * N) := hnil'.isUnit_one_sub
    have h2 : S = M * (1 - (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * N) := by
      rw [mul_sub, mul_one, ← hu, ← mul_assoc, Units.mul_inv, one_mul, hSdef, hu]
    rw [h2]
    exact hMunit.mul h1
  have hSdet : S.det ≠ 0 := by
    rw [Matrix.isUnit_iff_isUnit_det] at hSunit
    exact isUnit_iff_ne_zero.mp hSunit
  -- `N' = S⁻¹ N`
  obtain ⟨v, hv⟩ := hSunit
  set N' : Matrix (Fin n) (Fin n) ℂ := (↑v⁻¹ : Matrix (Fin n) (Fin n) ℂ) * N with hN'def
  have hcv : Commute (↑v⁻¹ : Matrix (Fin n) (Fin n) ℂ) N := by
    have : Commute (↑v : Matrix (Fin n) (Fin n) ℂ) N := by rw [hv]; exact hcommSN
    exact this.units_inv_left
  have hN'nil : IsNilpotent N' := hcv.isNilpotent_mul_left hNnil
  have hSN' : Commute S N' := by
    have h1 : Commute S (↑v⁻¹ : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hv]; exact (Units.commute_coe_inv v)
    exact h1.mul_right hcommSN
  have hM_eq : M = S * (1 + N') := by
    rw [mul_add, mul_one, hN'def, ← mul_assoc, ← hv, Units.mul_inv, one_mul, hv, hSdef]
    abel
  obtain ⟨BS, hBS, hexpS⟩ := exists_exp_eq_of_isSemisimple S hSss hSdet
  obtain ⟨X, hX, -, hexpX⟩ := exists_exp_eq_one_add_of_isNilpotent N' hN'nil
  have hSX : Commute S X := Algebra.commute_of_mem_adjoin_singleton_of_commute hX hSN'
  have hBX : Commute BS X :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hBS hSX.symm).symm
  refine ⟨BS + X, ?_⟩
  rw [Matrix.exp_add_of_commute _ _ hBX, hexpS, hexpX, ← hM_eq]

lemma RU_exp_eq_sum {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {k : ℕ} (hX : X ^ k = 0) :
    NormedSpace.exp X = ∑ i ∈ Finset.range k, ((i.factorial : ℝ)⁻¹) • X ^ i := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine tsum_eq_sum (s := Finset.range k) fun i hi => ?_
  have : k ≤ i := by simpa using hi
  rw [pow_eq_zero_of_le this hX, smul_zero]

lemma RU_exp_nilpotent {n : ℕ} {S : Subalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (y : S) (hy : IsNilpotent (y : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ e : S, NormedSpace.exp (y : Matrix (Fin n) (Fin n) ℝ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) + (y : Matrix (Fin n) (Fin n) ℝ) +
        (y : Matrix (Fin n) (Fin n) ℝ) ^ 2 * (e : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨m, hm⟩ := hy
  refine ⟨∑ j ∈ Finset.range m, (((j + 2).factorial : ℝ)⁻¹) • y ^ j, ?_⟩
  have hm2 : (y : Matrix (Fin n) (Fin n) ℝ) ^ (m + 2) = 0 :=
    pow_eq_zero_of_le (by omega) hm
  have hcoe : ((∑ j ∈ Finset.range m, (((j + 2).factorial : ℝ)⁻¹) • y ^ j : S) :
      Matrix (Fin n) (Fin n) ℝ) =
      ∑ j ∈ Finset.range m, (((j + 2).factorial : ℝ)⁻¹) • (y : Matrix (Fin n) (Fin n) ℝ) ^ j := by
    simp
  rw [hcoe, RU_exp_eq_sum hm2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have h1 : ∀ i ∈ Finset.range m,
      (((i + 1 + 1).factorial : ℝ)⁻¹) • (y : Matrix (Fin n) (Fin n) ℝ) ^ (i + 1 + 1) =
      (y : Matrix (Fin n) (Fin n) ℝ) ^ 2 *
        ((((i + 2).factorial : ℝ)⁻¹) • (y : Matrix (Fin n) (Fin n) ℝ) ^ i) := by
    intro i _
    rw [mul_smul_comm, ← pow_add, add_comm 2 i]
  rw [Finset.sum_congr rfl h1]
  simp only [zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    pow_zero, pow_one]
  abel


/-- The generator `N` viewed as an element of the commutative subalgebra `ℝ[N]`. -/
def RU_gen {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) : Algebra.adjoin ℝ {N} :=
  ⟨N, Algebra.self_mem_adjoin_singleton ℝ N⟩

@[simp] lemma RU_gen_coe {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) :
    ((RU_gen N : Algebra.adjoin ℝ {N}) : Matrix (Fin n) (Fin n) ℝ) = N := rfl

lemma RU_gen_pow_eq_zero {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} (hm : N ^ m = 0) :
    (RU_gen N) ^ m = 0 := by
  apply Subtype.ext
  simpa using hm

/-- Newton lifting: for every `j` there is a nilpotent `x ∈ ℝ[N]` with
`exp x = 1 + N + N ^ (j + 1) * d` for some `d ∈ ℝ[N]`. -/
lemma RU_lift {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} (hm : N ^ m = 0) (j : ℕ) :
    ∃ x d : Algebra.adjoin ℝ {N}, IsNilpotent x ∧
      NormedSpace.exp (x : Matrix (Fin n) (Fin n) ℝ) =
        ((1 + RU_gen N + (RU_gen N) ^ (j + 1) * d : Algebra.adjoin ℝ {N}) :
          Matrix (Fin n) (Fin n) ℝ) := by
  induction j with
  | zero =>
    refine ⟨0, -1, IsNilpotent.zero, ?_⟩
    have h : (1 + RU_gen N + (RU_gen N) ^ (0 + 1) * (-1) : Algebra.adjoin ℝ {N}) = 1 := by ring
    rw [h]
    simp
  | succ j ih =>
    obtain ⟨x, d, hx, hexp⟩ := ih
    set nR : Algebra.adjoin ℝ {N} := RU_gen N with hnR
    have hnil : IsNilpotent nR := ⟨m, RU_gen_pow_eq_zero N hm⟩
    set D : Algebra.adjoin ℝ {N} := nR ^ (j + 1) * d with hD
    have hDnil : IsNilpotent D := Commute.isNilpotent_mul_right (Commute.all _ _) (hnil.pow_succ j)
    have hnegDnil : IsNilpotent (-D) := hDnil.neg
    obtain ⟨e, he⟩ := RU_exp_nilpotent (-D) (hnegDnil.map (Subalgebra.val _))
    refine ⟨x - D, -d - nR ^ j * d ^ 2 + (1 + nR + D) * nR ^ j * d ^ 2 * e,
      Commute.isNilpotent_sub (Commute.all _ _) hx hDnil, ?_⟩
    have hxD : ((x - D : Algebra.adjoin ℝ {N}) : Matrix (Fin n) (Fin n) ℝ) =
        (x : Matrix (Fin n) (Fin n) ℝ) + ((-D : Algebra.adjoin ℝ {N}) : Matrix (Fin n) (Fin n) ℝ) := by
      rw [sub_eq_add_neg]; rfl
    have hcomm : Commute (x : Matrix (Fin n) (Fin n) ℝ)
        ((-D : Algebra.adjoin ℝ {N}) : Matrix (Fin n) (Fin n) ℝ) :=
      (Commute.all x (-D)).map (Subalgebra.val _)
    rw [hxD, Matrix.exp_add_of_commute _ _ hcomm, hexp, he]
    have hring : ((1 + nR + D) * (1 + (-D) + (-D) ^ 2 * e) : Algebra.adjoin ℝ {N}) =
        1 + nR + nR ^ (j + 1 + 1) *
          (-d - nR ^ j * d ^ 2 + (1 + nR + D) * nR ^ j * d ^ 2 * e) := by
      rw [hD]; ring
    rw [← hring]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_pow,
      Subalgebra.coe_neg]

/-- (RU) Logarithm of a unipotent matrix: `1 + N` with `N` nilpotent is an exponential of a nilpotent
polynomial in `N`. -/
theorem exists_exp_eq_one_add_of_isNilpotent_real {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hN : IsNilpotent N) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, X ∈ Algebra.adjoin ℝ {N} ∧ IsNilpotent X ∧
      NormedSpace.exp X = 1 + N := by
  obtain ⟨m, hm⟩ := hN
  obtain ⟨x, d, hx, hexp⟩ := RU_lift N hm m
  refine ⟨x, x.2, hx.map (Subalgebra.val _), ?_⟩
  rw [hexp]
  have h0 : (RU_gen N) ^ (m + 1) = 0 := by rw [pow_succ, RU_gen_pow_eq_zero N hm, zero_mul]
  rw [h0, zero_mul, add_zero]
  simp

/-- A continuous ring homomorphism commutes with the matrix exponential: complexification. -/
lemma RS_exp_map {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp (B.map (algebraMap ℝ ℂ)) = (NormedSpace.exp B).map (algebraMap ℝ ℂ) := by
  open scoped Matrix.Norms.Operator in
  have hc : Continuous ((algebraMap ℝ ℂ).mapMatrix : Matrix (Fin n) (Fin n) ℝ →+*
      Matrix (Fin n) (Fin n) ℂ) :=
    Continuous.matrix_map continuous_id (continuous_algebraMap ℝ ℂ)
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp ((algebraMap ℝ ℂ).mapMatrix) hc B).symm

/-- A semisimple matrix over `ℂ` is diagonalizable: `S * P = P * diagonal d` with `P` invertible. -/
lemma RS_eigenbasis_matrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S)) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      IsUnit P ∧ S * P = P * Matrix.diagonal d := by
  set f : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' S with hf
  have htop : ⨆ μ, f.eigenspace μ = ⊤ := hS.iSup_eigenspace_eq_top
  have hind : iSupIndep fun μ => f.eigenspace μ := f.eigenspaces_iSupIndep
  have hint : DirectSum.IsInternal fun μ => f.eigenspace μ :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let v : ∀ μ, Module.Basis (Fin (Module.finrank ℂ (f.eigenspace μ))) ℂ (f.eigenspace μ) :=
    fun μ => Module.finBasis ℂ _
  let b := hint.collectedBasis v
  let e : (Σ μ, Fin (Module.finrank ℂ (f.eigenspace μ))) ≃ Fin n :=
    b.indexEquiv (Pi.basisFun ℂ (Fin n))
  let b' : Module.Basis (Fin n) ℂ (Fin n → ℂ) := b.reindex e
  have hb' : ∀ j, f (b' j) = (e.symm j).1 • b' j := by
    intro j
    have h1 : b (e.symm j) ∈ f.eigenspace (e.symm j).1 := hint.collectedBasis_mem v (e.symm j)
    have h2 : b' j = b (e.symm j) := by simp [b']
    rw [h2]
    exact Module.End.mem_eigenspace_iff.mp h1
  have hP : ∀ i j, ((Pi.basisFun ℂ (Fin n)).toMatrix b') i j = b' j i := by
    intro i j
    simp [Module.Basis.toMatrix_apply]
  refine ⟨(Pi.basisFun ℂ (Fin n)).toMatrix b', fun j => (e.symm j).1, ?_, ?_⟩
  · have := (Pi.basisFun ℂ (Fin n)).invertibleToMatrix b'
    exact isUnit_of_invertible _
  · ext i j
    rw [Matrix.mul_diagonal, hP]
    have h := congrFun (hb' j) i
    simp only [hf, Matrix.toLin'_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_comm, ← h, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP]

/-- Intertwining `S * P = P * D` extends to polynomials in `S` and `D`. -/
lemma RS_aeval_mul_eq_of_intertwine {n : ℕ} (S P D : Matrix (Fin n) (Fin n) ℂ)
    (h : S * P = P * D) (q : Polynomial ℂ) :
    Polynomial.aeval S q * P = P * Polynomial.aeval D q := by
  have hpow : ∀ k : ℕ, S ^ k * P = P * D ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial]
    calc algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) a * S ^ k * P
        = algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) a * (P * D ^ k) := by rw [mul_assoc, hpow]
      _ = P * (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) a * D ^ k) := by
        rw [← mul_assoc, Algebra.commutes, mul_assoc]

/-- A polynomial in a diagonal matrix is the diagonal of the pointwise values. -/
lemma RS_aeval_diagonal_eq {n : ℕ} (d : Fin n → ℂ) (q : Polynomial ℂ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  have h1 : Matrix.diagonal d = Matrix.diagonalAlgHom (n := Fin n) ℂ d := rfl
  rw [h1, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal (Polynomial.aeval d q) = _
  congr 1
  funext i
  have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : Fin n => ℂ) i) d q
  simp [Polynomial.coe_aeval_eq_eval] at this ⊢

/-- Polynomials commute with complexification of a real matrix. -/
lemma RS_aeval_map {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (r : Polynomial ℝ) :
    Polynomial.aeval (S.map (algebraMap ℝ ℂ)) (r.map (algebraMap ℝ ℂ)) =
      (Polynomial.aeval S r).map (algebraMap ℝ ℂ) := by
  rw [Polynomial.aeval_map_algebraMap ℂ (S.map (algebraMap ℝ ℂ)) r]
  have := Polynomial.aeval_algHom_apply
    ((Algebra.ofId ℝ ℂ).mapMatrix : Matrix (Fin n) (Fin n) ℝ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ) S r
  exact this

/-- The complexification of a semisimple real matrix is semisimple. -/
lemma RS_semisimple_complexify {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S)) :
    Module.End.IsSemisimple (Matrix.toLin' (S.map (algebraMap ℝ ℂ))) := by
  set p : Polynomial ℝ := minpoly ℝ (Matrix.toLin' S) with hp
  have hsq : Squarefree p := hS.minpoly_squarefree
  have hp0 : Polynomial.aeval S p = 0 := by
    have h1 : Polynomial.aeval (Matrix.toLin' S) p = 0 := minpoly.aeval ℝ _
    have h2 := Polynomial.aeval_algHom_apply
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] Module.End ℝ (Fin n → ℝ)).toAlgHom S p
    have h3 : (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ]
        Module.End ℝ (Fin n → ℝ)).toAlgHom S = Matrix.toLin' S := rfl
    rw [h3, h1] at h2
    exact (map_eq_zero_iff _ (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin n)).injective).mp h2.symm
  have hsepmap : Squarefree (p.map (algebraMap ℝ ℂ)) :=
    (PerfectField.separable_iff_squarefree.mpr hsq).map.squarefree
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsepmap ?_
  have h1 : Polynomial.aeval (S.map (algebraMap ℝ ℂ)) (p.map (algebraMap ℝ ℂ)) = 0 := by
    rw [RS_aeval_map, hp0]
    simp
  have h2 := Polynomial.aeval_algHom_apply
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ)).toAlgHom
    (S.map (algebraMap ℝ ℂ)) (p.map (algebraMap ℝ ℂ))
  have h3 : (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ]
      Module.End ℂ (Fin n → ℂ)).toAlgHom (S.map (algebraMap ℝ ℂ)) =
        Matrix.toLin' (S.map (algebraMap ℝ ℂ)) := rfl
  rw [h3, h1] at h2
  simpa using h2

/-- Columns of the eigenbasis matrix are eigenvectors. -/
lemma RS_col_eig {n : ℕ} {S P : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ} (hP : IsUnit P)
    (hSP : S * P = P * Matrix.diagonal d) (i : Fin n) :
    (fun k => P k i) ≠ 0 ∧ S.mulVec (fun k => P k i) = d i • (fun k => P k i) := by
  constructor
  · intro h0
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hP
    have h1 : P.mulVec (Pi.single i 1) = P.mulVec 0 := by
      rw [Matrix.mulVec_zero]
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      exact congrFun h0 k
    have h2 := hinj h1
    have h3 := congrFun h2 i
    simp at h3
  · funext k
    have h := congrFun (congrFun hSP k) i
    rw [Matrix.mul_diagonal] at h
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h, mul_comm]

/-- Every eigenvalue of `S` is one of the diagonal entries `d j`. -/
lemma RS_eig_mem {n : ℕ} {S P : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ} (hP : IsUnit P)
    (hSP : S * P = P * Matrix.diagonal d) {z : ℂ} {w : Fin n → ℂ} (hw : w ≠ 0)
    (hz : S.mulVec w = z • w) : ∃ j, d j = z := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hP
  set u : Fin n → ℂ := P⁻¹.mulVec w with hu
  have hPu : P.mulVec u = w := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hu0 : u ≠ 0 := by
    intro h
    apply hw
    rw [← hPu, h, Matrix.mulVec_zero]
  have h1 : P.mulVec ((Matrix.diagonal d).mulVec u) = P.mulVec (z • u) := by
    rw [Matrix.mulVec_mulVec, ← hSP, ← Matrix.mulVec_mulVec, hPu, hz, Matrix.mulVec_smul, hPu]
  have h2 := hinj h1
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hu0
    exact ⟨j, by simpa using hj⟩
  refine ⟨j, ?_⟩
  have h3 := congrFun h2 j
  rw [Matrix.mulVec_diagonal] at h3
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  exact mul_right_cancel₀ hj (by rw [h3])

/-- A real matrix commutes with complex conjugation of vectors. -/
lemma RS_conj_mulVec {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) :
    (S.map (algebraMap ℝ ℂ)).mulVec (fun i => starRingEnd ℂ (v i)) =
      fun i => starRingEnd ℂ ((S.map (algebraMap ℝ ℂ)).mulVec v i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (Complex.conj_ofReal _).symm

/-- (RS) Functional calculus for a real semisimple matrix. -/
theorem exists_real_exp_eq_aeval {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S)) (p : Polynomial ℝ) (L : ℂ → ℂ)
    (hLconj : ∀ z, L (starRingEnd ℂ z) = starRingEnd ℂ (L z))
    (hL : ∀ z : ℂ, (∃ v : Fin n → ℂ, v ≠ 0 ∧
        (S.map (algebraMap ℝ ℂ)) *ᵥ v = z • v) →
      Complex.exp (L z) = (p.map (algebraMap ℝ ℂ)).eval z) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B ∈ Algebra.adjoin ℝ {S} ∧
      NormedSpace.exp B = Polynomial.aeval S p := by
  classical
  set Sc : Matrix (Fin n) (Fin n) ℂ := S.map (algebraMap ℝ ℂ) with hSc
  obtain ⟨P, d, hP, hSP⟩ := RS_eigenbasis_matrix Sc (RS_semisimple_complexify S hS)
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  set V : Finset ℂ := Finset.univ.image d with hV
  have hVmem : ∀ z, z ∈ V ↔ ∃ j, d j = z := by intro z; simp [hV]
  -- `V` is closed under complex conjugation
  have hVconj : ∀ z ∈ V, starRingEnd ℂ z ∈ V := by
    intro z hz
    obtain ⟨i, rfl⟩ := (hVmem z).mp hz
    obtain ⟨hne, heig⟩ := RS_col_eig hP hSP i
    have hw : (fun k => starRingEnd ℂ (P k i)) ≠ 0 := by
      intro h
      apply hne
      funext k
      have := congrFun h k
      simpa using this
    have hc := RS_conj_mulVec S (fun k => P k i)
    have hw2 : Sc.mulVec (fun k => starRingEnd ℂ (P k i)) =
        starRingEnd ℂ (d i) • (fun k => starRingEnd ℂ (P k i)) := by
      rw [hSc, hc, heig]
      funext k
      simp
    exact (hVmem _).mpr (RS_eig_mem hP hSP hw hw2)
  -- the interpolating polynomial
  set q : Polynomial ℂ := Lagrange.interpolate V (id : ℂ → ℂ) L with hq
  have hqeval : ∀ z ∈ V, q.eval z = L z := by
    intro z hz
    have := Lagrange.eval_interpolate_at_node (s := V) (v := (id : ℂ → ℂ)) (r := L) (i := z)
      Function.injective_id.injOn hz
    simpa [hq] using this
  have hqdeg : q.degree < V.card :=
    Lagrange.degree_interpolate_lt (s := V) (v := (id : ℂ → ℂ)) (r := L)
      Function.injective_id.injOn
  have hqmap : q.map (starRingEnd ℂ) = q := by
    have hdeg' : (q.map (starRingEnd ℂ)).degree < V.card := by
      rw [Polynomial.degree_map]; exact hqdeg
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq V hdeg' hqdeg ?_
    intro z hz
    have h1 : (q.map (starRingEnd ℂ)).eval z = starRingEnd ℂ (q.eval (starRingEnd ℂ z)) := by
      rw [Polynomial.eval_map, ← Polynomial.eval₂_at_apply, Complex.conj_conj]
    rw [h1, hqeval _ (hVconj z hz), hLconj, Complex.conj_conj, hqeval z hz]
  have hreal : ∀ k, ∃ r : ℝ, q.coeff k = (r : ℂ) := by
    intro k
    have := congrArg (fun r => Polynomial.coeff r k) hqmap
    simp only [Polynomial.coeff_map] at this
    exact Complex.conj_eq_iff_real.mp this
  have hlift : q ∈ Polynomial.lifts (algebraMap ℝ ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    obtain ⟨r, hr⟩ := hreal k
    exact ⟨r, hr.symm⟩
  obtain ⟨qR, hqR⟩ := (Polynomial.mem_lifts _).mp hlift
  -- the real logarithm
  refine ⟨Polynomial.aeval S qR, Polynomial.aeval_mem_adjoin_singleton ℝ S, ?_⟩
  apply Matrix.map_injective (algebraMap ℝ ℂ).injective
  show (NormedSpace.exp (Polynomial.aeval S qR)).map (algebraMap ℝ ℂ) =
    (Polynomial.aeval S p).map (algebraMap ℝ ℂ)
  rw [← RS_exp_map, ← RS_aeval_map, ← RS_aeval_map, hqR]
  have hconj : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, X * P = P * Y → X = P * Y * P⁻¹ := by
    intro X Y h
    rw [← h]
    exact (Matrix.mul_nonsing_inv_cancel_right P X hPdet).symm
  have hAq := hconj _ _ (RS_aeval_mul_eq_of_intertwine Sc P (Matrix.diagonal d) hSP q)
  rw [RS_aeval_diagonal_eq] at hAq
  have hAp := hconj _ _ (RS_aeval_mul_eq_of_intertwine Sc P (Matrix.diagonal d) hSP
    (p.map (algebraMap ℝ ℂ)))
  rw [RS_aeval_diagonal_eq] at hAp
  have hdiag : (fun i => q.eval (d i)) = fun i => L (d i) := by
    funext i
    exact hqeval _ ((hVmem _).mpr ⟨i, rfl⟩)
  rw [hdiag] at hAq
  rw [hAq, hAp, Matrix.exp_conj P _ hP, Matrix.exp_diagonal, Pi.exp_def]
  congr 2
  congr 1
  funext i
  rw [← Complex.exp_eq_exp_ℂ]
  exact hL (d i) ⟨_, (RS_col_eig hP hSP i).1, (RS_col_eig hP hSP i).2⟩

lemma FIN_jc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ N : Matrix (Fin n) (Fin n) ℝ, IsNilpotent N ∧ Commute A N ∧
      Module.End.IsSemisimple (Matrix.toLin' (A - N)) := by
  classical
  obtain ⟨n₀, hn₀, s₀, hs₀, hnil, hss, hsum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := Matrix.toLin' A)
  set e : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] Module.End ℝ (Fin n → ℝ) := Matrix.toLinAlgEquiv'
  have he : ∀ B : Matrix (Fin n) (Fin n) ℝ, e B = Matrix.toLin' B := fun B => rfl
  set N : Matrix (Fin n) (Fin n) ℝ := e.symm n₀ with hNdef
  have hNe : e N = n₀ := e.apply_symm_apply n₀
  have hNnil : IsNilpotent N := by
    have := hnil.map (e.symm : Module.End ℝ (Fin n → ℝ) →+* Matrix (Fin n) (Fin n) ℝ)
    simpa using this
  have hcomm : Commute A N := by
    have h1 : Commute (Matrix.toLin' A) n₀ := Algebra.commute_of_mem_adjoin_self hn₀
    have h2 : Commute (e A) (e N) := by rw [he, hNe]; exact h1
    exact e.injective (by simp only [map_mul]; exact h2.eq)
  refine ⟨N, hNnil, hcomm, ?_⟩
  have : Matrix.toLin' (A - N) = s₀ := by
    rw [← he, map_sub, hNe, he]
    rw [eq_sub_of_add_eq' hsum.symm]
  rw [this]; exact hss

/-- A unit minus a commuting nilpotent is a unit. -/
lemma FIN_isUnit_sub {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M)
    (hN : IsNilpotent N) (hc : Commute M N) : IsUnit (M - N) := by
  rw [sub_eq_add_neg]
  exact hN.neg.isUnit_add_left_of_commute hM hc.symm.neg_left

/-- Eigenvalues of the semisimple part `A - N` are eigenvalues of `A` (real case). -/
lemma FIN_eig_transfer {n : ℕ} {A N : Matrix (Fin n) (Fin n) ℝ} (hN : IsNilpotent N)
    (hc : Commute A N) (z : ℝ) (hw : ∃ w : Fin n → ℝ, w ≠ 0 ∧ (A - N) *ᵥ w = z • w) :
    ∃ w : Fin n → ℝ, w ≠ 0 ∧ A *ᵥ w = z • w := by
  by_contra h'
  have h : ∀ w : Fin n → ℝ, w ≠ 0 → A *ᵥ w ≠ z • w := fun w hw0 hw1 => h' ⟨w, hw0, hw1⟩
  have hdet : (A - z • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw1⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    refine h w hw0 ?_
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hw1
    exact hw1
  have hu : IsUnit (A - z • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hdet
  have hc' : Commute (A - z • (1 : Matrix (Fin n) (Fin n) ℝ)) N :=
    hc.sub_left ((Commute.one_left N).smul_left z)
  have hu2 := FIN_isUnit_sub hu hN hc'
  rw [Matrix.isUnit_iff_isUnit_det] at hu2
  have hdet2 := isUnit_iff_ne_zero.mp hu2
  obtain ⟨w, hw0, hw1⟩ := hw
  refine hdet2 ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨w, hw0, ?_⟩)
  have : A - z • (1 : Matrix (Fin n) (Fin n) ℝ) - N = (A - N) - z • 1 := by abel
  rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hw1, sub_self]

/-- A complex eigenvector of a real matrix with real eigenvalue yields a real eigenvector. -/
lemma FIN_real_eig_of_complex {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) (hz : z.im = 0)
    (v : Fin n → ℂ) (hv : v ≠ 0) (h : (S.map (algebraMap ℝ ℂ)) *ᵥ v = z • v) :
    ∃ w : Fin n → ℝ, w ≠ 0 ∧ S *ᵥ w = z.re • w := by
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = (x : ℂ) :=
    ⟨z.re, Complex.ext (by simp) (by simpa using hz)⟩
  simp only [Complex.ofReal_re]
  set M : Matrix (Fin n) (Fin n) ℝ := S - x • (1 : Matrix (Fin n) (Fin n) ℝ) with hM
  have hMv : (M.map (algebraMap ℝ ℂ)) *ᵥ v = 0 := by
    have : M.map (algebraMap ℝ ℂ) =
        S.map (algebraMap ℝ ℂ) - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hM]
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_self]
  have hdetc : (M.map (algebraMap ℝ ℂ)).det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff).1 ⟨v, hv, hMv⟩
  have hdet : M.det = 0 := by
    have h2 := RingHom.map_det (algebraMap ℝ ℂ) M
    have h3 : algebraMap ℝ ℂ M.det = 0 := h2.trans hdetc
    exact (algebraMap ℝ ℂ).injective (by rw [h3, map_zero])
  obtain ⟨w, hw0, hw1⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  refine ⟨w, hw0, ?_⟩
  rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hw1
  exact hw1

/-- The logarithm used for the semisimple part: principal branch off the real axis,
`log |x|` on the real axis. -/
noncomputable def FIN_L0 (z : ℂ) : ℂ :=
  if z.im = 0 then ((Real.log |z.re| : ℝ) : ℂ) else Complex.log z

lemma FIN_L0_conj (z : ℂ) : FIN_L0 (starRingEnd ℂ z) = starRingEnd ℂ (FIN_L0 z) := by
  unfold FIN_L0
  by_cases h : z.im = 0
  · have h' : (starRingEnd ℂ z).im = 0 := by simp [h]
    simp [h, h']
  · have h' : (starRingEnd ℂ z).im ≠ 0 := by simpa using h
    rw [if_neg h, if_neg h']
    apply Complex.log_conj
    intro harg
    exact h (Complex.arg_eq_pi_iff.mp harg).2

lemma FIN_exp_L0_nonreal {z : ℂ} (h : z.im ≠ 0) : Complex.exp (FIN_L0 z) = z := by
  unfold FIN_L0
  rw [if_neg h]
  exact Complex.exp_log (fun h0 => h (by simp [h0]))

lemma FIN_exp_L0_real {z : ℂ} (h : z.im = 0) (hre : z.re ≠ 0) :
    Complex.exp (FIN_L0 z) = ((|z.re| : ℝ) : ℂ) := by
  unfold FIN_L0
  rw [if_pos h, ← Complex.ofReal_exp, Real.exp_log (abs_pos.mpr hre)]

/-- A nonzero real vector with `A w = μ w` makes `μ` an eigenvalue of `toLin' A`. -/
lemma FIN_hasEigenvalue_of_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    {w : Fin n → ℝ} (hw : w ≠ 0) (h : A *ᵥ w = μ • w) :
    Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := w)
  refine ⟨?_, hw⟩
  rw [Module.End.mem_eigenspace_iff]
  simpa [Matrix.toLin'_apply] using h

/-- Exponential of a sum of commuting pieces taken from `adjoin ℝ {S}` and `adjoin ℝ {N'}`. -/
lemma FIN_exp_add {n : ℕ} {S N' BS X : Matrix (Fin n) (Fin n) ℝ} (hc : Commute S N')
    (hBS : BS ∈ Algebra.adjoin ℝ {S}) (hX : X ∈ Algebra.adjoin ℝ {N'}) :
    NormedSpace.exp (BS + X) = NormedSpace.exp BS * NormedSpace.exp X := by
  have hSX : Commute S X := Algebra.commute_of_mem_adjoin_singleton_of_commute hX hc
  have hBX : Commute BS X :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hBS hSX.symm).symm
  exact Matrix.exp_add_of_commute _ _ hBX

/-- Part (2): a real matrix whose real eigenvalues are all positive has a real logarithm. -/
lemma FIN_part2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → 0 < μ) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A := by
  classical
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw1⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have : Module.End.HasEigenvalue (Matrix.toLin' A) 0 :=
      FIN_hasEigenvalue_of_mulVec hw0 (by simpa using hw1)
    exact lt_irrefl _ (hA 0 this)
  obtain ⟨N, hN, hc, hss⟩ := FIN_jc A
  set S : Matrix (Fin n) (Fin n) ℝ := A - N with hSdef
  have hAunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hdet
  have hSunit : IsUnit S := FIN_isUnit_sub hAunit hN hc
  have hcSN : Commute S N := hc.sub_left (Commute.refl N)
  obtain ⟨v, hv⟩ := hSunit
  set N' : Matrix (Fin n) (Fin n) ℝ := (↑v⁻¹ : Matrix (Fin n) (Fin n) ℝ) * N with hN'def
  have hcv : Commute (↑v⁻¹ : Matrix (Fin n) (Fin n) ℝ) N := by
    have : Commute (↑v : Matrix (Fin n) (Fin n) ℝ) N := by rw [hv]; exact hcSN
    exact this.units_inv_left
  have hN'nil : IsNilpotent N' := hcv.isNilpotent_mul_left hN
  have hSN' : Commute S N' := by
    have h1 : Commute S (↑v⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
      rw [← hv]; exact Units.commute_coe_inv v
    exact h1.mul_right hcSN
  have hA_eq : A = S * (1 + N') := by
    rw [mul_add, mul_one, hN'def, ← mul_assoc, ← hv, Units.mul_inv, one_mul, hv, hSdef]
    abel
  -- the semisimple part
  have hL : ∀ z : ℂ, (∃ w : Fin n → ℂ, w ≠ 0 ∧
        (S.map (algebraMap ℝ ℂ)) *ᵥ w = z • w) →
      Complex.exp (FIN_L0 z) = ((Polynomial.X : Polynomial ℝ).map (algebraMap ℝ ℂ)).eval z := by
    intro z ⟨w, hw0, hw1⟩
    simp only [Polynomial.map_X, Polynomial.eval_X]
    by_cases him : z.im = 0
    · obtain ⟨u, hu0, hu1⟩ := FIN_real_eig_of_complex S z him w hw0 hw1
      obtain ⟨u', hu0', hu1'⟩ := FIN_eig_transfer hN hc z.re ⟨u, hu0, hu1⟩
      have hpos : 0 < z.re := hA _ (FIN_hasEigenvalue_of_mulVec hu0' hu1')
      rw [FIN_exp_L0_real him hpos.ne', abs_of_pos hpos]
      exact Complex.ext (by simp) (by simpa using him.symm)
    · exact FIN_exp_L0_nonreal him
  obtain ⟨BS, hBS, hexp⟩ := exists_real_exp_eq_aeval S hss Polynomial.X FIN_L0 FIN_L0_conj hL
  rw [Polynomial.aeval_X] at hexp
  obtain ⟨X, hX, -, hexpX⟩ := exists_exp_eq_one_add_of_isNilpotent_real N' hN'nil
  refine ⟨BS + X, ?_⟩
  rw [FIN_exp_add hSN' hBS hX, hexp, hexpX, ← hA_eq]

/-- Part (3): for an invertible real matrix, `A * A` has a real logarithm. -/
lemma FIN_part3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hdet : A.det ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A * A := by
  classical
  obtain ⟨N, hN, hc, hss⟩ := FIN_jc A
  set S : Matrix (Fin n) (Fin n) ℝ := A - N with hSdef
  have hAunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hdet
  have hSunit : IsUnit S := FIN_isUnit_sub hAunit hN hc
  have hSdet : S.det ≠ 0 := by
    have := hSunit
    rw [Matrix.isUnit_iff_isUnit_det] at this
    exact isUnit_iff_ne_zero.mp this
  have hcSN : Commute S N := hc.sub_left (Commute.refl N)
  obtain ⟨v, hv⟩ := hSunit
  set Vi : Matrix (Fin n) (Fin n) ℝ := (↑v⁻¹ : Matrix (Fin n) (Fin n) ℝ) with hVi
  have hVS : S * Vi = 1 := by rw [← hv]; exact Units.mul_inv v
  have hcVN : Commute Vi N := by
    have : Commute (↑v : Matrix (Fin n) (Fin n) ℝ) N := by rw [hv]; exact hcSN
    exact this.units_inv_left
  have hcSV : Commute S Vi := by rw [← hv]; exact Units.commute_coe_inv v
  have hcVS : Commute Vi S := hcSV.symm
  set Y : Matrix (Fin n) (Fin n) ℝ := S * N + N * S + N * N with hY
  set N'' : Matrix (Fin n) (Fin n) ℝ := Vi * Vi * Y with hN''
  have hAeq : A = S + N := by rw [hSdef]; abel
  have hAA : A * A = S * S * (1 + N'') := by
    have key : S * S * N'' = Y := by
      calc S * S * N'' = S * (S * Vi) * (Vi * Y) := by
            rw [hN'']
            noncomm_ring
        _ = S * (Vi * Y) := by rw [hVS, mul_one]
        _ = (S * Vi) * Y := by rw [mul_assoc]
        _ = Y := by rw [hVS, one_mul]
    rw [mul_add, mul_one, key, hAeq, hY]
    noncomm_ring
  have hYnil : IsNilpotent Y := by
    have hYeq : Y = N * (S + S + N) := by
      rw [hY, hcSN.eq]; noncomm_ring
    have hc2 : Commute N (S + S + N) :=
      (hcSN.symm.add_right hcSN.symm).add_right (Commute.refl N)
    rw [hYeq]
    exact hc2.isNilpotent_mul_right hN
  have hcVY : Commute Vi Y :=
    ((hcVS.mul_right hcVN).add_right (hcVN.mul_right hcVS)).add_right (hcVN.mul_right hcVN)
  have hN''nil : IsNilpotent N'' := (hcVY.mul_left hcVY).isNilpotent_mul_left hYnil
  have hcSY : Commute S Y :=
    (((Commute.refl S).mul_right hcSN).add_right (hcSN.mul_right (Commute.refl S))).add_right
      (hcSN.mul_right hcSN)
  have hSN'' : Commute S N'' := (hcSV.mul_right hcSV).mul_right hcSY
  -- the semisimple part
  have hconj : ∀ z, (fun z => 2 * FIN_L0 z) (starRingEnd ℂ z) =
      starRingEnd ℂ ((fun z => 2 * FIN_L0 z) z) := by
    intro z
    show 2 * FIN_L0 (starRingEnd ℂ z) = starRingEnd ℂ (2 * FIN_L0 z)
    rw [FIN_L0_conj z, map_mul, map_ofNat]
  have hL : ∀ z : ℂ, (∃ w : Fin n → ℂ, w ≠ 0 ∧
        (S.map (algebraMap ℝ ℂ)) *ᵥ w = z • w) →
      Complex.exp ((fun z => 2 * FIN_L0 z) z) =
        (((Polynomial.X : Polynomial ℝ) ^ 2).map (algebraMap ℝ ℂ)).eval z := by
    intro z ⟨w, hw0, hw1⟩
    simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X]
    rw [two_mul, Complex.exp_add]
    by_cases him : z.im = 0
    · obtain ⟨u, hu0, hu1⟩ := FIN_real_eig_of_complex S z him w hw0 hw1
      have hre : z.re ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hu1
        exact hSdet ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨u, hu0, hu1⟩)
      rw [FIN_exp_L0_real him hre]
      obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = (x : ℂ) :=
        ⟨z.re, Complex.ext (by simp) (by simpa using him)⟩
      rw [← Complex.ofReal_mul, abs_mul_abs_self, sq]
      simp
    · rw [FIN_exp_L0_nonreal him, sq]
  obtain ⟨BS, hBS, hexp⟩ := exists_real_exp_eq_aeval S hss (Polynomial.X ^ 2)
    (fun z => 2 * FIN_L0 z) hconj hL
  have hexp' : NormedSpace.exp BS = S * S := by
    rw [hexp]; simp [sq]
  obtain ⟨X, hX, -, hexpX⟩ := exists_exp_eq_one_add_of_isNilpotent_real N'' hN''nil
  refine ⟨BS + X, ?_⟩
  rw [FIN_exp_add hSN'' hBS hX, hexp', hexpX, ← hAA]

/-- (FIN) Teschl, Lemma 3.34, all three claims. -/
theorem matrix_logarithm_all (n : ℕ) :
    (∀ A : Matrix (Fin n) (Fin n) ℂ,
      (∃ B : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp B = A) ↔ A.det ≠ 0) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → 0 < μ) →
      ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A.det ≠ 0 →
      ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A * A) := by
  refine ⟨fun A => ⟨?_, exists_exp_eq_of_det_ne_zero A⟩, fun A hA => FIN_part2 A hA,
    fun A hA => FIN_part3 A hA⟩
  rintro ⟨B, rfl⟩
  have h := Matrix.isUnit_exp B
  rw [Matrix.isUnit_iff_isUnit_det] at h
  exact isUnit_iff_ne_zero.mp h

end FloquetAux

/-- Teschl, Lemma 3.34: matrix logarithms. -/
theorem solution (n : ℕ) :
    (∀ A : Matrix (Fin n) (Fin n) ℂ,
      (∃ B : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp B = A) ↔ A.det ≠ 0) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → 0 < μ) →
      ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A.det ≠ 0 →
      ∃ B : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp B = A * A) :=
  FloquetAux.matrix_logarithm_all n
