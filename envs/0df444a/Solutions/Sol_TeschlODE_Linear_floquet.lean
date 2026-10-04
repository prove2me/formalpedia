-- Prove2me | solution 1 for TeschlODE.Linear.floquet
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T01:41:49.06073+00:00
-- url     : https://prove2.me/submissions/629a26ed-76fb-4d27-9334-d68a6665f121

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution

open Set
open scoped Matrix NNReal

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

/-- Multiplication by a real matrix as a continuous linear map on `ℝⁿ`. -/
noncomputable def mvCLM {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin n → ℝ) (F' := Fin n → ℝ)).toLinearMap ∘ₗ
    (Matrix.toLin' : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).toLinearMap

lemma mvCLM_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    mvCLM B x = B *ᵥ x := by
  simp [mvCLM]

lemma continuous_mvCLM {n : ℕ} : Continuous (mvCLM (n := n)) :=
  LinearMap.continuous_of_finiteDimensional _

/-- Uniqueness for the linear system `ẋ = A(t) x` with continuous `A`. -/
lemma col_unique {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (hA : Continuous A)
    (f g : ℝ → Fin n → ℝ)
    (hf : ∀ s, HasDerivAt f (A s *ᵥ f s) s) (hg : ∀ s, HasDerivAt g (A s *ᵥ g s) s)
    (t₀ : ℝ) (h0 : f t₀ = g t₀) (t : ℝ) : f t = g t := by
  have hc : Continuous fun s => ‖mvCLM (A s)‖ := (continuous_mvCLM.comp hA).norm
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := min t t₀ - 1) (b := max t t₀ + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hv : ∀ s ∈ Ioo (min t t₀ - 1) (max t t₀ + 1),
      LipschitzOnWith K.toNNReal (fun x : Fin n → ℝ => A s *ᵥ x) univ := by
    intro s hs
    refine LipschitzWith.lipschitzOnWith ?_
    have h1 : ‖mvCLM (A s)‖₊ ≤ K.toNNReal := by
      have := hK s (Ioo_subset_Icc_self hs)
      rw [Real.norm_eq_abs, abs_norm] at this
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
      exact this.trans (le_max_left _ _)
    have h2 := (mvCLM (A s)).lipschitz
    have h3 : (⇑(mvCLM (A s)) : (Fin n → ℝ) → (Fin n → ℝ)) = fun x => A s *ᵥ x :=
      funext (mvCLM_apply _)
    rw [h3] at h2
    exact h2.weaken h1
  have ht0 : t₀ ∈ Ioo (min t t₀ - 1) (max t t₀ + 1) :=
    ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
  have ht : t ∈ Ioo (min t t₀ - 1) (max t t₀ + 1) :=
    ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩
  exact ODE_solution_unique_of_mem_Ioo (v := fun s x => A s *ᵥ x) (s := fun _ => univ) hv ht0
    (fun s _ => ⟨hf s, mem_univ _⟩) (fun s _ => ⟨hg s, mem_univ _⟩) h0 ht

/-- Each column of a principal matrix solution solves the system. -/
lemma hasDerivAt_col {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A Set.univ Φ) (t₀ : ℝ) (j : Fin n) (s : ℝ) :
    HasDerivAt (fun τ => fun i => Φ τ t₀ i j) (A s *ᵥ (fun i => Φ s t₀ i j)) s := by
  rw [hasDerivAt_pi]
  intro i
  have h := (hΦ t₀ (mem_univ _)).2 s (mem_univ _) i j
  rw [hasDerivWithinAt_univ] at h
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- The cocycle identity `Φ(t, s) Φ(s, t₀) = Φ(t, t₀)`. -/
lemma cocycle {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} (hA : Continuous A)
    {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A Set.univ Φ) (t s t₀ : ℝ) :
    Φ t s * Φ s t₀ = Φ t t₀ := by
  ext i j
  have key := col_unique A hA (fun τ k => (Φ τ s * Φ s t₀) k j) (fun τ k => Φ τ t₀ k j)
    ?_ (hasDerivAt_col hΦ t₀ j) s ?_ t
  · exact congrFun key i
  · intro τ
    rw [hasDerivAt_pi]
    intro k
    have hd : HasDerivAt (fun τ' => ∑ l, Φ τ' s k l * Φ s t₀ l j)
        (∑ l, (A τ * Φ τ s) k l * Φ s t₀ l j) τ := by
      refine HasDerivAt.fun_sum fun l _ => ?_
      have h := (hΦ s (mem_univ _)).2 τ (mem_univ _) k l
      rw [hasDerivWithinAt_univ] at h
      exact h.mul_const _
    have e : (∑ l, (A τ * Φ τ s) k l * Φ s t₀ l j) =
        (A τ *ᵥ fun k => (Φ τ s * Φ s t₀) k j) k := by
      rw [← Matrix.mul_apply, Matrix.mul_assoc]; rfl
    exact e ▸ hd
  · funext k
    simp only [(hΦ s (mem_univ _)).1, Matrix.one_mul]

/-- Periodicity of the principal matrix solution: `Φ(t + T, t₀ + T) = Φ(t, t₀)`. -/
lemma periodic_principal {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} (hA : Continuous A) {T : ℝ}
    (hper : ∀ t, A (t + T) = A t) {Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A Set.univ Φ) (t t₀ : ℝ) :
    Φ (t + T) (t₀ + T) = Φ t t₀ := by
  ext i j
  have key := col_unique A hA (fun s k => Φ (s + T) (t₀ + T) k j) (fun s k => Φ s t₀ k j)
    ?_ (hasDerivAt_col hΦ t₀ j) t₀ ?_ t
  · exact congrFun key i
  · intro s
    rw [hasDerivAt_pi]
    intro k
    have h := (hΦ (t₀ + T) (mem_univ _)).2 (s + T) (mem_univ _) k j
    rw [hasDerivWithinAt_univ] at h
    have h2 := h.comp_add_const s T
    rw [hper] at h2
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2
  · funext k
    simp only [(hΦ _ (mem_univ _)).1]

end FloquetAux

open FloquetAux in
theorem solution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (hA : Continuous A) (T : ℝ)
    (hT : 0 < T) (hper : ∀ t, A (t + T) = A t) (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hΦ : TeschlODE.Linear.IsPrincipalMatrixSolution A Set.univ Φ) (t₀ : ℝ) :
    ∃ (P : ℝ → Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ),
      (∀ t, P (t + T) = P t) ∧ P t₀ = 1 ∧
      ∀ t, (Φ t t₀).map (fun r : ℝ => (r : ℂ)) =
        P t * NormedSpace.exp (((t - t₀ : ℝ) : ℂ) • Q) := by
  -- the monodromy matrix
  set M : Matrix (Fin n) (Fin n) ℝ := Φ (t₀ + T) t₀ with hM
  have hper' : ∀ t, Φ (t + T) t₀ = Φ t t₀ * M := by
    intro t
    have h1 := periodic_principal hA hper hΦ t t₀
    have h2 := cocycle hA hΦ (t + T) (t₀ + T) t₀
    rw [← h2, h1]
  have hdet : M.det ≠ 0 := by
    have h := cocycle hA hΦ t₀ (t₀ + T) t₀
    rw [(hΦ t₀ (mem_univ _)).1] at h
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact right_ne_zero_of_mul_eq_one h2
  -- its complexification has a logarithm
  set Mc : Matrix (Fin n) (Fin n) ℂ := M.map (fun r : ℝ => (r : ℂ)) with hMc
  have hdetc : Mc.det ≠ 0 := by
    have h := RingHom.map_det Complex.ofRealHom M
    have h' : Mc.det = ((M.det : ℝ) : ℂ) := h.symm
    rw [h']
    exact_mod_cast hdet
  obtain ⟨B, hB⟩ := exists_exp_eq_of_det_ne_zero Mc hdetc
  set Q : Matrix (Fin n) (Fin n) ℂ := (T : ℂ)⁻¹ • B with hQ
  have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hTQ : NormedSpace.exp ((T : ℂ) • Q) = Mc := by
    rw [hQ, smul_smul, mul_inv_cancel₀ hTne, one_smul]
    exact hB
  -- exponential identities
  have hexp_add : ∀ a b : ℂ,
      NormedSpace.exp ((a + b) • Q) = NormedSpace.exp (a • Q) * NormedSpace.exp (b • Q) := by
    intro a b
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl Q).smul_left a).smul_right b)
  have hexp_inv : ∀ a : ℂ, NormedSpace.exp (a • Q) * NormedSpace.exp ((-a) • Q) = 1 := by
    intro a
    rw [← hexp_add, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  have hexp_inv' : ∀ a : ℂ, NormedSpace.exp ((-a) • Q) * NormedSpace.exp (a • Q) = 1 := by
    intro a
    have := hexp_inv (-a)
    rwa [neg_neg] at this
  -- the complexified principal matrix solution
  have hΦc : ∀ t, (Φ (t + T) t₀).map (fun r : ℝ => (r : ℂ)) =
      (Φ t t₀).map (fun r : ℝ => (r : ℂ)) * Mc := by
    intro t
    rw [hper' t, hMc]
    exact Matrix.map_mul (f := Complex.ofRealHom)
  refine ⟨fun t => (Φ t t₀).map (fun r : ℝ => (r : ℂ)) *
    NormedSpace.exp ((-((t - t₀ : ℝ) : ℂ)) • Q), Q, ?_, ?_, ?_⟩
  · intro t
    have hshift : NormedSpace.exp ((-(((t + T) - t₀ : ℝ) : ℂ)) • Q) =
        NormedSpace.exp ((-(T : ℂ)) • Q) * NormedSpace.exp ((-((t - t₀ : ℝ) : ℂ)) • Q) := by
      rw [← hexp_add]
      congr 2
      push_cast
      ring
    simp only
    rw [hΦc t, hshift, ← hTQ, mul_assoc, ← mul_assoc (NormedSpace.exp ((T : ℂ) • Q)),
      hexp_inv, one_mul]
  · simp only [sub_self, Complex.ofReal_zero, neg_zero, zero_smul, NormedSpace.exp_zero,
      mul_one, (hΦ t₀ (mem_univ _)).1]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro t
    simp only
    rw [mul_assoc, hexp_inv' _, mul_one]
