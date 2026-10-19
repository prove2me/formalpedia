-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.independence_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:24:51.389903+00:00
-- url     : https://prove2.me/submissions/5060e635-2162-473b-a30c-c33e8efee63d

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_assisted_independence_monotonicity

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma feasible_bound {I : Type} [Fintype I] [DecidableEq I]
    (S : Submodule ℂ (Matrix I I ℂ)) (hS : IsSystem S)
    {m : ℕ} (v : Fin m → EuclideanSpace ℂ I)
    (hv : ∀ i, IsState (v i))
    (ho : ∀ i j, i ≠ j → ∀ X ∈ S, inner ℂ (v i) (act X (v j)) = 0) :
    m ≤ Fintype.card I := by
  have hn : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    split_ifs with h
    · subst j
      rw [inner_self_eq_norm_sq_to_K, hv i]
      norm_num
    · simpa [act] using ho i j h 1 hS.1
  simpa using hn.linearIndependent.fintype_card_le_finrank


private lemma pull_inner {I J : Type} [Fintype I] [Fintype J]
    (A B : Matrix J I ℂ) (X : Matrix J J ℂ) (u v : EuclideanSpace ℂ I) :
    inner ℂ u (act (Aᴴ * X * B) v) =
      inner ℂ (WithLp.toLp 2 (A.mulVec u.ofLp))
        (act X (WithLp.toLp 2 (B.mulVec v.ofLp))) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, act]
  rw [dotProduct_comm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct_comm]

private lemma block_compress {I J : Type} [Fintype I] [Fintype J]
    {e : ℕ} (V : Matrix (J × Fin e) I ℂ) (X : Matrix J J ℂ) (a b : Fin e) :
    (V.submatrix (fun j => (j,a)) id)ᴴ * X *
      (V.submatrix (fun j => (j,b)) id) =
      Vᴴ * Matrix.kronecker X (Matrix.single a b 1) * V := by
  ext i k
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, Finset.sum_mul]

private lemma classical_feasible_transfer {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (h : GraphHom S T) {m : ℕ} (v : Fin m → EuclideanSpace ℂ I)
    (hv : ∀ i, IsState (v i))
    (ho : ∀ i j, i ≠ j → ∀ X ∈ S, inner ℂ (v i) (act X (v j)) = 0) :
    ∃ w : Fin m → EuclideanSpace ℂ J, (∀ i, IsState (w i)) ∧
      ∀ i j, i ≠ j → ∀ X ∈ T, inner ℂ (w i) (act X (w j)) = 0 := by
  classical
  obtain ⟨e,he,V,hV,hcomp⟩ := h
  let C (a : Fin e) : Matrix J I ℂ := V.submatrix (fun j => (j,a)) id
  let u (i : Fin m) (a : Fin e) : EuclideanSpace ℂ J :=
    WithLp.toLp 2 ((C a).mulVec (v i).ofLp)
  have hu (i : Fin m) : ∃ a, u i a ≠ 0 := by
    by_contra! hz
    have hzero : V.mulVec (v i).ofLp = 0 := by
      ext ⟨j,a⟩
      have hh := congrArg (fun w : EuclideanSpace ℂ J => w j) (hz a)
      simpa [u,C,Matrix.mulVec, dotProduct] using hh
    have hvzero : v i = 0 := by
      have hh := congrArg (fun z => Vᴴ.mulVec z) hzero
      rw [Matrix.mulVec_mulVec, hV] at hh
      simpa using hh
    have hh := hv i
    simp [IsState,hvzero] at hh
  choose a ha using hu
  have hcross (i j : Fin m) (hij : i ≠ j) (X : Matrix J J ℂ) (hX : X ∈ T) :
      inner ℂ (u i (a i)) (act X (u j (a j))) = 0 := by
    change inner ℂ (WithLp.toLp 2 ((C (a i)).mulVec (v i).ofLp))
      (act X (WithLp.toLp 2 ((C (a j)).mulVec (v j).ofLp))) = 0
    rw [← pull_inner]
    apply ho i j hij
    dsimp [C]
    rw [block_compress]
    exact hcomp X hX _
  refine ⟨fun i => (‖u i (a i)‖⁻¹ : ℂ) • u i (a i), ?_, ?_⟩
  · intro i
    change ‖(‖u i (a i)‖⁻¹ : ℂ) • u i (a i)‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (ha i))
  · intro i j hij X hX
    have heq : act X ((‖u j (a j)‖⁻¹ : ℂ) • u j (a j)) =
        (‖u j (a j)‖⁻¹ : ℂ) • act X (u j (a j)) := by
      ext k
      simp [act,Matrix.mulVec_smul]
    rw [heq, inner_smul_left, inner_smul_right, hcross i j hij X hX, mul_zero, mul_zero]

private lemma classical_mono {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hT : IsSystem T) (h : GraphHom S T) : alpha S ≤ alpha T := by
  apply csSup_le'
  intro m hm
  obtain ⟨v,hv,ho⟩ := hm
  obtain ⟨w,hw,hwo⟩ := classical_feasible_transfer S T h v hv ho
  apply le_csSup _ (show m ∈ {m | ∃ w : Fin m → EuclideanSpace ℂ J,
      (∀ i, IsState (w i)) ∧ ∀ i j, i ≠ j → ∀ X ∈ T,
        inner ℂ (w i) (act X (w j)) = 0} from ⟨w,hw,hwo⟩)
  refine ⟨Fintype.card J, ?_⟩
  rintro n ⟨w,hw,hwo⟩
  exact feasible_bound T hT w hw hwo


private lemma quantum_feasible_transfer {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hT : IsSystem T) (h : GraphHom S T)
    (P : Matrix I I ℂ) (hP : Code S P) :
    ∃ Q : Matrix J J ℂ, Code T Q ∧ Q.rank = P.rank := by
  classical
  by_cases hp0 : P = 0
  · refine ⟨0, ⟨⟨by simp, by simp⟩, ?_⟩, by simp [hp0]⟩
    intro X hX
    exact ⟨0,by simp⟩
  obtain ⟨e,he,V,hV,hcomp⟩ := h
  let C (a : Fin e) : Matrix J I ℂ := V.submatrix (fun j => (j,a)) id
  have hC : ∃ a, C a * P ≠ 0 := by
    by_contra! hz
    have hzV : V * P = 0 := by
      ext ⟨j,a⟩ i
      have hh := congrFun (congrFun (hz a) j) i
      simpa [C,Matrix.mul_apply] using hh
    have hh := congrArg (fun M => Vᴴ * M) hzV
    rw [← Matrix.mul_assoc, hV] at hh
    simp at hh
    exact hp0 hh
  obtain ⟨a,ha⟩ := hC
  let A : Matrix J I ℂ := C a * P
  have hAP : A * P = A := by
    dsimp [A]
    rw [Matrix.mul_assoc, hP.1.2]
  have hPA : P * Aᴴ = Aᴴ := by
    simpa [Matrix.conjTranspose_mul, hP.1.1] using congrArg Matrix.conjTranspose hAP
  have hPX (X : Matrix J J ℂ) (hX : X ∈ T) :
      ∃ c : ℂ, Aᴴ * X * A = c • P := by
    have hm : (C a)ᴴ * X * C a ∈ S := by
      dsimp [C]
      rw [block_compress]
      exact hcomp X hX _
    obtain ⟨c,hc⟩ := hP.2 _ hm
    refine ⟨c, ?_⟩
    simpa [A,Matrix.conjTranspose_mul,hP.1.1,Matrix.mul_assoc] using hc
  obtain ⟨z,hz⟩ := hPX 1 hT.1
  simp only [Matrix.mul_one] at hz
  have hz0 : z ≠ 0 := by
    intro hh
    have hAA : Aᴴ * A = 0 := by simpa [hh] using hz
    have hAz : A = 0 := (Matrix.conjTranspose_mul_self_eq_zero).mp hAA
    exact ha hAz
  have hstar : star z = z := by
    apply smul_left_injective ℂ hp0
    calc
      star z • P = (z • P)ᴴ := by rw [Matrix.conjTranspose_smul,hP.1.1]
      _ = (Aᴴ * A)ᴴ := congrArg Matrix.conjTranspose hz.symm
      _ = z • P := by simpa using hz
  let Q : Matrix J J ℂ := z⁻¹ • (A * Aᴴ)
  have hQ : IsProjection Q := by
    constructor
    · simp [Q,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,hstar]
    · change (z⁻¹ • (A * Aᴴ)) * (z⁻¹ • (A * Aᴴ)) = z⁻¹ • (A * Aᴴ)
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have heq : (A * Aᴴ) * (A * Aᴴ) = z • (A * Aᴴ) := by
        calc
          (A * Aᴴ) * (A * Aᴴ) = A * (Aᴴ * A) * Aᴴ := by simp [Matrix.mul_assoc]
          _ = z • (A * Aᴴ) := by rw [hz,Matrix.mul_smul,Matrix.smul_mul,hAP]
      rw [heq,smul_smul]
      field_simp
  refine ⟨Q, ⟨hQ, ?_⟩, ?_⟩
  · intro X hX
    obtain ⟨c,hc⟩ := hPX X hX
    refine ⟨z⁻¹ * c, ?_⟩
    change (z⁻¹ • (A * Aᴴ)) * X * (z⁻¹ • (A * Aᴴ)) =
      (z⁻¹ * c) • (z⁻¹ • (A * Aᴴ))
    rw [Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    have heq : (A * Aᴴ * X) * (A * Aᴴ) = c • (A * Aᴴ) := by
      calc
        (A * Aᴴ * X) * (A * Aᴴ) = A * (Aᴴ * X * A) * Aᴴ := by simp [Matrix.mul_assoc]
        _ = c • (A * Aᴴ) := by rw [hc,Matrix.mul_smul,Matrix.smul_mul,hAP]
    rw [heq,smul_smul,smul_smul]
    congr 1
    ring
  · calc
      Q.rank = (A * Aᴴ).rank := Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hz0))
      _ = A.rank := Matrix.rank_self_mul_conjTranspose A
      _ = (Aᴴ * A).rank := (Matrix.rank_conjTranspose_mul_self A).symm
      _ = P.rank := by
        rw [hz]
        exact Matrix.rank_smul_of_mem_nonZeroDivisors P (mem_nonZeroDivisors_of_ne_zero hz0)

private lemma quantum_mono {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hT : IsSystem T) (h : GraphHom S T) : alphaQ S ≤ alphaQ T := by
  apply csSup_le'
  rintro d ⟨P,hP,rfl⟩
  obtain ⟨Q,hQ,hq⟩ := quantum_feasible_transfer S T hT h P hP
  rw [← hq]
  apply le_csSup _ (show Q.rank ∈ {d | ∃ Q : Matrix J J ℂ, Code T Q ∧ Q.rank = d}
    from ⟨Q,hQ,rfl⟩)
  refine ⟨Fintype.card J, ?_⟩
  rintro d ⟨Q,_,rfl⟩
  exact Matrix.rank_le_card_width Q

theorem solution {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hS : IsSystem S) (hT : IsSystem T) (h : GraphHom S T) :
    (alpha S ≤ alpha T ∧ alphaEA S ≤ alphaEA T ∧ alphaQ S ≤ alphaQ T) ∧
    (GraphHom T S → alpha S = alpha T ∧ alphaEA S = alphaEA T ∧ alphaQ S = alphaQ T) := by
  have hc := classical_mono S T hT h
  have hq := quantum_mono S T hT h
  have hea := assisted_independence_monotonicity S T hS hT h
  refine ⟨⟨hc,hea,hq⟩, ?_⟩
  intro hr
  exact ⟨le_antisymm hc (classical_mono T S hS hr),
    le_antisymm hea (assisted_independence_monotonicity T S hT hS hr),
    le_antisymm hq (quantum_mono T S hS hr)⟩

#print axioms solution
