-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.operationCost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:21:11.10458+00:00
-- url     : https://prove2.me/submissions/dd605728-5124-425b-a8d1-d22dc5031a31

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open QAlgorithms QAlgorithms.ErrorMitigation
open QAlgorithms.Papers.Independent.Independent1.P09
open scoped Matrix.Norms.L2Operator NNReal

private lemma operator_bound {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (bound : ∀ x : EuclideanSpace ℝ (Fin d), ‖B.toEuclideanLin x‖ ≤ C * ‖x‖) :
    specNorm B ≤ C := by
  change ‖(B.toEuclideanLin).toContinuousLinearMap‖ ≤ C
  exact (B.toEuclideanLin).toContinuousLinearMap.opNorm_le_bound hC bound

private lemma least_lower {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    leastSingular hd A * ‖x‖ ≤ ‖A.toEuclideanLin x‖ := by
  let H := A.transpose * A
  have hH : H.IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self A
  let b := hH.eigenvectorBasis
  let e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let k : Fin (Fintype.card (Fin d)) := ⟨0, by simpa using hd⟩
  let m := hH.eigenvalues₀ k.rev
  have hmin (i : Fin d) : m ≤ hH.eigenvalues i := by
    apply hH.eigenvalues₀_antitone
    change (e i).val ≤ k.rev.val
    simp only [Fin.val_rev]
    have := (e i).isLt
    dsimp [k]
    omega
  have hm : 0 ≤ m := by
    have := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A (e.symm k.rev)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.IsHermitian.eigenvalues,
      H, m, e] using this
  have hs : leastSingular hd A = Real.sqrt m := by
    change Real.sqrt (ascEigenvalues H k) = Real.sqrt m
    rw [ascEigenvalues, dif_pos hH]
  have hc (i : Fin d) : b.repr (H.toEuclideanLin x) i =
      hH.eigenvalues i * b.repr x i := by
    rw [b.repr_apply_apply, b.repr_apply_apply]
    rw [← Matrix.isSymmetric_toEuclideanLin_iff.mpr hH]
    have he : H.toEuclideanLin (b i) = hH.eigenvalues i • b i := by
      apply PiLp.ext
      intro j
      exact congrFun (hH.mulVec_eigenvectorBasis i) j
    rw [he, inner_smul_left]
    simp
  have hinner : inner ℝ x (H.toEuclideanLin x) = ‖A.toEuclideanLin x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [Matrix.toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply,
      starRingEnd_apply, star_trivial, H]
    change ((A.transpose * A).mulVec x.ofLp) ⬝ᵥ x.ofLp =
      (A.mulVec x.ofLp) ⬝ᵥ (A.mulVec x.ofLp)
    rw [dotProduct_comm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hsum : m * ‖x‖ ^ 2 ≤ inner ℝ x (H.toEuclideanLin x) := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq,
      ← b.repr.inner_map_map, PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hc, Finset.mul_sum,
      Real.norm_eq_abs, sq_abs]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hmin i, sq_nonneg (b.repr x i)]
  rw [hinner] at hsum
  rw [hs]
  have hsq := Real.sq_sqrt hm
  nlinarith [norm_nonneg x, norm_nonneg (A.toEuclideanLin x),
    Real.sqrt_nonneg m, sq_nonneg (Real.sqrt m * ‖x‖ - ‖A.toEuclideanLin x‖)]

/-- Appendix C (C1)--(C3) and Appendix F (F10). -/
private theorem perturbation {d : ℕ} (hd : 0 < d)
    (A0 A : Matrix (Fin d) (Fin d) ℝ)
    (small : specNorm (A-A0) < leastSingular hd A0) :
    IsUnit A ∧
    (∀ x : EuclideanSpace ℝ (Fin d),
      (leastSingular hd A0-specNorm (A-A0))*‖x‖ ≤
        ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖) ∧
    specNorm A⁻¹ ≤ (leastSingular hd A0-specNorm (A-A0))⁻¹ := by
  let c := leastSingular hd A0 - specNorm (A-A0)
  have hc : 0 < c := sub_pos.mpr small
  have lower (x : EuclideanSpace ℝ (Fin d)) : c * ‖x‖ ≤ ‖A.toEuclideanLin x‖ := by
    have h0 := least_lower hd A0 x
    have herror := (A-A0).l2_opNorm_mulVec x
    have hadd : A0.toEuclideanLin x =
        A.toEuclideanLin x - (A-A0).toEuclideanLin x := by
      simp [map_sub]
    have ht := norm_sub_le (A.toEuclideanLin x) ((A-A0).toEuclideanLin x)
    rw [← hadd] at ht
    change ‖(A-A0).toEuclideanLin x‖ ≤ specNorm (A-A0) * ‖x‖ at herror
    dsimp [c]
    linarith
  have hu : IsUnit A := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro u v huv
    have h := lower (WithLp.toLp 2 (u-v))
    have hz : A.toEuclideanLin (WithLp.toLp 2 (u-v)) = 0 := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec_sub, huv]
    rw [hz, norm_zero] at h
    have hv : WithLp.toLp 2 (u-v) = (0 : EuclideanSpace ℝ (Fin d)) := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (WithLp.toLp 2 (u-v) : EuclideanSpace ℝ (Fin d))]
    have hv' : u-v = 0 := by
      simpa using congrArg WithLp.ofLp hv
    exact sub_eq_zero.mp hv'
  refine ⟨hu, lower, ?_⟩
  apply operator_bound A⁻¹ c⁻¹ (le_of_lt (inv_pos.mpr hc))
  intro y
  have h := lower (A⁻¹.toEuclideanLin y)
  have hy : A.toEuclideanLin (A⁻¹.toEuclideanLin y) = y := by
    simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp hu), Matrix.one_mulVec, WithLp.toLp_ofLp]
  rw [hy] at h
  change ‖A⁻¹.toEuclideanLin y‖ ≤ c⁻¹ * ‖y‖
  calc
    ‖A⁻¹.toEuclideanLin y‖ ≤ ‖y‖ / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)
    _ = c⁻¹ * ‖y‖ := by ring



private lemma entry_bound {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) (i : I) (j : J) :
    |A i j| ≤ entryMax A := by
  exact_mod_cast (Finset.le_sup (f := fun p : I × J => ‖A p.1 p.2‖₊)
    (Finset.mem_univ (i,j)))

/-- The dimension factor in the maximum-entry to spectral-norm bound. -/
private lemma spectral_entry_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    specNorm A ≤ (d : ℝ) * entryMax A := by
  have he : 0 ≤ entryMax A := NNReal.coe_nonneg _
  apply operator_bound A ((d : ℝ) * entryMax A) (by positivity)
  intro x
  have hx : ∑ j : Fin d, (x j)^2 = ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  have rows (i : Fin d) : (∑ j : Fin d, A i j * x j)^2 ≤
      ((d : ℝ) * (entryMax A)^2) * ‖x‖^2 := by
    have hc : (∑ j : Fin d, A i j * x j)^2 ≤
        (∑ j : Fin d, (A i j)^2) * ‖x‖^2 := by
      simpa only [hx] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x j)
    have hr : (∑ j : Fin d, (A i j)^2) ≤ (d : ℝ) * (entryMax A)^2 := by
      calc
        _ ≤ ∑ j : Fin d, (entryMax A)^2 := by
          apply Finset.sum_le_sum
          intro j _
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr (entry_bound A i j)
        _ = _ := by simp
    simpa only [hx] using hc.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg ‖x‖))
  have ht : ‖A.toEuclideanLin x‖^2 ≤ ((d : ℝ) * entryMax A)^2 * ‖x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ ∑ i : Fin d, ((d : ℝ) * (entryMax A)^2) * ‖x‖^2 :=
        Finset.sum_le_sum (fun i _ => rows i)
      _ = _ := by simp; ring
  nlinarith [norm_nonneg (A.toEuclideanLin x), norm_nonneg x,
    mul_nonneg (show 0 ≤ (d : ℝ) * entryMax A by positivity) (norm_nonneg x)]


private lemma spectral_entry {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    |A i j| ≤ specNorm A := by
  let v : EuclideanSpace ℝ (Fin d) := PiLp.single 2 j 1
  have h := A.l2_opNorm_mulVec v
  have hi := PiLp.norm_apply_le (A.toEuclideanLin v) i
  have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  have he : (A.toEuclideanLin v) i = A i j := by
    simp [v, Matrix.toLpLin_apply]
  rw [he, Real.norm_eq_abs] at hi
  change ‖A.toEuclideanLin v‖ ≤ specNorm A * ‖v‖ at h
  rw [hv, mul_one] at h
  exact hi.trans h

/-- Product of the local inverse kernels, including the empty tensor. -/
private lemma tensor_right_inverse {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j))) :
    tensorFlat B * (Matrix.of fun p i => ∏ j, (localFlat (B j))⁻¹ (p j) (i j)) = 1 := by
  classical
  ext p q
  change (∑ i : Fin n → Fin 16, (∏ j, localFlat (B j) (p j) (i j)) *
    ∏ j, (localFlat (B j))⁻¹ (i j) (q j)) = (1 : Matrix _ _ ℝ) p q
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin n) (i : Fin 16) =>
    localFlat (B j) (p j) i * (localFlat (B j))⁻¹ i (q j))]
  have hlocal (j : Fin n) :
      (∑ i, localFlat (B j) (p j) i * (localFlat (B j))⁻¹ i (q j)) =
        (1 : Matrix (Fin 16) (Fin 16) ℝ) (p j) (q j) := by
    exact congrArg (fun A : Matrix (Fin 16) (Fin 16) ℝ => A (p j) (q j))
      (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (complete j)))
  simp_rw [hlocal]
  by_cases h : p = q
  · subst q
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne hj

private lemma interleave_injective {n : ℕ} :
    Function.Injective (interleave (n := n)) := by
  intro E F h
  ext a b
  let p : Fin n → Fin 16 := fun j => finProdFinEquiv (b j, a j)
  have he := congrFun h p
  simpa [interleave, p] using he

private lemma interleave_synthesis {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (q : (Fin n → Fin 16) → ℝ) :
    interleave (∑ i, q i • tensorOperation B i) = (tensorFlat B).mulVec q := by
  ext p
  simp only [interleave, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorOperation, tensorFlat, localFlat, localBasisMatrix, Matrix.of_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private lemma reconstruction {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    E = ∑ i, tensorCoordinates B E i • tensorOperation B i := by
  classical
  have hu : IsUnit (tensorFlat B) :=
    IsUnit.of_mul_eq_one _ (tensor_right_inverse B complete)
  apply interleave_injective
  rw [interleave_synthesis]
  simp [tensorCoordinates, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]

/-- Appendix G: two sums over 16^n indices give the factor 16^(2*n). -/
private lemma tensor_cost {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (C : ℝ) (hC : 0 ≤ C)
    (bound : ∀ j a b, |(localFlat (B j))⁻¹ a b| ≤ C)
    (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    coefficientMass (tensorCoordinates B E) ≤ (16 : ℝ)^(2*n) * C^n * entryMax E := by
  classical
  have hinv := Matrix.inv_eq_right_inv (tensor_right_inverse B complete)
  have inv_entries (i p : Fin n → Fin 16) : |(tensorFlat B)⁻¹ i p| ≤ C^n := by
    rw [hinv]
    change |∏ j, (localFlat (B j))⁻¹ (i j) (p j)| ≤ C^n
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _j : Fin n, C := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        (fun j _ => bound j (i j) (p j))
      _ = _ := by simp
  have input_entries (p : Fin n → Fin 16) : |interleave E p| ≤ entryMax E := by
    unfold interleave
    exact entry_bound E _ _
  have hq (i : Fin n → Fin 16) :
      |tensorCoordinates B E i| ≤ (16 : ℝ)^n * C^n * entryMax E := by
    unfold tensorCoordinates
    change |∑ p, (tensorFlat B)⁻¹ i p * interleave E p| ≤ _
    calc
      _ ≤ ∑ p, |(tensorFlat B)⁻¹ i p * interleave E p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin n → Fin 16, C^n * entryMax E := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (inv_entries i p) (input_entries p) (abs_nonneg _) (pow_nonneg hC n)
      _ = _ := by simp; ring
  unfold coefficientMass
  calc
    _ ≤ ∑ _i : Fin n → Fin 16, (16 : ℝ)^n * C^n * entryMax E :=
      Finset.sum_le_sum (fun i _ => hq i)
    _ = _ := by
      rw [show 2*n = n+n by omega, pow_add]
      simp
      ring

theorem solution {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (ideal native : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    let e := (Finset.univ.sup fun j => Real.toNNReal
      (entryMax (localFlat (B j)-localFlat localTransfer)) : ℝ≥0)
    (e : ℝ) < leastSingular (by omega) (localFlat localTransfer)/16 →
      ideal = native + ∑ i, tensorCoordinates B (ideal-native) i • tensorOperation B i ∧
      1+coefficientMass (tensorCoordinates B (ideal-native)) ≤
        1+(16 : ℝ)^(2*n)*entryMax (ideal-native)/
          (leastSingular (by omega) (localFlat localTransfer)-16*(e : ℝ))^n := by
  classical
  dsimp only
  let A0 := localFlat localTransfer
  let e : ℝ := (Finset.univ.sup fun j => Real.toNNReal
    (entryMax (localFlat (B j)-A0)) : ℝ≥0)
  let s := leastSingular (by omega) A0
  change e < s / 16 → _
  intro small
  have delta_pos : 0 < s - 16*e := by linarith
  have errors (j : Fin n) : entryMax (localFlat (B j)-A0) ≤ e := by
    have h := Finset.le_sup
      (f := fun j => Real.toNNReal (entryMax (localFlat (B j)-A0))) (Finset.mem_univ j)
    exact Real.toNNReal_le_iff_le_coe.mp h
  have spectral_error (j : Fin n) : specNorm (localFlat (B j)-A0) ≤ 16*e := by
    exact (spectral_entry_bound _).trans (by have := errors j; norm_num at *; linarith)
  have local_info (j : Fin n) : IsUnit (localFlat (B j)) ∧
      specNorm (localFlat (B j))⁻¹ ≤ (s-16*e)⁻¹ := by
    have h := perturbation (by omega) A0 (localFlat (B j))
      ((spectral_error j).trans_lt (by linarith))
    refine ⟨h.1, h.2.2.trans ?_⟩
    have hd : s - 16*e ≤ s - specNorm (localFlat (B j)-A0) := by
      have := spectral_error j
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le delta_pos hd
  have complete := fun j => (local_info j).1
  refine ⟨?_, ?_⟩
  · have h := reconstruction B complete (ideal-native)
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · have h := tensor_cost B complete ((s-16*e)⁻¹) (le_of_lt (inv_pos.mpr delta_pos))
      (fun j a b => (spectral_entry _ a b).trans (local_info j).2) (ideal-native)
    have heq : (16 : ℝ)^(2*n) * ((s-16*e)⁻¹)^n * entryMax (ideal-native) =
        (16 : ℝ)^(2*n)*entryMax (ideal-native)/(s-16*e)^n := by
      simp only [div_eq_mul_inv, inv_pow]
      ring
    rw [heq] at h
    simpa only [add_comm] using add_le_add_left h 1

#print axioms solution
