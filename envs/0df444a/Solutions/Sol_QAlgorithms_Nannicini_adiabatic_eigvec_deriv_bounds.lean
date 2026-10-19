-- Prove2me | solution 1 for QAlgorithms.Nannicini.adiabatic_eigvec_deriv_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T01:19:45.083318+00:00
-- url     : https://prove2.me/submissions/5e54314b-b74f-47ac-b545-1636911b9738

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false
open QAlgorithms Matrix
open scoped ComplexConjugate

private lemma ed_coords {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (v : EuclideanSpace ℂ ι) (i : ι) :
    hA.eigenvectorBasis.repr (act A v) i =
      (hA.eigenvalues i : ℂ) * hA.eigenvectorBasis.repr v i := by
  rw [hA.eigenvectorBasis.repr_apply_apply, hA.eigenvectorBasis.repr_apply_apply]
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  change inner ℂ (hA.eigenvectorBasis i) (A.toEuclideanLin v) = _
  rw [← hs]
  have he : A.toEuclideanLin (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro k
    exact congrFun (hA.mulVec_eigenvectorBasis i) k
  rw [he, inner_smul_left]
  simp

private lemma ed_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (γ : ℝ) (hγ : 0 < γ) (hg : HasGapAround A 0 γ)
    (φ v : EuclideanSpace ℂ ι) (hφ : ‖φ‖ = 1) (hAφ : act A φ = 0)
    (hv : inner ℂ φ v = 0) : γ * ‖v‖ ≤ ‖act A v‖ := by
  classical
  let hA := hg.1
  let b := hA.eigenvectorBasis
  let e : ι ≃ Fin (Fintype.card ι) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  obtain ⟨k, hk, huniq⟩ := hg.2.1
  let i₀ := e.symm k.rev
  have heig (i : ι) : hA.eigenvalues i = ascEigenvalues A (e i).rev := by
    simp [ascEigenvalues, hA, Matrix.IsHermitian.eigenvalues, e]
  have hne (i : ι) (hi : i ≠ i₀) : hA.eigenvalues i ≠ 0 := by
    intro hz
    have he := huniq (e i).rev (by simpa [← heig] using hz)
    apply hi
    apply e.injective
    simpa [i₀] using congrArg Fin.rev he
  have hφc (i : ι) (hi : i ≠ i₀) : b.repr φ i = 0 := by
    have h := ed_coords A hA φ i
    rw [hAφ] at h
    simp only [map_zero, PiLp.zero_apply] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hne i hi)
  have hφ0 : b.repr φ i₀ ≠ 0 := by
    intro hz
    have hzero : b.repr φ = 0 := by
      ext i
      by_cases hi : i = i₀
      · simpa [hi] using hz
      · exact hφc i hi
    have hzφ : φ = 0 := b.repr.injective (by simpa using hzero)
    simp [hzφ] at hφ
  have hvc : b.repr v i₀ = 0 := by
    have hinner := b.repr.inner_map_map φ v
    rw [hv] at hinner
    simp only [PiLp.inner_apply, RCLike.inner_apply] at hinner
    have hs : (∑ i, conj (b.repr φ i) * b.repr v i) =
        conj (b.repr φ i₀) * b.repr v i₀ := by
      apply Finset.sum_eq_single i₀
      · intro i _ hi
        simp [hφc i hi]
      · simp
    rw [Finset.sum_congr rfl (fun i _ => mul_comm _ _), hs] at hinner
    exact (mul_eq_zero.mp hinner).resolve_left (by simpa using hφ0)
  have hpoint (i : ι) : γ ^ 2 * ‖b.repr v i‖ ^ 2 ≤ ‖b.repr (act A v) i‖ ^ 2 := by
    rw [ed_coords A hA v i, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    change γ ^ 2 * ‖b.repr v i‖ ^ 2 ≤ |hA.eigenvalues i| ^ 2 * ‖b.repr v i‖ ^ 2
    by_cases hi : i = i₀
    · simp [hi, hvc]
    · have h := hg.2.2 (e i).rev (by simpa [← heig] using hne i hi)
      simp only [sub_zero, ← heig] at h
      exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (hA.eigenvalues i)]) (sq_nonneg _)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpoint i)
  rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq,
    ← EuclideanSpace.norm_sq_eq, b.repr.norm_map, b.repr.norm_map] at hsum
  nlinarith [norm_nonneg (act A v), norm_nonneg v]

private lemma ed_apply_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' : ℝ → Matrix ι ι ℂ) (φ φ' : ℝ → EuclideanSpace ℂ ι)
    (s : ℝ) (S : Set ℝ)
    (hH : ∀ i j, HasDerivWithinAt (fun t => H t i j) (H' s i j) S s)
    (hφ : HasDerivWithinAt φ (φ' s) S s) (i : ι) :
    HasDerivWithinAt (fun t => act (H t) (φ t) i)
      (act (H' s) (φ s) i + act (H s) (φ' s) i) S s := by
  have hd (j : ι) : HasDerivWithinAt (fun t => φ t j) (φ' s j) S s :=
    (PiLp.proj 2 (fun _ : ι => ℂ) j).hasFDerivAt.comp_hasDerivWithinAt s hφ
  simpa only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp,
    Finset.sum_add_distrib, Pi.mul_apply] using
    (HasDerivWithinAt.fun_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) => (hH i j).mul (hd j))

set_option maxHeartbeats 800000 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (φ φ' φ'' : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (hφ' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s)
    (hφ'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ' (φ'' s) (Set.Icc 0 1) s)
    (hphase : ∀ s ∈ Set.Icc (0 : ℝ) 1, inner ℂ (φ' s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖φ' s‖ ≤ N1 / γ ∧ ‖φ'' s‖ ≤ N2 / γ + 3 * N1 ^ 2 / γ ^ 2  := by
  classical
  have hd1 (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      act (H' s) (φ s) + act (H s) (φ' s) = 0 := by
    apply PiLp.ext
    intro i
    have hd := ed_apply_deriv H H' φ φ' s (Set.Icc 0 1) (hH' s hs) (hφ' s hs) i
    have hz := hd.congr_of_mem (f₁ := fun _ => (0 : ℂ))
      (fun t ht => (congrArg (fun v : EuclideanSpace ℂ ι => v i) (hφ t ht).2).symm) hs
    exact (uniqueDiffOn_Icc_zero_one s hs).eq_deriv _ hz (hasDerivWithinAt_const s _ 0)
  have hd2 (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      act (H'' s) (φ s) + act (H' s) (φ' s) +
        (act (H' s) (φ' s) + act (H s) (φ'' s)) = 0 := by
    apply PiLp.ext
    intro i
    have hd := (ed_apply_deriv H' H'' φ φ' s (Set.Icc 0 1) (hH'' s hs) (hφ' s hs) i).add
      (ed_apply_deriv H H' φ' φ'' s (Set.Icc 0 1) (hH' s hs) (hφ'' s hs) i)
    have hz := hd.congr_of_mem (f₁ := fun _ => (0 : ℂ))
      (fun t ht => (congrArg (fun v : EuclideanSpace ℂ ι => v i) (hd1 t ht)).symm) hs
    exact (uniqueDiffOn_Icc_zero_one s hs).eq_deriv _ hz (hasDerivWithinAt_const s _ 0)
  have hphase' (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      inner ℂ (φ' s) (φ' s) + inner ℂ (φ'' s) (φ s) = 0 := by
    have hd := (hφ'' s hs).inner ℂ (hφ' s hs)
    have hz := hd.congr_of_mem (f₁ := fun _ => (0 : ℂ))
      (fun t ht => (hphase t ht).symm) hs
    exact (uniqueDiffOn_Icc_zero_one s hs).eq_deriv _ hz (hasDerivWithinAt_const s _ 0)
  intro s hs
  have hnφ : ‖φ s‖ = 1 := (hφ s hs).1
  have hN1pos : 0 ≤ N1 := by
    let _ := Matrix.instL2OpNormedAddCommGroup (𝕜 := ℂ) (m := ι) (n := ι)
    exact (norm_nonneg (H' s)).trans (hN1 s hs)
  have hact1 : ‖act (H' s) (φ s)‖ ≤ N1 := by
    calc
      _ ≤ specNorm (H' s) * ‖φ s‖ := Matrix.l2_opNorm_mulVec _ _
      _ ≤ N1 := by simpa [hnφ] using hN1 s hs
  have hfirst : ‖φ' s‖ ≤ N1 / γ := by
    apply (le_div_iff₀ hγ).2
    have h := ed_gap (H s) γ hγ (hgap s hs) (φ s) (φ' s) hnφ (hφ s hs).2
      (by rw [inner_eq_zero_symm]; exact hphase s hs)
    have heq : act (H s) (φ' s) = -act (H' s) (φ s) := eq_neg_of_add_eq_zero_right (hd1 s hs)
    rw [heq, norm_neg] at h
    nlinarith
  refine ⟨hfirst, ?_⟩
  have hpar : ‖inner ℂ (φ s) (φ'' s)‖ = ‖φ' s‖ ^ 2 := by
    rw [norm_inner_symm]
    have he : inner ℂ (φ'' s) (φ s) = -inner ℂ (φ' s) (φ' s) :=
      eq_neg_of_add_eq_zero_right (hphase' s hs)
    rw [he, norm_neg, inner_self_eq_norm_sq_to_K]
    simp
  let v := φ'' s - inner ℂ (φ s) (φ'' s) • φ s
  have horth : inner ℂ (φ s) v = 0 := by
    simp [v, inner_self_eq_norm_sq_to_K, hnφ]
  have hvact : act (H s) v = act (H s) (φ'' s) := by
    apply PiLp.ext
    intro i
    simp [v, act, Matrix.mulVec_sub, Matrix.mulVec_smul,
      show (H s) *ᵥ ⇑(φ s) = 0 from congrArg WithLp.ofLp (hφ s hs).2]
  have hvnorm : ‖φ'' s‖ ≤ ‖v‖ + ‖φ' s‖ ^ 2 := by
    calc
      ‖φ'' s‖ = ‖v + inner ℂ (φ s) (φ'' s) • φ s‖ := by simp [v]
      _ ≤ ‖v‖ + ‖inner ℂ (φ s) (φ'' s) • φ s‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, hnφ, mul_one, hpar]
  have hact2 : ‖act (H s) (φ'' s)‖ ≤ N2 + 2 * N1 * ‖φ' s‖ := by
    have heq : act (H s) (φ'' s) =
        -(act (H'' s) (φ s) + act (H' s) (φ' s) + act (H' s) (φ' s)) := by
      apply eq_neg_of_add_eq_zero_right
      simpa only [add_assoc] using hd2 s hs
    have hb : ‖act (H' s) (φ' s)‖ ≤ N1 * ‖φ' s‖ :=
      (Matrix.l2_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hN1 s hs) (norm_nonneg _))
    have hc : ‖act (H'' s) (φ s)‖ ≤ N2 := by
      simpa [act, hnφ] using (Matrix.l2_opNorm_mulVec (H'' s) (φ s)).trans
        (mul_le_mul_of_nonneg_right (hN2 s hs) (norm_nonneg _))
    rw [heq, norm_neg]
    have hh := (norm_add_le (act (H'' s) (φ s) + act (H' s) (φ' s)) (act (H' s) (φ' s))).trans
      (add_le_add (norm_add_le (act (H'' s) (φ s)) (act (H' s) (φ' s))) le_rfl)
    linarith
  have hvgap := ed_gap (H s) γ hγ (hgap s hs) (φ s) v hnφ (hφ s hs).2 horth
  rw [hvact] at hvgap
  have hvbound : ‖v‖ ≤ (N2 + 2 * N1 * ‖φ' s‖) / γ := by
    apply (le_div_iff₀ hγ).2
    nlinarith
  calc
    ‖φ'' s‖ ≤ (N2 + 2 * N1 * ‖φ' s‖) / γ + ‖φ' s‖ ^ 2 := hvnorm.trans (add_le_add hvbound le_rfl)
    _ ≤ (N2 + 2 * N1 * (N1 / γ)) / γ + (N1 / γ) ^ 2 := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ hγ.le
        have hm := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 2 * N1)
        linarith
      · nlinarith [norm_nonneg (φ' s), div_nonneg hN1pos hγ.le]
    _ = N2 / γ + 3 * N1 ^ 2 / γ ^ 2 := by ring
