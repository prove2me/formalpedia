-- Prove2me | solution 1 for QAlgorithms.Nannicini.adiabatic_unitary_replacement
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:55:03.458887+00:00
-- url     : https://prove2.me/submissions/ddd6c70e-8373-46bd-8a81-782312ebfb75

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open QAlgorithms Matrix
open scoped ComplexConjugate

namespace AdiabaticUnitaryReplacementAux

lemma ed_coords {ι : Type*} [Fintype ι] [DecidableEq ι]
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

lemma ed_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
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

lemma ed_apply_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
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

lemma norm_phi_deriv_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (φ φ' : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (hφ' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s)
    (hphase : ∀ s ∈ Set.Icc (0 : ℝ) 1, inner ℂ (φ' s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖φ' s‖ ≤ N1 / γ := by
  classical
  have hd1 (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      act (H' s) (φ s) + act (H s) (φ' s) = 0 := by
    apply PiLp.ext
    intro i
    have hd := ed_apply_deriv H H' φ φ' s (Set.Icc 0 1) (hH' s hs) (hφ' s hs) i
    have hz := hd.congr_of_mem (f₁ := fun _ => (0 : ℂ))
      (fun t ht => (congrArg (fun v : EuclideanSpace ℂ ι => v i) (hφ t ht).2).symm) hs
    exact (uniqueDiffOn_Icc_zero_one s hs).eq_deriv _ hz (hasDerivWithinAt_const s _ 0)
  intro s hs
  have hnφ : ‖φ s‖ = 1 := (hφ s hs).1
  have hact1 : ‖act (H' s) (φ s)‖ ≤ N1 := by
    calc
      _ ≤ specNorm (H' s) * ‖φ s‖ := Matrix.l2_opNorm_mulVec _ _
      _ ≤ N1 := by simpa [hnφ] using hN1 s hs
  apply (le_div_iff₀ hγ).2
  have h := ed_gap (H s) γ hγ (hgap s hs) (φ s) (φ' s) hnφ (hφ s hs).2
    (by rw [inner_eq_zero_symm]; exact hphase s hs)
  have heq : act (H s) (φ' s) = -act (H' s) (φ s) := eq_neg_of_add_eq_zero_right (hd1 s hs)
  rw [heq, norm_neg] at h
  nlinarith

noncomputable def matToCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  letI : NormedAddCommGroup (Matrix ι ι ℂ) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix ι ι ℂ) := Pi.normedSpace
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
      map_add' := map_add _
      map_smul' := fun r M => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
          RCLike.real_smul_eq_coe_smul (K := ℂ)] }

theorem hasDerivWithinAt_entrywise_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → Matrix ι ι ℂ} {f' : Matrix ι ι ℂ} {S : Set ℝ} {s : ℝ}
    (hf : ∀ i j, HasDerivWithinAt (fun t => f t i j) (f' i j) S s) :
    HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (f t))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) f') S s := by
  let _ : NormedAddCommGroup (Matrix ι ι ℂ) := Pi.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix ι ι ℂ) := Pi.normedSpace
  have hmat : HasDerivWithinAt f f' S s :=
    hasDerivWithinAt_pi.mpr fun i => hasDerivWithinAt_pi.mpr fun j => hf i j
  exact (matToCLM ι).hasFDerivAt.comp_hasDerivWithinAt s hmat

lemma specNorm_sub_le_of_entrywise_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (N1 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    specNorm (H b - H a) ≤ N1 * (b - a) := by
  have hclm : ∀ M : Matrix ι ι ℂ,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M‖ = specNorm M := fun _ => rfl
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t))
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H' s)) (Set.Icc 0 1) s :=
    fun s hs => hasDerivWithinAt_entrywise_toEuclideanCLM (hH' s hs)
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H' s)‖ ≤ N1 := by
    intro s hs; rw [hclm]; exact hN1 s hs
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H t))
    (f' := fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (H' t))
    (s := Set.Icc 0 1) (x := a) (y := b)
    hd hbound (convex_Icc 0 1) ha hb
  rw [← map_sub, hclm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hmvt
  exact hmvt

section L2OpNorm

open scoped Matrix.Norms.L2Operator

noncomputable local instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℝ (Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

noncomputable local instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℚ (Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

lemma act_zero {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    act A (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [act]

lemma zero_act {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    act (0 : Matrix ι ι ℂ) v = 0 := by
  simp [act]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) v = v := by
  simp [act]

lemma act_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    act A (x + y) = act A x + act A y := by
  simp [act, Matrix.mulVec_add]

lemma act_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    act A (x - y) = act A x - act A y := by
  simp [act, Matrix.mulVec_sub]

lemma add_act {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act (A + B) x = act A x + act B x := by
  simp [act, Matrix.add_mulVec]

lemma sub_act {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act (A - B) x = act A x - act B x := by
  simp [act, Matrix.sub_mulVec]

lemma act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (x : EuclideanSpace ℂ ι) :
    act A (c • x) = c • act A x := by
  simp [act, Matrix.mulVec_smul]

lemma smul_act {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act (c • A) x = c • act A x := by
  simp [act, Matrix.smul_mulVec]

lemma act_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act (A * B) x = act A (act B x) := by
  simp [act, Matrix.mulVec_mulVec]

lemma act_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : Matrix ι ι ℂ)
    (f : κ → EuclideanSpace ℂ ι) :
    act A (∑ j ∈ s, f j) = ∑ j ∈ s, act A (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [act_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

lemma norm_act_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    ‖act A x‖ ≤ ‖A‖ * ‖x‖ :=
  Matrix.l2_opNorm_mulVec A x

lemma exp_mem_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (hJ : J.IsHermitian) (s : ℝ) :
    NormedSpace.exp ((Complex.I * (s : ℂ)) • J) ∈ unitary (Matrix ι ι ℂ) := by
  have hsa : star J = J := hJ
  have hs : ((s : ℂ) • J) ∈ selfAdjoint (Matrix ι ι ℂ) := by
    rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
  have := (selfAdjoint.expUnitary ⟨(s : ℂ) • J, hs⟩).prop
  simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
  exact this

lemma exp_neg_mul_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (s : ℝ) :
    NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) *
      NormedSpace.exp ((Complex.I * (s : ℂ)) • J) = 1 := by
  rw [neg_smul, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)),
    neg_add_cancel, NormedSpace.exp_zero]

lemma hasDerivAt_exp_I_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((Complex.I * (u : ℂ)) • J))
      (NormedSpace.exp ((Complex.I * (s : ℂ)) • J) * (Complex.I • J)) s := by
  have hU_eq : (fun u : ℝ => NormedSpace.exp ((Complex.I * (u : ℂ)) • J)) =
      (fun u : ℝ => NormedSpace.exp (u • (Complex.I • J))) := by
    funext u; congr 1
    change (Complex.I * (u : ℂ)) • J = (u : ℂ) • (Complex.I • J)
    rw [smul_smul, mul_comm]
  rw [hU_eq]
  have hd := hasDerivAt_exp_smul_const (Complex.I • J) s
  rwa [← congr_fun hU_eq s] at hd

lemma hasDerivAt_exp_neg_I_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((-(Complex.I * (u : ℂ))) • J))
      (NormedSpace.exp ((-(Complex.I * (s : ℂ))) • J) * ((-Complex.I) • J)) s := by
  have hV_eq : (fun u : ℝ => NormedSpace.exp ((-(Complex.I * (u : ℂ))) • J)) =
      (fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • J))) := by
    funext u; congr 1
    change (-(Complex.I * (u : ℂ))) • J = (u : ℂ) • ((-Complex.I) • J)
    rw [smul_smul, mul_neg, mul_comm]
  rw [hV_eq]
  have hd := hasDerivAt_exp_smul_const ((-Complex.I) • J) s
  rwa [← congr_fun hV_eq s] at hd

lemma norm_sub_zero_le_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (τ M : ℝ)
    (hd : ∀ u, HasDerivAt f (f' u) u)
    (hb : ∀ u, |u| ≤ |τ| → ‖f' u‖ ≤ M) :
    ‖f τ - f 0‖ ≤ M * |τ| := by
  rcases le_total 0 τ with hτ | hτ
  · have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (s := Set.Icc 0 τ) (x := 0) (y := τ)
      (fun u _ => (hd u).hasDerivWithinAt)
      (fun u hu => hb u (by rw [abs_of_nonneg hu.1, abs_of_nonneg hτ]; exact hu.2))
      (convex_Icc 0 τ) ⟨le_rfl, hτ⟩ ⟨hτ, le_rfl⟩
    simpa [abs_of_nonneg hτ] using h1
  · have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (s := Set.Icc τ 0) (x := τ) (y := 0)
      (fun u _ => (hd u).hasDerivWithinAt)
      (fun u hu => hb u (by rw [abs_of_nonpos hu.2, abs_of_nonpos hτ]; linarith [hu.1]))
      (convex_Icc τ 0) ⟨le_rfl, hτ⟩ ⟨hτ, le_rfl⟩
    rw [norm_sub_rev]
    simpa [abs_of_nonpos hτ] using h1

lemma norm_exp_sub_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (hJ : J.IsHermitian) (τ : ℝ) :
    ‖NormedSpace.exp ((Complex.I * (τ : ℂ)) • J) - 1‖ ≤ ‖J‖ * |τ| := by
  have h := norm_sub_zero_le_of_hasDerivAt
    (fun u : ℝ => NormedSpace.exp ((Complex.I * (u : ℂ)) • J))
    (fun u : ℝ => NormedSpace.exp ((Complex.I * (u : ℂ)) • J) * (Complex.I • J))
    τ ‖J‖
    (fun u => hasDerivAt_exp_I_smul J u)
    (fun u _ => by
      rw [CStarRing.norm_mem_unitary_mul (Complex.I • J) (exp_mem_unitary J hJ u),
        norm_smul, Complex.norm_I, one_mul])
  simpa [NormedSpace.exp_zero] using h

lemma norm_exp_sub_one_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℂ) (hJ : J.IsHermitian) (τ : ℝ) :
    ‖NormedSpace.exp ((Complex.I * (τ : ℂ)) • J) - 1 - (Complex.I * (τ : ℂ)) • J‖ ≤
      ‖J‖ ^ 2 * |τ| ^ 2 := by
  have hd : ∀ u : ℝ,
      HasDerivAt
        (fun t : ℝ => NormedSpace.exp ((Complex.I * (t : ℂ)) • J) - 1 - (Complex.I * (t : ℂ)) • J)
        ((NormedSpace.exp ((Complex.I * (u : ℂ)) • J) - 1) * (Complex.I • J)) u := by
    intro u
    have hlin : HasDerivAt (fun t : ℝ => (Complex.I * (t : ℂ)) • J) (Complex.I • J) u := by
      have heq : (fun t : ℝ => (Complex.I * (t : ℂ)) • J) = fun t : ℝ => t • (Complex.I • J) := by
        funext t
        change (Complex.I * (t : ℂ)) • J = (t : ℂ) • (Complex.I • J)
        rw [smul_smul, mul_comm]
      rw [heq]
      simpa using (hasDerivAt_id u).smul_const (Complex.I • J)
    have h1 := ((hasDerivAt_exp_I_smul J u).sub_const (1 : Matrix ι ι ℂ)).sub hlin
    refine h1.congr_deriv ?_
    rw [sub_mul, one_mul]
  have h := norm_sub_zero_le_of_hasDerivAt
    (fun t : ℝ => NormedSpace.exp ((Complex.I * (t : ℂ)) • J) - 1 - (Complex.I * (t : ℂ)) • J)
    (fun u : ℝ => (NormedSpace.exp ((Complex.I * (u : ℂ)) • J) - 1) * (Complex.I • J))
    τ (‖J‖ ^ 2 * |τ|)
    hd
    (fun u hu => by
      calc ‖(NormedSpace.exp ((Complex.I * (u : ℂ)) • J) - 1) * (Complex.I • J)‖
          ≤ ‖NormedSpace.exp ((Complex.I * (u : ℂ)) • J) - 1‖ * ‖Complex.I • J‖ := norm_mul_le _ _
        _ ≤ (‖J‖ * |u|) * ‖J‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
          exact mul_le_mul_of_nonneg_right (norm_exp_sub_one_le J hJ u) (norm_nonneg J)
        _ ≤ (‖J‖ * |τ|) * ‖J‖ := by gcongr
        _ = ‖J‖ ^ 2 * |τ| := by ring)
  simpa only [Complex.ofReal_zero, mul_zero, zero_smul, NormedSpace.exp_zero, sub_self,
    sub_zero, sq, mul_assoc] using h

lemma norm_exp_sub_exp_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (τ : ℝ) :
    ‖NormedSpace.exp ((Complex.I * (τ : ℂ)) • A) -
      NormedSpace.exp ((Complex.I * (τ : ℂ)) • B)‖ ≤ ‖A - B‖ * |τ| := by
  let f : ℝ → Matrix ι ι ℂ := fun u =>
    NormedSpace.exp ((Complex.I * (u : ℂ)) • A) *
      NormedSpace.exp ((-(Complex.I * (u : ℂ))) • B)
  let f' : ℝ → Matrix ι ι ℂ := fun u =>
    NormedSpace.exp ((Complex.I * (u : ℂ)) • A) * (Complex.I • (A - B)) *
      NormedSpace.exp ((-(Complex.I * (u : ℂ))) • B)
  have hd : ∀ u : ℝ, HasDerivAt f (f' u) u := by
    intro u
    have htot := (hasDerivAt_exp_I_smul A u).mul (hasDerivAt_exp_neg_I_smul B u)
    have hcomm : NormedSpace.exp ((-(Complex.I * (u : ℂ))) • B) * ((-Complex.I) • B) =
        ((-Complex.I) • B) * NormedSpace.exp ((-(Complex.I * (u : ℂ))) • B) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      exact (Commute.refl B |>.smul_left (-(Complex.I * (u : ℂ)))).exp_left
    refine htot.congr_deriv ?_
    dsimp only [f']
    rw [hcomm, ← mul_assoc, ← add_mul, ← mul_add, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  have h := norm_sub_zero_le_of_hasDerivAt f f' τ ‖A - B‖ hd (fun u _ => by
    dsimp only [f']
    have hUA := exp_mem_unitary A hA u
    have hVB : NormedSpace.exp ((-(Complex.I * (u : ℂ))) • B) ∈ unitary (Matrix ι ι ℂ) := by
      have heq : -(Complex.I * (u : ℂ)) = Complex.I * ((-u : ℝ) : ℂ) := by push_cast; ring
      rw [heq]
      exact exp_mem_unitary B hB (-u)
    rw [CStarRing.norm_mul_mem_unitary _ hVB, CStarRing.norm_mem_unitary_mul _ hUA,
      norm_smul, Complex.norm_I, one_mul])
  have hf0 : f 0 = 1 := by simp [f, NormedSpace.exp_zero]
  have hmul : (f τ - 1) * NormedSpace.exp ((Complex.I * (τ : ℂ)) • B) =
      NormedSpace.exp ((Complex.I * (τ : ℂ)) • A) -
        NormedSpace.exp ((Complex.I * (τ : ℂ)) • B) := by
    dsimp only [f]
    rw [sub_mul, one_mul, mul_assoc, exp_neg_mul_exp B τ, mul_one]
  rw [← hmul, CStarRing.norm_mul_mem_unitary _ (exp_mem_unitary B hB τ)]
  simpa [hf0] using h

noncomputable def actRightCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ →L[ℝ] EuclideanSpace ℂ ι :=
  LinearMap.mkContinuous
    { toFun := fun M => act M v
      map_add' := fun M N => add_act M N v
      map_smul' := fun r M => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
        exact smul_act (r : ℂ) M v }
    ‖v‖
    (fun M => (norm_act_le M v).trans_eq (mul_comm _ _))

lemma act_exp_I_smul_of_act_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (φ1 : EuclideanSpace ℂ ι) (hBφ1 : act B φ1 = 0) (τ : ℝ) :
    act (NormedSpace.exp ((Complex.I * (τ : ℂ)) • B)) φ1 = φ1 := by
  have hd : ∀ u : ℝ,
      HasDerivAt (fun t : ℝ => act (NormedSpace.exp ((Complex.I * (t : ℂ)) • B)) φ1) 0 u := by
    intro u
    have h1 := (actRightCLM φ1).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_exp_I_smul B u)
    have h2 : act (NormedSpace.exp ((Complex.I * (u : ℂ)) • B) * (Complex.I • B)) φ1 = 0 := by
      rw [act_mul, smul_act, hBφ1, smul_zero, act_zero]
    exact h1.congr_deriv h2
  have hle := norm_sub_zero_le_of_hasDerivAt
    (fun t : ℝ => act (NormedSpace.exp ((Complex.I * (t : ℂ)) • B)) φ1)
    (fun _ => 0) τ 0 hd (fun _ _ => by simp)
  simp only [Complex.ofReal_zero, NormedSpace.exp_zero, smul_zero, mul_zero, zero_smul,
    act_one, zero_mul, norm_le_zero_iff, sub_eq_zero] at hle
  exact hle

lemma inner_act_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act M y) = inner ℂ (act (star M) x) y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, act, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Complex.star_def, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma inner_act_unitary_eq_of_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    {φ1 : EuclideanSpace ℂ ι} (hUφ1 : act U φ1 = φ1) (v : EuclideanSpace ℂ ι) :
    inner ℂ φ1 (act U v) = inner ℂ φ1 v := by
  have hmul : star U * U = 1 := Unitary.coe_star_mul_self ⟨U, hU⟩
  have hstar : act (star U) φ1 = φ1 := by
    calc act (star U) φ1 = act (star U) (act U φ1) := by rw [hUφ1]
      _ = act (star U * U) φ1 := (act_mul (star U) U φ1).symm
      _ = act 1 φ1 := by rw [hmul]
      _ = φ1 := act_one φ1
  rw [inner_act_right, hstar]

lemma prod_range_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ℕ → Matrix ι ι ℂ) (k j : ℕ) (hjk : j ≤ k) :
    ((List.range (k + 1 + 1 - j)).map fun i => U (k + 1 - i)).prod =
      U (k + 1) * ((List.range (k + 1 - j)).map fun i => U (k - i)).prod := by
  have hsub : k + 1 + 1 - j = (k + 1 - j) + 1 := by omega
  rw [hsub, List.range_succ_eq_map, List.map_cons, List.prod_cons, Nat.sub_zero, List.map_map]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  simp only [Function.comp_apply]
  congr 1
  omega

lemma sum_sub_one_le (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, ((m : ℝ) - 1) ≤ (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    linarith

end L2OpNorm

end AdiabaticUnitaryReplacementAux

open AdiabaticUnitaryReplacementAux
open scoped Matrix.Norms.L2Operator

noncomputable local instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℝ (Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

noncomputable local instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℚ (Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

set_option maxHeartbeats 800000 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (φ φ' : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (hφ' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s)
    (hphase : ∀ s ∈ Set.Icc (0 : ℝ) 1, inner ℂ (φ' s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : 10 ^ 3 / δ ^ 2 * max (N1 ^ 3 / γ ^ 4) (N1 * N2 / γ ^ 3) ≤ T) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ, 1 ≤ k → k ≤ N →
      let U : ℕ → Matrix ι ι ℂ := fun j =>
        NormedSpace.exp ((Complex.I * ((T / N : ℝ) : ℂ)) • H ((j : ℝ) / N))
      let g : ℕ → EuclideanSpace ℂ ι := fun j => φ ((j : ℝ) / N)
      let p1 : EuclideanSpace ℂ ι := (g 0 - g 1) - inner ℂ (g 1) (g 0 - g 1) • g 1
      ‖∑ j ∈ Finset.Icc 1 k, act ((List.range (k + 1 - j)).map fun i => U (k - i)).prod p1 -
          ∑ j ∈ Finset.Icc 1 k, act (U 1 ^ (k + 1 - j)) p1‖ ≤
        2 * ((k : ℝ) + 1) * k * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2) + C * k / (N : ℝ) ^ 3 := by
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hN1_nonneg : 0 ≤ N1 := (norm_nonneg (H' 0)).trans (hN1 0 h0_mem)
  have hφ'_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖φ' s‖ ≤ N1 / γ :=
    norm_phi_deriv_le H H' hH' φ φ' hφ hφ' hphase γ hγ hgap N1 hN1
  set B_H : ℝ := ‖H 0‖ + N1
  have hB_H_nonneg : 0 ≤ B_H := add_nonneg (norm_nonneg _) hN1_nonneg
  have hH_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖H s‖ ≤ B_H := by
    intro s hs
    have hsub : ‖H s - H 0‖ ≤ N1 * (s - 0) :=
      specNorm_sub_le_of_entrywise_deriv H H' hH' N1 hN1 0 s h0_mem hs hs.1
    have htri : ‖H s‖ ≤ ‖H 0‖ + ‖H s - H 0‖ := by
      simpa using norm_add_le (H 0) (H s - H 0)
    have hs1 : N1 * (s - 0) ≤ N1 := by nlinarith [hs.2]
    linarith
  refine ⟨0, Nat.ceil (2 * B_H ^ 2 * |T| / γ) + 1, ?_⟩
  intro N hN k hk1 hkN
  dsimp only
  set U : ℕ → Matrix ι ι ℂ := fun j =>
    NormedSpace.exp ((Complex.I * ((T / N : ℝ) : ℂ)) • H ((j : ℝ) / N))
  set g : ℕ → EuclideanSpace ℂ ι := fun j => φ ((j : ℝ) / N)
  set p1 : EuclideanSpace ℂ ι := (g 0 - g 1) - inner ℂ (g 1) (g 0 - g 1) • g 1
  have hN_pos_nat : 1 ≤ N := by omega
  have hN_pos : 0 < (N : ℝ) := by positivity
  have h_rhs_nonneg :
      0 ≤ 2 * ((k : ℝ) + 1) * k * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2) + 0 * k / (N : ℝ) ^ 3 := by
    positivity
  by_cases hT0 : T = 0
  · have hU_eq_one : ∀ j : ℕ, U j = 1 := by
      intro j
      simp [U, hT0, NormedSpace.exp_zero]
    have hprod_eq : ∀ j ∈ Finset.Icc 1 k,
        ((List.range (k + 1 - j)).map fun i => U (k - i)).prod = U 1 ^ (k + 1 - j) := by
      intro j _
      simp [hU_eq_one]
    have hsum_eq :
        ∑ j ∈ Finset.Icc 1 k, act ((List.range (k + 1 - j)).map fun i => U (k - i)).prod p1 =
          ∑ j ∈ Finset.Icc 1 k, act (U 1 ^ (k + 1 - j)) p1 :=
      Finset.sum_congr rfl fun j hj => by rw [hprod_eq j hj]
    rw [hsum_eq, sub_self, norm_zero]
    exact h_rhs_nonneg
  · have hT_abs_pos : 0 < |T| := abs_pos.mpr hT0
    set τ : ℝ := T / N
    have hτ_abs : |τ| = |T| / (N : ℝ) := by
      dsimp only [τ]
      rw [abs_div, abs_of_pos hN_pos]
    have hτ_pos : 0 < |τ| := by rw [hτ_abs]; positivity
    have h_div_mem : ∀ j : ℕ, j ≤ N → ((j : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
      intro j hj
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hN_pos]
      exact_mod_cast hj
    have h1_mem : ((1 : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := h_div_mem 1 hN_pos_nat
    have hU_unitary : ∀ j : ℕ, j ≤ N → U j ∈ unitary (Matrix ι ι ℂ) := by
      intro j hj
      exact exp_mem_unitary (H ((j : ℝ) / N)) (hgap ((j : ℝ) / N) (h_div_mem j hj)).1 τ
    have hU1_unitary : U 1 ∈ unitary (Matrix ι ι ℂ) := hU_unitary 1 hN_pos_nat
    have hU_norm : ∀ j : ℕ, j ≤ N → ∀ v : EuclideanSpace ℂ ι, ‖act (U j) v‖ = ‖v‖ :=
      fun j hj v => act_norm_of_mem_unitaryGroup (hU_unitary j hj) v
    have hU1_pow_unitary : ∀ r : ℕ, U 1 ^ r ∈ unitary (Matrix ι ι ℂ) :=
      fun r => Submonoid.pow_mem (unitary (Matrix ι ι ℂ)) hU1_unitary r
    have hg1_norm : ‖g 1‖ = 1 := (hφ (((1 : ℕ) : ℝ) / N) h1_mem).1
    have hHg1 : act (H (((1 : ℕ) : ℝ) / N)) (g 1) = 0 := (hφ (((1 : ℕ) : ℝ) / N) h1_mem).2
    have hU1_g1 : act (U 1) (g 1) = g 1 :=
      act_exp_I_smul_of_act_eq_zero (H (((1 : ℕ) : ℝ) / N)) (g 1) hHg1 τ
    have hp1_orth : inner ℂ (g 1) p1 = 0 := by
      dsimp only [p1]
      rw [inner_sub_right, inner_smul_right]
      have h1 : inner ℂ (g 1) (g 1) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hg1_norm]
        simp
      rw [h1, mul_one, sub_self]
    have hp1_norm_le_diff : ‖p1‖ ≤ ‖g 0 - g 1‖ := by
      have h_inner_p1 : inner ℂ p1 p1 = inner ℂ (g 0 - g 1) p1 := by
        conv_lhs => rw [show p1 = (g 0 - g 1) - inner ℂ (g 1) (g 0 - g 1) • g 1 from rfl]
        rw [inner_sub_left, inner_smul_left, hp1_orth, mul_zero, sub_zero]
      have hcs : ‖p1‖ ^ 2 ≤ ‖g 0 - g 1‖ * ‖p1‖ := by
        calc ‖p1‖ ^ 2 = ‖inner ℂ p1 p1‖ := by
              rw [inner_self_eq_norm_sq_to_K]; simp [norm_nonneg p1]
          _ = ‖inner ℂ (g 0 - g 1) p1‖ := by rw [h_inner_p1]
          _ ≤ ‖g 0 - g 1‖ * ‖p1‖ := norm_inner_le_norm (g 0 - g 1) p1
      nlinarith [norm_nonneg p1, norm_nonneg (g 0 - g 1)]
    have hg0_sub_g1 : ‖g 0 - g 1‖ ≤ N1 / (γ * (N : ℝ)) := by
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := φ) (f' := φ') (s := Set.Icc 0 1) (x := 0) (y := ((1 : ℕ) : ℝ) / N)
        hφ' hφ'_bound (convex_Icc 0 1) h0_mem h1_mem
      have heq0 : g 0 = φ 0 := by simp [g]
      rw [heq0, norm_sub_rev]
      calc ‖g 1 - φ 0‖ = ‖φ (((1 : ℕ) : ℝ) / N) - φ 0‖ := rfl
        _ ≤ (N1 / γ) * ‖((1 : ℕ) : ℝ) / N - 0‖ := hmvt
        _ = N1 / (γ * (N : ℝ)) := by
          rw [sub_zero, Real.norm_of_nonneg (by positivity)]
          ring
    have hp1_le : ‖p1‖ ≤ N1 / (γ * (N : ℝ)) := hp1_norm_le_diff.trans hg0_sub_g1
    set P : ℕ → ℕ → Matrix ι ι ℂ := fun m j =>
      ((List.range (m + 1 - j)).map fun i => U (m - i)).prod
    set D : ℕ → EuclideanSpace ℂ ι := fun m =>
      ∑ j ∈ Finset.Icc 1 m, act (P m j) p1 - ∑ j ∈ Finset.Icc 1 m, act (U 1 ^ (m + 1 - j)) p1
    set S : ℕ → EuclideanSpace ℂ ι := fun m =>
      p1 + ∑ j ∈ Finset.Icc 1 m, act (U 1 ^ (m + 1 - j)) p1
    have hD0 : D 0 = 0 := by simp [D]
    have hS0 : S 0 = p1 := by simp [S]
    have hS_succ : ∀ m : ℕ, S (m + 1) = p1 + act (U 1) (S m) := by
      intro m
      dsimp only [S]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1),
        show m + 1 + 1 - (m + 1) = 1 by omega, pow_one, act_add, act_sum]
      have hsum : ∑ j ∈ Finset.Icc 1 m, act (U 1 ^ (m + 1 + 1 - j)) p1 =
          ∑ j ∈ Finset.Icc 1 m, act (U 1) (act (U 1 ^ (m + 1 - j)) p1) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
        have hsub : m + 1 + 1 - j = (m + 1 - j) + 1 := by omega
        rw [hsub, pow_succ', act_mul]
      rw [hsum]
      abel
    have hD_succ : ∀ m : ℕ, D (m + 1) = act (U (m + 1)) (D m) + act (U (m + 1) - U 1) (S m) := by
      intro m
      have hP_sum : ∑ j ∈ Finset.Icc 1 (m + 1), act (P (m + 1) j) p1 =
          act (U (m + 1)) (S m + D m) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        have htop : P (m + 1) (m + 1) = U (m + 1) := by
          dsimp only [P]
          rw [show m + 1 + 1 - (m + 1) = 1 by omega]
          simp
        have hrest : ∑ j ∈ Finset.Icc 1 m, act (P (m + 1) j) p1 =
            ∑ j ∈ Finset.Icc 1 m, act (U (m + 1)) (act (P m j) p1) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
          dsimp only [P]
          rw [prod_range_succ U m j hjm, act_mul]
        have hSD : (∑ j ∈ Finset.Icc 1 m, act (P m j) p1) + p1 = S m + D m := by
          dsimp only [S, D]; abel
        rw [htop, hrest, ← act_sum, ← act_add, hSD]
      have hU1_sum : ∑ j ∈ Finset.Icc 1 (m + 1), act (U 1 ^ (m + 1 + 1 - j)) p1 =
          act (U 1) (S m) := by
        have := hS_succ m
        dsimp only [S] at this
        exact add_left_cancel (a := p1) this
      change ∑ j ∈ Finset.Icc 1 (m + 1), act (P (m + 1) j) p1 -
          ∑ j ∈ Finset.Icc 1 (m + 1), act (U 1 ^ (m + 1 + 1 - j)) p1 = _
      rw [hP_sum, hU1_sum, act_add, sub_act]
      abel
    have hD_norm_le : ∀ m : ℕ, m ≤ N →
        ‖D m‖ ≤ ∑ r ∈ Finset.Icc 1 m, ‖act (U r - U 1) (S (r - 1))‖ := by
      intro m hm
      induction m with
      | zero => simp [hD0]
      | succ m ih =>
        have hm_le : m ≤ N := by omega
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), Nat.add_sub_cancel, hD_succ m]
        calc ‖act (U (m + 1)) (D m) + act (U (m + 1) - U 1) (S m)‖
            ≤ ‖act (U (m + 1)) (D m)‖ + ‖act (U (m + 1) - U 1) (S m)‖ := norm_add_le _ _
          _ = ‖D m‖ + ‖act (U (m + 1) - U 1) (S m)‖ := by rw [hU_norm (m + 1) hm (D m)]
          _ ≤ (∑ r ∈ Finset.Icc 1 m, ‖act (U r - U 1) (S (r - 1))‖) +
                ‖act (U (m + 1) - U 1) (S m)‖ := add_le_add (ih hm_le) le_rfl
    have hS_orth : ∀ m : ℕ, inner ℂ (g 1) (S m) = 0 := by
      intro m
      induction m with
      | zero => simpa [hS0] using hp1_orth
      | succ m ih =>
        rw [hS_succ m, inner_add_right, hp1_orth, zero_add,
          inner_act_unitary_eq_of_fixed hU1_unitary hU1_g1, ih]
    have hS_geom : ∀ m : ℕ, act (U 1 - 1) (S m) = act (U 1 ^ (m + 1)) p1 - p1 := by
      intro m
      induction m with
      | zero =>
        rw [hS0, sub_act, act_one, pow_one]
      | succ m ih =>
        have hstep : act (U 1 - 1) (S (m + 1)) =
            act (U 1) p1 - p1 + act (U 1) (act (U 1 - 1) (S m)) := by
          rw [hS_succ m, sub_act, act_one, sub_act, act_one,
            act_add (U 1) p1 (act (U 1) (S m)), act_sub (U 1) (act (U 1) (S m)) (S m)]
          abel
        rw [hstep, ih, act_sub (U 1) (act (U 1 ^ (m + 1)) p1) p1, ← act_mul, ← pow_succ']
        abel
    have hS_geom_norm : ∀ m : ℕ, ‖act (U 1 - 1) (S m)‖ ≤ 2 * ‖p1‖ := by
      intro m
      rw [hS_geom m]
      calc ‖act (U 1 ^ (m + 1)) p1 - p1‖
          ≤ ‖act (U 1 ^ (m + 1)) p1‖ + ‖p1‖ := norm_sub_le _ _
        _ = ‖p1‖ + ‖p1‖ := by
          rw [act_norm_of_mem_unitaryGroup (hU1_pow_unitary (m + 1)) p1]
        _ = 2 * ‖p1‖ := by ring
    have hN_large : 2 * B_H ^ 2 * |T| / γ ≤ (N : ℝ) := by
      have h1 : 2 * B_H ^ 2 * |T| / γ ≤ (Nat.ceil (2 * B_H ^ 2 * |T| / γ) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (2 * B_H ^ 2 * |T| / γ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (2 * B_H ^ 2 * |T| / γ) ≤ N)
      exact h1.trans h2
    have h_rem_norm :
        ‖U 1 - 1 - (Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)‖ ≤ (γ / 2) * |τ| := by
      have h1 := norm_exp_sub_one_sub_le (H (((1 : ℕ) : ℝ) / N))
        (hgap (((1 : ℕ) : ℝ) / N) h1_mem).1 τ
      have h2 : ‖H (((1 : ℕ) : ℝ) / N)‖ ≤ B_H := hH_bound (((1 : ℕ) : ℝ) / N) h1_mem
      have h3 : ‖H (((1 : ℕ) : ℝ) / N)‖ ^ 2 ≤ B_H ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 : B_H ^ 2 * |τ| ≤ γ / 2 := by
        rw [hτ_abs]
        rw [div_le_iff₀ hγ] at hN_large
        have h4' : (B_H ^ 2 * (|T| / (N : ℝ))) * (2 * (N : ℝ)) ≤ (γ / 2) * (2 * (N : ℝ)) := by
          have heq1 : (B_H ^ 2 * (|T| / (N : ℝ))) * (2 * (N : ℝ)) = 2 * B_H ^ 2 * |T| := by
            field_simp
          have heq2 : (γ / 2) * (2 * (N : ℝ)) = (N : ℝ) * γ := by ring
          linarith
        exact le_of_mul_le_mul_right h4' (by positivity : 0 < 2 * (N : ℝ))
      calc ‖U 1 - 1 - (Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)‖
          ≤ ‖H (((1 : ℕ) : ℝ) / N)‖ ^ 2 * |τ| ^ 2 := h1
        _ ≤ B_H ^ 2 * |τ| ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        _ = (B_H ^ 2 * |τ|) * |τ| := by ring
        _ ≤ (γ / 2) * |τ| := mul_le_mul_of_nonneg_right h4 hτ_pos.le
    have hS_norm : ∀ m : ℕ, ‖S m‖ ≤ 4 * N1 / (|T| * γ ^ 2) := by
      intro m
      have hgap_S := ed_gap (H (((1 : ℕ) : ℝ) / N)) γ hγ
        (hgap (((1 : ℕ) : ℝ) / N) h1_mem) (g 1) (S m) hg1_norm hHg1 (hS_orth m)
      have hlin_norm :
          |τ| * (γ * ‖S m‖) ≤ ‖act ((Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)) (S m)‖ := by
        rw [smul_act, norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hgap_S hτ_pos.le
      have hrem_S :
          ‖act (U 1 - 1 - (Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)) (S m)‖ ≤
            (γ / 2) * |τ| * ‖S m‖ := by
        calc ‖act (U 1 - 1 - (Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)) (S m)‖
            ≤ ‖U 1 - 1 - (Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)‖ * ‖S m‖ :=
              norm_act_le _ _
          _ ≤ ((γ / 2) * |τ|) * ‖S m‖ :=
              mul_le_mul_of_nonneg_right h_rem_norm (norm_nonneg _)
      have htri :
          ‖act ((Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)) (S m)‖ ≤
            ‖act (U 1 - 1) (S m)‖ +
              ‖act (U 1 - 1 - (Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)) (S m)‖ := by
        have heq : act ((Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)) (S m) =
            act (U 1 - 1) (S m) -
              act (U 1 - 1 - (Complex.I * (τ : ℂ)) • H (((1 : ℕ) : ℝ) / N)) (S m) := by
          rw [← sub_act, sub_sub_cancel]
        rw [heq]
        exact norm_sub_le _ _
      have hlow : (|τ| * γ / 2) * ‖S m‖ ≤ 2 * (N1 / (γ * (N : ℝ))) := by
        have hgeom := hS_geom_norm m
        linarith
      rw [hτ_abs] at hlow
      rw [le_div_iff₀ (by positivity : 0 < |T| * γ ^ 2)]
      have hlow' : (|T| * γ ^ 2) * ‖S m‖ ≤ 4 * N1 := by
        have hmul := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 2 * (N : ℝ) * γ)
        have hsimp1 : (2 * (N : ℝ) * γ) * ((|T| / (N : ℝ) * γ / 2) * ‖S m‖) =
            (|T| * γ ^ 2) * ‖S m‖ := by
          field_simp
        have hsimp2 : (2 * (N : ℝ) * γ) * (2 * (N1 / (γ * (N : ℝ)))) = 4 * N1 := by
          field_simp
          ring
        linarith
      linarith
    have h_term_bound : ∀ r ∈ Finset.Icc 1 k,
        ‖act (U r - U 1) (S (r - 1))‖ ≤
          4 * ((r : ℝ) - 1) * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2) := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrk : r ≤ k := (Finset.mem_Icc.mp hr).2
      have hrN : r ≤ N := hrk.trans hkN
      have hr_mem : ((r : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := h_div_mem r hrN
      have h1r_le : ((1 : ℕ) : ℝ) / N ≤ (r : ℝ) / N := by gcongr
      have hH_diff : ‖H ((r : ℝ) / N) - H (((1 : ℕ) : ℝ) / N)‖ ≤
          N1 * (((r : ℝ) - 1) / (N : ℝ)) := by
        have hmvt := specNorm_sub_le_of_entrywise_deriv H H' hH' N1 hN1
          (((1 : ℕ) : ℝ) / N) ((r : ℝ) / N) h1_mem hr_mem h1r_le
        have hsub : (r : ℝ) / N - ((1 : ℕ) : ℝ) / N = ((r : ℝ) - 1) / (N : ℝ) := by
          push_cast; ring
        rwa [hsub] at hmvt
      have hU_diff : ‖U r - U 1‖ ≤ N1 * (((r : ℝ) - 1) / (N : ℝ)) * (|T| / (N : ℝ)) := by
        have h1 := norm_exp_sub_exp_le (H ((r : ℝ) / N)) (H (((1 : ℕ) : ℝ) / N))
          (hgap ((r : ℝ) / N) hr_mem).1 (hgap (((1 : ℕ) : ℝ) / N) h1_mem).1 τ
        rw [hτ_abs] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right hH_diff (by positivity))
      calc ‖act (U r - U 1) (S (r - 1))‖
          ≤ ‖U r - U 1‖ * ‖S (r - 1)‖ := norm_act_le _ _
        _ ≤ (N1 * (((r : ℝ) - 1) / (N : ℝ)) * (|T| / (N : ℝ))) *
              (4 * N1 / (|T| * γ ^ 2)) :=
            mul_le_mul hU_diff (hS_norm (r - 1)) (norm_nonneg _)
              (by have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
                  have : 0 ≤ (r : ℝ) - 1 := by linarith
                  positivity)
        _ = 4 * ((r : ℝ) - 1) * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2) := by
            field_simp
    have hsum_le :
        ∑ r ∈ Finset.Icc 1 k, ‖act (U r - U 1) (S (r - 1))‖ ≤
          2 * ((k : ℝ) + 1) * k * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2) := by
      calc ∑ r ∈ Finset.Icc 1 k, ‖act (U r - U 1) (S (r - 1))‖
          ≤ ∑ r ∈ Finset.Icc 1 k, (4 * ((r : ℝ) - 1) * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2)) :=
            Finset.sum_le_sum h_term_bound
        _ = (4 * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2)) * ∑ r ∈ Finset.Icc 1 k, ((r : ℝ) - 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            ring
        _ ≤ (4 * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2)) * ((k : ℝ) * ((k : ℝ) + 1) / 2) :=
            mul_le_mul_of_nonneg_left (sum_sub_one_le k) (by positivity)
        _ = 2 * ((k : ℝ) + 1) * k * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2) := by ring
    exact (hD_norm_le k hkN).trans (hsum_le.trans (by simp))
