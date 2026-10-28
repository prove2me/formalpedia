-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.positiveThresholdExists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T10:07:07.139276+00:00
-- url     : https://prove2.me/submissions/a9b2c016-463e-49f3-bb91-85ccfe48182a

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_positivePartSmoothing
open Matrix
open scoped ComplexOrder

namespace X5RT

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma qf {X : Matrix I I ℂ} (hX : X.IsHermitian) (g : ℝ → ℝ) (x : I → ℂ) :
    (star x ⬝ᵥ (cfc g X *ᵥ x)).re =
      ∑ j, g (hX.eigenvalues j) * ‖(star (hX.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x) j‖ ^ 2 := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]
  set U := (hX.eigenvectorUnitary : Matrix I I ℂ)
  set y := star U *ᵥ x
  have : star x ⬝ᵥ (U *ᵥ (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hX.eigenvalues) *ᵥ y)) =
      star y ⬝ᵥ (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hX.eigenvalues) *ᵥ y) := by
    rw [dotProduct_mulVec]
    congr 1
    simp only [y]
    rw [star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [this]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Function.comp_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, mul_assoc, RCLike.star_def, Complex.mul_conj']
  simp [Complex.mul_re, pow_two]

lemma qf_one {X : Matrix I I ℂ} (hX : X.IsHermitian) (x : I → ℂ) :
    ∑ j, ‖(star (hX.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x) j‖ ^ 2 = (star x ⬝ᵥ x).re := by
  have := qf hX (fun _ => 1) x
  rw [cfc_const_one ℝ X hX.isSelfAdjoint, one_mulVec] at this
  rw [this]; simp

lemma eig_le_one {X : Matrix I I ℂ} (hX : X.PosSemidef) (htr : X.trace = 1) (j : I) :
    hX.isHermitian.eigenvalues j ≤ 1 := by
  have h := hX.isHermitian.trace_eq_sum_eigenvalues
  rw [htr] at h
  have h' : ∑ i, hX.isHermitian.eigenvalues i = 1 := by
    have := congrArg Complex.re h
    simpa using this.symm
  rw [← h']
  exact Finset.single_le_sum (fun i _ => hX.eigenvalues_nonneg i) (Finset.mem_univ j)

lemma density_le {X : Matrix I I ℂ} (hX : X.PosSemidef) (htr : X.trace = 1) (x : I → ℂ) :
    (star x ⬝ᵥ (X *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
  have h1 := qf hX.isHermitian (fun t => t) x
  rw [cfc_id' ℝ X hX.isHermitian.isSelfAdjoint] at h1
  rw [h1, ← qf_one hX.isHermitian x]
  refine Finset.sum_le_sum fun j _ => ?_
  have := eig_le_one hX htr j
  have h0 : 0 ≤ ‖(star (hX.isHermitian.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x) j‖ ^ 2 := by positivity
  nlinarith

lemma eig_eq {X : Matrix I I ℂ} (hX : X.IsHermitian) (j : I) :
    hX.eigenvalues j = (star (hX.eigenvectorBasis j).ofLp ⬝ᵥ (X *ᵥ (hX.eigenvectorBasis j).ofLp)).re := by
  set v := (hX.eigenvectorBasis j).ofLp
  have hv : star v ⬝ᵥ v = 1 := by
    have hn := (hX.eigenvectorBasis).orthonormal.1 j
    have : inner ℂ (hX.eigenvectorBasis j) (hX.eigenvectorBasis j) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hn]; simp
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
    exact this
  rw [hX.mulVec_eigenvectorBasis j, dotProduct_smul, hv]
  simp

lemma posPart_zero {M : Matrix I I ℂ} (hM : M.IsHermitian) (h : ∀ j, hM.eigenvalues j ≤ 0) :
    cfc (fun x : ℝ => max x 0) M = 0 := by
  rw [cfc_congr (g := fun _ => 0) (fun x hx => by
    rw [hM.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨j, rfl⟩ := hx
    simp [h j]), cfc_const_zero]

lemma posPart_self {M : Matrix I I ℂ} (hM : M.PosSemidef) : cfc (fun x : ℝ => max x 0) M = M := by
  rw [cfc_congr (g := fun x => x) (fun x hx => by
    rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨j, rfl⟩ := hx
    simp [hM.eigenvalues_nonneg j]), cfc_id' ℝ M hM.isHermitian.isSelfAdjoint]

lemma exists_Lambda (ρ N : Matrix I I ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (hN : N.PosSemidef)
    (hker : ∀ v, N *ᵥ v = 0 → ρ *ᵥ v = 0) :
    ∃ Λ : ℝ, 0 < Λ ∧ cfc (fun x : ℝ => max x 0) (ρ - (Λ : ℂ) • N) = 0 := by
  have hNh := hN.isHermitian
  have hρh := hρ.isHermitian
  set μ := hNh.eigenvalues
  set χ : ℝ → ℝ := fun x => if x = 0 then 0 else 1
  set P := cfc χ N
  set Λ : ℝ := 1 + ∑ j, (if μ j = 0 then 0 else 1 / μ j)
  have hterm : ∀ j, 0 ≤ (if μ j = 0 then 0 else 1 / μ j) := by
    intro j; split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one (hN.eigenvalues_nonneg j)
  have hΛ : 0 < Λ := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hterm j
    linarith
  have hΛμ : ∀ j, μ j ≠ 0 → 1 ≤ Λ * μ j := by
    intro j hj
    have hμp : 0 < μ j := (hN.eigenvalues_nonneg j).lt_of_ne (Ne.symm hj)
    have h1 : 1 / μ j ≤ Λ := by
      have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i) (Finset.mem_univ j)
      rw [if_neg hj] at this
      linarith
    rw [div_le_iff₀ hμp] at h1
    linarith
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ N) := fun f => N.finite_real_spectrum.continuousOn _
  -- N (1 - P) = 0
  have hNP : N * (1 - P) = 0 := by
    have e1 : (1 : Matrix I I ℂ) - P = cfc (fun x => 1 - χ x) N := by
      rw [cfc_sub _ _ N (hc _) (hc _), cfc_const_one ℝ N hNh.isSelfAdjoint]
    have e2 := cfc_mul (fun x : ℝ => x) (fun x => 1 - χ x) N (hc _) (hc _)
    rw [cfc_id' ℝ N hNh.isSelfAdjoint] at e2
    rw [e1, ← e2]
    rw [cfc_congr (g := fun _ => 0) (fun x _ => by simp only [χ]; split_ifs with h <;> simp [h]), cfc_const_zero]
  -- ρ (1 - P) = 0
  have hρP : ρ * (1 - P) = 0 := by
    ext i k
    have hcol : N *ᵥ ((1 - P) *ᵥ Pi.single k 1) = 0 := by rw [mulVec_mulVec, hNP, zero_mulVec]
    have := congrFun (hker _ hcol) i
    rw [mulVec_mulVec, mulVec_single_one] at this
    simpa using this
  have hPh : Pᴴ = P := (cfc_predicate χ N : IsSelfAdjoint P)
  have hρ1 : ρ = ρ * P := by
    have h := hρP
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  have hρ2 : ρ = P * ρ := by
    have := congrArg conjTranspose hρ1
    rw [conjTranspose_mul, hPh, hρh.eq] at this
    exact this
  have hPP : P * P = P := by
    rw [← cfc_mul _ _ N (hc _) (hc _)]
    congr 1; funext x; simp only [χ]; split_ifs <;> simp
  -- quadratic form bound
  have hq : ∀ x : I → ℂ, (star x ⬝ᵥ (ρ *ᵥ x)).re ≤ Λ * (star x ⬝ᵥ (N *ᵥ x)).re := by
    intro x
    have s1 : star x ⬝ᵥ (ρ *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (ρ *ᵥ (P *ᵥ x)) := by
      conv_lhs => rw [hρ2, hρ1]
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, hPh]
    have s2 : star (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = star x ⬝ᵥ (P *ᵥ x) := by
      rw [star_mulVec, hPh, ← dotProduct_mulVec, mulVec_mulVec, hPP]
    have s3 : (star x ⬝ᵥ (P *ᵥ x)).re - Λ * (star x ⬝ᵥ (N *ᵥ x)).re =
        (star x ⬝ᵥ (cfc (fun t => χ t - Λ * t) N *ᵥ x)).re := by
      rw [cfc_sub _ _ N (hc _) (hc _), cfc_const_mul Λ (fun t : ℝ => t) N (hc _), cfc_id' ℝ N hNh.isSelfAdjoint,
        sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec, dotProduct_smul]
      simp
      rfl
    have s4 : (star x ⬝ᵥ (cfc (fun t => χ t - Λ * t) N *ᵥ x)).re ≤ 0 := by
      rw [qf hNh]
      refine Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
      simp only [χ]
      split_ifs with h
      · rw [h]; simp
      · linarith [hΛμ j h]
    have s5 := density_le hρ htr (P *ᵥ x)
    rw [s1]; rw [s2] at s5
    linarith
  refine ⟨Λ, hΛ, ?_⟩
  have hM : (ρ - (Λ : ℂ) • N).IsHermitian := by
    simp [IsHermitian, conjTranspose_sub, conjTranspose_smul, hρh.eq, hNh.eq]
  apply posPart_zero hM
  intro j
  rw [eig_eq hM j, sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec, dotProduct_smul]
  have := hq (hM.eigenvectorBasis j).ofLp
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  linarith

end X5RT

open Matrix Filter Set
open scoped ComplexOrder Topology Matrix.Norms.L2Operator

namespace X5RT
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma ker_lift (ρ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.PosSemidef) (σ : Matrix B B ℂ)
    (h : supportedBy (traceLeft ρ) σ) (v : A × B → ℂ)
    (hv : identityTensorReference (A := A) σ *ᵥ v = 0) : ρ *ᵥ v = 0 := by
  have hva : ∀ a, σ *ᵥ (fun b => v (a, b)) = 0 := by
    intro a; funext b
    have := congrFun hv (a, b)
    simp only [identityTensorReference, Matrix.kronecker, mulVec, dotProduct, kroneckerMap_apply, one_apply,
      Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Pi.zero_apply] at this ⊢
    simpa [Finset.sum_ite_irrel] using this
  have hBa : ∀ a, traceLeft ρ *ᵥ (fun b => v (a, b)) = 0 := by
    intro a
    have := h (show (fun b => v (a, b)) ∈ LinearMap.ker σ.mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply]; exact hva a)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  let u : A → (B → ℂ) → (A × B → ℂ) := fun a0 w p => if p.1 = a0 then w p.2 else 0
  have hsum : ∀ w : B → ℂ, ∑ a0, star (u a0 w) ⬝ᵥ (ρ *ᵥ u a0 w) = star w ⬝ᵥ (traceLeft ρ *ᵥ w) := by
    intro w
    simp only [u, dotProduct, mulVec, traceLeft, of_apply, Fintype.sum_prod_type, Pi.star_apply,
      apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.mul_sum, Finset.sum_mul]
    simp [Finset.sum_ite_irrel]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
  have hzero : ∀ a a0, ρ *ᵥ u a0 (fun b => v (a, b)) = 0 := by
    intro a a0
    have h0 := hsum (fun b => v (a, b))
    rw [hBa a, dotProduct_zero] at h0
    have hnn : ∀ a1, 0 ≤ star (u a1 (fun b => v (a, b))) ⬝ᵥ (ρ *ᵥ u a1 (fun b => v (a, b))) :=
      fun a1 => hρ.dotProduct_mulVec_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a1 _ => hnn a1)).1 h0 a0 (Finset.mem_univ _)
    exact (hρ.dotProduct_mulVec_zero_iff _).1 this
  have hdec : v = ∑ a, u a (fun b => v (a, b)) := by
    funext p
    simp only [u, Finset.sum_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hdec, mulVec_sum]
  exact Finset.sum_eq_zero fun a _ => hzero a a

lemma herm_sub {n : Type*} [Fintype n] (R N : Matrix n n ℂ) (hR : R.IsHermitian) (hN : N.IsHermitian) (t : ℝ) :
    (R - (t : ℂ) • N).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hR.eq, hN.eq]

lemma pt_cont {n : Type*} [Fintype n] [DecidableEq n] (R N : Matrix n n ℂ) (hR : R.IsHermitian)
    (hN : N.IsHermitian) :
    Continuous (fun t : ℝ => (cfc (fun x : ℝ => max x 0) (R - (t : ℂ) • N)).trace.re) := by
  have := Continuous.cfc_of_mem_nhdsSet (𝕜 := ℝ) (A := Matrix n n ℂ) (X := ℝ) (s := Set.univ)
    (p := IsSelfAdjoint) (fun x : ℝ => max x 0) (a := fun t : ℝ => R - (t : ℂ) • N) Filter.univ_mem
    (by fun_prop) (fun t : ℝ => (herm_sub R N hR hN t).isSelfAdjoint) (by fun_prop)
  exact Complex.continuous_re.comp (Continuous.matrix_trace this)

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : supportedBy (traceLeft rho) sigma)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ lambda : ℝ, 0 < lambda ∧ thresholdRadius rho sigma lambda = epsilon ∧
      ((-Real.logb 2 lambda : ℝ) : EReal) ≤ sineSmoothFixedMin rho sigma epsilon := by
  set N := identityTensorReference (A := A) sigma
  have hNpsd : N.PosSemidef := by
    simp only [N, identityTensorReference, Matrix.kronecker]
    exact Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hsigma.1
  obtain ⟨Λ, hΛ, hzero⟩ := exists_Lambda rho N hrho.1 hrho.2 hNpsd
    (fun v hv => ker_lift rho hrho.1 sigma hsupport v hv)
  set f := fun t : ℝ => thresholdRadius rho sigma t
  have hfc : Continuous f := by
    have := pt_cont rho N hrho.1.isHermitian hNpsd.isHermitian
    exact Real.continuous_sqrt.comp (continuous_const.mul this)
  have hfΛ : f Λ = 0 := by
    simp only [f, thresholdRadius]
    rw [hzero]; simp
  have hf0 : f 0 = Real.sqrt 2 := by
    simp only [f, thresholdRadius]
    rw [Complex.ofReal_zero, zero_smul, sub_zero, posPart_self hrho.1, hrho.2]; simp
  have hgt : ∀ᶠ t in 𝓝 (0 : ℝ), 1 < f t := by
    refine hfc.continuousAt.eventually (lt_mem_nhds ?_)
    rw [hf0, Real.lt_sqrt zero_le_one]; norm_num
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hgt
  set δ := min (r / 2) Λ
  have hδ : 0 < δ := lt_min (by linarith) hΛ
  have hδΛ : δ ≤ Λ := min_le_right _ _
  have hfδ : 1 < f δ := hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
  obtain ⟨l, hl, hfl⟩ := intermediate_value_Icc' hδΛ hfc.continuousOn
    (show epsilon ∈ Icc (f Λ) (f δ) from ⟨hfΛ ▸ hepsilon0, by linarith⟩)
  have hlpos : 0 < l := lt_of_lt_of_le hδ hl.1
  refine ⟨l, hlpos, hfl, ?_⟩
  have := positivePartSmoothing rho sigma hrho hsigma l hlpos
  rw [show thresholdRadius rho sigma l = epsilon from hfl] at this
  exact this

end X5RT

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : supportedBy (traceLeft rho) sigma)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ lambda : ℝ, 0 < lambda ∧ thresholdRadius rho sigma lambda = epsilon ∧
      ((-Real.logb 2 lambda : ℝ) : EReal) ≤ sineSmoothFixedMin rho sigma epsilon :=
  X5RT.main rho sigma hrho hsigma hsupport epsilon hepsilon0 hepsilon1

end
