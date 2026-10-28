-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.alphaIsometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:13:13.316597+00:00
-- url     : https://prove2.me/submissions/198367e3-5491-4024-9a06-a07ff0633cea

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
open Matrix

section X5mod_AI_Base

/-- conjugation by an isometry as a non-unital star algebra hom -/
noncomputable def x5ai_conjHom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix n n ℂ where
  toFun X := W * X * Wᴴ
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

theorem x5ai_finite_cont {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ M) := by
  have : (quasispectrum ℝ M).Finite := by
    rw [quasispectrum_eq_spectrum_union_zero]
    exact (M.finite_real_spectrum).union (Set.finite_singleton 0)
  exact this.continuousOn _

theorem x5ai_finite_cont' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  M.finite_real_spectrum.continuousOn _

theorem x5ai_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (W * M * Wᴴ) = W * cfc f M * Wᴴ := by
  have hWM : (W * M * Wᴴ).IsHermitian := by
    simp [IsHermitian, conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hc : Continuous (x5ai_conjHom W hW) := by
    change Continuous fun X : Matrix m m ℂ => W * X * Wᴴ; fun_prop
  have h := NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_conjHom W hW) f M (x5ai_finite_cont M f) hf hc hM.isSelfAdjoint hWM.isSelfAdjoint
  have h2 : W * cfcₙ f M * Wᴴ = cfcₙ f (W * M * Wᴴ) := h
  have e1 : cfcₙ f M = cfc f M := cfcₙ_eq_cfc (x5ai_finite_cont M f) hf
  have e2 : cfcₙ f (W * M * Wᴴ) = cfc f (W * M * Wᴴ) := cfcₙ_eq_cfc (x5ai_finite_cont (W * M * Wᴴ) f) hf
  rw [← e1, ← e2, h2]

/-- identity tensor X as a star algebra hom -/
noncomputable def x5ai_kronHom (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (C × n) (C × n) ℂ where
  toFun X := Matrix.kronecker (1 : Matrix C C ℂ) X
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    have := Matrix.mul_kronecker_mul (1 : Matrix C C ℂ) (1 : Matrix C C ℂ) X Y
    rw [Matrix.mul_one] at this
    exact this
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.kronecker_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

theorem x5ai_kron (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.kronecker (1 : Matrix C C ℂ) M) = Matrix.kronecker (1 : Matrix C C ℂ) (cfc f M) := by
  have hK : (Matrix.kronecker (1 : Matrix C C ℂ) M).IsHermitian := by
    simp [IsHermitian, Matrix.conjTranspose_kronecker, hM.eq]
  have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_kronHom C (n := n)) f M (x5ai_finite_cont' M f)
    (by
      change Continuous fun X : Matrix n n ℂ => Matrix.kronecker (1 : Matrix C C ℂ) X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _)))
    hM.isSelfAdjoint hK.isSelfAdjoint
  exact h.symm

end X5mod_AI_Base

open Matrix
open scoped ENNReal ComplexOrder

namespace X5AI
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem iso_kron (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) :
    (Matrix.kronecker U V)ᴴ * Matrix.kronecker U V = 1 := by
  unfold Matrix.kronecker
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hV, one_kronecker_one]

theorem cfc_ref (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (g : ℝ → ℝ) (hg : g 0 = 0) :
    (Matrix.kronecker U V)ᴴ * cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ)) *
      Matrix.kronecker U V = cfc g (identityTensorReference (A := A) sigma) := by
  unfold identityTensorReference
  rw [x5ai_kron, x5ai_conj V hV sigma hs g hg, x5ai_kron _ _ hs]
  unfold Matrix.kronecker
  rw [conjTranspose_kronecker,
    ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, hU]
  · congr 1
    calc Vᴴ * (V * cfc g sigma * Vᴴ) * V = (Vᴴ * V) * cfc g sigma * (Vᴴ * V) := by
          simp [Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp
  · simp [IsHermitian, conjTranspose_mul, hs.eq, Matrix.mul_assoc]

theorem trace_eq (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (hr : rho.IsHermitian)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (f g : ℝ → ℝ) (hf : f 0 = 0) (hg : g 0 = 0) :
    (cfc f (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) *
      cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))).trace =
    (cfc f rho * cfc g (identityTensorReference (A := A) sigma)).trace := by
  rw [x5ai_conj _ (iso_kron U V hU hV) rho hr f hf, ← cfc_ref U V hU hV sigma hs g hg]
  set W := Matrix.kronecker U V
  set G := cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

theorem intertw (U : Matrix C A ℂ) (V : Matrix D B ℂ) (hV : V.conjTranspose * V = 1)
    (sigma : Matrix B B ℂ) :
    identityTensorReference (A := C) (V * sigma * Vᴴ) * Matrix.kronecker U V =
      Matrix.kronecker U V * identityTensorReference (A := A) sigma := by
  unfold identityTensorReference Matrix.kronecker
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hV,
    Matrix.mul_one]

theorem supp_iff (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) :
    supportedBy (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ)
        (identityTensorReference (A := C) (V * sigma * Vᴴ)) ↔
      supportedBy rho (identityTensorReference (A := A) sigma) := by
  have hW := iso_kron U V hU hV
  have hI := intertw U V hV sigma
  set W := Matrix.kronecker U V
  set N' := identityTensorReference (A := C) (V * sigma * Vᴴ)
  set N := identityTensorReference (A := A) sigma
  have hNh : Nᴴ = N := by
    simp [N, identityTensorReference, Matrix.kronecker, conjTranspose_kronecker, hs.eq]
  have hN'h : N'ᴴ = N' := by
    simp [N', identityTensorReference, Matrix.kronecker, conjTranspose_kronecker, conjTranspose_mul,
      hs.eq, Matrix.mul_assoc]
  have hI' : Wᴴ * N' = N * Wᴴ := by
    have := congrArg conjTranspose hI
    rw [conjTranspose_mul, conjTranspose_mul, hNh, hN'h] at this
    exact this
  unfold supportedBy
  constructor
  · intro h x hx
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    have h1 : N' *ᵥ (W *ᵥ x) = 0 := by rw [mulVec_mulVec, hI, ← mulVec_mulVec, hx, mulVec_zero]
    have h2 := h (show W *ᵥ x ∈ _ from by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1)
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hW, Matrix.mul_one] at h2
    have h3 := congrArg (Wᴴ *ᵥ ·) h2
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hW, Matrix.one_mul, mulVec_zero] at h3
    exact h3
  · intro h y hy
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy ⊢
    have h1 : N *ᵥ (Wᴴ *ᵥ y) = 0 := by rw [mulVec_mulVec, ← hI', ← mulVec_mulVec, hy, mulVec_zero]
    have h2 := h (show Wᴴ *ᵥ y ∈ _ from by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1)
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    rw [← mulVec_mulVec, ← mulVec_mulVec, h2, mulVec_zero]

theorem vn_eq (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (hr : rho.IsHermitian) :
    vnEntropy (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) = vnEntropy rho := by
  unfold vnEntropy
  rw [x5ai_conj _ (iso_kron U V hU hV) rho hr _ (by simp), Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    iso_kron U V hU hV, Matrix.one_mul]

theorem trace_eq0 (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (g : ℝ → ℝ) (hg : g 0 = 0) :
    ((Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) *
      cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))).trace =
    (rho * cfc g (identityTensorReference (A := A) sigma)).trace := by
  rw [← cfc_ref U V hU hV sigma hs g hg]
  set W := Matrix.kronecker U V
  set G := cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

theorem fa_eq (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (hr : rho.IsHermitian)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (t : ℝ) (ht : 0 < t) :
    finiteAlpha (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) (V * sigma * Vᴴ) t =
      finiteAlpha rho sigma t := by
  unfold finiteAlpha fixedVonNeumann
  have hsupp := supp_iff U V hU hV rho sigma hs
  by_cases hS : supportedBy rho (identityTensorReference (A := A) sigma)
  · have hS' := hsupp.2 hS
    simp only [hS, hS', not_true_eq_false, and_false, if_false, if_true]
    simp only [vn_eq U V hU hV rho hr,
      trace_eq0 U V hU hV rho sigma hs (fun x : ℝ => Real.logb 2 x) (by simp),
      trace_eq U V hU hV rho hr sigma hs (fun x : ℝ => x ^ t) (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t))
        (Real.zero_rpow ht.ne') (by simp)]

  · have hS' : ¬ _ := fun h => hS (hsupp.1 h)
    simp only [hS, hS', not_false_eq_true, and_true, if_false, if_true]
    simp only [vn_eq U V hU hV rho hr,
      trace_eq0 U V hU hV rho sigma hs (fun x : ℝ => Real.logb 2 x) (by simp),
      trace_eq U V hU hV rho hr sigma hs (fun x : ℝ => x ^ t) (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t))
        (Real.zero_rpow ht.ne') (by simp)]

end X5AI

theorem x5ai_main {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) (alpha : ℝ≥0∞) :
    QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy rho sigma alpha =
      QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy
        (Matrix.kronecker U V * rho * (Matrix.kronecker U V).conjTranspose)
        (V * sigma * V.conjTranspose) alpha := by
  have hr := hrho.1.isHermitian
  have hs := hsigma.1.isHermitian
  have key := fun t (ht : (0 : ℝ) < t) => X5AI.fa_eq U V hU hV rho hr sigma hs t ht
  unfold QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy
  split_ifs with h0 h1
  · congr 1; ext h
    exact ⟨fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht).symm⟩, fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht)⟩⟩
  · congr 1; ext h
    exact ⟨fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht).symm⟩, fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht)⟩⟩
  · exact (key _ (ENNReal.toReal_pos h0 h1)).symm

theorem solution {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) (alpha : ℝ≥0∞) :
    QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy rho sigma alpha =
      QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy
        (Matrix.kronecker U V * rho * (Matrix.kronecker U V).conjTranspose)
        (V * sigma * V.conjTranspose) alpha :=
  x5ai_main rho sigma hrho hsigma U V hU hV alpha
