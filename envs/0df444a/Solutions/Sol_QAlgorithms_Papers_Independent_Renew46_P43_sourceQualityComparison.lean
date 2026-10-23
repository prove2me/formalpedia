-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.sourceQualityComparison
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T20:32:25.125818+00:00
-- url     : https://prove2.me/submissions/d35fa2f7-6c19-4bf1-a93f-58ea035d2d5c

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace SrcQuality

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix QAlgorithms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_conj_unitary (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * (star U : Matrix ι ι ℂ)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

lemma trace_cfc_herm {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (g : ℝ → ℝ) :
    (cfc g M).trace = ∑ i, ((g (hM.eigenvalues i) : ℝ) : ℂ) := by
  rw [hM.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_conj_unitary,
    Matrix.trace_diagonal]
  rfl

lemma traceNorm_herm {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    traceNorm M = ∑ i, |hM.eigenvalues i| := by
  unfold traceNorm
  have h1 : Mᴴ * M = cfc (fun x : ℝ => x * x) M := by
    rw [hM.cfc_eq, Matrix.IsHermitian.cfc, hM.eq]
    conv_lhs => rw [hM.spectral_theorem]
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    simp
  rw [h1, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) M, trace_cfc_herm hM]
  simp only [Function.comp_apply, Real.sqrt_mul_self_eq_abs]
  rw [Complex.re_sum]
  simp

lemma sqrt_mul_sqrt_psd {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
  have hH := hρ.isHermitian
  rw [hH.cfc_eq, Matrix.IsHermitian.cfc, ← map_mul, Matrix.diagonal_mul_diagonal]
  conv_rhs => rw [hH.spectral_theorem]
  congr 2
  funext i
  simp only [Function.comp_apply]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hρ.eigenvalues_nonneg i)]

lemma sqrt_herm (ρ : Matrix ι ι ℂ) : (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ :=
  (cfc_predicate (p := IsSelfAdjoint) Real.sqrt ρ).star_eq


lemma cs_sum {κ : Type*} (s : Finset κ) (c d : κ → ℂ) :
    ‖∑ j ∈ s, c j * d j‖ ^ 2 ≤ (∑ j ∈ s, ‖c j‖ ^ 2) * (∑ j ∈ s, ‖d j‖ ^ 2) := by
  have h1 : ‖∑ j ∈ s, c j * d j‖ ≤ ∑ j ∈ s, ‖c j‖ * ‖d j‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖c j‖) (fun j => ‖d j‖)
  have h0 : 0 ≤ ‖∑ j ∈ s, c j * d j‖ := norm_nonneg _
  calc _ ≤ (∑ j ∈ s, ‖c j‖ * ‖d j‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

lemma mul_star_self' (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma half_abs_sum (lam : ι → ℝ) (h0 : ∑ i, lam i = 0) :
    (∑ i, |lam i|) / 2 = ∑ i ∈ Finset.univ.filter (fun i => lam i < 0), -lam i := by
  rw [Finset.sum_filter]
  have : ∑ i, |lam i| = ∑ i, (|lam i| - lam i) := by
    rw [Finset.sum_sub_distrib, h0, sub_zero]
  rw [this, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

lemma core (S : Matrix ι ι ℂ) (hS : S.PosSemidef) (hTr : S.trace = 1) (a : ι → ℂ)
    (ha : ∑ i, ‖a i‖ ^ 2 = 1) (lam : ι → ℝ)
    (hD : S = diagonal (fun i => (lam i : ℂ)) + vecMulVec a (star a)) :
    1 - (S * vecMulVec a (star a)).trace.re ≤ (∑ i, |lam i|) / 2 ∧
    ((∑ i, |lam i|) / 2) ^ 2 ≤ 1 - (S * vecMulVec a (star a)).trace.re := by
  set s : ι → ℝ := fun i => ‖a i‖ ^ 2 with hs_def
  have hdiag : ∀ i, (S i i).re = lam i + s i := by
    intro i
    rw [hD]
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, vecMulVec_apply, Pi.star_apply,
      mul_star_self', Complex.add_re, Complex.ofReal_re, hs_def]
  have hsumS : ∑ i, (S i i).re = 1 := by
    have := congrArg Complex.re hTr
    rw [Matrix.trace, Complex.re_sum] at this
    simpa using this
  have hlam0 : ∑ i, lam i = 0 := by
    have : ∑ i, (S i i).re = ∑ i, lam i + ∑ i, s i := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => hdiag i)
    have ha' : ∑ i, s i = 1 := ha
    linarith
  have hs_nn : ∀ i, 0 ≤ s i := fun i => by positivity
  have hs_le : ∀ i, s i ≤ 1 := fun i => by
    have ha' : ∑ i, s i = 1 := ha
    rw [← ha']; exact Finset.single_le_sum (fun j _ => hs_nn j) (Finset.mem_univ i)
  -- formula for f via hD
  have hf1 : (S * vecMulVec a (star a)).trace.re = ∑ i, lam i * s i + 1 := by
    have hss : (star a) ⬝ᵥ a = 1 := by
      simp only [dotProduct, Pi.star_apply]
      have : ∀ i, star (a i) * a i = ((s i : ℝ) : ℂ) := fun i => by
        rw [mul_comm, mul_star_self']
      simp only [this]
      rw [← Complex.ofReal_sum]
      have ha' : ∑ i, s i = 1 := ha
      rw [ha']; simp
    rw [hD, Matrix.add_mul, Matrix.trace_add, vecMulVec_mul_vecMulVec, hss, one_smul,
      Matrix.trace_vecMulVec, Complex.add_re]
    have h2 : (a ⬝ᵥ star a).re = 1 := by
      rw [dotProduct_comm, hss]; simp
    rw [h2, Matrix.trace, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, Matrix.diagonal_mul, vecMulVec_apply, Pi.star_apply, mul_star_self', ← Complex.ofReal_mul,
      Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · -- part A1
    rw [hf1]
    have key : ∀ i, -(lam i * s i) ≤ (|lam i| - lam i) / 2 := by
      intro i
      rcases le_or_gt 0 (lam i) with h | h
      · rw [abs_of_nonneg h]; nlinarith [hs_nn i]
      · rw [abs_of_neg h]; nlinarith [hs_le i]
    have : ∑ i, -(lam i * s i) ≤ ∑ i, (|lam i| - lam i) / 2 := Finset.sum_le_sum (fun i _ => key i)
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hlam0, Finset.sum_neg_distrib] at this
    linarith
  · rw [half_abs_sum lam hlam0]
    obtain ⟨m, u, hu⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hS
    set N := Finset.univ.filter (fun i => lam i < 0) with hN
    set w : ι → ℝ := fun j => ∑ k, ‖u k j‖ ^ 2 with hw_def
    have hSw : ∀ j, (S j j).re = w j := by
      intro j
      rw [hu, Matrix.sum_apply, Complex.re_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [vecMulVec_apply, Pi.star_apply, mul_star_self', Complex.ofReal_re]
    have hlamw : ∀ j, -lam j = s j - w j := by
      intro j; have := hdiag j; rw [hSw] at this; linarith
    set q := ∑ j ∈ N, s j with hq_def
    set t := ∑ j ∈ N, w j with ht_def
    have hT : ∑ i ∈ N, -lam i = q - t := by
      rw [Finset.sum_congr rfl (fun j _ => hlamw j), Finset.sum_sub_distrib]
    have hwsum : ∑ j, w j = 1 := by
      rw [← hsumS]; exact Finset.sum_congr rfl (fun j _ => (hSw j).symm)
    have hssum : ∑ j, s j = 1 := ha
    have hw_nn : ∀ j, 0 ≤ w j := fun j => Finset.sum_nonneg (fun k _ => by positivity)
    have hqc : ∑ j ∈ Nᶜ, s j = 1 - q := by
      rw [← hssum, ← Finset.sum_add_sum_compl N s]; ring
    have htc : ∑ j ∈ Nᶜ, w j = 1 - t := by
      rw [← hwsum, ← Finset.sum_add_sum_compl N w]; ring
    have hq0 : 0 ≤ q := Finset.sum_nonneg (fun j _ => hs_nn j)
    have ht0 : 0 ≤ t := Finset.sum_nonneg (fun j _ => hw_nn j)
    have hq1 : 0 ≤ 1 - q := hqc ▸ Finset.sum_nonneg (fun j _ => hs_nn j)
    have ht1 : 0 ≤ 1 - t := htc ▸ Finset.sum_nonneg (fun j _ => hw_nn j)
    set x : Fin m → ℂ := fun k => ∑ j ∈ N, star (u k j) * a j with hx_def
    set y : Fin m → ℂ := fun k => ∑ j ∈ Nᶜ, star (u k j) * a j with hy_def
    have hf2 : (S * vecMulVec a (star a)).trace.re = ∑ k, ‖x k + y k‖ ^ 2 := by
      have hxy : ∀ k, x k + y k = ∑ j, star (u k j) * a j := fun k =>
        Finset.sum_add_sum_compl N _
      simp_rw [hxy]
      rw [hu, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul]
      have h3 : u k ⬝ᵥ star a = star (star (u k) ⬝ᵥ a) := by
        simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      rw [h3, mul_star_self', Complex.ofReal_re]
      rfl
    set X := ∑ k, ‖x k‖ ^ 2 with hX_def
    set Y := ∑ k, ‖y k‖ ^ 2 with hY_def
    set Z := ∑ k, ‖x k‖ * ‖y k‖ with hZ_def
    have hfle : ∑ k, ‖x k + y k‖ ^ 2 ≤ X + Y + 2 * Z := by
      have e : X + Y + 2 * Z = ∑ k, (‖x k‖ + ‖y k‖) ^ 2 := by
        simp only [hX_def, hY_def, hZ_def, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [e]
      exact Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
    have hZ2 : Z ^ 2 ≤ X * Y := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hX : X ≤ t * q := by
      calc X ≤ ∑ k, (∑ j ∈ N, ‖star (u k j)‖ ^ 2) * (∑ j ∈ N, ‖a j‖ ^ 2) :=
            Finset.sum_le_sum (fun k _ => cs_sum _ _ _)
        _ = t * q := by
          rw [← Finset.sum_mul, Finset.sum_comm]
          simp only [norm_star]
          rfl
    have hY : Y ≤ (1 - t) * (1 - q) := by
      calc Y ≤ ∑ k, (∑ j ∈ Nᶜ, ‖star (u k j)‖ ^ 2) * (∑ j ∈ Nᶜ, ‖a j‖ ^ 2) :=
            Finset.sum_le_sum (fun k _ => cs_sum _ _ _)
        _ = (1 - t) * (1 - q) := by
          rw [← Finset.sum_mul, Finset.sum_comm, ← htc, ← hqc]
          simp only [norm_star]
          rfl
    have hX0 : 0 ≤ X := Finset.sum_nonneg (fun k _ => by positivity)
    have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun k _ => by positivity)
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun k _ => by positivity)
    have hXY : X * Y ≤ (t * q) * ((1 - t) * (1 - q)) :=
      mul_le_mul hX hY hY0 (mul_nonneg ht0 hq0)
    have hA0 : 0 ≤ q * (1 - q) := mul_nonneg hq0 hq1
    have hB0 : 0 ≤ t * (1 - t) := mul_nonneg ht0 ht1
    have h2Z : 2 * Z ≤ q * (1 - q) + t * (1 - t) := by
      nlinarith [sq_nonneg (q * (1 - q) - t * (1 - t))]
    rw [hT, hf2]
    nlinarith

lemma perword (σ : Matrix ι ι ℂ) (hσ : IsDensityMatrix σ) (v : ι → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    1 - effectProb σ (vecMulVec v (star v)) ≤ traceDistance σ (vecMulVec v (star v)) ∧
    (traceDistance σ (vecMulVec v (star v))) ^ 2 ≤ 1 - effectProb σ (vecMulVec v (star v)) := by
  set P := vecMulVec v (star v) with hP
  have hPH : P.IsHermitian := (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
  have hM : (σ - P).IsHermitian := hσ.1.isHermitian.sub hPH
  set U := hM.eigenvectorUnitary with hU
  set lam := hM.eigenvalues with hlam
  set Um : Matrix ι ι ℂ := (U : Matrix ι ι ℂ) with hUm
  have hsU : star Um * Um = 1 := Unitary.coe_star_mul_self U
  have hUs : Um * star Um = 1 := Unitary.coe_mul_star_self U
  set S := star Um * σ * Um with hS_def
  set a := star Um *ᵥ v with ha_def
  have hPa : star Um * P * Um = vecMulVec a (star a) := by
    rw [hP, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ha_def, Matrix.star_mulVec,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hdiag : star Um * (σ - P) * Um = diagonal (fun i => (lam i : ℂ)) := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at this
    exact this
  have hD : S = diagonal (fun i => (lam i : ℂ)) + vecMulVec a (star a) := by
    rw [← hdiag, ← hPa, Matrix.mul_sub, Matrix.sub_mul, hS_def]
    abel
  have htr : ∀ X : Matrix ι ι ℂ, (star Um * X * Um).trace = X.trace := by
    intro X
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUs, Matrix.one_mul]
  have hTr : S.trace = 1 := by rw [hS_def, htr]; exact hσ.2
  have hPtr : P.trace = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hP, Matrix.trace_vecMulVec, dotProduct, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Pi.star_apply, mul_star_self'])
  have ha : ∑ i, ‖a i‖ ^ 2 = 1 := by
    have h1 : (vecMulVec a (star a)).trace = ((∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.trace_vecMulVec, dotProduct, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [Pi.star_apply, mul_star_self'])
    rw [← hPa, htr, hPtr, hv] at h1
    exact_mod_cast h1.symm
  have hSP : (S * vecMulVec a (star a)).trace = (σ * P).trace := by
    rw [← hPa, hS_def]
    have : star Um * σ * Um * (star Um * P * Um) = star Um * (σ * P) * Um := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Um (star Um), hUs, Matrix.one_mul]
    rw [this, htr]
  obtain ⟨h1, h2⟩ := core S (hσ.1.conjTranspose_mul_mul_same Um) hTr a ha lam hD
  have hTD : traceDistance σ P = (∑ i, |lam i|) / 2 := by
    unfold traceDistance
    rw [traceNorm_herm hM]
    ring
  have hEP : effectProb σ P = (S * vecMulVec a (star a)).trace.re := by
    unfold effectProb; rw [hSP]
  rw [hTD, hEP]
  exact ⟨h1, h2⟩

lemma jensen_sq {κ : Type*} (s : Finset κ) (p r : κ → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∑ i ∈ s, p i = 1) : (∑ i ∈ s, p i * r i) ^ 2 ≤ ∑ i ∈ s, p i * r i ^ 2 := by
  have := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (r := fun i => p i * r i)
    (f := p) (g := fun i => p i * r i ^ 2) hp
    (fun i hi => mul_nonneg (hp i hi) (sq_nonneg _)) (fun i _ => by ring_nf; exact le_refl _)
  rw [h1, one_mul] at this
  exact this

lemma jensen_cplx {κ : Type*} (s : Finset κ) (p : κ → ℝ) (z : κ → ℂ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∑ i ∈ s, p i = 1) : ‖∑ i ∈ s, (p i : ℂ) * z i‖ ^ 2 ≤ ∑ i ∈ s, p i * ‖z i‖ ^ 2 := by
  have hn : ‖∑ i ∈ s, (p i : ℂ) * z i‖ ≤ ∑ i ∈ s, p i * ‖z i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun i hi => ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp i hi)]
  calc _ ≤ (∑ i ∈ s, p i * ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ _ := jensen_sq s p _ hp h1

lemma conj_vecMulVec {κ : Type*} [Fintype κ] (A : Matrix κ ι ℂ) (x y : ι → ℂ) :
    A * vecMulVec x (star y) * Aᴴ = vecMulVec (A *ᵥ x) (star (A *ᵥ y)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma channel_density {κ : Type*} [Fintype κ] (Φ : Superop ι κ) (hΦ : IsChannel Φ)
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Φ ρ) := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  rw [hΦE, krausApply]
  refine ⟨Matrix.posSemidef_sum _ (fun j _ => hρ.1.mul_mul_conjTranspose_same (E j)), ?_⟩
  rw [Matrix.trace_sum]
  have : ∀ j, (E j * ρ * (E j)ᴴ).trace = (ρ * ((E j)ᴴ * E j)).trace := by
    intro j
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp_rw [this, ← Matrix.trace_sum, ← Matrix.mul_sum]
  unfold IsKrausFamily at hE
  rw [hE, Matrix.mul_one]
  exact hρ.2

open QAlgorithms.Papers.Independent.Renew46.P43 in
lemma fe_formula {J : Type*} [Fintype J] (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (A : J → Matrix ι ι ℂ) (T : Superop ι ι) (hT : ∀ X, T X = ∑ j, A j * X * (A j)ᴴ) :
    sourceFe ρ T = ∑ j, ‖(A j * ρ).trace‖ ^ 2 := by
  set s := cfc Real.sqrt ρ with hs
  have hsH : sᴴ = s := sqrt_herm ρ
  have hss : s * s = ρ := sqrt_mul_sqrt_psd hρ
  set B : J → Matrix ι ι ℂ := fun j => A j * s with hB
  set c : J → ℂ := fun j => ∑ p : ι × ι, B j p.2 p.1 * star (s p.2 p.1) with hc_def
  have hc : ∀ j, c j = (A j * ρ).trace := by
    intro j
    have : c j = (sᴴ * B j).trace := by
      simp only [hc_def, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun i _ => mul_comm _ _))
    rw [this, Matrix.trace_mul_comm, hsH, hB]
    simp only
    rw [Matrix.mul_assoc, hss]
  have hZ : ∀ p q : ι × ι, idTensorSuperop (R := ι) T (purification ρ) p q =
      ∑ j, B j p.2 p.1 * star (B j q.2 q.1) := by
    intro p q
    simp only [idTensorSuperop, Matrix.of_apply]
    have hblk : (Matrix.of fun i i' => purification ρ (p.1, i) (q.1, i')) =
        vecMulVec (fun i => s i p.1) (star (fun i => s i q.1)) := by
      ext i i'
      simp [purification, vecMulVec_apply, hs, Complex.star_def]
    rw [hblk, hT, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [conj_vecMulVec, vecMulVec_apply, Pi.star_apply]
    simp [hB, Matrix.mulVec, Matrix.mul_apply, dotProduct]
  have hΩ : ∀ q p : ι × ι, purification ρ q p = s q.2 q.1 * star (s p.2 p.1) := fun q p => rfl
  unfold sourceFe effectProb
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, hZ, hΩ]
  have key : ∑ p : ι × ι, ∑ q : ι × ι, (∑ j, B j p.2 p.1 * star (B j q.2 q.1)) *
      (s q.2 q.1 * star (s p.2 p.1)) = ∑ j, c j * star (c j) := by
    simp only [hc_def, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
    refine (Finset.sum_congr rfl (fun p _ => Finset.sum_comm)).trans (Finset.sum_comm.trans ?_)
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm.trans (Finset.sum_congr rfl
      (fun p _ => Finset.sum_congr rfl (fun q _ => by ring))))
  rw [key, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_star_self', Complex.ofReal_re, hc]

end SrcQuality

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open Matrix

/-- A chosen unit vector for each pure letter. -/
def srcVec {a d : ℕ} (S : PureSource a d) (x : Fin a) : Fin d → ℂ :=
  fun i => (Classical.choose (S.pure x)) i

lemma srcVec_letter {a d : ℕ} (S : PureSource a d) (x : Fin a) :
    S.letter x = vecMulVec (srcVec S x) (star (srcVec S x)) := by
  have h := (Classical.choose_spec (S.pure x)).2
  conv_lhs => rw [h]
  ext i j
  simp [pureDensity, vecMulVec_apply, srcVec, Complex.star_def]

lemma srcVec_norm {a d : ℕ} (S : PureSource a d) (x : Fin a) :
    ∑ i, ‖srcVec S x i‖ ^ 2 = 1 := by
  have h := (Classical.choose_spec (S.pure x)).1
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

/-- The product vector of a word. -/
def srcPhi {a d n : ℕ} (S : PureSource a d) (w : Fin n → Fin a) : (Fin n → Fin d) → ℂ :=
  fun x => ∏ i, srcVec S (w i) (x i)

lemma srcPhi_word {a d n : ℕ} (S : PureSource a d) (w : Fin n → Fin a) :
    S.word w = vecMulVec (srcPhi S w) (star (srcPhi S w)) := by
  ext x y
  simp only [PureSource.word, wordTensor, srcVec_letter, vecMulVec_apply, srcPhi, Pi.star_apply,
    star_prod, Finset.prod_mul_distrib]

lemma srcPhi_norm {a d n : ℕ} (S : PureSource a d) (w : Fin n → Fin a) :
    ∑ x, ‖srcPhi S w x‖ ^ 2 = 1 := by
  simp only [srcPhi, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i y => ‖srcVec S (w i) y‖ ^ 2)]
  simp [srcVec_norm]

lemma law_sum {a d : ℕ} (S : PureSource a d) : ∑ x, (S.law x).toReal = 1 := by
  have h := S.law.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ _), h]
  simp

lemma weight_nonneg {a d n : ℕ} (S : PureSource a d) (w : Fin n → Fin a) : 0 ≤ S.weight w :=
  Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)

lemma weight_sum {a d n : ℕ} (S : PureSource a d) :
    ∑ w : Fin n → Fin a, S.weight w = 1 := by
  unfold PureSource.weight
  rw [← Fintype.prod_sum (fun _ x => (S.law x).toReal)]
  simp [law_sum]

lemma copies_average {a d n : ℕ} (S : PureSource a d) :
    copies n S.average =
      ∑ w : Fin n → Fin a, ((S.weight w : ℝ) : ℂ) • vecMulVec (srcPhi S w) (star (srcPhi S w)) := by
  ext x y
  simp only [copies, Matrix.of_apply, PureSource.average, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← srcPhi_word]
  simp [PureSource.weight, PureSource.word, wordTensor, Finset.prod_mul_distrib,
    Complex.ofReal_prod]

theorem sourceQualityComparison {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n) :
    c.distortion^2 ≤ 1 - c.fidelity ∧ 1 - c.fidelity ≤ c.distortion ∧
    ∀ E, EncoderExtension c E →
      1 - c.fidelity ≤ 1 - sourceFe (copies n S.average) (c.decode ∘ E) := by
  have hpw : ∀ w, 1 - effectProb (c.decode (c.encode w)) (S.word w) ≤
      traceDistance (c.decode (c.encode w)) (S.word w) ∧
      (traceDistance (c.decode (c.encode w)) (S.word w)) ^ 2 ≤
        1 - effectProb (c.decode (c.encode w)) (S.word w) := by
    intro w
    rw [srcPhi_word]
    exact SrcQuality.perword _ (SrcQuality.channel_density _ c.decoder_channel _
      (c.encoded_state w)) _ (srcPhi_norm S w)
  have hp0 : ∀ w : Fin n → Fin a, 0 ≤ S.weight w := weight_nonneg S
  have hp1 : ∑ w : Fin n → Fin a, S.weight w = 1 := weight_sum S
  have hF : 1 - c.fidelity = ∑ w, S.weight w * (1 - effectProb (c.decode (c.encode w)) (S.word w)) := by
    unfold SourceCode.fidelity
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]
    unfold SourceCode.distortion
    calc _ ≤ ∑ w, S.weight w * (traceDistance (c.decode (c.encode w)) (S.word w)) ^ 2 :=
          SrcQuality.jensen_sq _ _ _ (fun w _ => hp0 w) hp1
      _ ≤ _ := Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hpw w).2 (hp0 w))
  · rw [hF]
    unfold SourceCode.distortion
    exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hpw w).1 (hp0 w))
  · intro E hE
    obtain ⟨m1, K, -, hK⟩ := c.decoder_channel
    obtain ⟨m2, L, -, hL⟩ := hE.1
    set A : Fin m1 × Fin m2 → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
      fun jl => K jl.1 * L jl.2 with hA
    have hT : ∀ X, (c.decode ∘ E) X = ∑ jl, A jl * X * (A jl)ᴴ := by
      intro X
      simp only [Function.comp_apply, hK, hL, krausApply, hA, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hρ : (copies n S.average).PosSemidef := by
      rw [copies_average]
      refine Matrix.posSemidef_sum _ (fun w _ => ?_)
      exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hp0 w)
    rw [SrcQuality.fe_formula _ hρ A _ hT]
    set z : Fin m1 × Fin m2 → (Fin n → Fin a) → ℂ :=
      fun jl w => (A jl *ᵥ srcPhi S w) ⬝ᵥ star (srcPhi S w) with hz
    have htr : ∀ jl, (A jl * copies n S.average).trace = ∑ w, ((S.weight w : ℝ) : ℂ) * z jl w := by
      intro jl
      rw [copies_average, Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
        smul_eq_mul]
    have hfw : ∀ w, effectProb (c.decode (c.encode w)) (S.word w) = ∑ jl, ‖z jl w‖ ^ 2 := by
      intro w
      rw [← hE.2 w]
      have := hT (S.word w)
      simp only [Function.comp_apply] at this
      rw [this, srcPhi_word]
      unfold effectProb
      rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun jl _ => ?_)
      rw [SrcQuality.conj_vecMulVec, vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec,
        dotProduct_smul, smul_eq_mul]
      have h3 : star (A jl *ᵥ srcPhi S w) ⬝ᵥ srcPhi S w = star (z jl w) := by
        simp only [hz, dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      rw [h3, mul_comm, SrcQuality.mul_star_self', Complex.ofReal_re]
    have hFid : c.fidelity = ∑ w, S.weight w * ∑ jl, ‖z jl w‖ ^ 2 := by
      unfold SourceCode.fidelity
      exact Finset.sum_congr rfl (fun w _ => by rw [hfw])
    have : ∑ jl, ‖(A jl * copies n S.average).trace‖ ^ 2 ≤ c.fidelity := by
      rw [hFid]
      simp_rw [htr]
      calc _ ≤ ∑ jl, ∑ w, S.weight w * ‖z jl w‖ ^ 2 :=
            Finset.sum_le_sum (fun jl _ => SrcQuality.jensen_cplx _ _ _ (fun w _ => hp0 w) hp1)
        _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun w _ => by rw [Finset.mul_sum])
    linarith

end QAlgorithms.Papers.Independent.Renew46.P43


-- Platform entry point: restates the target verbatim.
noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem I.1, PDF p.8. The first chain holds for every arbitrary encoder;
the entanglement-fidelity clause uses each actual quantum extension separately. -/
theorem _root_.solution {a d n : ℕ} {S : PureSource a d} (c : SourceCode S n) :
    c.distortion^2 ≤ 1 - c.fidelity ∧ 1 - c.fidelity ≤ c.distortion ∧
    ∀ E, EncoderExtension c E →
      1 - c.fidelity ≤ 1 - sourceFe (copies n S.average) (c.decode ∘ E) := by
  apply @QAlgorithms.Papers.Independent.Renew46.P43.sourceQualityComparison <;> assumption

end QAlgorithms.Papers.Independent.Renew46.P43

end
