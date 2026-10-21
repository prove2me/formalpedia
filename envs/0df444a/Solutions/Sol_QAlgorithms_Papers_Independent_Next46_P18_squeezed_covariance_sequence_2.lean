-- Prove2me | solution 2 for QAlgorithms.Papers.Independent.Next46.P18.squeezed_covariance_sequence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:34:48.698796+00:00
-- url     : https://prove2.me/submissions/08574738-772a-4e2d-8040-3fcbff8b1f3e

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel homogeneousEntropy mutualInformation boundedConjugation traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix
   gaussianFunction weylTraceCharacteristic tracePair)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable zeroObservable feasibleStates informationSupremum
   operationalAssistedCapacity regularizedUnassistedCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance)

open QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open Matrix in
lemma g62h_J_eq (s : ℕ) : physicalCommutationMatrix s 1 = interleavedSymplecticForm s := by
  ext ⟨k, a⟩ ⟨l, b⟩
  simp only [physicalCommutationMatrix, interleavedSymplecticForm]
  fin_cases a <;> fin_cases b <;> simp

open Matrix in
lemma g62h_J_tr (s : ℕ) : (interleavedSymplecticForm s)ᵀ = -interleavedSymplecticForm s := by
  ext ⟨k, a⟩ ⟨l, b⟩
  show interleavedSymplecticForm s (l, b) (k, a) = -(interleavedSymplecticForm s (k, a) (l, b))
  unfold interleavedSymplecticForm
  by_cases h : k = l
  · subst h; fin_cases a <;> fin_cases b <;> simp
  · simp [h, Ne.symm h]

open Matrix in
lemma g62h_J_orth (s : ℕ) :
    (interleavedSymplecticForm s)ᵀ * interleavedSymplecticForm s = 1 := by
  ext ⟨k, a⟩ ⟨l, b⟩
  simp only [mul_apply, transpose_apply, interleavedSymplecticForm, one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  by_cases h : k = l
  · subst h; fin_cases a <;> fin_cases b <;> simp [Finset.sum_ite_eq']
  · fin_cases a <;> fin_cases b <;> simp [h, Finset.sum_ite_eq', Prod.ext_iff] <;>
      (intro x; exact h x.symm)

section g62h_lin
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Matrix

lemma g62h_JJ (J : Matrix ι ι ℝ) (hJ : Jᵀ * J = 1) (y : ι → ℝ) :
    (J *ᵥ y) ⬝ᵥ (J *ᵥ y) = y ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hJ, one_mulVec]

lemma g62h_self_nonneg (x : ι → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

lemma g62h_amgm (J : Matrix ι ι ℝ) (hJ : Jᵀ * J = 1) (x y : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    2 * (x ⬝ᵥ J *ᵥ y) ≤ δ * (x ⬝ᵥ x) + δ⁻¹ * (y ⬝ᵥ y) := by
  have h0 := g62h_self_nonneg (δ • x - J *ᵥ y)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_dotProduct, dotProduct_smul, g62h_JJ J hJ, dotProduct_comm (J *ᵥ y) x] at h0
  simp only [smul_eq_mul] at h0
  have h1 : δ * (2 * (x ⬝ᵥ J *ᵥ y)) ≤ δ * (δ * (x ⬝ᵥ x) + δ⁻¹ * (y ⬝ᵥ y)) := by
    rw [mul_add, ← mul_assoc δ δ⁻¹, mul_inv_cancel₀ hδ.ne']
    nlinarith
  exact le_of_mul_le_mul_left h1 hδ

lemma g62h_sym_dot (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (u v : ι → ℝ) :
    u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

lemma g62h_anti_dot (J : Matrix ι ι ℝ) (hJ : Jᵀ = -J) (u v : ι → ℝ) :
    u ⬝ᵥ J *ᵥ v = -(v ⬝ᵥ J *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hJ, neg_mulVec, neg_dotProduct, dotProduct_comm]

lemma g62h_main (J : Matrix ι ι ℝ) (hJo : Jᵀ * J = 1) (P : Matrix ι ι ℝ)
    (hiso : ∀ a b, (P *ᵥ a) ⬝ᵥ J *ᵥ (P *ᵥ b) = 0) (ε : ℝ) (hε : 0 < ε) (a b : ι → ℝ) :
    2 * (a ⬝ᵥ J *ᵥ b) ≤ ε * ((P *ᵥ a) ⬝ᵥ (P *ᵥ a) + (P *ᵥ b) ⬝ᵥ (P *ᵥ b)) +
      (ε⁻¹ + 1) * ((a - P *ᵥ a) ⬝ᵥ (a - P *ᵥ a) + (b - P *ᵥ b) ⬝ᵥ (b - P *ᵥ b)) := by
  set pa := P *ᵥ a
  set pb := P *ᵥ b
  set qa := a - pa
  set qb := b - pb
  have ha : a = pa + qa := by simp [qa]
  have hb : b = pb + qb := by simp [qb]
  have hexp : a ⬝ᵥ J *ᵥ b = pa ⬝ᵥ J *ᵥ pb + pa ⬝ᵥ J *ᵥ qb + qa ⬝ᵥ J *ᵥ pb + qa ⬝ᵥ J *ᵥ qb := by
    conv_lhs => rw [ha, hb]
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]; ring
  have h0 : pa ⬝ᵥ J *ᵥ pb = 0 := hiso a b
  have h1 := g62h_amgm J hJo pa qb ε hε
  have h2 := g62h_amgm J hJo qa pb ε⁻¹ (inv_pos.mpr hε)
  rw [inv_inv] at h2
  have h3 := g62h_amgm J hJo qa qb 1 one_pos
  have h4 := g62h_self_nonneg qa
  have h5 := g62h_self_nonneg qb
  rw [inv_one, one_mul, one_mul] at h3
  rw [hexp]
  nlinarith

lemma g62h_quad (A : Matrix ι ι ℝ) (a : ι → ℝ) : a ⬝ᵥ (Aᵀ * A) *ᵥ a = (A *ᵥ a) ⬝ᵥ (A *ᵥ a) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma g62h_cast (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (fun i => (u i : ℂ)) ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ (fun i => (v i : ℂ))) =
      ((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) := by
  simp [dotProduct, mulVec, Complex.ofReal_sum]

end g62h_lin

section g62h_lin2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Matrix

lemma g62h_psd (G J : Matrix ι ι ℝ) (hG : Gᵀ = G) (hJ : Jᵀ = -J)
    (h : ∀ a b : ι → ℝ, 2 * (a ⬝ᵥ J *ᵥ b) ≤ a ⬝ᵥ G *ᵥ a + b ⬝ᵥ G *ᵥ b) :
    (G.map (fun x : ℝ => (x : ℂ)) + Complex.I • J.map (fun x : ℝ => (x : ℂ))).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    have h1 := congrFun (congrFun hG i) j
    have h2 := congrFun (congrFun hJ i) j
    simp only [transpose_apply, neg_apply] at h1 h2
    simp [Matrix.conjTranspose_apply, h1, h2]
  · set a : ι → ℝ := fun i => (x i).re
    set b : ι → ℝ := fun i => (x i).im
    have hx : x = (fun i => (a i : ℂ)) + Complex.I • (fun i => (b i : ℂ)) := by
      funext i; apply Complex.ext <;> simp [a, b]
    have hsx : star x = (fun i => (a i : ℂ)) - Complex.I • (fun i => (b i : ℂ)) := by
      funext i; apply Complex.ext <;> simp [a, b]
    rw [hsx, hx]
    simp only [add_mulVec, mulVec_add, mulVec_smul, smul_mulVec, dotProduct_add,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, g62h_cast, smul_eq_mul]
    have hs : (b ⬝ᵥ G *ᵥ a) = (a ⬝ᵥ G *ᵥ b) := g62h_sym_dot G hG b a
    have hj1 : (b ⬝ᵥ J *ᵥ a) = -(a ⬝ᵥ J *ᵥ b) := g62h_anti_dot J hJ b a
    have hj2 : (a ⬝ᵥ J *ᵥ a) = 0 := by have := g62h_anti_dot J hJ a a; linarith
    have hj3 : (b ⬝ᵥ J *ᵥ b) = 0 := by have := g62h_anti_dot J hJ b b; linarith
    have hs' : ((b ⬝ᵥ G *ᵥ a : ℝ) : ℂ) = ((a ⬝ᵥ G *ᵥ b : ℝ) : ℂ) := by rw [hs]
    have hj1' : ((b ⬝ᵥ J *ᵥ a : ℝ) : ℂ) = -((a ⬝ᵥ J *ᵥ b : ℝ) : ℂ) := by rw [hj1]; push_cast; ring
    have hj2' : ((a ⬝ᵥ J *ᵥ a : ℝ) : ℂ) = 0 := by rw [hj2]; simp
    have hj3' : ((b ⬝ᵥ J *ᵥ b : ℝ) : ℂ) = 0 := by rw [hj3]; simp
    have key : ((a ⬝ᵥ G *ᵥ a : ℝ) : ℂ) - Complex.I * ((b ⬝ᵥ G *ᵥ a : ℝ) : ℂ) +
        Complex.I * (((a ⬝ᵥ J *ᵥ a : ℝ) : ℂ) - Complex.I * ((b ⬝ᵥ J *ᵥ a : ℝ) : ℂ)) +
        Complex.I * (((a ⬝ᵥ G *ᵥ b : ℝ) : ℂ) - Complex.I * ((b ⬝ᵥ G *ᵥ b : ℝ) : ℂ) +
          Complex.I * (((a ⬝ᵥ J *ᵥ b : ℝ) : ℂ) - Complex.I * ((b ⬝ᵥ J *ᵥ b : ℝ) : ℂ))) =
        ((a ⬝ᵥ G *ᵥ a + b ⬝ᵥ G *ᵥ b - 2 * (a ⬝ᵥ J *ᵥ b) : ℝ) : ℂ) := by
      push_cast
      linear_combination (-Complex.I) * hs' + Complex.I * hj2' + (-Complex.I * Complex.I * Complex.I) * hj3'
        + (-Complex.I * Complex.I) * hj1' + (-(b ⬝ᵥ G *ᵥ b : ℝ) + 2 * (a ⬝ᵥ J *ᵥ b : ℝ) : ℂ) * Complex.I_sq
    rw [key]
    exact Complex.zero_le_real.mpr (by linarith [h a b])

end g62h_lin2

open Matrix in
lemma g62h_ginv {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (K : Matrix m k ℝ) : ∃ R : Matrix k m ℝ, K * R * K = K := by
  set f := Matrix.toLin' K
  obtain ⟨h, hh⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype
    (Submodule.ker_subtype _)
  refine ⟨LinearMap.toMatrix' (h ∘ₗ π), ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply]
  have e1 : π (f v) = f.rangeRestrict v := by
    have := LinearMap.congr_fun hπ (f.rangeRestrict v)
    simpa using this
  rw [← show f = Matrix.toLin' K from rfl, e1]
  have := LinearMap.congr_fun hh (f.rangeRestrict v)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  exact congrArg Subtype.val this

open Matrix in
theorem solution {s t : ℕ}
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ) (hisotropic : K.transpose * (physicalCommutationMatrix s 1) * K = 0) :
    ∃ gamma : ℕ → Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ,
      (∀ n, quantumCovariance ((2 : ℝ) • gamma n)) ∧
      Tendsto (fun n => K.transpose * gamma n * K) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := g62h_ginv K
  set J := interleavedSymplecticForm s
  have hJK : Kᵀ * J * K = 0 := by
    rw [show J = physicalCommutationMatrix s 1 from (g62h_J_eq s).symm]; exact hisotropic
  set P := K * R
  have hPK : P * K = K := hR
  have hKdot : ∀ u w, (K *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Kᵀ *ᵥ w) := fun u w => by
    rw [dotProduct_mulVec, vecMul_transpose]
  have hiso : ∀ a b, (P *ᵥ a) ⬝ᵥ J *ᵥ (P *ᵥ b) = 0 := by
    intro a b
    rw [← mulVec_mulVec, ← mulVec_mulVec, hKdot, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
      hJK, Matrix.zero_mul, zero_mulVec, dotProduct_zero]
  let γ : ℕ → Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ := fun n =>
    (1 / ((n : ℝ) + 1)) • (Pᵀ * P) + ((1 / ((n : ℝ) + 1))⁻¹ + 1) • ((1 - P)ᵀ * (1 - P))
  refine ⟨γ, fun n => ?_, ?_⟩
  · set ε : ℝ := 1 / ((n : ℝ) + 1)
    have hε : 0 < ε := by positivity
    unfold quantumCovariance
    apply g62h_psd _ J
    · simp [γ, transpose_add, transpose_smul, transpose_mul]
    · exact g62h_J_tr s
    · intro a b
      have hq : ∀ c : QuadratureIndex s → ℝ, c ⬝ᵥ ((2 : ℝ) • γ n) *ᵥ c =
          2 * (ε * ((P *ᵥ c) ⬝ᵥ (P *ᵥ c)) + (ε⁻¹ + 1) * ((c - P *ᵥ c) ⬝ᵥ (c - P *ᵥ c))) := by
        intro c
        simp only [γ, smul_add, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
          g62h_quad, sub_mulVec, one_mulVec]
        ring
      rw [hq, hq]
      have hm := g62h_main J (g62h_J_orth s) P hiso ε hε a b
      have n1 := g62h_self_nonneg (P *ᵥ a)
      have n2 := g62h_self_nonneg (P *ᵥ b)
      have n3 := g62h_self_nonneg (a - P *ᵥ a)
      have n4 := g62h_self_nonneg (b - P *ᵥ b)
      have hεi : 0 < ε⁻¹ + 1 := by positivity
      nlinarith [mul_nonneg hε.le n1, mul_nonneg hε.le n2, mul_nonneg hεi.le n3, mul_nonneg hεi.le n4]
  · have hQK : (1 - P) * K = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPK, sub_self]
    have e1 : Kᵀ * (Pᵀ * P) * K = Kᵀ * K := by
      rw [show Kᵀ * (Pᵀ * P) * K = (Kᵀ * Pᵀ) * (P * K) by simp only [Matrix.mul_assoc],
        ← transpose_mul, hPK]
    have e2 : Kᵀ * ((1 - P)ᵀ * (1 - P)) * K = 0 := by
      rw [show Kᵀ * ((1 - P)ᵀ * (1 - P)) * K = (Kᵀ * (1 - P)ᵀ) * ((1 - P) * K) by
        simp only [Matrix.mul_assoc], ← transpose_mul, hQK, Matrix.mul_zero]
    have hform : ∀ n : ℕ, Kᵀ * γ n * K = (1 / ((n : ℝ) + 1)) • (Kᵀ * K) := by
      intro n
      simp only [γ]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_mul, e1, e2, smul_zero, add_zero]
    simp only [hform]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (Kᵀ * K)
    simpa using this
