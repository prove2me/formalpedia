-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.swap_werner_private_bit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:44:11.393822+00:00
-- url     : https://prove2.me/submissions/532aab27-30fd-4df1-b9a0-64c9111911ad

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section G53D
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
lemma g55bx_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt (Q * Q) = Q := by
  have hsa : IsSelfAdjoint Q := hQ.1.isSelfAdjoint
  have h1 : Q * Q = cfc (fun t : ℝ => t * t) Q := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Q, cfc_id' ℝ Q]
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  have : 0 ≤ t := spectrum_nonneg_of_nonneg hnn ht
  simp only [Function.comp, id]
  exact Real.sqrt_mul_self this

lemma g55bx_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g55bx_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g55bx_polar {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := g55bx_sqrt_psd _
  have hPP : P * P = Xᴴ * X := g55bx_sqrt_mul_self X
  let a : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin P
  let b : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin X
  have hinner : ∀ v, ⟪a v, a v⟫_ℂ = ⟪b v, b v⟫_ℂ := by
    intro v
    simp only [a, b, Matrix.toEuclideanLin_apply, EuclideanSpace.inner_toLp_toLp]
    rw [dotProduct_comm, dotProduct_comm (X *ᵥ _)]
    rw [Matrix.star_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.1.eq, hPP]
  have hnorm : ∀ v, ‖a v‖ = ‖b v‖ := by
    intro v
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
      hinner]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← norm_eq_zero, ← hnorm, hv, norm_zero]
  let L0 : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ n :=
    (LinearMap.ker a).liftQ b hker ∘ₗ a.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ v, L0 ⟨a v, LinearMap.mem_range_self a v⟩ = b v := by
    intro v
    simp only [L0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range a →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        rw [hL0, ← hnorm]
        rfl }
  let E := L.extend
  have hE : ∀ v, E (a v) = b v := by
    intro v
    have := L.extend_apply ⟨a v, LinearMap.mem_range_self a v⟩
    rw [this]
    exact hL0 v
  let W : Matrix n n ℂ := fun i j => (E (EuclideanSpace.single j 1)) i
  have hWv : ∀ v : EuclideanSpace ℂ n, W *ᵥ (WithLp.ofLp v) = WithLp.ofLp (E v) := by
    intro v
    have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext i; simp [EuclideanSpace.single_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    ext i
    simp [Matrix.mulVec, dotProduct, W, map_sum, map_smul, mul_comm]
  refine ⟨W, ?_, ?_⟩
  · ext i j
    have := E.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [dotProduct] at this
    simp only [Pi.star_apply] at this
    rw [show (∑ k, star (W k i) * W k j) = ∑ k, (E (EuclideanSpace.single j 1)) k *
      star ((E (EuclideanSpace.single i 1)) k) from Finset.sum_congr rfl (fun k _ => mul_comm _ _)]
    rw [this]
    simp [dotProduct, Pi.single_apply, eq_comm]
  · ext i j
    have h1 := congrFun (hWv (WithLp.toLp 2 (fun k => P k j))) i
    have h2 := hE (EuclideanSpace.single j 1)
    have h3 : a (EuclideanSpace.single j 1) = WithLp.toLp 2 (fun k => P k j) := by
      ext k; simp [a, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
    rw [h3] at h2
    rw [h2] at h1
    simp only [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    simp [b, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

end G53D

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

def g55bx_M {H : Type*} [Fintype H] [DecidableEq H] (U : Fin 2 → Matrix.unitaryGroup H ℂ) : Matrix (Key 2 × H) H ℂ :=
  fun k t => if k.1.1 = k.1.2 then (U k.1.1 : Op H) k.2 t else 0

lemma g55bx_priv_eq {H : Type*} [Fintype H] [DecidableEq H] (tau : Op H)
    (U : Fin 2 → Matrix.unitaryGroup H ℂ) :
    privateMatrix tau U = (1/2 : ℂ) • (g55bx_M U * tau * (g55bx_M U)ᴴ) := by
  ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, t⟩
  by_cases ha : a1 = a2 <;> by_cases hb : b1 = b2 <;>
    simp [privateMatrix, g55bx_M, ha, hb, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma g55bx_priv_density {H : Type*} [Fintype H] [DecidableEq H] {tau : Op H}
    (htau : IsDensityMatrix tau) (U : Fin 2 → Matrix.unitaryGroup H ℂ) :
    IsDensityMatrix (privateMatrix tau U) := by
  rw [g55bx_priv_eq]
  set M : Matrix (Key 2 × H) H ℂ := g55bx_M U with hM
  have hMM : Mᴴ * M = (2 : ℂ) • 1 := by
    have h0 := Unitary.star_mul_self_of_mem (U 0).2
    have h1 := Unitary.star_mul_self_of_mem (U 1).2
    ext t t'
    have e0 := congrFun (congrFun h0 t) t'
    have e1 := congrFun (congrFun h1 t) t'
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at e0 e1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hM, g55bx_M, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply]
    simp only [Fin.isValue, if_true, if_false, star_zero, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add, show ((0 : Fin 2) = 1) = False by decide,
      show ((1 : Fin 2) = 0) = False by decide]
    rw [e0, e1]
    split_ifs <;> norm_num
  refine ⟨(htau.1.mul_mul_conjTranspose_same M).smul (by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]; exact Complex.zero_le_real.mpr (by norm_num)), ?_⟩
  rw [Matrix.trace_smul, Matrix.trace_mul_cycle, hMM, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, htau.2]
  norm_num

lemma g55bx_main {H : Type*} [Fintype H] (gamma : Op (Key 2 × H)) :
    IsPrivate gamma ↔ ∃ X : Op H, traceNorm X = 1 ∧ gamma = xForm X := by
  constructor
  · rintro ⟨hγ, tau, htau, U, rfl⟩
    set U0 : Op H := (U 0 : Op H) with hU0
    set U1 : Op H := (U 1 : Op H) with hU1
    have h0 : U0ᴴ * U0 = 1 := Unitary.star_mul_self_of_mem (U 0).2
    have h1 : U1ᴴ * U1 = 1 := Unitary.star_mul_self_of_mem (U 1).2
    have h0' : ∀ Z : Op H, U0ᴴ * (U0 * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, h0, Matrix.one_mul]
    have h1' : ∀ Z : Op H, U1ᴴ * (U1 * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hτh := htau.1.1.eq
    let X : Op H := U0 * tau * U1ᴴ
    have hXh : Xᴴ = U1 * tau * U0ᴴ := by
      simp only [X, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hτh,
        Matrix.mul_assoc]
    have hA : Xᴴ * X = (U1 * tau * U1ᴴ) * (U1 * tau * U1ᴴ) := by
      rw [hXh]; simp only [X, Matrix.mul_assoc, h0', h1']
    have hB : X * Xᴴ = (U0 * tau * U0ᴴ) * (U0 * tau * U0ᴴ) := by
      rw [hXh]; simp only [X, Matrix.mul_assoc, h0', h1']
    have sA : cfc Real.sqrt (Xᴴ * X) = U1 * tau * U1ᴴ := by
      rw [hA]; exact g55bx_sqrt_sq (htau.1.mul_mul_conjTranspose_same U1)
    have sB : cfc Real.sqrt (X * Xᴴ) = U0 * tau * U0ᴴ := by
      rw [hB]; exact g55bx_sqrt_sq (htau.1.mul_mul_conjTranspose_same U0)
    refine ⟨X, ?_, ?_⟩
    · unfold QAlgorithms.traceNorm
      rw [sA, Matrix.trace_mul_cycle, h1, Matrix.one_mul, htau.2]
      simp
    · unfold xForm
      simp only [sA, sB, hXh]
      ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, t⟩
      fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
        simp [privateMatrix, X, hU0, hU1]
      all_goals first
        | (convert (congrFun (congrFun sB s) t).symm using 3 <;>
            simp [X, hU0, hU1, Matrix.conjTranspose_mul, hτh, Matrix.mul_assoc]; done)
        | (convert (congrFun (congrFun sA s) t).symm using 3 <;>
            simp [X, hU0, hU1, Matrix.conjTranspose_mul, hτh, Matrix.mul_assoc]; done)
  · rintro ⟨X, htn, rfl⟩
    obtain ⟨W, hW, hX⟩ := g55bx_polar X
    have hP := g55bx_sqrt_psd (Xᴴ * X)
    have hWu : W ∈ Matrix.unitaryGroup H ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact hW
    have hW' : ∀ Z : Op H, Wᴴ * (W * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
    have hB : X * Xᴴ = (W * cfc Real.sqrt (Xᴴ * X) * Wᴴ) * (W * cfc Real.sqrt (Xᴴ * X) * Wᴴ) := by
      conv_lhs => rw [hX]
      simp only [Matrix.conjTranspose_mul, hP.1.eq, Matrix.mul_assoc, hW']
    have sB : cfc Real.sqrt (X * Xᴴ) = W * cfc Real.sqrt (Xᴴ * X) * Wᴴ := by
      rw [hB]; exact g55bx_sqrt_sq (hP.mul_mul_conjTranspose_same W)
    have htr : (cfc Real.sqrt (Xᴴ * X)).trace = 1 := by
      have h1 : (cfc Real.sqrt (Xᴴ * X)).trace.re = 1 := htn
      have h2 := hP.trace_nonneg
      apply Complex.ext
      · simpa using h1
      · simpa using (Complex.nonneg_iff.mp h2).2.symm
    let U : Fin 2 → Matrix.unitaryGroup H ℂ := ![⟨W, hWu⟩, 1]
    have hxf : xForm X = privateMatrix (cfc Real.sqrt (Xᴴ * X)) U := by
      unfold xForm
      rw [sB]
      generalize cfc Real.sqrt (Xᴴ * X) = P at hX hP ⊢
      subst hX
      ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, t⟩
      fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
        simp [privateMatrix, U, Matrix.conjTranspose_mul, hP.1.eq]
      all_goals
        have hc := congrFun (congrFun (show (W * P)ᴴ = P * Wᴴ by
          rw [Matrix.conjTranspose_mul, hP.1.eq]) s) t
        simpa [Matrix.conjTranspose_apply] using hc
    rw [hxf]
    exact ⟨g55bx_priv_density ⟨hP, htr⟩ U, _, ⟨hP, htr⟩, U, rfl⟩


open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

lemma g55b_cfc_alg {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hY : Y = algebraMap ℝ (Matrix ι ι ℂ) (c ^ 2)) : cfc Real.sqrt Y = (c : ℂ) • 1 := by
  rw [hY, cfc_algebraMap, Real.sqrt_sq hc, Algebra.algebraMap_eq_smul_one]
  rw [← Complex.coe_smul]

lemma g55b_swap_herm (d : ℕ) : (swapMatrix (I := Fin d))ᴴ = swapMatrix (I := Fin d) := by
  ext a b
  simp only [Matrix.conjTranspose_apply, swapMatrix]
  by_cases h : b.1 = a.2 ∧ b.2 = a.1
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)]; simp

lemma g55b_swap_sq (d : ℕ) : swapMatrix (I := Fin d) * swapMatrix (I := Fin d) = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (a.2, a.1)]
  · simp only [swapMatrix, Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp
    · simp only [true_and, if_true]
      rw [if_neg h, if_neg]; · simp
      intro h'; exact h (Prod.ext h'.2 h'.1)
  · intro c _ hc
    simp only [swapMatrix]
    rw [if_neg]; · simp
    intro h; exact hc (Prod.ext h.2.symm h.1.symm)
  · simp

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    IsPrivate (swapPrivate d) ∧
    swapPrivate d =
      ((1/2*(1+1/(d:ℝ)) : ℝ) : ℂ) • Matrix.kronecker (signedBell false false) (symmetricWerner d) +
      ((1-1/2*(1+1/(d:ℝ)) : ℝ) : ℂ) • Matrix.kronecker (signedBell false true) (antisymmetricWerner d) := by
  have hd0 : (d : ℂ) ≠ 0 := by norm_cast; omega
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    intro h; have : (d : ℂ) = 1 := by linear_combination h
    norm_cast at this; omega
  have hdm : (d : ℂ) ^ 2 - d ≠ 0 := by
    rw [show (d : ℂ) ^ 2 - d = d * (d - 1) by ring]; exact mul_ne_zero hd0 hd1
  have hdp : (d : ℂ) ^ 2 + d ≠ 0 := by
    rw [show (d : ℂ) ^ 2 + d = d * (d + 1) by ring]
    refine mul_ne_zero hd0 ?_
    norm_cast
  set c : ℝ := ((d : ℝ) ^ 2)⁻¹ with hc
  have hcC : ((d : ℂ) ^ 2)⁻¹ = (c : ℂ) := by rw [hc]; push_cast; ring
  have hcpos : 0 ≤ c := by positivity
  set X : Op (Fin d × Fin d) := ((d : ℂ) ^ 2)⁻¹ • swapMatrix (I := Fin d) with hX
  have hXX : X * Xᴴ = algebraMap ℝ (Op (Fin d × Fin d)) (c ^ 2) := by
    rw [hX, Matrix.conjTranspose_smul, g55b_swap_herm, Matrix.smul_mul, Matrix.mul_smul,
      g55b_swap_sq, Algebra.algebraMap_eq_smul_one, smul_smul, hcC]
    rw [show star (c : ℂ) = (c : ℂ) from Complex.conj_ofReal c]
    rw [← Complex.coe_smul]; push_cast; ring_nf
  have hXX' : Xᴴ * X = algebraMap ℝ (Op (Fin d × Fin d)) (c ^ 2) := by
    rw [← hXX, hX, Matrix.conjTranspose_smul, g55b_swap_herm, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul]
    rw [show star ((d : ℂ) ^ 2)⁻¹ = ((d : ℂ) ^ 2)⁻¹ by simp]
  have hsq : ∀ Y : Op (Fin d × Fin d), Y = algebraMap ℝ (Op (Fin d × Fin d)) (c ^ 2) →
      cfc Real.sqrt Y = (c : ℂ) • 1 := by
    intro Y hY
    rw [hY, cfc_algebraMap, Real.sqrt_sq hcpos, Algebra.algebraMap_eq_smul_one]
    rw [← Complex.coe_smul]
  have hs1 := hsq _ hXX
  have hs2 := hsq _ hXX'
  have htn : traceNorm X = 1 := by
    unfold traceNorm
    rw [hs2, Matrix.trace_smul, Matrix.trace_one]
    have e : ((d:ℂ)^2).re = (d:ℝ)^2 := by norm_cast
    simp [hc, Fintype.card_prod, e]
    field_simp
  refine ⟨by convert (g55bx_main (swapPrivate d)).mpr ⟨X, by convert htn, by rfl⟩, ?_⟩
  have hsw : swapPrivate d = xForm X := rfl
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  rw [hsw]
  ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, t⟩
  simp only [xForm]
  rw [@g55b_cfc_alg _ _ (Classical.decEq _) (X * Xᴴ) c hcpos (by convert hXX),
    @g55b_cfc_alg _ _ (Classical.decEq _) (Xᴴ * X) c hcpos (by convert hXX')]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.kronecker_apply, signedBell, pureDensity,
    symmetricWerner, antisymmetricWerner, Matrix.of_apply, hX, smul_eq_mul]
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, h2, hc] <;>
    simp only [swapMatrix, map_one] <;> split_ifs <;> first | (exfalso; grind) | (field_simp; (try simp only [map_one, map_zero]); ring)
end
