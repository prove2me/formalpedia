-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.private_bit_x_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:13:05.803235+00:00
-- url     : https://prove2.me/submissions/a6cf224a-8225-4a00-8cf6-ca9b1a54b7a6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section G53D
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
lemma g53d_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
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

lemma g53d_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g53d_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g53d_polar {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := g53d_sqrt_psd _
  have hPP : P * P = Xᴴ * X := g53d_sqrt_mul_self X
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

def g53d_M {H : Type*} [Fintype H] [DecidableEq H] (U : Fin 2 → Matrix.unitaryGroup H ℂ) : Matrix (Key 2 × H) H ℂ :=
  fun k t => if k.1.1 = k.1.2 then (U k.1.1 : Op H) k.2 t else 0

lemma g53d_priv_eq {H : Type*} [Fintype H] [DecidableEq H] (tau : Op H)
    (U : Fin 2 → Matrix.unitaryGroup H ℂ) :
    privateMatrix tau U = (1/2 : ℂ) • (g53d_M U * tau * (g53d_M U)ᴴ) := by
  ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, t⟩
  by_cases ha : a1 = a2 <;> by_cases hb : b1 = b2 <;>
    simp [privateMatrix, g53d_M, ha, hb, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma g53d_priv_density {H : Type*} [Fintype H] [DecidableEq H] {tau : Op H}
    (htau : IsDensityMatrix tau) (U : Fin 2 → Matrix.unitaryGroup H ℂ) :
    IsDensityMatrix (privateMatrix tau U) := by
  rw [g53d_priv_eq]
  set M : Matrix (Key 2 × H) H ℂ := g53d_M U with hM
  have hMM : Mᴴ * M = (2 : ℂ) • 1 := by
    have h0 := Unitary.star_mul_self_of_mem (U 0).2
    have h1 := Unitary.star_mul_self_of_mem (U 1).2
    ext t t'
    have e0 := congrFun (congrFun h0 t) t'
    have e1 := congrFun (congrFun h1 t) t'
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at e0 e1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hM, g53d_M, Fintype.sum_prod_type,
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

lemma g53d_main {H : Type*} [Fintype H] (gamma : Op (Key 2 × H)) :
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
      rw [hA]; exact g53d_sqrt_sq (htau.1.mul_mul_conjTranspose_same U1)
    have sB : cfc Real.sqrt (X * Xᴴ) = U0 * tau * U0ᴴ := by
      rw [hB]; exact g53d_sqrt_sq (htau.1.mul_mul_conjTranspose_same U0)
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
    obtain ⟨W, hW, hX⟩ := g53d_polar X
    have hP := g53d_sqrt_psd (Xᴴ * X)
    have hWu : W ∈ Matrix.unitaryGroup H ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact hW
    have hW' : ∀ Z : Op H, Wᴴ * (W * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
    have hB : X * Xᴴ = (W * cfc Real.sqrt (Xᴴ * X) * Wᴴ) * (W * cfc Real.sqrt (Xᴴ * X) * Wᴴ) := by
      conv_lhs => rw [hX]
      simp only [Matrix.conjTranspose_mul, hP.1.eq, Matrix.mul_assoc, hW']
    have sB : cfc Real.sqrt (X * Xᴴ) = W * cfc Real.sqrt (Xᴴ * X) * Wᴴ := by
      rw [hB]; exact g53d_sqrt_sq (hP.mul_mul_conjTranspose_same W)
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
    exact ⟨g53d_priv_density ⟨hP, htr⟩ U, _, ⟨hP, htr⟩, U, rfl⟩


/-- PDF pp.9–10, Eq.(43): one-operator characterization of every fixed-basis pbit. -/
theorem solution {S T : Type*} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] (gamma : Op (Key 2 × (S × T))) :
    IsPrivate gamma ↔ ∃ X : Op (S × T), traceNorm X = 1 ∧ gamma = xForm X := by
  convert g53d_main gamma

end
