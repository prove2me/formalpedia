-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.eve_block_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:41:08.205474+00:00
-- url     : https://prove2.me/submissions/c08d4ae2-e5a9-494b-bf88-707e4cf13c7e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)


theorem g59d_tel_mul {l m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  ext x i
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

theorem g59d_sp_eq {n : Type*} [Fintype n] [DecidableEq n] (P X : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : LinearMap.range (Matrix.toEuclideanLin P) = LinearMap.range (Matrix.toEuclideanLin X)) :
    supportProjector X = P := by
  have hsp : (Matrix.toEuclideanLin P).IsSymmetricProjection := by
    refine ⟨?_, (Matrix.isHermitian_iff_isSymmetric).mp hP⟩
    show (Matrix.toEuclideanLin P).comp (Matrix.toEuclideanLin P) = Matrix.toEuclideanLin P
    rw [← g59d_tel_mul, hPP]
  obtain ⟨_, h⟩ := (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range).mp hsp
  have key : ∀ (K : Submodule ℂ (EuclideanSpace ℂ n)) [K.HasOrthogonalProjection],
      K = LinearMap.range (Matrix.toEuclideanLin P) →
      (K.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = Matrix.toEuclideanLin P := by
    intro K _ hK
    subst hK
    exact h.symm
  unfold supportProjector
  rw [LinearEquiv.symm_apply_eq]
  exact key _ hr.symm

section g59d_polar_sec
open scoped MatrixOrder

theorem g59d_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt (Q * Q) = Q := by
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

theorem g59d_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

theorem g59d_range_mul_le {l m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    LinearMap.range (Matrix.toEuclideanLin (A * B)) ≤ LinearMap.range (Matrix.toEuclideanLin A) := by
  rw [g59d_tel_mul]; exact LinearMap.range_comp_le_range _ _

theorem g59d_range_eq {l m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℂ) (B : Matrix l n ℂ) (X : Matrix m n ℂ) (Y : Matrix n m ℂ)
    (h1 : B = A * X) (h2 : A = B * Y) :
    LinearMap.range (Matrix.toEuclideanLin A) = LinearMap.range (Matrix.toEuclideanLin B) := by
  apply le_antisymm
  · rw [h2]; exact g59d_range_mul_le _ _
  · rw [h1]; exact g59d_range_mul_le _ _

theorem g59d_aux1 (x : ℝ) (hx0 : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = (Real.sqrt x)⁻¹ * Real.sqrt x := by
  by_cases hs : Real.sqrt x = 0
  · simp [hs]
  · have h1 : (Real.sqrt x)⁻¹ * Real.sqrt x = 1 := inv_mul_cancel₀ hs
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    calc (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹
        = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by rw [hxx]
      _ = ((Real.sqrt x)⁻¹ * Real.sqrt x) * ((Real.sqrt x)⁻¹ * Real.sqrt x) := by ring
      _ = (Real.sqrt x)⁻¹ * Real.sqrt x := by rw [h1]; ring

theorem g59d_aux2 (x : ℝ) (hx0 : 0 ≤ x) :
    x * (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = (Real.sqrt x)⁻¹ * Real.sqrt x := by
  rw [← g59d_aux1 x hx0]; ring

/-- polar data for a rectangular matrix -/
theorem g59d_polar {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) :
    ∃ V : Matrix m n ℂ, Vᴴ * V = supportProjector (Mᴴ * M) ∧ V * Vᴴ = supportProjector (M * Mᴴ) ∧
      M = V * cfc Real.sqrt (Mᴴ * M) ∧
      cfc Real.sqrt (M * Mᴴ) = V * cfc Real.sqrt (Mᴴ * M) * Vᴴ ∧
      (V * cfc Real.sqrt (Mᴴ * M) * Vᴴ).trace = (cfc Real.sqrt (Mᴴ * M)).trace := by
  set Q := Mᴴ * M with hQdef
  have hQ : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  set g : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹ with hg
  set h : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹ * Real.sqrt x with hh
  set r := cfc Real.sqrt Q with hr
  set k := cfc g Q with hk
  set Pi := cfc h Q with hPi
  have hrP : r.PosSemidef := g59d_cfc_psd Q _ (fun t => Real.sqrt_nonneg t)
  have hkP : k.PosSemidef := g59d_cfc_psd Q _ (fun t => inv_nonneg.mpr (Real.sqrt_nonneg t))
  have hPiP : Pi.PosSemidef := g59d_cfc_psd Q _ (fun t => mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t))
    (Real.sqrt_nonneg t))
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ Q) := fun f =>
    (Matrix.finite_real_spectrum).continuousOn _
  have hQid : Q = cfc (fun x : ℝ => x) Q := (cfc_id' ℝ Q).symm
  have hhv : ∀ x, h x = 0 ∨ h x = 1 := by
    intro x; simp only [hh]
    by_cases hx : Real.sqrt x = 0
    · left; simp [hx]
    · right; exact inv_mul_cancel₀ hx
  have F1 : k * Q * k = Pi := by
    rw [hk, hPi]
    rw [show cfc g Q * Q * cfc g Q = cfc g Q * cfc (fun x : ℝ => x) Q * cfc g Q by rw [← hQid]]
    rw [← cfc_mul _ _ Q (hc _) (hc _), ← cfc_mul _ _ Q (hc _) (hc _)]
    apply cfc_congr
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hnn hx
    simp only [hg, hh]
    exact g59d_aux1 x hx0
  have F2 : k * r = Pi := by rw [hk, hr, hPi, ← cfc_mul _ _ Q (hc _) (hc _)]
  have F3 : r * Pi = r := by
    rw [hr, hPi, ← cfc_mul _ _ Q (hc _) (hc _)]
    congr 1; funext x
    by_cases hs : Real.sqrt x = 0
    · simp [hs]
    · simp only [hh]; field_simp
  have F3' : Pi * r = r := by
    rw [hr, hPi, ← cfc_mul _ _ Q (hc _) (hc _)]
    congr 1; funext x
    by_cases hs : Real.sqrt x = 0
    · simp [hs]
    · simp only [hh]; field_simp
  have F4 : Pi * Pi = Pi := by
    rw [hPi, ← cfc_mul _ _ Q (hc _) (hc _)]
    congr 1; funext x
    rcases hhv x with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring
  have Fk : k * Pi = k := by
    rw [hk, hPi, ← cfc_mul _ _ Q (hc _) (hc _)]
    congr 1; funext x
    by_cases hs : Real.sqrt x = 0
    · simp [hg, hs]
    · simp only [hg, hh]; field_simp
  have FQ1 : Pi * Q = Q := by
    rw [hPi]
    rw [show cfc h Q * Q = cfc h Q * cfc (fun x : ℝ => x) Q by rw [← hQid]]
    rw [← cfc_mul _ _ Q (hc _) (hc _)]
    conv_rhs => rw [hQid]
    apply cfc_congr
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hnn hx
    simp only [hh]
    by_cases hs : Real.sqrt x = 0
    · have : x = 0 := by rw [Real.sqrt_eq_zero hx0] at hs; exact hs
      simp [this]
    · field_simp
  have FQ2 : Q * Pi = Q := by
    have := congrArg Matrix.conjTranspose FQ1
    rwa [Matrix.conjTranspose_mul, hPiP.1.eq, hQ.1.eq] at this
  have FQk : Q * k * k = Pi := by
    rw [hk, hPi]
    rw [show Q * cfc g Q * cfc g Q = cfc (fun x : ℝ => x) Q * cfc g Q * cfc g Q by rw [← hQid]]
    rw [← cfc_mul _ _ Q (hc _) (hc _), ← cfc_mul _ _ Q (hc _) (hc _)]
    apply cfc_congr
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hnn hx
    simp only [hg, hh]
    exact g59d_aux2 x hx0
  have F5 : M * Pi = M := by
    have hD : (M - M * Pi)ᴴ * (M - M * Pi) = 0 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPiP.1.eq]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      have e1 : Mᴴ * (M * Pi) = Q := by rw [← Matrix.mul_assoc, ← hQdef, FQ2]
      have e2 : Pi * (Mᴴ * M) = Q := by rw [← hQdef, FQ1]
      rw [e1, e2]
      simp [hQdef]
    have := (Matrix.conjTranspose_mul_self_eq_zero).mp hD
    exact (sub_eq_zero.mp this).symm
  set V := M * k with hV
  have P1 : Vᴴ * V = Pi := by
    rw [hV, Matrix.conjTranspose_mul, hkP.1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, ← hQdef,
      ← Matrix.mul_assoc, F1]
  have P3 : V * r = M := by rw [hV, Matrix.mul_assoc, F2, F5]
  have VPi : V * Pi = V := by rw [hV, Matrix.mul_assoc, Fk]
  refine ⟨V, ?_, ?_, P3.symm, ?_, ?_⟩
  · rw [P1]
    refine (g59d_sp_eq Pi Q hPiP.1 F4 ?_).symm
    exact g59d_range_eq Pi Q Q (cfc (fun x => g x * g x) Q) FQ1.symm (by
      rw [cfc_mul g g Q (hc _) (hc _), ← hk, ← Matrix.mul_assoc, FQk])
  · have hVV : (V * Vᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self V
    have hidem : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, P1, ← Matrix.mul_assoc, VPi]
    refine (g59d_sp_eq (V * Vᴴ) (M * Mᴴ) hVV hidem ?_).symm
    have r1 : LinearMap.range (Matrix.toEuclideanLin (V * Vᴴ)) = LinearMap.range (Matrix.toEuclideanLin M) :=
      g59d_range_eq (V * Vᴴ) M (V * r) (k * Vᴴ)
        (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, P1, ← Matrix.mul_assoc, VPi, P3])
        (by rw [hV, Matrix.mul_assoc])
    have r2 : LinearMap.range (Matrix.toEuclideanLin M) = LinearMap.range (Matrix.toEuclideanLin (M * Mᴴ)) :=
      g59d_range_eq M (M * Mᴴ) Mᴴ (M * k * k) rfl
        (by rw [show M * Mᴴ * (M * k * k) = M * (Q * k * k) by rw [hQdef]; simp only [Matrix.mul_assoc],
          FQk, F5])
    exact r1.trans r2
  · have hY : (V * r * Vᴴ).PosSemidef := hrP.mul_mul_conjTranspose_same V
    have hYY : V * r * Vᴴ * (V * r * Vᴴ) = M * Mᴴ := by
      calc V * r * Vᴴ * (V * r * Vᴴ) = V * (r * (Vᴴ * V) * r) * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = (V * r) * (V * r)ᴴ := by
          have hVr : (V * r)ᴴ = r * Vᴴ := by rw [Matrix.conjTranspose_mul, hrP.1.eq]
          rw [hVr, P1, F3]; simp only [Matrix.mul_assoc]
        _ = M * Mᴴ := by rw [P3]
    rw [← hYY, g59d_sqrt_sq hY]
  · rw [Matrix.trace_mul_cycle, P1, F3']


theorem g59d_sqrt_mul {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

theorem g59d_sqrt_transpose {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q.transpose = (cfc Real.sqrt Q).transpose := by
  have hY : (cfc Real.sqrt Q).transpose.PosSemidef := (g59d_cfc_psd Q _ (fun t => Real.sqrt_nonneg t)).transpose
  have : (cfc Real.sqrt Q).transpose * (cfc Real.sqrt Q).transpose = Q.transpose := by
    rw [← Matrix.transpose_mul, g59d_sqrt_mul hQ]
  rw [← this, g59d_sqrt_sq hY]

theorem g59d_traceNorm_smul {n : Type*} [Fintype n] [DecidableEq n] (c : ℝ) (hc : 0 ≤ c) (X : Matrix n n ℂ) :
    traceNorm ((c : ℂ) • X) = c * traceNorm X := by
  unfold traceNorm
  have hP : (cfc Real.sqrt (Xᴴ * X)).PosSemidef := g59d_cfc_psd _ _ (fun t => Real.sqrt_nonneg t)
  have hY : ((c : ℂ) • cfc Real.sqrt (Xᴴ * X)).PosSemidef :=
    hP.smul (by exact_mod_cast hc)
  have e : ((c : ℂ) • X)ᴴ * ((c : ℂ) • X) = ((c : ℂ) • cfc Real.sqrt (Xᴴ * X)) * ((c : ℂ) • cfc Real.sqrt (Xᴴ * X)) := by
    have l : ((c:ℂ) • X)ᴴ * ((c:ℂ) • X) = ((c:ℂ) * c) • (Xᴴ * X) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      simp [Complex.conj_ofReal]
    rw [l, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      g59d_sqrt_mul (Matrix.posSemidef_conjTranspose_mul_self X)]
  rw [e, g59d_sqrt_sq hY, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem g59d_fid {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Ca Cb : Matrix m n ℂ) :
    traceNorm (Ca * Cbᴴ) = rootFidelity (Caᴴ * Ca).transpose (Cbᴴ * Cb).transpose := by
  set A := Caᴴ * Ca with hA
  set B := Cbᴴ * Cb with hB
  have hAP : A.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Ca
  have hBP : B.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Cb
  set ra := cfc Real.sqrt A with hra
  have hraP : ra.PosSemidef := g59d_cfc_psd A _ (fun t => Real.sqrt_nonneg t)
  set Mb := Cb * ra with hMb
  have e1 : (Ca * Cbᴴ)ᴴ * (Ca * Cbᴴ) = Mb * Mbᴴ := by
    rw [hMb, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hraP.1.eq]
    have : ra * ra = A := g59d_sqrt_mul hAP
    calc Cb * Caᴴ * (Ca * Cbᴴ) = Cb * (Caᴴ * Ca) * Cbᴴ := by simp only [Matrix.mul_assoc]
      _ = Cb * ra * (ra * Cbᴴ) := by rw [← hA, ← this]; simp only [Matrix.mul_assoc]
  have e2 : Mbᴴ * Mb = ra * B * ra := by
    rw [hMb, Matrix.conjTranspose_mul, hraP.1.eq, hB]; simp only [Matrix.mul_assoc]
  obtain ⟨V, -, -, -, h4, h5⟩ := g59d_polar Mb
  unfold traceNorm rootFidelity
  rw [e1, h4, h5, g59d_sqrt_transpose hAP, ← hra]
  have e3 : ra.transpose * B.transpose * ra.transpose = (Mbᴴ * Mb).transpose := by
    rw [e2, Matrix.transpose_mul (ra * B) ra, Matrix.transpose_mul ra B, Matrix.mul_assoc]
  rw [e3, g59d_sqrt_transpose (Matrix.posSemidef_conjTranspose_mul_self Mb), Matrix.trace_transpose]

end g59d_polar_sec

theorem g59d_w_nonneg {d : ℕ} {H E : Type*} [Fintype H] [Fintype E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a : Key d) : 0 ≤ outcomeWeight psi a :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

theorem g59d_w_zero {d : ℕ} {H E : Type*} [Fintype H] [Fintype E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a : Key d) (h : outcomeWeight psi a = 0) (s : H) (e : E) :
    psi ((a, s), e) = 0 := by
  unfold outcomeWeight at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Complex.normSq_nonneg _))).mp h s (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp h1 e
    (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp h2

theorem g59d_C_norm {d : ℕ} {H E : Type*} [Fintype H] [Fintype E] [Nonempty H] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a : Key d) :
    ∑ s, ∑ e, Complex.normSq (conditionalAmplitude psi a s e) = 1 := by
  unfold conditionalAmplitude
  by_cases hw : outcomeWeight psi a = 0
  · simp only [hw, if_true]
    rw [Fintype.sum_eq_single (Classical.choice (inferInstance : Nonempty H)) (fun s hs => by simp [hs])]
    rw [Fintype.sum_eq_single (Classical.choice (inferInstance : Nonempty E)) (fun e he => by simp [he])]
    simp
  · simp only [hw, if_false]
    have hpos : 0 < outcomeWeight psi a := lt_of_le_of_ne (g59d_w_nonneg psi a) (Ne.symm hw)
    simp only [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hpos.le]
    simp only [← Finset.sum_div]
    exact div_self hw

theorem g59d_sum_w {d : ℕ} {H E : Type*} [Fintype H] [Fintype E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (hpsi : IsState psi) :
    ∑ a, outcomeWeight psi a = 1 := by
  have h := hpsi
  unfold IsState at h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  rw [← h]
  simp only [outcomeWeight, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]

theorem g59d_block {d : ℕ} {H E : Type*} [Fintype H] [Fintype E] [Nonempty H] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a b : Key d) :
    keyBlock (traceRight (pureDensity psi)) a b =
      ((Real.sqrt (outcomeWeight psi a * outcomeWeight psi b) : ℝ) : ℂ) •
        (conditionalAmplitude psi a * (conditionalAmplitude psi b)ᴴ) := by
  ext s t
  simp only [keyBlock, traceRight, pureDensity, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul]
  by_cases ha : outcomeWeight psi a = 0
  · simp [ha, g59d_w_zero psi a ha]
  by_cases hb : outcomeWeight psi b = 0
  · simp [hb, g59d_w_zero psi b hb]
  have hpa : 0 < outcomeWeight psi a := lt_of_le_of_ne (g59d_w_nonneg psi a) (Ne.symm ha)
  have hpb : 0 < outcomeWeight psi b := lt_of_le_of_ne (g59d_w_nonneg psi b) (Ne.symm hb)
  have sa : (Real.sqrt (outcomeWeight psi a) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpa).ne'
  have sb : (Real.sqrt (outcomeWeight psi b) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpb).ne'
  simp only [conditionalAmplitude, ha, hb, if_false, Real.sqrt_mul hpa.le, Complex.ofReal_mul,
    Finset.mul_sum, star_div₀, Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  field_simp

theorem g59d_eve_density {d : ℕ} {H E : Type*} [Fintype H] [Fintype E] [Nonempty H] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a : Key d) : IsDensityMatrix (conditionalEve psi a) := by
  refine ⟨(Matrix.posSemidef_conjTranspose_mul_self _).transpose, ?_⟩
  unfold conditionalEve
  rw [Matrix.trace_transpose]
  have h := g59d_C_norm psi a
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm] at h
  have : ∀ x : ℂ, star x * x = (Complex.normSq x : ℂ) := fun x => by
    rw [Complex.star_def, mul_comm, Complex.mul_conj]
  simp only [this]
  exact_mod_cast h

end QAlgorithms.Papers.Independent.Dependency50.P24

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)
open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.15–16, Eqs.(97)–(98); pp.31–32: actual coefficient blocks and Eve fidelity.
The printed maps from the whole shield onto Eve support in (97),(199) cannot be
isometries when the conditional rank is smaller than the shield dimension. Use polar
partial isometries with the explicitly specified initial and final support projections.
Transposes follow C(s,e)=<s,e|psi_a>; no full-rank assumption is added. -/
theorem solution {d : ℕ} [NeZero d] {S T E : Type*}
    [Fintype S] [Fintype T] [Fintype E] [Nonempty S] [Nonempty T] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × (S × T)) × E)) (hpsi : IsState psi) :
    (∀ a, 0 ≤ outcomeWeight psi a ∧ IsDensityMatrix (conditionalEve psi a)) ∧
    (∑ a, outcomeWeight psi a) = 1 ∧
    (∀ a b, keyBlock (traceRight (pureDensity psi)) a b =
      ((Real.sqrt (outcomeWeight psi a * outcomeWeight psi b) : ℝ) : ℂ) •
        (conditionalAmplitude psi a * (conditionalAmplitude psi b)ᴴ)) ∧
    (∀ a b, traceNorm (keyBlock (traceRight (pureDensity psi)) a b) =
      Real.sqrt (outcomeWeight psi a * outcomeWeight psi b) *
        rootFidelity (conditionalEve psi a) (conditionalEve psi b)) ∧
    ∃ V : Key d → Matrix (S × T) E ℂ,
      (∀ a, (V a)ᴴ * V a = supportProjector (conditionalEve psi a).transpose ∧
        V a * (V a)ᴴ = supportProjector
          (conditionalAmplitude psi a * (conditionalAmplitude psi a)ᴴ) ∧
        conditionalAmplitude psi a = V a * cfc Real.sqrt (conditionalEve psi a).transpose) ∧
      ∀ a b, keyBlock (traceRight (pureDensity psi)) a b =
        ((Real.sqrt (outcomeWeight psi a * outcomeWeight psi b) : ℝ) : ℂ) •
          (V a * cfc Real.sqrt (conditionalEve psi a).transpose *
            cfc Real.sqrt (conditionalEve psi b).transpose * (V b)ᴴ) := by
  have hblock := g59d_block psi
  choose V hV using fun a => g59d_polar (conditionalAmplitude psi a)
  refine ⟨fun a => ⟨g59d_w_nonneg psi a, g59d_eve_density psi a⟩, g59d_sum_w psi hpsi, hblock, ?_, V, ?_, ?_⟩
  · intro a b
    rw [hblock, g59d_traceNorm_smul _ (Real.sqrt_nonneg _), g59d_fid]
    rfl
  · intro a
    obtain ⟨h1, h2, h3, -, -⟩ := hV a
    refine ⟨?_, h2, ?_⟩
    · unfold conditionalEve; rw [Matrix.transpose_transpose]; exact h1
    · unfold conditionalEve; rw [Matrix.transpose_transpose]; exact h3
  · intro a b
    rw [hblock]
    congr 1
    obtain ⟨-, -, ha, -, -⟩ := hV a
    obtain ⟨-, -, hb, -, -⟩ := hV b
    unfold conditionalEve
    simp only [Matrix.transpose_transpose]
    conv_lhs => rw [ha, hb]
    rw [Matrix.conjTranspose_mul, (g59d_cfc_psd _ _ (fun t => Real.sqrt_nonneg t)).1.eq]
    simp only [Matrix.mul_assoc]

end
