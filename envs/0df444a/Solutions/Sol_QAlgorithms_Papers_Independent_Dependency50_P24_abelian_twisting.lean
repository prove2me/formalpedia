-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.abelian_twisting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:56:04.61786+00:00
-- url     : https://prove2.me/submissions/dc3895dc-a2fe-420c-9f0d-4439166e5f8d

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
noncomputable section
namespace QAlgorithms.Papers.Independent.Dependency50.P24
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)
open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

namespace A3AT

open scoped MatrixOrder
open Matrix

lemma sqrt_sq' {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
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

lemma sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma sqrt_mul_sqrt {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}
    (hQ : Q.PosSemidef) : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma dot_star_real {n : Type*} [Fintype n] (v : n → ℂ) :
    star v ⬝ᵥ v = (((star v ⬝ᵥ v).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, dotProduct, Complex.im_sum]
    apply Finset.sum_eq_zero
    intro i _
    simp [Complex.mul_im]; ring

lemma dot_star_re_nonneg {n : Type*} [Fintype n] (v : n → ℂ) : 0 ≤ (star v ⬝ᵥ v).re := by
  have := dotProduct_star_self_nonneg v
  exact (Complex.nonneg_iff.mp this).1

lemma sqrt_rankOne {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℂ) :
    cfc Real.sqrt (vecMulVec v (star v)) =
      (((Real.sqrt (star v ⬝ᵥ v).re)⁻¹ : ℝ) : ℂ) • vecMulVec v (star v) := by
  set t := (star v ⬝ᵥ v).re with ht
  set Q := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) • vecMulVec v (star v) with hQ
  have hQpsd : Q.PosSemidef :=
    (posSemidef_vecMulVec_self_star v).smul
      (Complex.zero_le_real.mpr (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hQQ : Q * Q = vecMulVec v (star v) := by
    by_cases hv : v = 0
    · subst hv; simp [Q]
    have htpos : 0 < t := by
      rcases (dot_star_re_nonneg v).lt_or_eq with h | h
      · exact h
      · exfalso; apply hv
        rw [← dotProduct_star_self_eq_zero, dot_star_real v, ← h]; simp
    rw [hQ, smul_mul_smul_comm, vecMulVec_mul_vecMulVec, dot_star_real v, ← ht]
    have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htpos.le
    have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr htpos).ne'
    have hc : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (t : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      have : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = 1 := by
        rw [show (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = t / (Real.sqrt t * Real.sqrt t) by ring,
          hs, div_self htpos.ne']
      rw [this]; simp
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (v i * star v j) * hc
  rw [← hQQ, sqrt_sq' hQpsd]

lemma trace_sqrt_rankOne {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℂ) :
    (cfc Real.sqrt (vecMulVec v (star v))).trace.re = Real.sqrt (star v ⬝ᵥ v).re := by
  rw [sqrt_rankOne, trace_smul, trace_vecMulVec, dotProduct_comm v (star v), dot_star_real v]
  simp only [smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rcases (dot_star_re_nonneg v).lt_or_eq with h | h
  · rw [inv_mul_eq_div, Real.div_sqrt]
  · rw [← h]; simp

lemma fid_pure {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (b : n → ℂ) :
    rootFidelity ρ (vecMulVec b (star b)) ^ 2 = (star b ⬝ᵥ (ρ *ᵥ b)).re := by
  unfold rootFidelity
  set S := cfc Real.sqrt ρ with hS
  have hSH : Sᴴ = S := (sqrt_psd ρ).1
  have hSS : S * S = ρ := sqrt_mul_sqrt hρ
  have h1 : S * vecMulVec b (star b) * S = vecMulVec (S *ᵥ b) (star (S *ᵥ b)) := by
    rw [mul_vecMulVec, vecMulVec_mul, star_mulVec, hSH]
  have h2 : star (S *ᵥ b) ⬝ᵥ (S *ᵥ b) = star b ⬝ᵥ (ρ *ᵥ b) := by
    rw [star_mulVec, hSH, ← dotProduct_mulVec, mulVec_mulVec, hSS]
  rw [h1, trace_sqrt_rankOne, h2]
  apply Real.sq_sqrt
  rw [← h2]; exact dot_star_re_nonneg _

/-- the Bell vector -/
def bv (θ : Key 2 → ℝ) : Key 2 → ℂ :=
  fun a => if a.1 = a.2 then Complex.exp ((θ a : ℂ) * Complex.I) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

lemma c2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma star_c : star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  simp [Complex.conj_ofReal]

lemma star_exp_mul (φ : ℝ) :
    star (Complex.exp ((φ : ℂ) * Complex.I)) * Complex.exp ((φ : ℂ) * Complex.I) = 1 := by
  have := Complex.conj_mul' (Complex.exp ((φ : ℂ) * Complex.I))
  rw [Complex.norm_exp_ofReal_mul_I] at this
  simpa using this

lemma phaseBell_eq (θ : Key 2 → ℝ) : phaseBell θ = vecMulVec (bv θ) (star (bv θ)) := by
  ext x y
  simp only [phaseBell, phaseMatrix, bellProjector, bv, vecMulVec_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_conjTranspose, Pi.star_apply]
  by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2 <;> simp only [hx, hy, and_self,
    and_false, false_and, if_true, if_false, mul_zero, zero_mul, star_zero]
  rw [star_mul, star_c]
  have := c2
  push_cast at this ⊢
  linear_combination (Complex.exp (↑(θ x) * Complex.I) * star (Complex.exp (↑(θ y) * Complex.I))) * this.symm

lemma quad (ρ : Matrix (Key 2) (Key 2) ℂ) (w : Key 2 → ℂ) (h01 : w (0,1) = 0)
    (h10 : w (1,0) = 0) : star w ⬝ᵥ (ρ *ᵥ w) =
      star (w (0,0)) * (ρ (0,0) (0,0) * w (0,0) + ρ (0,0) (1,1) * w (1,1)) +
      star (w (1,1)) * (ρ (1,1) (0,0) * w (0,0) + ρ (1,1) (1,1) * w (1,1)) := by
  simp [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, h01, h10]

theorem clause2 (ρ : Op (Key 2)) (hρ : IsDensityMatrix ρ) (eps : ℝ)
    (h : ‖ρ (0,0) (1,1)‖ > 1/2 - eps) :
    ∃ θ : Key 2 → ℝ, (rootFidelity ρ (phaseBell θ))^2 ≥ 1 - 2*eps := by
  set z := ρ (0,0) (1,1) with hzdef
  set φ : ℝ := -Complex.arg z with hφ
  set e := Complex.exp ((φ : ℂ) * Complex.I) with he
  have hz : z * e = (‖z‖ : ℂ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [he, mul_assoc, ← Complex.exp_add, hφ]; push_cast; ring_nf; simp
  have hH : ρ (1,1) (0,0) = star z := (hρ.1.isHermitian.apply (1,1) (0,0)).symm
  have hz' : star z * star e = (‖z‖ : ℂ) := by
    rw [← star_mul, mul_comm, hz]; simp [Complex.conj_ofReal]
  have hee : star e * e = 1 := star_exp_mul φ
  refine ⟨fun a => if a = (1,1) then φ else 0, ?_⟩
  rw [phaseBell_eq, fid_pure hρ.1]
  have hq := quad ρ (bv fun a => if a = (1,1) then φ else 0) (by simp [bv]) (by simp [bv])
  have hb0 : bv (fun a => if a = (1,1) then φ else 0) (0,0) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    simp [bv]
  have hb1 : bv (fun a => if a = (1,1) then φ else 0) (1,1) = e * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    simp [bv, he]
  rw [hb0, hb1, star_mul, star_c, hH] at hq
  have hq2 : star (bv fun a => if a = (1,1) then φ else 0) ⬝ᵥ
      (ρ *ᵥ bv fun a => if a = (1,1) then φ else 0) =
      (ρ (0,0) (0,0) + ρ (1,1) (1,1) + 2 * (‖z‖ : ℂ)) / 2 := by
    rw [hq]
    linear_combination (ρ (0,0) (0,0) + ρ (1,1) (1,1) * (star e * e) + z * e + star z * star e) * c2
      + (1/2 : ℂ) * ρ (1,1) (1,1) * hee + (1/2 : ℂ) * hz + (1/2 : ℂ) * hz'
  rw [hq2]
  -- minor
  set w : Key 2 → ℂ := fun a => if a = (0,0) then 1 else if a = (1,1) then -e else 0 with hw
  have hm := quad ρ w (by simp [hw]) (by simp [hw])
  have hw0 : w (0,0) = 1 := by simp [hw]
  have hw1 : w (1,1) = -e := by simp [hw]
  rw [hw0, hw1, hH] at hm
  have hm2 : star w ⬝ᵥ (ρ *ᵥ w) = ρ (0,0) (0,0) + ρ (1,1) (1,1) - 2 * (‖z‖ : ℂ) := by
    rw [hm]
    simp only [star_neg, star_one]
    linear_combination ρ (1,1) (1,1) * hee - hz - hz'
  have hnn := (Complex.nonneg_iff.mp (hρ.1.dotProduct_mulVec_nonneg w)).1
  rw [hm2] at hnn
  have hre : ((ρ (0,0) (0,0) + ρ (1,1) (1,1) + 2 * (‖z‖ : ℂ)) / 2).re =
      ((ρ (0,0) (0,0)).re + (ρ (1,1) (1,1)).re + 2 * ‖z‖) / 2 := by
    simp
  rw [hre]
  simp at hnn
  linarith

lemma bv_norm (θ : Key 2 → ℝ) : star (bv θ) ⬝ᵥ bv θ = 1 := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, bv, Pi.star_apply]
  simp only [Fin.isValue, if_true, show ((0 : Fin 2) = 1) = False by decide,
    show ((1 : Fin 2) = 0) = False by decide, if_false, star_zero, mul_zero, add_zero, zero_add,
    star_mul, star_c]
  have h1 := star_exp_mul (θ (0,0))
  have h2 := star_exp_mul (θ (1,1))
  linear_combination (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (h1 + h2)
    + 2 * c2

lemma bv_sq (θ : Key 2 → ℝ) (x : Key 2) :
    bv θ x * star (bv θ x) = if x.1 = x.2 then (2 : ℂ)⁻¹ else 0 := by
  by_cases hx : x.1 = x.2
  · simp only [bv, hx, if_true, star_mul, star_c]
    have h1 := star_exp_mul (θ x)
    have := c2
    linear_combination (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * h1 + this
  · simp [bv, hx]

theorem dir_back (θ : Key 2 → ℝ) {e : ℕ} (ψ : EuclideanSpace ℂ ((Key 2 × Unit) × Fin e))
    (htr : traceRight (pureDensity ψ) = singletonShield (phaseBell θ)) :
    ∃ omega : Op (Fin e), IsDensityMatrix omega ∧ associatedCCQ ψ = idealCCQ omega := by
  set b := bv θ with hb
  set B := vecMulVec b (star b) with hBdef
  set Ψ : Matrix (Key 2) (Fin e) ℂ := Matrix.of fun x f => ψ ((x, ()), f) with hΨdef
  have hPP : Ψ * Ψᴴ = B := by
    ext x y
    have := congrFun (congrFun htr (x, ())) (y, ())
    simp only [traceRight, pureDensity, singletonShield, Matrix.of_apply] at this
    rw [phaseBell_eq] at this
    simpa [Matrix.mul_apply, Ψ, Complex.star_def] using this
  have hBB : B * B = B := by
    rw [hBdef, vecMulVec_mul_vecMulVec, bv_norm, one_smul]
  have hX : (1 - B) * Ψ * ((1 - B) * Ψ)ᴴ = 0 := by
    rw [conjTranspose_mul]
    rw [show (1 - B) * Ψ * (Ψᴴ * (1 - B)ᴴ) = (1 - B) * (Ψ * Ψᴴ) * (1 - B)ᴴ by
      simp only [Matrix.mul_assoc], hPP, sub_mul, one_mul, hBB, sub_self, zero_mul]
  have hX0 := Matrix.self_mul_conjTranspose_eq_zero.mp hX
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, hBdef, vecMulVec_mul] at hX0
  obtain ⟨χ, hΨ⟩ : ∃ χ, Ψ = vecMulVec b χ := ⟨_, hX0⟩
  have hent : ∀ x f, ψ ((x, ()), f) = b x * χ f := fun x f => by
    have := congrFun (congrFun hΨ x) f
    simpa [Ψ, vecMulVec_apply] using this
  have hχ : χ ⬝ᵥ star χ = 1 := by
    have h1 := congrArg Matrix.trace hPP
    rw [hΨ, conjTranspose_vecMulVec, vecMulVec_mul_vecMulVec, hBdef, trace_vecMulVec,
      trace_vecMulVec, dotProduct_smul, dotProduct_comm b (star b), bv_norm] at h1
    simpa using h1
  refine ⟨vecMulVec χ (star χ), ⟨posSemidef_vecMulVec_self_star χ, ?_⟩, ?_⟩
  · rw [trace_vecMulVec, hχ]
  · ext ⟨x, f⟩ ⟨y, f'⟩
    simp only [associatedCCQ, idealCCQ, Fintype.sum_unique]
    have hd : (default : Unit) = () := rfl
    rw [hd, hent, hent]
    by_cases hxy : x = y
    · subst hxy
      have hs := bv_sq θ x
      by_cases hx : x.1 = x.2
      · simp only [hx, if_true, and_self, vecMulVec_apply, ← Complex.star_def]
        rw [hx] at hs; simp only [if_true] at hs
        push_cast
        rw [star_mul]
        linear_combination (χ f * star (χ f')) * hs
      · simp only [hx, if_true, and_false, if_false, ← Complex.star_def]
        rw [if_neg hx] at hs
        rw [star_mul]
        linear_combination (χ f * star (χ f')) * hs
    · simp [hxy]

lemma good_cases : ∀ x : Key 2, x.1 = x.2 → x = (0,0) ∨ x = (1,1) := by decide

theorem dir_fwd (ρ : Op (Key 2)) (hρ : IsDensityMatrix ρ) (hK : HasKey (singletonShield ρ)) :
    ∃ θ : Key 2 → ℝ, ρ = phaseBell θ := by
  set S := cfc Real.sqrt ρ with hSdef
  have hSH : Sᴴ = S := (sqrt_psd ρ).1
  have hSS : S * S = ρ := sqrt_mul_sqrt hρ.1
  have hG : ∀ x y, ρ x y = ∑ k, S x k * star (S y k) := by
    intro x y
    rw [← hSS, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [← Matrix.conjTranspose_apply, hSH]
  let j : Fin (2*2) ≃ Fin 2 × Fin 2 := finProdFinEquiv.symm
  let ψ : EuclideanSpace ℂ ((Key 2 × Unit) × Fin (2*2)) :=
    WithLp.toLp 2 (fun p => S p.1.1 (j p.2))
  have hψ : ∀ p, ψ p = S p.1.1 (j p.2) := fun p => rfl
  have hdiag : ∀ x, ∑ k, ‖S x k‖ ^ 2 = (ρ x x).re := fun x => by
    rw [hG x x, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
    norm_cast
  have hstate : IsState ψ := by
    unfold IsState
    rw [EuclideanSpace.norm_eq]
    have : ∑ p, ‖ψ p‖ ^ 2 = 1 := by
      rw [Fintype.sum_prod_type (fun p : (Key 2 × Unit) × Fin (2*2) => ‖ψ p‖ ^ 2),
        Fintype.sum_prod_type (fun a : Key 2 × Unit => ∑ f : Fin (2*2), ‖ψ (a, f)‖ ^ 2)]
      simp only [hψ, Fintype.sum_unique]
      rw [Finset.sum_congr rfl fun x _ => Equiv.sum_comp j (fun k => ‖S x k‖ ^ 2)]
      simp only [hdiag]
      rw [← Complex.re_sum]
      have := hρ.2
      unfold Matrix.trace at this
      simp only [Matrix.diag] at this
      rw [this]; simp
    rw [this, Real.sqrt_one]
  have htr : traceRight (pureDensity ψ) = singletonShield ρ := by
    ext ⟨x, u⟩ ⟨y, u'⟩
    simp only [traceRight, pureDensity, Matrix.of_apply, singletonShield, hψ]
    rw [hG x y]
    simp only [Complex.star_def]
    exact Equiv.sum_comp j (fun k => S x k * (starRingEnd ℂ) (S y k))
  obtain ⟨ω, -, hA⟩ := hK (2*2) (by norm_num) ψ hstate htr
  have hE : ∀ x k k', S x k * star (S x k') =
      if x.1 = x.2 then (2:ℂ)⁻¹ * ω (j.symm k) (j.symm k') else 0 := by
    intro x k k'
    have := congrFun (congrFun hA (x, j.symm k)) (x, j.symm k')
    simp only [associatedCCQ, idealCCQ, hψ, Fintype.sum_unique, if_true, true_and,
      Equiv.apply_symm_apply] at this
    rw [Complex.star_def]
    convert this using 2
    push_cast; ring
  have hrow : ∀ x : Key 2, x.1 ≠ x.2 → ∀ k, S x k = 0 := by
    intro x hx k
    have := hE x k k
    rw [if_neg hx, Complex.star_def, Complex.mul_conj'] at this
    have h2 : ‖S x k‖ = 0 := by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    exact norm_eq_zero.mp h2
  have hM : ∀ k k', S (0,0) k * star (S (0,0) k') = S (1,1) k * star (S (1,1) k') := by
    intro k k'; rw [hE, hE]; simp
  have hz1 : ∀ x y : Key 2, x.1 ≠ x.2 → ρ x y = 0 := by
    intro x y hx; rw [hG]; simp [hrow x hx]
  have hz2 : ∀ x y : Key 2, y.1 ≠ y.2 → ρ x y = 0 := by
    intro x y hy; rw [hG]; simp [hrow y hy]
  have heq : ρ (0,0) (0,0) = ρ (1,1) (1,1) := by
    rw [hG, hG]; exact Finset.sum_congr rfl fun k _ => hM k k
  have htr1 : ρ (0,0) (0,0) + ρ (1,1) (1,1) = 1 := by
    have := hρ.2
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two] at this
    rw [hz1 (0,1) (0,1) (by decide), hz1 (1,0) (1,0) (by decide)] at this
    linear_combination this
  have h00 : ρ (0,0) (0,0) = 1/2 := by linear_combination (htr1 + heq) / 2
  have h11 : ρ (1,1) (1,1) = 1/2 := by linear_combination (htr1 - heq) / 2
  have hprod : ρ (1,1) (0,0) * ρ (0,0) (1,1) = ρ (1,1) (1,1) * ρ (1,1) (1,1) := by
    rw [hG (1,1) (0,0), hG (0,0) (1,1), hG (1,1) (1,1), Finset.sum_mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    have := hM k' k
    linear_combination (S (1,1) k * star (S (1,1) k')) * this
  have hH : ρ (0,0) (1,1) = star (ρ (1,1) (0,0)) := (hρ.1.isHermitian.apply (0,0) (1,1)).symm
  set z := ρ (1,1) (0,0) with hzdef
  have hzn : ‖z‖ = 1/2 := by
    rw [hH, h11, Complex.star_def, Complex.mul_conj'] at hprod
    have : ‖z‖ ^ 2 = (1/2) ^ 2 := by
      have := congrArg Complex.re hprod
      norm_num at this
      norm_cast at this ⊢
      linarith
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp this
  set φ := Complex.arg z with hφ
  set e := Complex.exp ((φ : ℂ) * Complex.I) with he
  have hze : z = e / 2 := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [hzn]; push_cast; ring
  have hee : star e * e = 1 := star_exp_mul φ
  refine ⟨fun a => if a = (1,1) then φ else 0, ?_⟩
  have hb0 : bv (fun a => if a = (1,1) then φ else 0) (0,0) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    simp [bv]
  have hb1 : bv (fun a => if a = (1,1) then φ else 0) (1,1) =
      e * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    simp [bv, he]
  rw [phaseBell_eq]
  ext x y
  rw [vecMulVec_apply, Pi.star_apply]
  by_cases hx : x.1 = x.2
  swap
  · rw [hz1 x y hx]; simp [bv, hx]
  by_cases hy : y.1 = y.2
  swap
  · rw [hz2 x y hy]; simp [bv, hy]
  have hc := c2
  rcases good_cases x hx with rfl | rfl <;> rcases good_cases y hy with rfl | rfl
  · rw [hb0, h00, star_c]; linear_combination -hc
  · rw [hb0, hb1, star_mul, star_c]
    refine hH.trans ?_
    rw [hze, star_div₀, star_ofNat]
    linear_combination (-star e) * hc
  · rw [hb0, hb1, star_c]
    refine hze.trans ?_
    linear_combination (-e) * hc
  · rw [hb1, h11, star_mul, star_c]
    linear_combination (-1 : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * hee - hc

theorem main (rho : Op (Key 2)) (hrho : IsDensityMatrix rho) :
    (HasKey (singletonShield rho) ↔ ∃ theta : Key 2 → ℝ, rho = phaseBell theta) ∧
    (∀ eps : ℝ, 0 < eps → ‖rho (0,0) (1,1)‖ > 1/2-eps →
      ∃ theta : Key 2 → ℝ, (rootFidelity rho (phaseBell theta))^2 ≥ 1-2*eps) := by
  refine ⟨⟨dir_fwd rho hrho, ?_⟩, fun eps _ h => clause2 rho hrho eps h⟩
  rintro ⟨θ, rfl⟩ e _ ψ _ htr
  exact dir_back θ ψ htr

end A3AT

end QAlgorithms.Papers.Independent.Dependency50.P24

end

open scoped Matrix ComplexOrder in
open QAlgorithms.Papers.Independent.Dependency50.P24 in
theorem solution (rho : QAlgorithms.Papers.Independent.Information100.P21.Op (Key 2))
    (hrho : QAlgorithms.IsDensityMatrix rho) :
    (HasKey (singletonShield rho) ↔ ∃ theta : Key 2 → ℝ, rho = phaseBell theta) ∧
    (∀ eps : ℝ, 0 < eps → ‖rho (0,0) (1,1)‖ > 1/2-eps →
      ∃ theta : Key 2 → ℝ, (QAlgorithms.rootFidelity rho (phaseBell theta))^2 ≥ 1-2*eps) :=
  QAlgorithms.Papers.Independent.Dependency50.P24.A3AT.main rho hrho

#print axioms solution
