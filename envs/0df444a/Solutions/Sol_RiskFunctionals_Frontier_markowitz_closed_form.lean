-- Prove2me | solution 1 for RiskFunctionals.Frontier.markowitz_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:36:13.130177+00:00
-- url     : https://prove2.me/submissions/ea79f629-93ca-4220-9d05-36acab0e6561

import Mathlib
import Definitions.Def_RiskFunctionals_Frontier_MeanVariance

open MeasureTheory ProbabilityTheory Matrix RiskFunctionals.Frontier

section g79m
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ}
  {ξ : Fin M → Ω → ℝ}

lemma g79m_memLp (hξ : ∀ m, MemLp (ξ m) 2 P) (c : ℝ) (a : Fin M → ℝ) :
    MemLp (fun ω => c + ∑ m, a m * ξ m ω) 2 P := by
  have h1 : MemLp (fun ω => ∑ m, a m * ξ m ω) 2 P := by
    have := memLp_finsetSum' (μ := P) (p := 2) Finset.univ (fun m _ => (hξ m).const_mul (a m))
    convert this using 1; ext ω; simp [Finset.sum_apply]
  exact (memLp_const c).add h1

lemma g79m_mean (hξ : ∀ m, MemLp (ξ m) 2 P) (c : ℝ) (a : Fin M → ℝ) :
    ∫ ω, (c + ∑ m, a m * ξ m ω) ∂P = c + a ⬝ᵥ meanVector P ξ := by
  have hi : ∀ m, Integrable (fun ω => a m * ξ m ω) P :=
    fun m => ((hξ m).integrable (by norm_num)).const_mul (a m)
  rw [integral_add (integrable_const c) (integrable_finset_sum _ (fun m _ => hi m)),
    integral_finset_sum _ (fun m _ => hi m)]
  simp [dotProduct, meanVector, integral_const_mul]

lemma g79m_cov (hξ : ∀ m, MemLp (ξ m) 2 P) (c d : ℝ) (a b : Fin M → ℝ) :
    covariance (fun ω => c + ∑ m, a m * ξ m ω) (fun ω => d + ∑ m, b m * ξ m ω) P =
      a ⬝ᵥ covMatrix P ξ *ᵥ b := by
  have hA : ∀ (a : Fin M → ℝ), MemLp (fun ω => ∑ m, a m * ξ m ω) 2 P := by
    intro a; simpa using g79m_memLp hξ 0 a
  rw [covariance_const_add_left ((hA a).integrable (by norm_num)),
    covariance_const_add_right ((hA b).integrable (by norm_num)),
    covariance_fun_sum_fun_sum (fun m => (hξ m).const_mul (a m)) (fun m => (hξ m).const_mul (b m))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, dotProduct, mulVec,
    covMatrix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma g79m_var (hξ : ∀ m, MemLp (ξ m) 2 P) (c : ℝ) (a : Fin M → ℝ) :
    variance (fun ω => c + ∑ m, a m * ξ m ω) P = a ⬝ᵥ covMatrix P ξ *ᵥ a := by
  rw [← covariance_self (g79m_memLp hξ c a).aemeasurable, g79m_cov hξ]

lemma g79m_symm : (covMatrix P ξ)ᵀ = covMatrix P ξ := by
  ext i j; simp [covMatrix, covariance_comm]

lemma g79m_psd (hξ : ∀ m, MemLp (ξ m) 2 P) : (covMatrix P ξ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simpa [Matrix.IsHermitian] using g79m_symm (P := P) (ξ := ξ)
  · have := g79m_var hξ 0 x
    simp only [star_trivial]
    rw [← this]; exact variance_nonneg _ _

lemma g79m_posDef (hξ : ∀ m, MemLp (ξ m) 2 P) (hC : IsUnit (covMatrix P ξ)) :
    (covMatrix P ξ).PosDef := (g79m_psd hξ).posDef_iff_isUnit.mpr hC

lemma g79m_inv_pos (hξ : ∀ m, MemLp (ξ m) 2 P) (hC : IsUnit (covMatrix P ξ))
    {v : Fin M → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ (covMatrix P ξ)⁻¹ *ᵥ v := by
  have h := ((g79m_posDef hξ hC).inv)
  have := (Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hv
  simpa using this

lemma g79m_mul_inv (hC : IsUnit (covMatrix P ξ)) (v : Fin M → ℝ) :
    covMatrix P ξ *ᵥ ((covMatrix P ξ)⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hC), one_mulVec]

lemma g79m_inv_symm (v w : Fin M → ℝ) :
    v ⬝ᵥ (covMatrix P ξ)⁻¹ *ᵥ w = w ⬝ᵥ (covMatrix P ξ)⁻¹ *ᵥ v := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, Matrix.transpose_nonsing_inv,
    g79m_symm]

/-- quadratic form symmetric: `a ⬝ C b = b ⬝ C a` -/
lemma g79m_C_symm (a b : Fin M → ℝ) :
    a ⬝ᵥ covMatrix P ξ *ᵥ b = b ⬝ᵥ covMatrix P ξ *ᵥ a := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, g79m_symm]

end g79m


lemma g79m_quad {M : ℕ} (C : Matrix (Fin M) (Fin M) ℝ) (hC : Cᵀ = C) (x z : Fin M → ℝ) :
    (x + z) ⬝ᵥ C *ᵥ (x + z) = x ⬝ᵥ C *ᵥ x + 2 * (z ⬝ᵥ C *ᵥ x) + z ⬝ᵥ C *ᵥ z := by
  have : x ⬝ᵥ C *ᵥ z = z ⬝ᵥ C *ᵥ x := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hC]
  simp only [mulVec_add, dotProduct_add, add_dotProduct, this]; ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : ℕ} (ξ : Fin M → Ω → ℝ) (hξ : ∀ m, MemLp (ξ m) 2 P)
    (hC : IsUnit (covMatrix P ξ))
    (hr : ¬ ∃ k : ℝ, meanVector P ξ = fun _ => k) :
    let C := covMatrix P ξ
    let r := meanVector P ξ
    let one : Fin M → ℝ := fun _ => 1
    let a := r ⬝ᵥ C⁻¹ *ᵥ r
    let b := r ⬝ᵥ C⁻¹ *ᵥ one
    let c := one ⬝ᵥ C⁻¹ *ᵥ one
    let d := a * c - b ^ 2
    let xstar : ℝ → Fin M → ℝ := fun μ =>
      μ • ((c / d) • C⁻¹ *ᵥ r - (b / d) • C⁻¹ *ᵥ one) +
        ((a / d) • C⁻¹ *ᵥ one - (b / d) • C⁻¹ *ᵥ r)
    (∀ μ : ℝ, IsSolution420 C r μ (xstar μ)) ∧
    (∀ (μ : ℝ) (x : Fin M → ℝ), IsSolution420 C r μ x → x = xstar μ) ∧
    (∀ μ₁ μ₂ : ℝ, μ₁ ≠ μ₂ → ∀ (μ : ℝ) (x : Fin M → ℝ), IsSolution420 C r μ x →
      ∃ t : ℝ, x = t • xstar μ₁ + (1 - t) • xstar μ₂) ∧
    (∀ μ : ℝ, ∫ ω, portfolioReturn ξ (xstar μ) ω ∂P = μ ∧
      variance (portfolioReturn ξ (xstar μ)) P = (μ ^ 2 * c - 2 * μ * b + a) / d) := by
  intro C r one a b c d xstar
  have hsym : Cᵀ = C := g79m_symm
  have hPD : C.PosDef := g79m_posDef hξ hC
  have hpos : ∀ z : Fin M → ℝ, z ≠ 0 → 0 < z ⬝ᵥ C *ᵥ z := by
    intro z hz; have := (Matrix.posDef_iff_dotProduct_mulVec.mp hPD).2 hz; simpa using this
  set A := C⁻¹ with hA
  set Ar := A *ᵥ r with hAr
  set A1 := A *ᵥ one with hA1
  have hCAr : C *ᵥ Ar = r := g79m_mul_inv hC r
  have hCA1 : C *ᵥ A1 = one := g79m_mul_inv hC one
  have h1r : one ⬝ᵥ Ar = b := g79m_inv_symm one r
  have hone : one ≠ 0 := by
    intro h; apply hr; refine ⟨0, funext fun i => ?_⟩
    have := congrFun h i; simp [one] at this
  have hcpos : 0 < c := g79m_inv_pos hξ hC hone
  -- strict Cauchy-Schwarz: d > 0
  have hdpos : 0 < d := by
    have hne : r - (b / c) • one ≠ 0 := by
      intro h; apply hr; refine ⟨b / c, funext fun i => ?_⟩
      have := congrFun h i; simp [one] at this; linarith
    have := g79m_inv_pos hξ hC hne
    have e : (r - (b / c) • one) ⬝ᵥ A *ᵥ (r - (b / c) • one) = a - b ^ 2 / c := by
      simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      have e1 : r ⬝ᵥ Ar = a := rfl
      have e2 : r ⬝ᵥ A1 = b := rfl
      have e3 : one ⬝ᵥ A1 = c := rfl
      rw [h1r, e1, e2, e3]; field_simp; ring
    rw [e] at this
    have : 0 < (a - b ^ 2 / c) * c := mul_pos this hcpos
    simp only [d]; field_simp at this; linarith
  have hd : d ≠ 0 := hdpos.ne'
  have hx : ∀ μ, xstar μ = ((μ * c - b) / d) • Ar + ((a - μ * b) / d) • A1 := by
    intro μ; funext i; simp only [xstar, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp; ring
  have hrx : ∀ μ, r ⬝ᵥ xstar μ = μ := by
    intro μ; rw [hx]; simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    show (μ * c - b) / d * a + (a - μ * b) / d * b = μ
    field_simp; simp only [d]; ring
  have h1x : ∀ μ, one ⬝ᵥ xstar μ = 1 := by
    intro μ; rw [hx]; simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, h1r]
    show (μ * c - b) / d * b + (a - μ * b) / d * c = 1
    field_simp; simp only [d]; ring
  have hCx : ∀ μ, C *ᵥ xstar μ = ((μ * c - b) / d) • r + ((a - μ * b) / d) • one := by
    intro μ; rw [hx, mulVec_add, mulVec_smul, mulVec_smul, hCAr, hCA1]
  -- for z with r ⬝ z = 0, one ⬝ z = 0: z ⬝ C x* = 0
  have hzx : ∀ μ z, r ⬝ᵥ z = 0 → one ⬝ᵥ z = 0 → z ⬝ᵥ C *ᵥ xstar μ = 0 := by
    intro μ z h1 h2
    rw [hCx, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm z r,
      dotProduct_comm z one, h1, h2]; simp
  have hsol : ∀ μ, IsSolution420 C r μ (xstar μ) := by
    intro μ
    refine ⟨hrx μ, h1x μ, fun y hy1 hy2 => ?_⟩
    have := g79m_quad C hsym (xstar μ) (y - xstar μ)
    rw [add_sub_cancel, hzx μ (y - xstar μ) (by rw [dotProduct_sub, hy1, hrx]; ring)
      (by rw [dotProduct_sub, hy2, h1x]; ring)] at this
    have h0 : 0 ≤ (y - xstar μ) ⬝ᵥ C *ᵥ (y - xstar μ) := by
      by_cases hz : y - xstar μ = 0
      · rw [hz]; simp
      · exact (hpos _ hz).le
    linarith
  have huniq : ∀ (μ : ℝ) (x : Fin M → ℝ), IsSolution420 C r μ x → x = xstar μ := by
    intro μ x ⟨hx1, hx2, hmin⟩
    have hle := hmin (xstar μ) (hrx μ) (h1x μ)
    have := g79m_quad C hsym (xstar μ) (x - xstar μ)
    rw [add_sub_cancel, hzx μ (x - xstar μ) (by rw [dotProduct_sub, hx1, hrx]; ring)
      (by rw [dotProduct_sub, hx2, h1x]; ring)] at this
    by_contra hne
    have := hpos (x - xstar μ) (sub_ne_zero.mpr hne)
    linarith
  refine ⟨hsol, huniq, ?_, ?_⟩
  · intro μ₁ μ₂ h12 μ x hxs
    refine ⟨(μ - μ₂) / (μ₁ - μ₂), ?_⟩
    rw [huniq μ x hxs]
    have h12' : μ₁ - μ₂ ≠ 0 := sub_ne_zero.mpr h12
    funext i; simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp; ring
  · intro μ
    have hpr : portfolioReturn ξ (xstar μ) = fun ω => 0 + ∑ m, xstar μ m * ξ m ω := by
      funext ω; simp [portfolioReturn]
    rw [hpr, g79m_mean hξ, g79m_var hξ]
    refine ⟨by rw [zero_add, dotProduct_comm]; exact hrx μ, ?_⟩
    rw [hCx, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm _ r, hrx,
      dotProduct_comm _ one, h1x]
    simp only [smul_eq_mul]
    field_simp; ring
