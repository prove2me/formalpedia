-- Prove2me | solution 1 for SpikedWishart.Separated.spiked_block_psd_limit_of_sesquilinear_clt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:19:44.857734+00:00
-- url     : https://prove2.me/submissions/caa528a6-5131-4f4a-89fa-a01a629f978f

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE

set_option autoImplicit false
set_option linter.all false

open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder
open Filter Topology MeasureTheory
open Filter Topology MeasureTheory Set

namespace SpikedWishart.Separated.Lib

-- ===== from ChildStatements.lean =====
section

/-- Q4 (BBP Def. 1.2 / (26)-(28), Weyl integration formula for the GUE): for the `k × k` GUE
`H = (Z + Zᴴ)/√2` built from i.i.d. standard complex Gaussians (diagonal `N(0,1)`, off-diagonal
`E|H_ij|² = 1`, density `∝ exp(-tr H²/2)`), `P(λ_max(H) ≤ x) = G k x`; `λ_max ≤ x` is written as
`x·1 - H ⪰ 0`. -/
def Q4_gueMax : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ x : ℝ,
    (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x

/-- Q3 (CLT for Gaussian sesquilinear forms; Bai-Yao 2008 Ann. IHP Thm 7.1, Paul 2007 Lemma):
`H` the `r × M` matrix of i.i.d. standard complex Gaussians, `A` deterministic Hermitian with
`-C ≤ A ≤ C` and `s² = (1/M) tr A² ≥ s₀ > 0`; then `(√M/s)((1/M) H A Hᴴ - ((1/M) tr A)·1)`
converges in law to the `r × r` GUE `(Z + Zᴴ)/√2`. -/
def Q3_sesqCLT : Prop :=
  ∀ (r : ℕ) (C s₀ : ℝ), 0 < s₀ → ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    ∀ f : Matrix (Fin r) (Fin r) ℂ → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
    Tendsto (fun n => ∫ X, f (((Real.sqrt (M n) / Real.sqrt (((A n * A n).trace).re / M n) : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))
        ∂(SpikedWishart.SoftEdge.sampleLaw (M n) r))
      atTop (𝓝 (∫ Z, f ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ))
        ∂(SpikedWishart.SoftEdge.sampleLaw r r)))

/-- DL (conditional limit of the spiked block; Baik-Ben Arous-Peche 2005, proof of Thm 1.1(b), Section 3,
the step after conditioning on the null block): for deterministic Hermitian `A_n` with `-C ≤ A_n ≤ C`,
`s₀ ≤ (1/M) tr A_n² ≤ S₁`, spike block `D_n = diag(L_n,…,L_n, d)` and shifts `x_n` with
`√M (x_n - L_n (1/M) tr A_n) / (L_n √((1/M) tr A_n²)) → t`, the probability that
`x_n - (1/M) D^{1/2} Hᵀ A_n H̄ D^{1/2}` is positive semidefinite (`H` an `M × (k+q)` complex Gaussian array)
tends to `G k t`. -/
def DL_blockLimit : Prop :=
  ∀ (k q : ℕ), 1 ≤ k → ∀ (C s₀ S₁ c x₀ : ℝ), 0 < s₀ → 0 < c → 0 < x₀ →
    ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    (∀ n, ((A n * A n).trace).re / M n ≤ S₁) →
    ∀ (L : ℕ → ℝ), (∀ n, c ≤ L n ∧ L n ≤ C) →
    ∀ (D : ℕ → Fin (k + q) → ℝ), (∀ n i, D n (Fin.castAdd q i) = L n) →
    (∀ n j, c ≤ D n (Fin.natAdd k j) ∧ D n (Fin.natAdd k j) ≤ L n - c) →
    ∀ (x : ℕ → ℝ), (∀ n, x₀ ≤ x n) → ∀ (t : ℝ),
    Tendsto (fun n => Real.sqrt (M n) * (x n - L n * (((A n).trace).re / M n)) /
        (L n * Real.sqrt (((A n * A n).trace).re / M n))) atTop (𝓝 t) →
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
      {X | ((x n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
        (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef})
      atTop (𝓝 (G k t))

/-- Child: the spiked-block limit DL from the sesquilinear CLT Q3 and the GUE law Q4. -/
def DL_of : Prop := Q3_sesqCLT → Q4_gueMax → DL_blockLimit

end

-- ===== from Slutsky.lean =====
section

/-- P8 (Slutsky for distribution functions): if `P(Y_n ≤ x) → F x` at every `x`, `F` is continuous at
`x`, and `Z_n - Y_n → 0` in probability, then `P(Z_n ≤ x) → F x`. The sample spaces may depend on `n`. -/
theorem cdf_slutsky {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsFiniteMeasure (μ n)] (Y Z : ∀ n, Ω n → ℝ) (F : ℝ → ℝ) (x : ℝ) (hF : ContinuousAt F x)
    (hY : ∀ y, Tendsto (fun n => (μ n).real {ω | Y n ω ≤ y}) atTop (𝓝 (F y)))
    (hZY : ∀ ε, 0 < ε → Tendsto (fun n => (μ n).real {ω | ε < |Z n ω - Y n ω|}) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real {ω | Z n ω ≤ x}) atTop (𝓝 (F x)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.mp hF (η / 3) (by positivity)
  have hε : 0 < δ / 2 := by positivity
  have h1 : dist (F (x + δ / 2)) (F x) < η / 3 := hδF (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hε]; linarith only [hδ])
  have h2 : dist (F (x - δ / 2)) (F x) < η / 3 := hδF (by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hε]; linarith only [hδ])
  have e1 := (Metric.tendsto_nhds.mp (hY (x + δ / 2))) (η / 3) (by positivity)
  have e2 := (Metric.tendsto_nhds.mp (hY (x - δ / 2))) (η / 3) (by positivity)
  have e3 := (Metric.tendsto_nhds.mp (hZY (δ / 2) hε)) (η / 3) (by positivity)
  filter_upwards [e1, e2, e3] with n h1n h2n h3n
  rw [Real.dist_eq] at h1 h2 h1n h2n h3n ⊢
  have hbad0 : 0 ≤ (μ n).real {ω | δ / 2 < |Z n ω - Y n ω|} := measureReal_nonneg
  rw [sub_zero, abs_of_nonneg hbad0] at h3n
  have up : (μ n).real {ω | Z n ω ≤ x} ≤ (μ n).real {ω | Y n ω ≤ x + δ / 2} +
      (μ n).real {ω | δ / 2 < |Z n ω - Y n ω|} := by
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hc
    rw [not_or, not_le, not_lt] at hc
    have := (abs_le.mp hc.2).1
    linarith only [hc.1, this, hω]
  have down : (μ n).real {ω | Y n ω ≤ x - δ / 2} ≤ (μ n).real {ω | Z n ω ≤ x} +
      (μ n).real {ω | δ / 2 < |Z n ω - Y n ω|} := by
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hc
    rw [not_or, not_le, not_lt] at hc
    have := (abs_le.mp hc.2).2
    linarith only [hc.1, this, hω]
  rw [abs_lt] at h1 h2 h1n h2n ⊢
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h1n.1, h1n.2, h2n.1, h2n.2, h3n, up, down]

end

-- ===== from LamMax.lean =====
section

variable {k : ℕ}

/-- The quadratic form of a Hermitian matrix is real. -/
theorem im_quad_eq_zero {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) (x : Fin k → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  have h : star (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : star (A j i) = A i j := by
      have := congrFun (congrFun hA i) j
      simpa [conjTranspose_apply] using this
    rw [hij]; ring
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem psd_iff_re {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ x : Fin k → ℂ, 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x
    exact (Complex.nonneg_iff.mp (h x)).1
  · intro h
    refine ⟨hA, fun x => Complex.nonneg_iff.mpr ⟨h x, (im_quad_eq_zero hA x).symm⟩⟩

/-- The Hermitian part `(H + Hᴴ)/2` of an array. -/
noncomputable def herm (H : Fin k → Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  (1 / 2 : ℂ) • (Matrix.of H + (Matrix.of H)ᴴ)

theorem herm_isHermitian (H : Fin k → Fin k → ℂ) : (herm H).IsHermitian := by
  unfold herm
  ext i j
  simp [conjTranspose_apply] <;> ring

theorem herm_of_isHermitian (H : Fin k → Fin k → ℂ) (hH : (Matrix.of H).IsHermitian) :
    herm H = Matrix.of H := by
  unfold herm
  rw [hH.eq]
  ext i j
  simp [Matrix.smul_apply] <;> ring

/-- The unit sphere `Σ |v_i|² = 1`. -/
def sph (k : ℕ) : Set (Fin k → ℂ) := {v | ∑ i, Complex.normSq (v i) = 1}

theorem isCompact_sph : IsCompact (sph k) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin k → ℂ)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : Complex.normSq (v i) ≤ 1 := by
      rw [← hv]
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    rw [Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (v i)]

/-- The quadratic form, as a jointly continuous function. -/
noncomputable def quad (H : Fin k → Fin k → ℂ) (v : Fin k → ℂ) : ℝ := (star v ⬝ᵥ (herm H *ᵥ v)).re

theorem continuous_quad : Continuous ↿(quad (k := k)) := by
  unfold quad herm
  simp only [dotProduct, mulVec, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    conjTranspose_apply, Pi.star_apply]
  fun_prop

/-- `λ_max` of the Hermitian part, as a sup over the unit sphere (continuous). -/
noncomputable def phi (H : Fin k → Fin k → ℂ) : ℝ := sSup (quad H '' sph k)

theorem continuous_phi : Continuous (phi (k := k)) :=
  isCompact_sph.continuous_sSup continuous_quad

theorem re_star_self (x : Fin k → ℂ) : (star x ⬝ᵥ x).re = ∑ i, Complex.normSq (x i) := by
  simp [dotProduct, Complex.normSq_apply, Complex.mul_re]

theorem quad_smul (H : Fin k → Fin k → ℂ) (x : Fin k → ℂ) (a : ℝ) :
    quad H ((a : ℂ) • x) = a ^ 2 * quad H x := by
  unfold quad
  rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im]
  ring

theorem phi_le_iff (hk : 1 ≤ k) (H : Fin k → Fin k → ℂ) (t : ℝ) :
    phi H ≤ t ↔ ((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - herm H).PosSemidef := by
  have hherm : ((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - herm H).IsHermitian := by
    refine IsHermitian.sub ?_ (herm_isHermitian H)
    simp [IsHermitian, conjTranspose_smul]
  have hquad : ∀ x : Fin k → ℂ, (star x ⬝ᵥ (((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - herm H) *ᵥ x)).re
      = t * ∑ i, Complex.normSq (x i) - quad H x := by
    intro x
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, Complex.sub_re,
      ← re_star_self]
    unfold quad
    simp [Complex.mul_re]
  have hne : (sph k).Nonempty := by
    refine ⟨Pi.single ⟨0, hk⟩ 1, ?_⟩
    simp [sph, Pi.single_apply, Finset.sum_ite_eq']
  have hbdd : BddAbove (quad H '' sph k) :=
    (isCompact_sph.image_of_continuousOn
      (continuous_quad.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn).bddAbove
  rw [psd_iff_re hherm, phi, csSup_le_iff hbdd (hne.image _)]
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hquad]
  constructor
  · intro h x
    by_cases hx : ∑ i, Complex.normSq (x i) = 0
    · have hx0 : x = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp hx i
          (Finset.mem_univ i)
        simpa using this
      subst hx0
      simp [quad]
    · have hpos : 0 < ∑ i, Complex.normSq (x i) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (x j)) (Ne.symm hx)
      set s := ∑ i, Complex.normSq (x i)
      set a := 1 / Real.sqrt s
      have ha2 : a ^ 2 = 1 / s := by
        rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
      have hv : ((a : ℂ) • x) ∈ sph k := by
        simp only [sph, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
          Complex.normSq_ofReal, ← Finset.mul_sum]
        rw [← sq, ha2]; field_simp; rfl
      have := h _ hv
      rw [quad_smul, ha2] at this
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos] at this
      linarith
  · intro h v hv
    have := h v
    rw [show ∑ i, Complex.normSq (v i) = 1 from hv] at this
    linarith

/-- The `k × k` GUE matrix built from a Gaussian array. -/
noncomputable def gueMat (Z : Fin k → Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)

theorem gueMat_isHermitian (Z : Fin k → Fin k → ℂ) : (gueMat Z).IsHermitian := by
  unfold gueMat
  ext i j
  simp [conjTranspose_apply] <;> ring

theorem continuous_gueMat : Continuous (gueMat (k := k)) := by
  unfold gueMat
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, conjTranspose_apply, smul_eq_mul]
  fun_prop

/-- Under Q4, the law of `λ_max(GUE_k)` (as `phi`) has distribution function `G k`. -/
theorem gue_phi_cdf (hk : 1 ≤ k)
    (hQ4 : ∀ x : ℝ, (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x) (s : ℝ) :
    (SpikedWishart.SoftEdge.sampleLaw k k).real {Z | phi (gueMat Z) ≤ s} = G k s := by
  rw [← hQ4 s]
  congr 1
  ext Z
  simp only [Set.mem_ofPred_eq]
  have hh : herm (gueMat Z) = gueMat Z := herm_of_isHermitian _ (gueMat_isHermitian Z)
  exact (phi_le_iff hk (gueMat Z) s).trans (by rw [hh]; exact Iff.rfl)

/-- Portmanteau for `λ_max`: if `T n ⇒ GUE_k` (tested on bounded continuous functions), then
`P(λ_max(T n) ≤ t) → G k t`. -/
theorem cdf_of_weak (hk : 1 ≤ k)
    (hQ4 : ∀ x : ℝ, (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x)
    (hG : Continuous (G k))
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (T : ∀ n, Ω n → (Fin k → Fin k → ℂ)) (hT : ∀ n, Measurable (T n))
    (hweak : ∀ f : (Fin k → Fin k → ℂ) → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
      Tendsto (fun n => ∫ ω, f (T n ω) ∂μ n) atTop
        (𝓝 (∫ Z, f (gueMat Z) ∂SpikedWishart.SoftEdge.sampleLaw k k)))
    (t : ℝ) :
    Tendsto (fun n => (μ n).real {ω | phi (T n ω) ≤ t}) atTop (𝓝 (G k t)) := by
  have hφm : Measurable (phi (k := k)) := continuous_phi.measurable
  have hgm : Measurable (fun Z : Fin k → Fin k → ℂ => phi (gueMat Z)) :=
    (continuous_phi.comp continuous_gueMat).measurable
  let νs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(μ n).map (fun ω => phi (T n ω)), Measure.isProbabilityMeasure_map (hφm.comp (hT n)).aemeasurable⟩
  let ν : ProbabilityMeasure ℝ :=
    ⟨(SpikedWishart.SoftEdge.sampleLaw k k).map (fun Z => phi (gueMat Z)),
      Measure.isProbabilityMeasure_map hgm.aemeasurable⟩
  have hlim : Tendsto νs atTop (𝓝 ν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have h1 : ∀ n, ∫ x, f x ∂(νs n : Measure ℝ) = ∫ ω, f (phi (T n ω)) ∂μ n := fun n =>
      integral_map (hφm.comp (hT n)).aemeasurable f.continuous.aestronglyMeasurable
    have h2 : ∫ x, f x ∂(ν : Measure ℝ) = ∫ Z, f (phi (gueMat Z)) ∂SpikedWishart.SoftEdge.sampleLaw k k :=
      integral_map hgm.aemeasurable f.continuous.aestronglyMeasurable
    simp only [h1, h2]
    exact hweak (fun X => f (phi X)) (f.continuous.comp continuous_phi)
      ⟨‖f‖, fun X => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (phi X)⟩
  have hνIic : ∀ s, (ν : Measure ℝ).real (Set.Iic s) = G k s := by
    intro s
    have : (ν : Measure ℝ).real (Set.Iic s) =
        (SpikedWishart.SoftEdge.sampleLaw k k).real ((fun Z => phi (gueMat Z)) ⁻¹' Set.Iic s) := by
      simp only [ν, ProbabilityMeasure.coe_mk]
      rw [map_measureReal_apply hgm measurableSet_Iic]
    rw [this]
    exact gue_phi_cdf hk hQ4 s
  have hnull : (ν : Measure ℝ) (frontier (Set.Iic t)) = 0 := by
    rw [frontier_Iic]
    have hle : ∀ δ > 0, (ν : Measure ℝ).real {t} ≤ G k t - G k (t - δ) := by
      intro δ hδ
      rw [← hνIic, ← hνIic, ← measureReal_sdiff (Set.Iic_subset_Iic.mpr (by linarith))
        measurableSet_Iic]
      refine measureReal_mono ?_ (measure_ne_top _ _)
      · intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst hy
        simp [hδ]
    have hlim0 : Tendsto (fun δ : ℝ => G k t - G k (t - δ)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => G k t - G k (t - δ)) (𝓝 0) (𝓝 (G k t - G k (t - 0))) :=
        tendsto_const_nhds.sub ((hG.tendsto _).comp (tendsto_const_nhds.sub tendsto_id))
      simpa using this.mono_left nhdsWithin_le_nhds
    have h0 : (ν : Measure ℝ).real {t} ≤ 0 :=
      ge_of_tendsto hlim0 (eventually_nhdsWithin_of_forall fun δ hδ => hle δ hδ)
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
      (le_antisymm h0 measureReal_nonneg)
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hlim
    (E := Set.Iic t) (by simpa using hnull)
  have key' := (NNReal.tendsto_coe.mpr key)
  have e1 : ∀ n, ((νs n (Set.Iic t) : NNReal) : ℝ) = (μ n).real {ω | phi (T n ω) ≤ t} := by
    intro n
    simp only [νs, ProbabilityMeasure.mk_apply]
    rw [ENNReal.coe_toNNReal_eq_toReal, ← measureReal_def,
      map_measureReal_apply (show Measurable (fun ω => phi (T n ω)) from hφm.comp (hT n))
        measurableSet_Iic]
    rfl
  have e2 : ((ν (Set.Iic t) : NNReal) : ℝ) = G k t := by
    rw [← hνIic]
    simp only [ν, ProbabilityMeasure.coe_mk, ProbabilityMeasure.mk_apply]
    rw [ENNReal.coe_toNNReal_eq_toReal, ← measureReal_def]
  simp only [e1, e2] at key'
  exact key'

/-- Entrywise `ℓ¹` size of an array. -/
noncomputable def ent (E : Fin k → Fin k → ℂ) : ℝ := ∑ i, ∑ j, ‖E i j‖

theorem ent_neg (E : Fin k → Fin k → ℂ) : ent (-E) = ent E := by
  simp [ent]

theorem continuous_ent : Continuous (ent (k := k)) := by
  unfold ent; fun_prop

theorem norm_le_one_of_sph {v : Fin k → ℂ} (hv : v ∈ sph k) (i : Fin k) : ‖v i‖ ≤ 1 := by
  have h1 : Complex.normSq (v i) ≤ 1 := by
    rw [← hv]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (v i)]

theorem sph_nonempty (hk : 1 ≤ k) : (sph k).Nonempty := by
  refine ⟨Pi.single ⟨0, hk⟩ 1, ?_⟩
  simp [sph, Pi.single_apply, Finset.sum_ite_eq']

theorem bdd_quad (H : Fin k → Fin k → ℂ) : BddAbove (quad H '' sph k) :=
  (isCompact_sph.image_of_continuousOn
    (continuous_quad.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn).bddAbove

theorem herm_add (H E : Fin k → Fin k → ℂ) : herm (H + E) = herm H + herm E := by
  unfold herm
  ext i j
  simp [conjTranspose_apply] <;> ring

theorem quad_add (H E : Fin k → Fin k → ℂ) (v : Fin k → ℂ) :
    quad (H + E) v = quad H v + quad E v := by
  unfold quad
  rw [herm_add, add_mulVec, dotProduct_add, Complex.add_re]

theorem norm_herm_le (E : Fin k → Fin k → ℂ) (i j : Fin k) :
    ‖herm E i j‖ ≤ (‖E i j‖ + ‖E j i‖) / 2 := by
  unfold herm
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, conjTranspose_apply,
    smul_eq_mul, norm_mul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  have := norm_add_le (E i j) (star (E j i))
  rw [norm_star] at this
  linarith

theorem abs_quad_le (E : Fin k → Fin k → ℂ) {v : Fin k → ℂ} (hv : v ∈ sph k) :
    |quad E v| ≤ ent E := by
  have hv1 := norm_le_one_of_sph hv
  calc |quad E v| ≤ ‖star v ⬝ᵥ (herm E *ᵥ v)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖herm E i j‖ := by
        simp only [dotProduct, mulVec, Pi.star_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_star]
        calc ‖v i‖ * ‖∑ j, herm E i j * v j‖ ≤ 1 * ∑ j, ‖herm E i j‖ := by
              refine mul_le_mul (hv1 i) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
                (norm_nonneg _) zero_le_one
              rw [norm_mul]
              exact mul_le_of_le_one_right (norm_nonneg _) (hv1 j)
          _ = ∑ j, ‖herm E i j‖ := one_mul _
    _ ≤ ∑ i, ∑ j, (‖E i j‖ + ‖E j i‖) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_herm_le E i j
    _ = ent E := by
        unfold ent
        simp only [add_div, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => ‖E j i‖ / 2)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring

theorem phi_add_le (hk : 1 ≤ k) (H E : Fin k → Fin k → ℂ) : phi (H + E) ≤ phi H + ent E := by
  refine csSup_le ((sph_nonempty hk).image _) ?_
  rintro b ⟨v, hv, rfl⟩
  rw [quad_add]
  have h1 : quad H v ≤ phi H := le_csSup (bdd_quad H) ⟨v, hv, rfl⟩
  have h2 := (abs_le.mp (abs_quad_le E hv)).2
  linarith

/-- `λ_max` is 1-Lipschitz for the entrywise `ℓ¹` size. -/
theorem abs_phi_add_sub_le (hk : 1 ≤ k) (H E : Fin k → Fin k → ℂ) :
    |phi (H + E) - phi H| ≤ ent E := by
  have h1 := phi_add_le hk H E
  have h2 := phi_add_le hk (H + E) (-E)
  rw [add_neg_cancel_right, ent_neg] at h2
  rw [abs_le]; constructor <;> linarith

/-- Tightness from weak convergence: `P(ent T_n > K)` is uniformly small for large `K`. -/
theorem tight_of_weak {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (T : ∀ n, Ω n → (Fin k → Fin k → ℂ)) (hT : ∀ n, Measurable (T n))
    {Θ : Type*} [MeasurableSpace Θ] (ρ : Measure Θ) [IsProbabilityMeasure ρ]
    (Y : Θ → (Fin k → Fin k → ℂ)) (hY : Measurable Y)
    (hweak : ∀ f : (Fin k → Fin k → ℂ) → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
      Tendsto (fun n => ∫ ω, f (T n ω) ∂μ n) atTop (𝓝 (∫ z, f (Y z) ∂ρ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ᶠ n in atTop, (μ n).real {ω | K < ent (T n ω)} ≤ ε := by
  have hentm : Measurable (ent (k := k)) := continuous_ent.measurable
  -- tail of the limit
  let S : ℕ → Set Θ := fun K => {z | (K : ℝ) < ent (Y z)}
  have hSm : ∀ K, MeasurableSet (S K) := fun K =>
    measurableSet_lt measurable_const (hentm.comp hY)
  have hanti : Antitone S := by
    intro a b hab z hz
    simp only [S, Set.mem_ofPred_eq] at hz ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hab) hz
  have hinter : (⋂ K, S K) = ∅ := by
    ext z
    simp only [S, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    obtain ⟨K, hK⟩ := exists_nat_ge (ent (Y z))
    exact ⟨K, hK⟩
  have htend := tendsto_measure_iInter_atTop (μ := ρ) (fun K => (hSm K).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at htend
  have htend' : Tendsto (fun K => ρ.real (S K)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    simpa [Function.comp_def, measureReal_def] using this
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 ((tendsto_order.1 htend').2 (ε / 2) (half_pos hε))
  have hK₀' := hK₀ K₀ le_rfl
  -- the cutoff function
  let f : (Fin k → Fin k → ℂ) → ℝ := fun X => min 1 (max 0 (ent X - K₀))
  have hfc : Continuous f := by
    exact continuous_const.min (continuous_const.max (continuous_ent.sub continuous_const))
  have hf01 : ∀ X, 0 ≤ f X ∧ f X ≤ 1 := fun X =>
    ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hfB : ∃ B, ∀ X, |f X| ≤ B := ⟨1, fun X => by
    rw [abs_of_nonneg (hf01 X).1]; exact (hf01 X).2⟩
  have hlim := hweak f hfc hfB
  have hlimval : ∫ z, f (Y z) ∂ρ ≤ ρ.real (S K₀) := by
    rw [← integral_indicator_one (hSm K₀)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => (hf01 _).1)
      ((integrable_const (1 : ℝ)).indicator (hSm K₀)) (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ S K₀
    · rw [Set.indicator_of_mem hz]; exact (hf01 _).2
    · rw [Set.indicator_of_notMem hz]
      simp only [S, Set.mem_ofPred_eq, not_lt] at hz
      simp only [f]
      rw [max_eq_left (by linarith)]
      exact min_le_right _ _
  have hev : ∀ᶠ n in atTop, ∫ ω, f (T n ω) ∂μ n < ε :=
    (tendsto_order.1 hlim).2 ε (by linarith)
  refine ⟨K₀ + 1, ?_⟩
  filter_upwards [hev] with n hn
  have hset : MeasurableSet {ω | (K₀ : ℝ) + 1 < ent (T n ω)} :=
    measurableSet_lt measurable_const (hentm.comp (hT n))
  have : (μ n).real {ω | (K₀ : ℝ) + 1 < ent (T n ω)} ≤ ∫ ω, f (T n ω) ∂μ n := by
    rw [← integral_indicator_one hset]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · by_cases h : ω ∈ {ω | (K₀ : ℝ) + 1 < ent (T n ω)}
      · rw [Set.indicator_of_mem h]; exact zero_le_one
      · rw [Set.indicator_of_notMem h]; exact le_rfl
    · refine Integrable.of_bound (C := 1)
        (hfc.measurable.comp (hT n)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hf01 _).1]; exact (hf01 _).2
    · by_cases h : ω ∈ {ω | (K₀ : ℝ) + 1 < ent (T n ω)}
      · rw [Set.indicator_of_mem h]
        simp only [Set.mem_ofPred_eq] at h
        simp only [f]
        rw [max_eq_right (by linarith), min_eq_left (by linarith)]
        exact le_rfl
      · rw [Set.indicator_of_notMem h]; exact (hf01 _).1
  linarith

end

-- ===== from Perturb.lean =====
section

/-- (needs LamMax.lean + Slutsky.lean above it) `P(λ_max(T_n + E_n) ≤ t_n) → G k t` when `T_n ⇒ GUE_k`,
`E_n → 0` in probability (entrywise) and `t_n → t`. -/
theorem cdf_perturbed {k : ℕ} (hk : 1 ≤ k)
    (hQ4 : ∀ x : ℝ, (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x)
    (hG : Continuous (G k))
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (T : ∀ n, Ω n → (Fin k → Fin k → ℂ)) (hT : ∀ n, Measurable (T n))
    (hweak : ∀ f : (Fin k → Fin k → ℂ) → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
      Tendsto (fun n => ∫ ω, f (T n ω) ∂μ n) atTop
        (𝓝 (∫ Z, f (gueMat Z) ∂SpikedWishart.SoftEdge.sampleLaw k k)))
    (E : ∀ n, Ω n → (Fin k → Fin k → ℂ))
    (hE : ∀ ε, 0 < ε → Tendsto (fun n => (μ n).real {ω | ε < ent (E n ω)}) atTop (𝓝 0))
    (tn : ℕ → ℝ) (t : ℝ) (htn : Tendsto tn atTop (𝓝 t)) :
    Tendsto (fun n => (μ n).real {ω | phi (T n ω + E n ω) ≤ tn n}) atTop (𝓝 (G k t)) := by
  have hY := cdf_of_weak hk hQ4 hG μ T hT hweak
  have key := cdf_slutsky μ (fun n ω => phi (T n ω)) (fun n ω => phi (T n ω + E n ω) - (tn n - t))
    (G k) t (hG.continuousAt) hY ?_
  · refine key.congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  · intro ε hε
    have hev : ∀ᶠ n in atTop, |tn n - t| < ε / 2 := by
      have := (Metric.tendsto_nhds.mp htn) (ε / 2) (half_pos hε)
      simpa [Real.dist_eq] using this
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => measureReal_nonneg) ?_
      (hE (ε / 2) (half_pos hε))
    filter_upwards [hev] with n hn
    refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h1 := abs_phi_add_sub_le hk (T n ω) (E n ω)
    have h2 : |phi (T n ω + E n ω) - (tn n - t) - phi (T n ω)| ≤
        |phi (T n ω + E n ω) - phi (T n ω)| + |tn n - t| := by
      rw [show phi (T n ω + E n ω) - (tn n - t) - phi (T n ω) =
        (phi (T n ω + E n ω) - phi (T n ω)) + (-(tn n - t)) by ring]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    linarith

end

-- ===== from Split.lean =====
section

/-- One row of i.i.d. coordinates splits along `e : ι ≃ α ⊕ β` into two independent rows. -/
theorem row_split_measurePreserving {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (e : ι ≃ α ⊕ β) :
    MeasurePreserving (fun v : ι → ℂ => ((fun a => v (e.symm (Sum.inl a))),
        (fun b => v (e.symm (Sum.inr b)))))
      (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_piCongrLeft (α := fun _ : α ⊕ β => ℂ) (fun _ => μ) e
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : α ⊕ β => ℂ) (fun _ => μ)
  have h := h2.comp h1
  convert h using 1
  funext v
  simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft]
  ext a
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]

/-- The `M`-sample Gaussian array splits along `e : ι ≃ α ⊕ β` (coordinates) into two independent
arrays. -/
theorem array_split_measurePreserving {M : ℕ} {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (e : ι ≃ α ⊕ β) :
    MeasurePreserving (fun X : Fin M → ι → ℂ => ((fun k a => X k (e.symm (Sum.inl a))),
        (fun k b => X k (e.symm (Sum.inr b)))))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : α => μ).prod
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_pi (fun _ : Fin M => Measure.pi fun _ : ι => μ)
    (fun _ : Fin M => (Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ))
    (fun _ => row_split_measurePreserving μ e)
  have h2 := measurePreserving_arrowProdEquivProdArrow (α → ℂ) (β → ℂ) (Fin M)
    (fun _ => Measure.pi fun _ : α => μ) (fun _ => Measure.pi fun _ : β => μ)
  exact h2.comp h1

/-- The sample law splits: `sampleLaw M N = sampleLaw M r ⊗ sampleLaw M p` along `e`. -/
theorem sampleLaw_split {M N r p : ℕ} (e : Fin N ≃ Fin r ⊕ Fin p) :
    MeasurePreserving (fun X : Fin M → Fin N → ℂ => ((fun k a => X k (e.symm (Sum.inl a))),
        (fun k b => X k (e.symm (Sum.inr b)))))
      (SpikedWishart.SoftEdge.sampleLaw M N)
      ((SpikedWishart.SoftEdge.sampleLaw M r).prod (SpikedWishart.SoftEdge.sampleLaw M p)) :=
  array_split_measurePreserving _ e

/-- Generic version of `row_split_measurePreserving` for any probability space of coordinates. -/
theorem pi_split_measurePreserving {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (e : ι ≃ α ⊕ β) :
    MeasurePreserving (fun v : ι → X => ((fun a => v (e.symm (Sum.inl a))),
        (fun b => v (e.symm (Sum.inr b)))))
      (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_piCongrLeft (α := fun _ : α ⊕ β => X) (fun _ => μ) e
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : α ⊕ β => X) (fun _ => μ)
  have h := h2.comp h1
  convert h using 1
  funext v
  simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft]
  ext a
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]

/-- The top-left corner (along `e`) of an `r × r` Gaussian array is a `k × k` Gaussian array. -/
theorem sampleLaw_corner {r k q : ℕ} (e : Fin r ≃ Fin k ⊕ Fin q) :
    MeasurePreserving (fun Z : Fin r → Fin r → ℂ => fun i j => Z (e.symm (Sum.inl i)) (e.symm (Sum.inl j)))
      (SpikedWishart.SoftEdge.sampleLaw r r) (SpikedWishart.SoftEdge.sampleLaw k k) := by
  have h1 := (measurePreserving_fst (μ := SpikedWishart.SoftEdge.sampleLaw r k)
    (ν := SpikedWishart.SoftEdge.sampleLaw r q)).comp (sampleLaw_split (M := r) e)
  have h2 := (measurePreserving_fst (μ := Measure.pi fun _ : Fin k =>
      Measure.pi fun _ : Fin k => SpikedWishart.SoftEdge.stdComplexGaussian)
    (ν := Measure.pi fun _ : Fin q =>
      Measure.pi fun _ : Fin k => SpikedWishart.SoftEdge.stdComplexGaussian)).comp
    (pi_split_measurePreserving (Measure.pi fun _ : Fin k => SpikedWishart.SoftEdge.stdComplexGaussian) e)
  exact h2.comp h1

/-- The GUE matrix commutes with taking corners. -/
theorem gue_corner {r k q : ℕ} (e : Fin r ≃ Fin k ⊕ Fin q) (Z : Fin r → Fin r → ℂ) :
    (Matrix.of fun i j => ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ))
        (e.symm (Sum.inl i)) (e.symm (Sum.inl j))) =
      (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of (fun i j => Z (e.symm (Sum.inl i)) (e.symm (Sum.inl j))) +
        (Matrix.of (fun i j => Z (e.symm (Sum.inl i)) (e.symm (Sum.inl j))))ᴴ) := by
  ext i j; simp [Matrix.conjTranspose_apply]

end

-- ===== from Block.lean =====
section

/-- Real part of the sesquilinear form `v* T v`. -/
noncomputable def qf {n : ℕ} (T : Fin n → Fin n → ℂ) (v : Fin n → ℂ) : ℝ :=
  (∑ i, ∑ j, star (v i) * T i j * v j).re

theorem re_dot_eq_qf {n : ℕ} (T : Fin n → Fin n → ℂ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (Matrix.of T *ᵥ v)).re = qf T v := by
  unfold qf
  congr 1
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]

theorem re_dot_diag_sub {n : ℕ} (d : Fin n → ℝ) (T : Fin n → Fin n → ℂ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ ((diagonal (fun j => (d j : ℂ)) - Matrix.of T) *ᵥ v)).re =
      ∑ j, d j * Complex.normSq (v j) - qf T v := by
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, re_dot_eq_qf]
  congr 1
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  ring

theorem diag_sub_isHermitian {n : ℕ} (d : Fin n → ℝ) (T : Fin n → Fin n → ℂ)
    (hT : (Matrix.of T).IsHermitian) :
    (diagonal (fun j => (d j : ℂ)) - Matrix.of T).IsHermitian := by
  refine IsHermitian.sub ?_ hT
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun j => by simp)

/-- `2xy ≤ u x² + y²/u`. -/
theorem two_mul_le_amgm (x y u : ℝ) (hu : 0 < u) : 2 * (x * y) ≤ u * x ^ 2 + y ^ 2 / u := by
  have h0 : 0 ≤ (u * x - y) ^ 2 / u := div_nonneg (sq_nonneg _) hu.le
  have e : (u * x - y) ^ 2 / u = u * x ^ 2 + y ^ 2 / u - 2 * (x * y) := by
    field_simp
    ring
  linarith

theorem norm_dsum_le {m n : ℕ} (x : Fin m → ℂ) (A : Fin m → Fin n → ℂ) (y : Fin n → ℂ) (B : ℝ)
    (h : ∀ i j, ‖x i‖ * ‖y j‖ ≤ B) :
    ‖∑ i, ∑ j, star (x i) * A i j * y j‖ ≤ (∑ i, ∑ j, ‖A i j‖) * B := by
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  calc ‖x i‖ * ‖A i j‖ * ‖y j‖ = ‖A i j‖ * (‖x i‖ * ‖y j‖) := by ring
    _ ≤ ‖A i j‖ * B := mul_le_mul_of_nonneg_left (h i j) (norm_nonneg _)

/-- `quad H a ≤ λ_max(H) |a|²`. -/
theorem quad_le_phi_mul {k : ℕ} (hk : 1 ≤ k) (H : Fin k → Fin k → ℂ) (a : Fin k → ℂ) :
    quad H a ≤ phi H * ∑ i, Complex.normSq (a i) := by
  have hα0 : 0 ≤ ∑ i, Complex.normSq (a i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  rcases hα0.eq_or_lt with h0 | hpos
  · have ha : a = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (a i))).mp
        h0.symm i (Finset.mem_univ i)
      simpa using this
    subst ha
    simp [quad]
  · set s := (Real.sqrt (∑ i, Complex.normSq (a i)))⁻¹ with hs
    have hs2 : s ^ 2 = (∑ i, Complex.normSq (a i))⁻¹ := by rw [hs, inv_pow, Real.sq_sqrt hα0]
    have hw : ((s : ℂ) • a) ∈ sph k := by
      show ∑ i, Complex.normSq (((s : ℂ) • a) i) = 1
      simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        ← Finset.mul_sum]
      rw [← sq, hs2, inv_mul_cancel₀ hpos.ne']
    have h1 : quad H ((s : ℂ) • a) ≤ phi H := le_csSup (bdd_quad H) ⟨_, hw, rfl⟩
    rw [quad_smul, hs2, inv_mul_le_iff₀ hpos] at h1
    linarith [mul_comm (phi H) (∑ i, Complex.normSq (a i))]

section block

variable {k q : ℕ}

/-- Upper-left `k × k` corner of a `(k+q) × (k+q)` array. -/
def corner (T : Fin (k + q) → Fin (k + q) → ℂ) : Fin k → Fin k → ℂ :=
  fun i j => T (Fin.castAdd q i) (Fin.castAdd q j)

theorem continuous_corner : Continuous (corner (k := k) (q := q)) := by
  unfold corner
  fun_prop

theorem corner_isHermitian (T : Fin (k + q) → Fin (k + q) → ℂ) (hT : (Matrix.of T).IsHermitian) :
    (Matrix.of (corner T)).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by
    simpa [corner] using hT.apply (Fin.castAdd q i) (Fin.castAdd q j)

theorem quad_corner (T : Fin (k + q) → Fin (k + q) → ℂ) (hT : (Matrix.of T).IsHermitian)
    (w : Fin k → ℂ) : quad (corner T) w = qf (corner T) w := by
  unfold quad
  rw [herm_of_isHermitian _ (corner_isHermitian T hT), re_dot_eq_qf]

theorem qf_split (T : Fin (k + q) → Fin (k + q) → ℂ) (v : Fin (k + q) → ℂ) :
    qf T v = qf (corner T) (fun i => v (Fin.castAdd q i)) +
      ((∑ i : Fin k, ∑ j : Fin q, star (v (Fin.castAdd q i)) * T (Fin.castAdd q i) (Fin.natAdd k j) *
          v (Fin.natAdd k j)) +
       (∑ i : Fin q, ∑ j : Fin k, star (v (Fin.natAdd k i)) * T (Fin.natAdd k i) (Fin.castAdd q j) *
          v (Fin.castAdd q j)) +
       (∑ i : Fin q, ∑ j : Fin q, star (v (Fin.natAdd k i)) * T (Fin.natAdd k i) (Fin.natAdd k j) *
          v (Fin.natAdd k j))).re := by
  unfold qf corner
  rw [← Complex.add_re]
  congr 1
  simp only [Fin.sum_univ_add, Finset.sum_add_distrib]
  ring

theorem ent_split (T : Fin (k + q) → Fin (k + q) → ℂ) :
    ent T = (∑ i : Fin k, ∑ j : Fin k, ‖T (Fin.castAdd q i) (Fin.castAdd q j)‖) +
      (∑ i : Fin k, ∑ j : Fin q, ‖T (Fin.castAdd q i) (Fin.natAdd k j)‖) +
      (∑ i : Fin q, ∑ j : Fin k, ‖T (Fin.natAdd k i) (Fin.castAdd q j)‖) +
      (∑ i : Fin q, ∑ j : Fin q, ‖T (Fin.natAdd k i) (Fin.natAdd k j)‖) := by
  unfold ent
  simp only [Fin.sum_univ_add, Finset.sum_add_distrib]
  ring

theorem qf_le (T : Fin (k + q) → Fin (k + q) → ℂ) (v : Fin (k + q) → ℂ) (u : ℝ) (hu : 0 < u) :
    qf T v ≤ qf (corner T) (fun i => v (Fin.castAdd q i)) +
      ent T * (u * ∑ i, Complex.normSq (v (Fin.castAdd q i)) +
        (∑ j, Complex.normSq (v (Fin.natAdd k j))) / u + ∑ j, Complex.normSq (v (Fin.natAdd k j))) := by
  have hna : ∀ i, ‖v (Fin.castAdd q i)‖ ^ 2 ≤ ∑ i, Complex.normSq (v (Fin.castAdd q i)) := fun i => by
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (f := fun i => Complex.normSq (v (Fin.castAdd q i)))
      (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hnb : ∀ j, ‖v (Fin.natAdd k j)‖ ^ 2 ≤ ∑ j, Complex.normSq (v (Fin.natAdd k j)) := fun j => by
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (f := fun j => Complex.normSq (v (Fin.natAdd k j)))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  have hα0 : 0 ≤ ∑ i, Complex.normSq (v (Fin.castAdd q i)) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hβ0 : 0 ≤ ∑ j, Complex.normSq (v (Fin.natAdd k j)) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  rw [qf_split]
  generalize ∑ i, Complex.normSq (v (Fin.castAdd q i)) = α at *
  generalize ∑ j, Complex.normSq (v (Fin.natAdd k j)) = β at *
  have hB0 : 0 ≤ u * α + β / u + β := by positivity
  have hab : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ 2 ≤ α → y ^ 2 ≤ β → x * y ≤ u * α + β / u + β := by
    intro x y hx hy hxa hyb
    have h1 := two_mul_le_amgm x y u hu
    have h2 : u * x ^ 2 ≤ u * α := mul_le_mul_of_nonneg_left hxa hu.le
    have h3 : y ^ 2 / u ≤ β / u := div_le_div_of_nonneg_right hyb hu.le
    have h4 := mul_nonneg hx hy
    linarith
  have hbb : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ 2 ≤ β → y ^ 2 ≤ β → x * y ≤ u * α + β / u + β := by
    intro x y hx hy hxb hyb
    have h1 := two_mul_le_amgm x y 1 one_pos
    have h2 : 0 ≤ u * α := mul_nonneg hu.le hα0
    have h3 : 0 ≤ β / u := div_nonneg hβ0 hu.le
    have h4 := mul_nonneg hx hy
    simp only [one_mul, div_one] at h1
    linarith
  have e12 := norm_dsum_le (fun i => v (Fin.castAdd q i))
    (fun i j => T (Fin.castAdd q i) (Fin.natAdd k j)) (fun j => v (Fin.natAdd k j)) _
    (fun i j => hab _ _ (norm_nonneg _) (norm_nonneg _) (hna i) (hnb j))
  have e21 := norm_dsum_le (fun i => v (Fin.natAdd k i))
    (fun i j => T (Fin.natAdd k i) (Fin.castAdd q j)) (fun j => v (Fin.castAdd q j)) _
    (fun i j => by rw [mul_comm]; exact hab _ _ (norm_nonneg _) (norm_nonneg _) (hna j) (hnb i))
  have e22 := norm_dsum_le (fun i => v (Fin.natAdd k i))
    (fun i j => T (Fin.natAdd k i) (Fin.natAdd k j)) (fun j => v (Fin.natAdd k j)) _
    (fun i j => hbb _ _ (norm_nonneg _) (norm_nonneg _) (hnb i) (hnb j))
  beta_reduce at e12 e21 e22
  have hE11 : 0 ≤ ∑ i : Fin k, ∑ j : Fin k, ‖T (Fin.castAdd q i) (Fin.castAdd q j)‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hE11B := mul_nonneg hE11 hB0
  refine add_le_add le_rfl ?_
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [ent_split]
  nlinarith [e12, e21, e22, hE11B]

theorem phi_corner_le_of_psd (hk : 1 ≤ k) (T : Fin (k + q) → Fin (k + q) → ℂ)
    (hT : (Matrix.of T).IsHermitian) (d : Fin (k + q) → ℝ) (t : ℝ)
    (hd1 : ∀ i, d (Fin.castAdd q i) = t)
    (hpsd : (diagonal (fun j => (d j : ℂ)) - Matrix.of T).PosSemidef) :
    phi (corner T) ≤ t := by
  rw [psd_iff_re (diag_sub_isHermitian d T hT)] at hpsd
  refine csSup_le ((sph_nonempty hk).image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : ∑ i, Complex.normSq (w i) = 1 := hw
  have h := hpsd (Fin.append w (0 : Fin q → ℂ))
  rw [re_dot_diag_sub, qf_split, Fin.sum_univ_add] at h
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, hd1, mul_zero, star_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Complex.zero_re, map_zero] at h
  rw [quad_corner T hT]
  have ht : ∑ i, t * Complex.normSq (w i) = t := by rw [← Finset.mul_sum, hw1, mul_one]
  have hq : qf (corner T) (fun i => w i) = qf (corner T) w := rfl
  linarith

theorem psd_of_corner (hk : 1 ≤ k) (T : Fin (k + q) → Fin (k + q) → ℂ)
    (hT : (Matrix.of T).IsHermitian) (d : Fin (k + q) → ℝ) (t η K : ℝ) (hη : 0 < η) (hK0 : 0 ≤ K)
    (hd1 : ∀ i, d (Fin.castAdd q i) = t) (hd2 : ∀ j, K * ((K + 1) / η + 1) ≤ d (Fin.natAdd k j))
    (hphi : phi (corner T) ≤ t - η) (hent : ent T ≤ K) :
    (diagonal (fun j => (d j : ℂ)) - Matrix.of T).PosSemidef := by
  rw [psd_iff_re (diag_sub_isHermitian d T hT)]
  intro v
  rw [re_dot_diag_sub]
  have hu : 0 < η / (K + 1) := by positivity
  have h1 := qf_le T v (η / (K + 1)) hu
  have hα0 : 0 ≤ ∑ i, Complex.normSq (v (Fin.castAdd q i)) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hβ0 : 0 ≤ ∑ j, Complex.normSq (v (Fin.natAdd k j)) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h2 : qf (corner T) (fun i => v (Fin.castAdd q i)) ≤
      (t - η) * ∑ i, Complex.normSq (v (Fin.castAdd q i)) := by
    rw [← quad_corner T hT]
    exact (quad_le_phi_mul hk _ _).trans (mul_le_mul_of_nonneg_right hphi hα0)
  have hsum : ∑ j, d j * Complex.normSq (v j) = t * ∑ i, Complex.normSq (v (Fin.castAdd q i)) +
      ∑ j, d (Fin.natAdd k j) * Complex.normSq (v (Fin.natAdd k j)) := by
    rw [Fin.sum_univ_add, Finset.mul_sum]
    simp only [hd1]
  have h3 : K * ((K + 1) / η + 1) * ∑ j, Complex.normSq (v (Fin.natAdd k j)) ≤
      ∑ j, d (Fin.natAdd k j) * Complex.normSq (v (Fin.natAdd k j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hd2 j) (Complex.normSq_nonneg _)
  generalize ∑ i, Complex.normSq (v (Fin.castAdd q i)) = α at *
  generalize ∑ j, Complex.normSq (v (Fin.natAdd k j)) = β at *
  have hB0 : 0 ≤ η / (K + 1) * α + β / (η / (K + 1)) + β := by positivity
  have h4 : ent T * (η / (K + 1) * α + β / (η / (K + 1)) + β) ≤
      K / (K + 1) * η * α + K * ((K + 1) / η + 1) * β := by
    calc ent T * (η / (K + 1) * α + β / (η / (K + 1)) + β)
        ≤ K * (η / (K + 1) * α + β / (η / (K + 1)) + β) := mul_le_mul_of_nonneg_right hent hB0
      _ = K / (K + 1) * η * α + K * ((K + 1) / η + 1) * β := by
        field_simp
        ring
  have h5 : K / (K + 1) * η * α ≤ η * α := by
    have hK1 : K / (K + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hη.le) hα0
    linarith
  linarith

/-- The `k × k` corner of `T_n ⇒ GUE_{k+q}` converges to `GUE_k`. -/
theorem corner_weak {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (T : ∀ n, Ω n → (Fin (k + q) → Fin (k + q) → ℂ))
    (hweak : ∀ f : (Fin (k + q) → Fin (k + q) → ℂ) → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
      Tendsto (fun n => ∫ ω, f (T n ω) ∂μ n) atTop
        (𝓝 (∫ Z, f (gueMat Z) ∂SpikedWishart.SoftEdge.sampleLaw (k + q) (k + q)))) :
    ∀ f : (Fin k → Fin k → ℂ) → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
      Tendsto (fun n => ∫ ω, f (corner (T n ω)) ∂μ n) atTop
        (𝓝 (∫ Z, f (gueMat Z) ∂SpikedWishart.SoftEdge.sampleLaw k k)) := by
  intro f hf hfb
  obtain ⟨B, hB⟩ := hfb
  have h := hweak (fun X => f (corner X)) (hf.comp continuous_corner) ⟨B, fun X => hB _⟩
  have hmp := sampleLaw_corner (r := k + q) (k := k) (q := q) finSumFinEquiv.symm
  have hc : ∀ Z : Fin (k + q) → Fin (k + q) → ℂ,
      corner (gueMat Z) = gueMat (fun i j => Z (Fin.castAdd q i) (Fin.castAdd q j)) := by
    intro Z
    have h' := gue_corner (finSumFinEquiv.symm : Fin (k + q) ≃ Fin k ⊕ Fin q) Z
    simp only [Equiv.symm_symm, finSumFinEquiv_apply_left] at h'
    exact h'
  have key : ∫ Z, f (gueMat Z) ∂SpikedWishart.SoftEdge.sampleLaw k k =
      ∫ Z, (f ∘ gueMat) ((fun Z i j => Z (finSumFinEquiv.symm.symm (Sum.inl i))
        (finSumFinEquiv.symm.symm (Sum.inl j))) Z) ∂SpikedWishart.SoftEdge.sampleLaw (k + q) (k + q) := by
    rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable (hf.comp continuous_gueMat).aestronglyMeasurable
  have key2 : ∫ Z, (f ∘ gueMat) ((fun Z i j => Z (finSumFinEquiv.symm.symm (Sum.inl i))
        (finSumFinEquiv.symm.symm (Sum.inl j))) Z) ∂SpikedWishart.SoftEdge.sampleLaw (k + q) (k + q) =
      ∫ Z, f (corner (gueMat Z)) ∂SpikedWishart.SoftEdge.sampleLaw (k + q) (k + q) := by
    refine integral_congr_ae (Eventually.of_forall fun Z => ?_)
    simp only [Equiv.symm_symm, finSumFinEquiv_apply_left]
    exact congrArg f (hc Z).symm
  rw [key, key2]
  exact h

/-- Sandwich: if `T_n ⇒ GUE_{k+q}` (Hermitian), `d_n = t_n` on the first `k` coordinates with
`t_n → t` and `d_n → +∞` on the last `q`, then `P(diag(d_n) - T_n ⪰ 0) → G k t`. -/
theorem cdf_block (hk : 1 ≤ k)
    (hQ4 : ∀ x : ℝ, (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x)
    (hG : Continuous (G k))
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (T : ∀ n, Ω n → (Fin (k + q) → Fin (k + q) → ℂ))
    (hT : ∀ n, Measurable (T n)) (hH : ∀ n ω, (Matrix.of (T n ω)).IsHermitian)
    (hweak : ∀ f : (Fin (k + q) → Fin (k + q) → ℂ) → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
      Tendsto (fun n => ∫ ω, f (T n ω) ∂μ n) atTop
        (𝓝 (∫ Z, f (gueMat Z) ∂SpikedWishart.SoftEdge.sampleLaw (k + q) (k + q))))
    (d : ℕ → Fin (k + q) → ℝ) (tn : ℕ → ℝ) (t : ℝ) (htn : Tendsto tn atTop (𝓝 t))
    (hd1 : ∀ n i, d n (Fin.castAdd q i) = tn n)
    (hd2 : ∀ B : ℝ, ∀ᶠ n in atTop, ∀ j, B ≤ d n (Fin.natAdd k j)) :
    Tendsto (fun n => (μ n).real
        {ω | (diagonal (fun j => (d n j : ℂ)) - Matrix.of (T n ω)).PosSemidef})
      atTop (𝓝 (G k t)) := by
  have hTc : ∀ n, Measurable (fun ω => corner (T n ω)) :=
    fun n => continuous_corner.measurable.comp (hT n)
  have hwc := corner_weak μ T hweak
  have h0 : ent (0 : Fin k → Fin k → ℂ) = 0 := by simp [ent]
  have hE0 : ∀ ε, 0 < ε → Tendsto (fun n => (μ n).real
      {ω : Ω n | ε < ent (0 : Fin k → Fin k → ℂ)}) atTop (𝓝 0) := by
    intro ε hε
    have hempty : ∀ n, {ω : Ω n | ε < ent (0 : Fin k → Fin k → ℂ)} = ∅ := fun n => by
      rw [h0]
      exact Set.eq_empty_of_forall_notMem fun ω hω => lt_irrefl _ (hε.trans hω)
    simp only [hempty, measureReal_empty]
    exact tendsto_const_nhds
  have hcdf : ∀ (sn : ℕ → ℝ) (s : ℝ), Tendsto sn atTop (𝓝 s) →
      Tendsto (fun n => (μ n).real {ω | phi (corner (T n ω)) ≤ sn n}) atTop (𝓝 (G k s)) := by
    intro sn s hs
    have := cdf_perturbed hk hQ4 hG μ (fun n ω => corner (T n ω)) hTc hwc (fun n _ => 0) hE0 sn s hs
    simpa using this
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · set ε := (G k t - a) / 3 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    obtain ⟨δ, hδ, hδG⟩ := Metric.continuous_iff.mp hG t ε hε0
    have hη : 0 < δ / 2 := half_pos hδ
    have hGη : G k t - ε < G k (t - δ / 2) := by
      have hd : dist (t - δ / 2) t < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have := hδG (t - δ / 2) hd
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hgm : Measurable (fun Z : Fin (k + q) → Fin (k + q) → ℂ => fun i j => gueMat Z i j) :=
      measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_gueMat)).measurable
    obtain ⟨K0, hK0⟩ := tight_of_weak μ T hT (SpikedWishart.SoftEdge.sampleLaw (k + q) (k + q))
      (fun Z i j => gueMat Z i j) hgm hweak ε hε0
    have hlow := hcdf (fun n => tn n - δ / 2) (t - δ / 2) (htn.sub_const _)
    have hlow' : ∀ᶠ n in atTop,
        G k t - 2 * ε < (μ n).real {ω | phi (corner (T n ω)) ≤ tn n - δ / 2} :=
      (tendsto_order.1 hlow).1 _ (by linarith)
    filter_upwards [hlow', hK0, hd2 (max K0 0 * ((max K0 0 + 1) / (δ / 2) + 1))] with n h1 h2 h3
    have hsub : {ω | phi (corner (T n ω)) ≤ tn n - δ / 2} ⊆
        {ω | (diagonal (fun j => (d n j : ℂ)) - Matrix.of (T n ω)).PosSemidef} ∪
          {ω | K0 < ent (T n ω)} := by
      intro ω hω
      by_cases hent : ent (T n ω) ≤ max K0 0
      · left
        exact psd_of_corner hk (T n ω) (hH n ω) (d n) (tn n) (δ / 2) (max K0 0) hη
          (le_max_right _ _) (hd1 n) h3 hω hent
      · right
        exact lt_of_le_of_lt (le_max_left _ _) (not_le.mp hent)
    have := (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le (μ := μ n) _ _)
    linarith
  · have hup := hcdf tn t htn
    filter_upwards [(tendsto_order.1 hup).2 a ha] with n hn
    refine lt_of_le_of_lt (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) hn
    exact phi_corner_le_of_psd hk (T n ω) (hH n ω) (d n) (tn n) (hd1 n) hω

end block

end

-- ===== from DetLimit.lean =====
section

theorem psd_scale_iff {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) (hε : 0 < ε) :
    ((ε : ℂ) • P).PosSemidef ↔ P.PosSemidef := by
  constructor
  · intro h
    have h2 := h.smul (a := ((ε⁻¹ : ℝ) : ℂ)) (Complex.zero_le_real.mpr (inv_nonneg.mpr hε.le))
    rwa [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hε.ne', Complex.ofReal_one, one_smul] at h2
  · intro h
    exact h.smul (Complex.zero_le_real.mpr hε.le)

/-- Congruence by `diag(√D)`: `x - Δ B Δ ⪰ 0 ↔ diag(x / D) - B ⪰ 0` for `D > 0`. -/
theorem psd_congr_diag {n : ℕ} (D : Fin n → ℝ) (hD : ∀ j, 0 < D j) (x : ℝ)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        diagonal (fun j => (Real.sqrt (D j) : ℂ)) * B * diagonal (fun j => (Real.sqrt (D j) : ℂ))).PosSemidef ↔
      (diagonal (fun j => ((x / D j : ℝ) : ℂ)) - B).PosSemidef := by
  have hstar : star (diagonal (fun j => (Real.sqrt (D j) : ℂ))) =
      diagonal (fun j => (Real.sqrt (D j) : ℂ)) := by
    rw [star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext j
    simp
  have hunit : IsUnit (diagonal (fun j => (Real.sqrt (D j) : ℂ))) := by
    rw [isUnit_diagonal, Pi.isUnit_iff]
    intro j
    rw [isUnit_iff_ne_zero, Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (hD j)).ne'
  have heq : (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      diagonal (fun j => (Real.sqrt (D j) : ℂ)) * B * diagonal (fun j => (Real.sqrt (D j) : ℂ)) =
      diagonal (fun j => (Real.sqrt (D j) : ℂ)) * (diagonal (fun j => ((x / D j : ℝ) : ℂ)) - B) *
        star (diagonal (fun j => (Real.sqrt (D j) : ℂ))) := by
    rw [hstar, Matrix.mul_sub, Matrix.sub_mul, diagonal_mul_diagonal, diagonal_mul_diagonal,
      smul_one_eq_diagonal]
    congr 1
    congr 1
    funext j
    have hr : Real.sqrt (D j) * (x / D j) * Real.sqrt (D j) = x := by
      rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt (hD j).le]
      field_simp [(hD j).ne']
    exact_mod_cast hr.symm
  rw [heq]
  exact hunit.posSemidef_star_right_conjugate_iff

/-- Deterministic-`A` limit (BBP / Paul): given `Q3` and `Q4`, for deterministic Hermitian `A_n`
with bounded spectrum and `(1/M) tr A_n² ∈ [s₀, S₁]`, spike strengths `D_n = L_n` on the first `k`
coordinates and `D_n ∈ [c, L_n - c]` on the last `q`, and thresholds `x_n ≥ x₀ > 0` with
`√M (x_n - L_n m_n) / (L_n s_n) → t`, the probability `P(x_n - M⁻¹ Δ H A Hᴴ Δ ⪰ 0) → G k t`. -/
theorem detLimit {k q : ℕ} (hk : 1 ≤ k) (hQ3 : Q3_sesqCLT)
    (hQ4 : ∀ x : ℝ, (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x)
    (hG : Continuous (G k))
    (C s₀ S₁ c x₀ : ℝ) (hs₀ : 0 < s₀) (hc : 0 < c) (hx₀ : 0 < x₀)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ) (hAH : ∀ n, (A n).IsHermitian)
    (hAC : ∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef)
    (hAs : ∀ n, s₀ ≤ ((A n * A n).trace).re / M n)
    (hAs1 : ∀ n, ((A n * A n).trace).re / M n ≤ S₁)
    (L : ℕ → ℝ) (hL : ∀ n, c ≤ L n ∧ L n ≤ C)
    (D : ℕ → Fin (k + q) → ℝ) (hD1 : ∀ n i, D n (Fin.castAdd q i) = L n)
    (hD2 : ∀ n j, c ≤ D n (Fin.natAdd k j) ∧ D n (Fin.natAdd k j) ≤ L n - c)
    (x : ℕ → ℝ) (hx : ∀ n, x₀ ≤ x n) (t : ℝ)
    (ht : Tendsto (fun n => Real.sqrt (M n) * (x n - L n * (((A n).trace).re / M n)) /
        (L n * Real.sqrt (((A n * A n).trace).re / M n))) atTop (𝓝 t)) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
      {X | ((x n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
        (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef})
      atTop (𝓝 (G k t)) := by
  have hM1 : ∀ n, 0 < (M n : ℝ) := fun n => by
    by_contra h
    push_neg at h
    have h0 : (M n : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    have := hAs n
    rw [h0, div_zero] at this
    linarith only [this, hs₀]
  have hS₁ : 0 < S₁ := lt_of_lt_of_le hs₀ ((hAs 0).trans (hAs1 0))
  have hC : 0 < C := lt_of_lt_of_le hc ((hL 0).1.trans (hL 0).2)
  set s : ℕ → ℝ := fun n => Real.sqrt (((A n * A n).trace).re / M n) with hs_def
  set m : ℕ → ℝ := fun n => ((A n).trace).re / M n with hm_def
  have hs_pos : ∀ n, 0 < s n := fun n => Real.sqrt_pos.mpr (lt_of_lt_of_le hs₀ (hAs n))
  have hs_le : ∀ n, s n ≤ Real.sqrt S₁ := fun n => Real.sqrt_le_sqrt (hAs1 n)
  have hsM : ∀ n, 0 < Real.sqrt (M n) := fun n => Real.sqrt_pos.mpr (hM1 n)
  have hDpos : ∀ n j, 0 < D n j := fun n j => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [hD1]; linarith only [(hL n).1, hc]
    · linarith only [(hD2 n i).1, hc]
  have htr : ∀ n, (((A n).trace.re : ℝ) : ℂ) = (A n).trace := fun n => by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      rw [Matrix.trace, Complex.im_sum]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      have h := (hAH n).apply i i
      exact Complex.conj_eq_iff_im.mp h
  have hmc : ∀ n, (M n : ℂ)⁻¹ * (A n).trace = ((m n : ℝ) : ℂ) := fun n => by
    rw [← htr n, hm_def]
    push_cast
    ring
  -- the centred, rescaled matrix of Q3
  let T : ∀ n, (Fin (M n) → Fin (k + q) → ℂ) → (Fin (k + q) → Fin (k + q) → ℂ) := fun n X =>
    (((Real.sqrt (M n) / Real.sqrt (((A n * A n).trace).re / M n) : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ)))
  have hweak : ∀ f : (Fin (k + q) → Fin (k + q) → ℂ) → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
      Tendsto (fun n => ∫ X, f (T n X) ∂SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)) atTop
        (𝓝 (∫ Z, f (gueMat Z) ∂SpikedWishart.SoftEdge.sampleLaw (k + q) (k + q))) :=
    fun f hf hb => hQ3 (k + q) C s₀ hs₀ M hM A hAH hAC hAs f hf hb
  have hofT : ∀ n X, Matrix.of (T n X) = ((Real.sqrt (M n) / s n : ℝ) : ℂ) •
      ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
        ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ)) := fun n X => rfl
  have hTc : ∀ n, Continuous (T n) := fun n => by
    have h0 : Continuous fun X : Fin (M n) → Fin (k + q) → ℂ => Matrix.of X := continuous_id
    have h1 : Continuous fun X : Fin (M n) → Fin (k + q) → ℂ =>
        (Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ :=
      (h0.matrix_transpose.matrix_mul (continuous_const (y := A n))).matrix_mul
        h0.matrix_transpose.matrix_conjTranspose
    exact ((h1.const_smul ((M n : ℂ)⁻¹)).sub (continuous_const (y := ((M n : ℂ)⁻¹ * (A n).trace) •
      (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ)))).const_smul
        ((Real.sqrt (M n) / s n : ℝ) : ℂ)
  have hH : ∀ n X, (Matrix.of (T n X)).IsHermitian := fun n X => by
    have hsa : ∀ r : ℝ, IsSelfAdjoint (r : ℂ) := fun r => by
      show star (r : ℂ) = r
      simp
    have hMi : (M n : ℂ)⁻¹ = (((M n : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [hofT n X, hmc n, hMi]
    exact ((((isHermitian_mul_mul_conjTranspose _ (hAH n)).smul (hsa _)).sub
      (isHermitian_one.smul (hsa _))).smul (hsa _))
  -- the diagonal shift
  let d : ℕ → Fin (k + q) → ℝ := fun n j => (x n / D n j - m n) * (Real.sqrt (M n) / s n)
  have hd1 : ∀ n i, d n (Fin.castAdd q i) =
      Real.sqrt (M n) * (x n - L n * m n) / (L n * s n) := fun n i => by
    simp only [d, hD1]
    have hL0 : L n ≠ 0 := (lt_of_lt_of_le hc (hL n).1).ne'
    field_simp [hL0, (hs_pos n).ne']
  have hsqrt : ∀ R : ℝ, ∀ᶠ n in atTop, R ≤ Real.sqrt (M n) := fun R => by
    have := (tendsto_natCast_atTop_atTop.comp hM).eventually_ge_atTop (R ^ 2)
    filter_upwards [this] with n hn
    exact (le_abs_self R).trans (Real.abs_le_sqrt hn)
  have hd2 : ∀ B : ℝ, ∀ᶠ n in atTop, ∀ j, B ≤ d n (Fin.natAdd k j) := fun B => by
    set κ : ℝ := x₀ * (c / C ^ 2) / Real.sqrt S₁ with hκ
    have hκ0 : 0 < κ := by rw [hκ]; have := Real.sqrt_pos.mpr hS₁; positivity
    have hlow : ∀ᶠ n in atTop, t - 1 < Real.sqrt (M n) * (x n - L n * m n) / (L n * s n) :=
      (tendsto_order.1 ht).1 _ (sub_one_lt t)
    filter_upwards [hlow, hsqrt ((B - t + 1) / κ)] with n h1 h2 j
    have hDj := hDpos n (Fin.natAdd k j)
    have hLn : 0 < L n := lt_of_lt_of_le hc (hL n).1
    have hdj : d n (Fin.natAdd k j) = Real.sqrt (M n) * (x n - L n * m n) / (L n * s n) +
        x n * ((L n - D n (Fin.natAdd k j)) / (D n (Fin.natAdd k j) * L n)) *
          (Real.sqrt (M n) / s n) := by
      simp only [d]
      field_simp [hDj.ne', hLn.ne', (hs_pos n).ne']
      ring
    have hDC : D n (Fin.natAdd k j) ≤ C := by linarith only [(hD2 n j).2, (hL n).2, hc]
    have hDL : D n (Fin.natAdd k j) * L n ≤ C ^ 2 := by
      rw [sq]; exact mul_le_mul hDC (hL n).2 hLn.le hC.le
    have a1 : c / C ^ 2 ≤ (L n - D n (Fin.natAdd k j)) / (D n (Fin.natAdd k j) * L n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : c ≤ L n - D n (Fin.natAdd k j) := by linarith only [(hD2 n j).2]
      calc c * (D n (Fin.natAdd k j) * L n) ≤ c * C ^ 2 := mul_le_mul_of_nonneg_left hDL hc.le
        _ ≤ (L n - D n (Fin.natAdd k j)) * C ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
    have a2 : Real.sqrt (M n) / Real.sqrt S₁ ≤ Real.sqrt (M n) / s n :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (hs_pos n) (hs_le n)
    have a3 : x₀ * (c / C ^ 2) * (Real.sqrt (M n) / Real.sqrt S₁) ≤
        x n * ((L n - D n (Fin.natAdd k j)) / (D n (Fin.natAdd k j) * L n)) *
          (Real.sqrt (M n) / s n) :=
      mul_le_mul (mul_le_mul (hx n) a1 (by positivity) (by linarith only [hx n, hx₀])) a2 (by positivity)
        (mul_nonneg (by linarith only [hx n, hx₀]) (le_trans (by positivity) a1))
    have a4 : x₀ * (c / C ^ 2) * (Real.sqrt (M n) / Real.sqrt S₁) = κ * Real.sqrt (M n) := by
      rw [hκ]; ring
    have a5 : B - t + 1 ≤ κ * Real.sqrt (M n) := by
      have := (div_le_iff₀ hκ0).mp h2
      linarith only [this]
    rw [hdj]
    linarith only [h1, a3, a4, a5]
  -- event identity
  have hev : ∀ n, {X : Fin (M n) → Fin (k + q) → ℂ | ((x n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
        (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef} =
      {X | (diagonal (fun j => (d n j : ℂ)) - Matrix.of (T n X)).PosSemidef} := fun n => by
    ext X
    simp only [Set.mem_setOf_eq]
    have e1 : (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ))) =
        diagonal (fun j => (Real.sqrt (D n j) : ℂ)) *
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ)) *
          diagonal (fun j => (Real.sqrt (D n j) : ℂ)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [e1, psd_congr_diag (D n) (hDpos n) (x n)]
    have hε : 0 < s n / Real.sqrt (M n) := div_pos (hs_pos n) (hsM n)
    have hεε : ((s n / Real.sqrt (M n) : ℝ) : ℂ) * ((Real.sqrt (M n) / s n : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, div_mul_div_comm, mul_comm (s n), div_self, Complex.ofReal_one]
      exact (mul_pos (hsM n) (hs_pos n)).ne'
    have e2 : diagonal (fun j => ((x n / D n j : ℝ) : ℂ)) -
        (M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) =
        ((s n / Real.sqrt (M n) : ℝ) : ℂ) • (diagonal (fun j => (d n j : ℂ)) - Matrix.of (T n X)) := by
      rw [hofT n X, hmc n]
      ext i j
      simp only [d, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
        smul_eq_mul]
      generalize ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) i j = u
      push_cast at hεε ⊢
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        linear_combination (-((x n : ℂ) / (D n i : ℂ) - (M n : ℂ)⁻¹ * u)) * hεε
      · simp only [hij, if_false]
        linear_combination ((M n : ℂ)⁻¹ * u) * hεε
    rw [e2, psd_scale_iff _ _ hε]
  have key := cdf_block hk hQ4 hG (fun n => SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)) T
    (fun n => (hTc n).measurable) hH hweak d
    (fun n => Real.sqrt (M n) * (x n - L n * m n) / (L n * s n)) t ht hd1 hd2
  refine key.congr fun n => ?_
  rw [hev n]

end

-- ===== from GContinuous.lean =====
section

theorem pair_bound (D a b : ℝ) (hD : 0 < D) (s : ℝ) (hs : a ^ 2 + b ^ 2 ≤ s) :
    |a - b| ^ 2 ≤ (2 * D + 1) * Real.exp (s / D) := by
  have h1 : |a - b| ^ 2 ≤ 2 * s := by
    rw [sq_abs]; nlinarith [sq_nonneg (a + b)]
  have h2 : s / D + 1 ≤ Real.exp (s / D) := Real.add_one_le_exp _
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have h3 : 2 * s = 2 * D * (s / D) := by field_simp
  have h4 : 0 ≤ s / D := div_nonneg hs0 hD.le
  have h5 : 1 ≤ Real.exp (s / D) := Real.one_le_exp h4
  have h6 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * D)
  nlinarith

theorem two_le_sum {k : ℕ} (ξ : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j) :
    ξ i ^ 2 + ξ j ^ 2 ≤ ∑ l, ξ l ^ 2 := by
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => ξ l ^ 2)
    (Finset.subset_univ {i, j}) (fun l _ _ => sq_nonneg (ξ l))
  rwa [Finset.sum_pair hij] at this

theorem pairProd_le {k : ℕ} (ξ : Fin k → ℝ) (D : ℝ) (hD : 0 < D) :
    (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, |ξ i - ξ j| ^ 2) ≤
      ((2 * D + 1) * Real.exp ((∑ l, ξ l ^ 2) / D)) ^ (k * k) := by
  set c := (2 * D + 1) * Real.exp ((∑ l, ξ l ^ 2) / D) with hc
  have hc1 : 1 ≤ c := by
    have : 1 ≤ Real.exp ((∑ l, ξ l ^ 2) / D) :=
      Real.one_le_exp (div_nonneg (Finset.sum_nonneg fun l _ => sq_nonneg _) hD.le)
    nlinarith
  calc (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, |ξ i - ξ j| ^ 2)
      ≤ ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, c := by
        apply Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by positivity)
        intro i _
        apply Finset.prod_le_prod (fun j _ => by positivity)
        intro j hj
        have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
        exact pair_bound D _ _ hD _ (two_le_sum ξ i j hij)
    _ ≤ ∏ _i : Fin k, c ^ k := by
        apply Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by linarith)
        intro i _
        rw [Finset.prod_const]
        exact pow_le_pow_right₀ hc1 (by simpa using Finset.card_le_univ (Finset.Ioi i))
    _ = c ^ (k * k) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem gueWeight_nonneg (k : ℕ) (ξ : Fin k → ℝ) : 0 ≤ gueWeight k ξ := by
  unfold gueWeight; positivity

theorem gueWeight_le (k : ℕ) (ξ : Fin k → ℝ) :
    gueWeight k ξ ≤ (2 * (4 * (k : ℝ) * k + 4) + 1) ^ (k * k) *
      ∏ i : Fin k, Real.exp (-(1 / 4) * ξ i ^ 2) := by
  have hD0 : (0 : ℝ) < 4 * (k : ℝ) * k + 4 := by positivity
  have hs0 : 0 ≤ ∑ l, ξ l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hB : ∏ i : Fin k, Real.exp (-(1 / 2) * ξ i ^ 2) = Real.exp (-(1 / 2) * ∑ l, ξ l ^ 2) := by
    rw [← Real.exp_sum, Finset.mul_sum]
  have hH : ∏ i : Fin k, Real.exp (-(1 / 4) * ξ i ^ 2) = Real.exp (-(1 / 4) * ∑ l, ξ l ^ 2) := by
    rw [← Real.exp_sum, Finset.mul_sum]
  unfold gueWeight
  rw [hB, hH]
  have hA := pairProd_le ξ (4 * (k : ℝ) * k + 4) hD0
  set s := ∑ l, ξ l ^ 2 with hs
  set D : ℝ := 4 * (k : ℝ) * k + 4 with hD
  have hkey : ((k * k : ℕ) : ℝ) * (s / D) ≤ s / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hD0 (by norm_num)]
    push_cast
    nlinarith
  calc _ ≤ ((2 * D + 1) * Real.exp (s / D)) ^ (k * k) * Real.exp (-(1 / 2) * s) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ = (2 * D + 1) ^ (k * k) * Real.exp (((k * k : ℕ) : ℝ) * (s / D) + (-(1 / 2) * s)) := by
        rw [mul_pow, ← Real.exp_nat_mul, Real.exp_add]; ring
    _ ≤ (2 * D + 1) ^ (k * k) * Real.exp (-(1 / 4) * s) := by
        gcongr
        linarith

theorem gueWeight_continuous (k : ℕ) : Continuous (gueWeight k) := by
  unfold gueWeight
  refine Continuous.mul ?_ ?_
  · exact continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ =>
      (((continuous_apply i).sub (continuous_apply j)).abs).pow 2
  · exact continuous_finsetProd _ fun i _ =>
      Real.continuous_exp.comp (continuous_const.mul ((continuous_apply i).pow 2))

theorem gueWeight_integrable (k : ℕ) : Integrable (gueWeight k) := by
  have hdom : Integrable (fun ξ : Fin k → ℝ => (2 * (4 * (k : ℝ) * k + 4) + 1) ^ (k * k) *
      ∏ i : Fin k, Real.exp (-(1 / 4) * ξ i ^ 2)) := by
    refine Integrable.const_mul ?_ _
    exact Integrable.fintype_prod (f := fun _ t => Real.exp (-(1 / 4) * t ^ 2))
      (fun _ => integrable_exp_neg_mul_sq (by norm_num))
  refine hdom.mono' (gueWeight_continuous k).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gueWeight_nonneg k ξ)]
  exact gueWeight_le k ξ

/-- P7: `G k` is continuous. -/
theorem G_continuous (k : ℕ) : Continuous (G k) := by
  have hint := gueWeight_integrable k
  have hG : G k = fun x => (1 / Z k) *
      ∫ ξ, (Set.pi univ (fun _ : Fin k => Iic x)).indicator (gueWeight k) ξ := by
    funext x; unfold G; rw [integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Iic)]
  rw [hG]
  refine Continuous.mul continuous_const ?_
  rw [continuous_iff_continuousAt]
  intro x0
  refine continuousAt_of_dominated (bound := gueWeight k) ?_ ?_ hint ?_
  · exact Eventually.of_forall fun x =>
      (hint.indicator (MeasurableSet.univ_pi fun _ => measurableSet_Iic)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ξ _ => gueWeight_nonneg k ξ) ξ)]
    exact Set.indicator_le_self' (fun ξ _ => gueWeight_nonneg k ξ) ξ
  · have hae : ∀ᵐ ξ : Fin k → ℝ, ∀ i, ξ i ≠ x0 := by
      rw [ae_all_iff]; intro i
      rw [ae_iff]; simp only [ne_eq, not_not]
      rw [volume_pi]; exact Measure.pi_hyperplane (fun _ : Fin k => (volume : Measure ℝ)) i x0
    filter_upwards [hae] with ξ hξ
    by_cases h : ∀ i, ξ i < x0
    · have hev : ∀ᶠ x in 𝓝 x0, ∀ i, ξ i ≤ x := by
        rw [eventually_all]; intro i; exact (eventually_gt_nhds (h i)).mono fun x hx => hx.le
      apply Filter.EventuallyEq.continuousAt (y := gueWeight k ξ)
      filter_upwards [hev] with x hx
      rw [Set.indicator_of_mem]
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
      exact hx
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      have hi' : x0 < ξ i := lt_of_le_of_ne hi (Ne.symm (hξ i))
      apply Filter.EventuallyEq.continuousAt (y := 0)
      filter_upwards [eventually_lt_nhds hi'] with x hx
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies, not_forall, not_le]
      exact ⟨i, hx⟩

end

-- ===== from DL.lean =====
section

/-- DL from Q3 and Q4 (`detLimit` with the GUE law and the continuity of `G k`). -/
theorem dl_of : DL_of := by
  intro h3 h4 k q hk C s₀ S₁ c x₀ hs₀ hc hx₀ M hM A hAH hAC hAs hAs1 L hL D hD1 hD2 x hx t ht
  exact detLimit hk h3 (h4 k hk) (G_continuous k) C s₀ S₁ c x₀ hs₀ hc hx₀ M hM A hAH hAC hAs hAs1
    L hL D hD1 hD2 x hx t ht

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution :
  (∀ (r : ℕ) (C s₀ : ℝ), 0 < s₀ → ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    ∀ f : Matrix (Fin r) (Fin r) ℂ → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
    Tendsto (fun n => ∫ X, f (((Real.sqrt (M n) / Real.sqrt (((A n * A n).trace).re / M n) : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))
        ∂(SpikedWishart.SoftEdge.sampleLaw (M n) r))
      atTop (𝓝 (∫ Z, f ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ))
        ∂(SpikedWishart.SoftEdge.sampleLaw r r)))) →
  (∀ (k : ℕ), 1 ≤ k → ∀ x : ℝ,
    (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x) →
  ∀ (k q : ℕ), 1 ≤ k → ∀ (C s₀ S₁ c x₀ : ℝ), 0 < s₀ → 0 < c → 0 < x₀ →
    ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    (∀ n, ((A n * A n).trace).re / M n ≤ S₁) →
    ∀ (L : ℕ → ℝ), (∀ n, c ≤ L n ∧ L n ≤ C) →
    ∀ (D : ℕ → Fin (k + q) → ℝ), (∀ n i, D n (Fin.castAdd q i) = L n) →
    (∀ n j, c ≤ D n (Fin.natAdd k j) ∧ D n (Fin.natAdd k j) ≤ L n - c) →
    ∀ (x : ℕ → ℝ), (∀ n, x₀ ≤ x n) → ∀ (t : ℝ),
    Tendsto (fun n => Real.sqrt (M n) * (x n - L n * (((A n).trace).re / M n)) /
        (L n * Real.sqrt (((A n * A n).trace).re / M n))) atTop (𝓝 t) →
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
      {X | ((x n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
        (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef})
      atTop (𝓝 (G k t)) := by
  exact SpikedWishart.Separated.Lib.dl_of
