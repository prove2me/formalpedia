-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.flow_mem_of_tube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:29.086932+00:00
-- url     : https://prove2.me/submissions/98ad7c09-de2e-4e5f-8fe1-3b1fb090c9ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
section line
variable {X}
private lemma hsubl_lemma_21 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (u u' w : Fin n → ℂ) : hermC σ G (u - u') w = hermC σ G u w - hermC σ G u' w := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private lemma hsmull_lemma_22 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (k : ℂ) (u w : Fin n → ℂ) : hermC σ G (k • u) w = k * hermC σ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
private lemma hsubr_lemma_23 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (v w w' : Fin n → ℂ) : hermC σ G v (w - w') = hermC σ G v w - hermC σ G v w' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
private lemma hsmulr_lemma_24 {n : ℕ} (σ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (k : ℂ) (v w : Fin n → ℂ) : hermC σ G v (k • w) = conj k * hermC σ G v w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma hconj_lemma_25 (τ : X.Ψ) (u v : Fin r → ℂ) :
    conj (hermC τ.1 X.Gm u v) = hermC τ.1 X.Gm v u := by
  have hG : ∀ a b, conj (τ.1 (X.Gm a b)) = τ.1 (X.Gm b a) := by
    intro a b
    rw [← X.Gm_herm a b]
    first
      | simp [cc, IsCMField.complexEmbedding_complexConj]
      | simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  simp only [hermC, map_sum, map_mul, Complex.conj_conj, hG]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma huu_lemma_26 {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
  have h : τ.1 (herm X.Gm ξ ξ) = hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) := by
    first
      | simp [herm, hermC, Data.emb, cc, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
      | simp [herm, hermC, Data.emb, cc, map_sum, map_mul,
          NumberField.IsCMField.complexEmbedding_complexConj]
  rw [← h, hξ, map_zero]
private lemma colmul_lemma_27 (A M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (A * M) a = A *ᵥ col M a := by
  funext k
  simp only [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
private lemma flowmv_lemma_28 (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (p : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ p =
      p - (I * (X.c τ : ℂ) * s * hermC τ.1 X.Gm p (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.flowMat, Matrix.of_apply, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hermC, Data.emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring
private lemma gramflow_lemma_29 {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.flowMat ξ τ s * M) =
      gram τ.1 X.Gm M + ((2 * X.c τ * s.im : ℝ) : ℂ) • rk1 X ξ τ M := by
  ext a b
  have hu := huu_lemma_26 hξ τ
  simp only [gram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rk1,
    Matrix.vecMulVec_apply, hv]
  rw [colmul_lemma_27, colmul_lemma_27, flowmv_lemma_28, flowmv_lemma_28]
  simp only [hsubl_lemma_21, hsubr_lemma_23, hsmull_lemma_22, hsmulr_lemma_24, hu]
  rw [← hconj_lemma_25 τ (col M b) (Data.emb τ.1 ξ)]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
  have hs : (starRingEnd ℂ) s = s - 2 * I * (s.im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [hs]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring
private lemma flowdet_lemma_210 {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ) :
    (X.flowMat ξ τ s).det ≠ 0 := by
  have hu := huu_lemma_26 hξ τ
  have key : ∀ p, (X.flowMat ξ τ s * X.flowMat ξ τ (-s)) *ᵥ p = p := by
    intro p
    rw [← Matrix.mulVec_mulVec, flowmv_lemma_28, flowmv_lemma_28]
    simp only [hsubl_lemma_21, hsmull_lemma_22, hu, mul_zero, sub_zero]
    funext a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hinv : X.flowMat ξ τ s * X.flowMat ξ τ (-s) = 1 := by
    ext a b
    have h1 := congrFun (key (Pi.single b 1)) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h1
  have h2 := congrArg Matrix.det hinv
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact left_ne_zero_of_mul_eq_one h2
end line
end
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
variable {X}
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
theorem _root_.solution {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) {s : Fin (Fintype.card X.Ψ) → ℂ}
    (hs : s ∈ tube (Fintype.card X.Ψ) (Om ξ x ω)) :
    X.flow ξ (fun τ => ∑ j, s j * (ω j τ : ℂ)) x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (X.flowMat ξ τ (∑ j, s j * (ω j τ : ℂ)) * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (flowdet_lemma_210 hξ τ _) (hx τ).1
  · show 0 < psgn X.p0 i *
      (lminor (gram τ.1 X.Gm (X.flowMat ξ τ (∑ j, s j * (ω j τ : ℂ)) * mat x τ)) i).re
    have h1 : (fun τ => ∑ j, (s j).im * ω j τ) ∈ admissibleImaginary X ξ x := hs
    have h2 := h1 τ i
    have him : (∑ j, s j * (ω j τ : ℂ)).im = ∑ j, (s j).im * ω j τ := by
      simp [Complex.im_sum]
    rw [gramflow_lemma_29 hξ τ, him]
    exact h2
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
