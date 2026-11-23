-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.dmin_flow_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:05.094112+00:00
-- url     : https://prove2.me/submissions/b47f994f-bf44-45ad-97b5-514b2a23d110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma hermC_sub_smul_sub_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v w : Fin r → ℂ) (α β : ℂ) :
    hermC τ G (u - α • w) (v - β • w) = hermC τ G u v - starRingEnd ℂ β * hermC τ G u w -
      α * hermC τ G w v + α * starRingEnd ℂ β * hermC τ G w w := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma hermC_emb_self_eq_zero_of_herm_self_eq_zero {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    hermC τ.1 X.Gm (fun k => τ.1 (ξ k)) (fun k => τ.1 (ξ k)) = 0 := by
  have h := congrArg τ.1 hξ
  rw [map_zero] at h
  rw [← h]
  simp only [hermC, herm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cc, NumberField.IsCMField.complexEmbedding_complexConj (K := E)]
private lemma hermC_eq_conj_hermC_swap' (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = starRingEnd ℂ (hermC τ.1 X.Gm v u) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hG : τ.1 (X.Gm b a) = starRingEnd ℂ (τ.1 (X.Gm a b)) := by
    rw [← X.Gm_herm a b, cc, NumberField.IsCMField.complexEmbedding_complexConj (K := E)]
  rw [hG]
  ring
private lemma col_flowMat_mul (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (M : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) :
    col (X.flowMat ξ τ s * M) a = col M a -
      (I * X.c τ * s * hermC τ.1 X.Gm (col M a) (fun k => τ.1 (ξ k))) • (fun k => τ.1 (ξ k)) := by
  funext k
  simp only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hermC, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
  ring
end
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
theorem _root_.solution {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (x : Frame X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm (X.flow ξ (cR X p) x) τ i = dmin X.Gm x τ i := by
  have key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r),
      hermC τ.1 X.Gm (col (X.flowMat ξ τ (p τ) * M) a) (col (X.flowMat ξ τ (p τ) * M) b) =
      hermC τ.1 X.Gm (col M a) (col M b) := by
    intro M a b
    rw [col_flowMat_mul, col_flowMat_mul, hermC_sub_smul_sub_smul, hermC_emb_self_eq_zero_of_herm_self_eq_zero X hξ τ,
      hermC_eq_conj_hermC_swap' X τ (fun k => τ.1 (ξ k)) (col M b)]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  unfold dmin
  congr 1
  ext a b
  exact key (mat x τ) a b
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
