-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.flow_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:44.42537+00:00
-- url     : https://prove2.me/submissions/0c506fc7-7614-4d5b-9b7c-a534ad46bbce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg {r : ℕ} (g : Fin r → Fin r → ℂ) (hg : ∀ a b, conj (g a b) = g b a)
    (z v w : Fin r → ℂ) (α : ℂ) (hα : conj α = -α)
    (hz : ∑ a, ∑ b, z a * g a b * conj (z b) = 0) :
    ∑ a, ∑ b, (v a - α * (∑ p, ∑ q, v p * g p q * conj (z q)) * z a) * g a b *
        conj (w b - α * (∑ p, ∑ q, w p * g p q * conj (z q)) * z b) =
      ∑ a, ∑ b, v a * g a b * conj (w b) := by
  set A := ∑ p, ∑ q, v p * g p q * conj (z q) with hA
  set B := ∑ p, ∑ q, w p * g p q * conj (z q) with hB
  have hB' : conj B = ∑ a, ∑ b, z a * g a b * conj (w b) := by
    rw [hB, map_sum]
    simp_rw [map_sum, map_mul, Complex.conj_conj, hg]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have expand : ∀ a b, (v a - α * A * z a) * g a b * conj (w b - α * B * z b) =
      v a * g a b * conj (w b) + α * (conj B * (v a * g a b * conj (z b))) -
        α * A * (z a * g a b * conj (w b)) - α * α * A * conj B * (z a * g a b * conj (z b)) := by
    intro a b
    simp only [map_sub, map_mul, hα]
    ring
  simp_rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← hA, ← hB', hz]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
theorem _root_.solution {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℝ) (la : Wt X.Ψ r) :
    X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := by
  have hflow : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) =
      gram τ.1 X.Gm (mat x τ) ∧ (X.flowMat ξ τ (s τ)).det = 1 := by
    intro τ
    have hg : ∀ p q, conj (τ.1 (X.Gm p q)) = τ.1 (X.Gm q p) := fun p q => by
      rw [← X.Gm_herm p q, cc, IsCMField.complexEmbedding_complexConj]
    have hz : ∑ a, ∑ b, τ.1 (ξ a) * τ.1 (X.Gm a b) * conj (τ.1 (ξ b)) = 0 := by
      have h0 := congrArg τ.1 hξ.2.1
      simp only [herm, map_sum, map_mul, map_zero, cc, IsCMField.complexEmbedding_complexConj] at h0
      exact h0
    have hα : conj (I * (X.c τ : ℂ) * (s τ : ℂ)) = -(I * (X.c τ : ℂ) * (s τ : ℂ)) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    constructor
    · ext a b
      show hermC τ.1 X.Gm (col (X.flowMat ξ τ (s τ) * mat x τ) a) (col (X.flowMat ξ τ (s τ) * mat x τ) b) =
        hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b)
      have hcol : ∀ c : Fin r, col (X.flowMat ξ τ (s τ) * mat x τ) c = fun p => col (mat x τ) c p -
          (I * (X.c τ : ℂ) * (s τ : ℂ)) * (∑ p', ∑ q, col (mat x τ) c p' * τ.1 (X.Gm p' q) * conj (τ.1 (ξ q))) * τ.1 (ξ p) := by
        intro c
        funext p
        simp only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
          ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
      unfold hermC
      rw [hcol a, hcol b]
      exact sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (fun p q => τ.1 (X.Gm p q)) hg (fun q => τ.1 (ξ q)) (col (mat x τ) a)
        (col (mat x τ) b) (I * (X.c τ : ℂ) * (s τ : ℂ)) hα hz
    · have hT : X.flowMat ξ τ (s τ) = 1 + Matrix.replicateCol (Fin 1) (fun a => -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ a))) *
          Matrix.replicateRow (Fin 1) (fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) := by
        ext a b
        simp [Data.flowMat, Matrix.mul_apply, Matrix.one_apply] <;> ring
      have h5 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) = 0 := by
        have h6 : ∑ b, (∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))) * -((I * (X.c τ : ℂ) * (s τ : ℂ)) * τ.1 (ξ b)) =
            -(I * (X.c τ : ℂ) * (s τ : ℂ)) * ∑ b, ∑ k, τ.1 (ξ b) * τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h6, hz, mul_zero]
      rw [hT]
      refine (Matrix.det_one_add_replicateCol_mul_replicateRow _ _).trans ?_
      simp only [dotProduct]
      rw [h5, add_zero]
  have hdmin : ∀ τ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i := by
    intro τ i
    unfold dmin
    rw [(hflow τ).1]
  refine ⟨?_, ?_⟩
  · show ∀ τ : X.Ψ, (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i).re
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · show (X.flowMat ξ τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, (hflow τ).2, one_mul]
      exact (hx τ).1
    · rw [hdmin]
      exact (hx τ).2 i
  · unfold Data.nfac
    simp only [hdmin]
end ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds
