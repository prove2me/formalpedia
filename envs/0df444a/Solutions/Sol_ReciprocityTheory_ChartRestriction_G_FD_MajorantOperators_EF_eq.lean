-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.EF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:34:02.224079+00:00
-- url     : https://prove2.me/submissions/3e5d3091-6f74-40e5-aff7-16e2a04efdb4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_Bop_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_trace_eq_sum
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
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
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
private theorem hermC_smul_left_embedding (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (k : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (k • u) v = k * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
private theorem hermC_sub_left_of_natDim (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private theorem hermC_sub_right_of_conj_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
private theorem hermC_smul_right_embedding (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (k : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (k • v) = conj k * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private theorem hermC_emb_emb_eq_tau_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]
private theorem hermC_ucomp_ucomp_of_herm_eq_zero {z : Frame X.Ψ r} {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0)
    {μ ν : Fin r → E} (hμ : herm X.Gm μ ξ = 0) (hν : herm X.Gm ν ξ = 0) (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.ucomp z ξ (X.embV μ) τ) (X.ucomp z ξ (X.embV ν) τ) = τ.1 (herm X.Gm μ ν) := by
  simp only [Data.ucomp, Data.aproj, Data.lineV, Data.embV, Pi.sub_apply]
  have e1 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_tau_herm, hμ, map_zero]
  have e2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ν) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, hermC_emb_emb_eq_tau_herm, hν, map_zero, map_zero]
  have e3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_tau_herm, hξξ, map_zero]
  simp only [hermC_sub_left_of_natDim, hermC_sub_right_of_conj_symm, hermC_smul_left_embedding, hermC_smul_right_embedding, e1, e2, e3,
    mul_zero, sub_zero]
  exact hermC_emb_emb_eq_tau_herm _ _ _ _
section dataX
variable {Y : DataX E r}
end dataX
end MajorantOperators
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0)
    {μ ν : Fin r → E} (hμ : herm X.Gm μ ξ = 0) (hν : herm X.Gm ν ξ = 0) :
    ((EFf X.ξ0 X.Gm μ ν : ℚ) : ℝ) =
      gI z (Bop z (X.ucomp z ξ (X.embV μ))) (X.ucomp z ξ (X.embV ν)) := by
  unfold EFf
  rw [trace_eq_sum (X := X), gI_Bop_left hz]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hermC_ucomp_ucomp_of_herm_eq_zero hξξ hμ hν τ, map_mul, mul_assoc]
  simp [Complex.mul_re]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
