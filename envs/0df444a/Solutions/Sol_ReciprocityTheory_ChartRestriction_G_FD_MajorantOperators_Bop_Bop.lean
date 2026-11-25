-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.Bop_Bop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:29.523593+00:00
-- url     : https://prove2.me/submissions/0ffdf983-b945-4dae-be29-bce2b0fafb2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_conj_purely_imaginary_generator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_jp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_smul
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
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
section dataX
variable {Y : DataX E r}
private theorem two_tau_neg_xi0_sq_eq_neg_k0_sq (τ : Y.Ψ) :
    (2 * τ.1 (-Y.ξ0)) * (2 * τ.1 (-Y.ξ0)) = -((Y.k0 : ℂ) ^ 2) := by
  have h1 := conj_purely_imaginary_generator (X := Y.toData) τ
  have h2 : τ.1 Y.ξ0 * conj (τ.1 Y.ξ0) = (((Y.k0 / 2) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ξ0_abs τ]
  rw [h1] at h2
  rw [map_neg]
  push_cast at h2 ⊢
  linear_combination -4 * h2
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
variable {Y : DataX E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
theorem _root_.solution {z : Frame Y.Ψ r} (hz : z ∈ Y.dom) (u : Y.Ψ → Fin r → ℂ) :
    Bop (X := Y.toData) z (Bop (X := Y.toData) z u) = (-(Y.k0 ^ 2) : ℝ) • u := by
  funext τ
  simp only [Bop, Data.jp_smul, Data.jp_jp Y.toData hz, smul_smul, Pi.smul_apply]
  rw [two_tau_neg_xi0_sq_eq_neg_k0_sq τ]
  ext a
  simp [Complex.real_smul]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
