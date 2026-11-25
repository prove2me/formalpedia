-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.ucomp_drop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:20.318879+00:00
-- url     : https://prove2.me/submissions/6084b528-f8c1-496f-b06e-bd855f452b75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsPerpHermitianReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_emb_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_embV_add_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicIndexSums_ucomp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
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
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section Sesq
variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
private lemma hermC_add_left_eq_add (u v w : Fin r → ℂ) :
    hermC τ G (u + v) w = hermC τ G u w + hermC τ G v w := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private lemma hermC_const_smul_left (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end Sesq
section Sig
variable (X : Data E r)
end Sig
section Ucomp
variable (X : Data E r)
private lemma ppos_add_smul (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) (c : ℂ) :
    X.ppos x τ (u + c • w) = X.ppos x τ u + c • X.ppos x τ w := by
  unfold Data.ppos
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, ← add_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hermC_add_left_eq_add, hermC_const_smul_left]
  ring
end Ucomp
end
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hne : ξ ≠ 0)
    (v : Fin r → E) (e : E) (τ : X.Ψ) :
    X.ucomp x ξ (X.embV (v + e • ξ)) τ = X.ucomp x ξ (X.embV v) τ := by
  have hw0 : Data.emb τ.1 ξ ≠ 0 := emb_ne hne τ.1
  have hH : X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [Data.Hf_self X hx]
    exact_mod_cast (Data.maj_pos X hx τ hw0).ne'
  have hlin : ∀ (u w : Fin r → ℂ) (c : ℂ), X.Hf x τ (u + c • w) (Data.emb τ.1 ξ) =
      X.Hf x τ u (Data.emb τ.1 ξ) + c * X.Hf x τ w (Data.emb τ.1 ξ) := by
    intro u w c
    simp only [Data.Hf, ppos_add_smul]
    rw [show (2 : ℂ) • (X.ppos x τ u + c • X.ppos x τ w) - (u + c • w) =
        ((2 : ℂ) • X.ppos x τ u - u) + c • ((2 : ℂ) • X.ppos x τ w - w) by module]
    rw [hermC_add_left_eq_add, hermC_const_smul_left]
  rw [ucomp_apply, ucomp_apply, embV_add_smul, hlin, add_div, mul_div_cancel_right₀ _ hH, add_smul]
  abel
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums
