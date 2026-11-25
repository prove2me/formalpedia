-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.ucomp_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:28.579849+00:00
-- url     : https://prove2.me/submissions/408b00f1-3a13-405d-a6d4-a896f73c5b11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
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
namespace RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E)
variable [hz : Fact (z ∈ X.dom)]
private lemma Hf_smul_left_frame (y : Frame X.Ψ r) (σ : X.Ψ) (c : ℂ) (v w : Fin r → ℂ) :
    X.Hf y σ (c • v) w = c * X.Hf y σ v w := by
  have hp : X.ppos y σ (c • v) = c • X.ppos y σ v := by
    simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum]
  rw [Data.Hf, Data.Hf, hp, ← hermC_smul_left]
  congr 1
  rw [smul_sub, smul_smul, smul_smul, mul_comm]
end RealTangentSpace
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E)
variable [hz : Fact (z ∈ X.dom)]
namespace ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
theorem _root_.solution (hξ : X.IsIso ξ) (e : E) : X.ucomp z ξ (X.embV (e • ξ)) = 0 := by
  funext τ
  have hξ0 : Data.emb τ.1 ξ ≠ 0 := by
    intro h
    apply hξ.2.2
    funext a
    have := congrFun h a
    simpa [Data.emb] using this
  have hpos : X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hz.out]
    exact_mod_cast (X.maj_pos hz.out τ hξ0).ne'
  have hw : X.embV (e • ξ) τ = τ.1 e • Data.emb τ.1 ξ := by
    funext a
    simp [Data.embV, Data.emb]
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.sub_apply, Pi.zero_apply, hw, Hf_smul_left_frame,
    mul_div_assoc, div_self hpos, mul_one, sub_self]
end ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
