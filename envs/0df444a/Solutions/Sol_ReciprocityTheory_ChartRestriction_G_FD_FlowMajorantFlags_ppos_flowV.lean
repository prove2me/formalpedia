-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.ppos_flowV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:00.849741+00:00
-- url     : https://prove2.me/submissions/c5898671-ccab-4e56-9377-da5b2b552d78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_flowMatV_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_col_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_right
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
theorem _root_.solution (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.ppos (X.flowV e s z) τ v = X.ppos z τ v := by
  have hcol : ∀ a, col (mat (X.flowV e s z) τ) a =
      Matrix.mulVec (X.flowMatV (e τ) τ (s τ)) (col (mat z τ) a) :=
    fun a => Data.col_mul (X.flowMatV (e τ) τ (s τ)) (mat z τ) a
  have hT := flowMatV_mulVec X (e τ) τ (s τ)
  set β : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos z τ)⁻¹ b a with hβ
  have hp : X.ppos z τ v = ∑ a, β a • col (mat z τ) (Fin.castLE X.p0_le a) := rfl
  have hcoef : ∑ a, β a * (-(I * X.c τ * s τ) *
      hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) = 0 := by
    have : ∑ a, β a * (-(I * X.c τ * s τ) *
        hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) =
        -(I * X.c τ * s τ) * hermC τ.1 X.Gm (X.ppos z τ v) (e τ) := by
      rw [hp, hermC_sum_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_left]; ring
    rw [this, hpe, mul_zero]
  have hsum : ∑ a, β a • col (mat (X.flowV e s z) τ) (Fin.castLE X.p0_le a) = X.ppos z τ v := by
    simp only [hcol, hT, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [← hp, ← Finset.sum_smul, hcoef, zero_smul, add_zero]
  rw [← hsum]
  apply X.ppos_eq_of _ τ (X.gramPos_det_ne hTz τ) v β
  intro b
  rw [hsum, hcol, hT, hermC_add_right, hermC_smul_right,
    X.ppos_orth z τ (X.gramPos_det_ne hz τ) v b, zero_add, hermC_sub_left, hve, hpe, sub_zero,
    mul_zero]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
