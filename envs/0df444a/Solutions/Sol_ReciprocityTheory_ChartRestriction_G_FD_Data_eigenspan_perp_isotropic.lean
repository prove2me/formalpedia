-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.eigenspan_perp_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:13.521237+00:00
-- url     : https://prove2.me/submissions/3bc1cb3d-7aef-428d-84ff-183c9ea197e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ReducedLatticeShortBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramSchmidtEigenframe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryFixingIsotropicPlane
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalShortVectorBoundOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_complexStructure_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_complexStructure_smul
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {z0 : Frame X.Ψ r} {ξ : Fin r → E} {f : X.Ψ → Fin (r - 2) → Fin r → ℂ}
    (hf : X.UBasis z0 ξ f) (τ : X.Ψ) (s : Set (Fin (r - 2))) (σ : ℂ)
    (hs : ∀ k ∈ s, (if (k : ℕ) < X.p0 - 1 then I else -I) = σ) (v : Fin r → ℂ)
    (hv : v ∈ Submodule.span ℂ (f τ '' s)) :
    hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 ∧
      X.Jt z0 τ v = σ • v := by
  have hadd : ∀ a b w, hermC τ.1 X.Gm (a + b) w = hermC τ.1 X.Gm a w + hermC τ.1 X.Gm b w := by
    intro a b w
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsm : ∀ (c : ℂ) a w, hermC τ.1 X.Gm (c • a) w = c * hermC τ.1 X.Gm a w := by
    intro c a w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ0 : X.Jt z0 τ 0 = 0 := by simpa using complexStructure_smul X z0 τ 0 0
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.UBasis at hf
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    exact ⟨((hf τ).1 k).1, ((hf τ).1 k).2, by rw [(hf τ).2.1 k, hs k hk]⟩
  | zero => exact ⟨by simp [hermC], by rw [hJ0]; simp [hermC], by rw [hJ0, smul_zero]⟩
  | add a b _ _ ha hb =>
    exact ⟨by rw [hadd, ha.1, hb.1, add_zero], by rw [complexStructure_add, hadd, ha.2.1, hb.2.1, add_zero],
      by rw [complexStructure_add, ha.2.2, hb.2.2, smul_add]⟩
  | smul c a _ ha =>
    exact ⟨by rw [hsm, ha.1, mul_zero], by rw [complexStructure_smul, hsm, ha.2.1, mul_zero],
      by rw [complexStructure_smul, ha.2.2, smul_comm]⟩
end ReciprocityTheory.ChartRestriction.G.FD.Data
