-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.herm_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:55.327295+00:00
-- url     : https://prove2.me/submissions/bd3fce50-4a5f-4801-a660-8030bf61ac2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
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
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)
private lemma herm_sum_smul_left' {m : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : Fin m → E)
    (v : Fin m → Fin r → E) (y : Fin r → E) :
    herm G (∑ k, c k • v k) y = ∑ k, c k * herm G (v k) y := by
  unfold herm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * v k a * G a b * cc (y b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * v k a * G a b * cc (y b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
end
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
theorem _root_.solution (hβξ : ∀ k, herm X.Gm (β k) ξ = 0) (c : Fin n → E) :
    herm X.Gm (∑ k, c k • β k) ξ = 0 := by
  rw [herm_sum_smul_left']
  simp [hβξ]
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
