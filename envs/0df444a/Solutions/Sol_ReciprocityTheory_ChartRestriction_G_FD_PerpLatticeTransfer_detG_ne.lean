-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.detG_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:34.486988+00:00
-- url     : https://prove2.me/submissions/2a266337-410c-4363-875b-0396257f71df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_herm_perp
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_left__9bdb38af119e
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_right__48d7e64a9d84
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_herm_smul_right
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_exists_eq_smul_of_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
theorem _root_.solution (hξ : X.IsIso ξ) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin n → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    (Sform X β).G.det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hcG⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set μ := ∑ a, cc (c a) • β a with hμdef
  have hβμ : ∀ b, herm X.Gm (β b) μ = 0 := by
    intro b
    have h1 := congrFun hcG b
    simp only [Matrix.vecMul, dotProduct, Sform, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hμdef, herm_sum_right']
    simp only [HermitianTraceFormVanishing.herm_smul_right, HermitianTraceFormVanishing.cc_cc]
    rw [← h1]
  have hμξ : herm X.Gm ξ μ = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm, hμdef, herm_perp X β ξ hβξ, HermitianTraceFormVanishing.cc_zero]
  have hperp : ∀ y, herm X.Gm y ξ = 0 → herm X.Gm μ y = 0 := by
    intro y hy
    obtain ⟨c', e', rfl⟩ := hspan y hy
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hμξ,
      herm_sum_left']
    simp only [HermitianTraceFormVanishing.herm_smul_left, hβμ, mul_zero, Finset.sum_const_zero, add_zero,
      HermitianTraceFormVanishing.cc_zero]
  obtain ⟨e, he⟩ := HermitianTraceFormVanishing.exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ.2.2 hperp
  have h := Fintype.linearIndependent_iff.mp hli (Fin.cons (-e) (fun a => cc (c a))) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    show -e • ξ + μ = 0
    rw [he, neg_smul, neg_add_cancel])
  apply hc0
  funext a
  have := h a.succ
  simpa using this
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
