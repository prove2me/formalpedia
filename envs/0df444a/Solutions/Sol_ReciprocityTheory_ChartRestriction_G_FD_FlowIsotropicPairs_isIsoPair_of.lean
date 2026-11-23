-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.isIsoPair_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:38.788149+00:00
-- url     : https://prove2.me/submissions/0c4c7eed-c74e-4124-8dba-1dd071f38126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
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
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma herm_swap_eq_zero_of_eq_zero (X : Data E r) (x y : Fin r → E) (h : herm X.Gm x y = 0) :
    herm X.Gm y x = 0 := by
  have e : cc (herm X.Gm x y) = herm X.Gm y x := by
    simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    first
      | (have hg := X.Gm_herm b a
         simp only [cc] at hg
         rw [hg]
         ring)
      | (have hg := X.Gm_herm a b
         simp only [cc] at hg
         rw [hg]
         ring)
  rw [← e, h]
  simp [cc]
private lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private lemma herm_smul_right_eq_cc_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
theorem _root_.solution (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hxξ : herm X.Gm x ξ = 0)
    (hxx : herm X.Gm x x = 0) (hne : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by
  obtain ⟨-, hξξ, hξ0⟩ := hξ
  have hξx : herm X.Gm ξ x = 0 := herm_swap_eq_zero_of_eq_zero X.toData x ξ hxξ
  unfold IsIsoPair
  refine ⟨?_, LinearIndependent.pair_iff.mpr fun s t hst => ?_⟩
  · intro i k
    fin_cases i <;> fin_cases k <;>
      simp [herm_smul_left_fundamental_domains, herm_smul_right_eq_cc_mul, hξξ, hxξ, hxx, hξx]
  · by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNC : (X.NC : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NC_pos.ne'
      have htn : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNC
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]
        exact eq_neg_of_add_eq_zero_right hst
      apply hne (-(s / (t * X.NC)))
      calc x = (t * X.NC)⁻¹ • ((t * X.NC) • x) := by rw [smul_smul, inv_mul_cancel₀ htn, one_smul]
        _ = -(s / (t * X.NC)) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
