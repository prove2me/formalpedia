-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.herm_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:02.410354+00:00
-- url     : https://prove2.me/submissions/0d05cbbc-dea4-411a-9d1f-1ee2afae7b7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_herm_perp
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_conj
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
private lemma herm_sum_smul_right' {m : ℕ} (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E)
    (c : Fin m → E) (v : Fin m → Fin r → E) :
    herm G x (∑ k, c k • v k) = ∑ k, cc (c k) * herm G x (v k) := by
  unfold herm cc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, x a * G a b * ((IsCMField.complexConj E) (c k) *
        (IsCMField.complexConj E) (v k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, x a * G a b * ((IsCMField.complexConj E) (c k) *
        (IsCMField.complexConj E) (v k b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
private lemma herm_add_left_of_matrix (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  unfold herm
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
private lemma herm_add_right_of_matrix (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  unfold herm cc
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
private lemma herm_smul_left_of_matrix (G : Matrix (Fin r) (Fin r) E) (e : E) (x y : Fin r → E) :
    herm G (e • x) y = e * herm G x y := by
  unfold herm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma herm_smul_right_lemma_6 (G : Matrix (Fin r) (Fin r) E) (e : E) (x y : Fin r → E) :
    herm G x (e • y) = cc e * herm G x y := by
  unfold herm cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
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
theorem _root_.solution (hβξ : ∀ k, herm X.Gm (β k) ξ = 0) (hξξ : herm X.Gm ξ ξ = 0)
    (c c' : Fin n → E) (e e' : E) :
    herm X.Gm (∑ k, c' k • β k + e' • ξ) (∑ k, c k • β k + e • ξ) =
      herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k) := by
  have hξβ : ∀ k, herm X.Gm ξ (β k) = 0 := fun k => by
    have h := HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm (β k) ξ
    rw [hβξ k] at h
    first
    | simpa [cc] using h
    | simpa [cc] using h.symm
  have hB : herm X.Gm ξ (∑ k, c k • β k) = 0 := by
    rw [herm_sum_smul_right']
    simp [hξβ]
  rw [herm_add_left_of_matrix, herm_add_right_of_matrix, herm_add_right_of_matrix, herm_smul_left_of_matrix,
    herm_smul_left_of_matrix, herm_smul_right_lemma_6, herm_smul_right_lemma_6, hB, herm_perp X β ξ hβξ c', hξξ]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
