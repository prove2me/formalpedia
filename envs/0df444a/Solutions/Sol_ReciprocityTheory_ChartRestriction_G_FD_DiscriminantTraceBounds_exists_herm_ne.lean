-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds.exists_herm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:04.588634+00:00
-- url     : https://prove2.me/submissions/c223da30-4ce9-4ff9-b1e9-041dd124e7c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
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
open ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E] {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
theorem _root_.solution (hr : 0 < r) : ∃ x ∈ X.L', ∃ y ∈ X.L', herm X.Gm x y ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcc_add : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by
    unfold cc
    exact map_add _ a b
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  have hcc0 : cc (0 : E) = 0 := by
    unfold cc
    exact map_zero _
  have hcc1 : cc (1 : E) = 1 := by
    unfold cc
    exact map_one _
  have hadd2 : ∀ x y y' : Fin r → E, herm X.Gm x (y + y') = herm X.Gm x y + herm X.Gm x y' := by
    intro x y y'
    simp only [herm, Pi.add_apply, hcc_add, mul_add, Finset.sum_add_distrib]
  have hsmul2 : ∀ (x y : Fin r → E) (c : E), herm X.Gm x (c • y) = cc c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero2 : ∀ x : Fin r → E, herm X.Gm x 0 = 0 := fun x => by simp [herm, hcc0]
  have hadd1 : ∀ x x' y : Fin r → E, herm X.Gm (x + x') y = herm X.Gm x y + herm X.Gm x' y := by
    intro x x' y
    simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsmul1 : ∀ (x y : Fin r → E) (c : E), herm X.Gm (c • x) y = c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero1 : ∀ y : Fin r → E, herm X.Gm 0 y = 0 := fun y => by simp [herm]
  have hspan : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← X.Λ_span]
    apply Submodule.span_le.mpr
    intro z hz
    have h1 := X.NA_sub z hz
    have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
    have hz' : z = (X.NA : E)⁻¹ • ((X.NA : E) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hall2 : ∀ x ∈ X.L', ∀ y, herm X.Gm x y = 0 := by
    intro x hx y
    have hy : y ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hcon x hx y hy
    | zero => exact hzero2 x
    | add y y' _ _ h1 h2 => rw [hadd2, h1, h2, add_zero]
    | smul c y _ h => rw [hsmul2, h, mul_zero]
  have hall : ∀ x y : Fin r → E, herm X.Gm x y = 0 := by
    intro x y
    have hx : x ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact hall2 x hx y
    | zero => exact hzero1 y
    | add x x' _ _ h1 h2 => rw [hadd1, h1, h2, add_zero]
    | smul c x _ h => rw [hsmul1, h, mul_zero]
  have hG : X.Gm = 0 := by
    ext a b
    have hval : herm X.Gm (Pi.single a 1) (Pi.single b 1) = X.Gm a b := by
      simp [herm, Pi.single_apply, apply_ite cc, hcc1, hcc0]
    rw [Matrix.zero_apply, ← hval]
    exact hall _ _
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact X.Gm_det (by rw [hG]; exact Matrix.det_zero)
end ReciprocityTheory.ChartRestriction.G.FD.DiscriminantTraceBounds
