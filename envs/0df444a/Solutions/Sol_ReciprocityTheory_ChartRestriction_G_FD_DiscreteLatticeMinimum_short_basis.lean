-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum.short_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:13.925154+00:00
-- url     : https://prove2.me/submissions/ae1cce04-273e-4ef2-aff5-ab6c27bf13a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscreteLatticeMinimum_mem_Lat_of_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscreteLatticeMinimum_min_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscreteLatticeMinimum_discrete_Lat
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_span_Lat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_transference_dual
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
open ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]
variable {ξ} (hξ : Y.IsIso ξ)
variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))
include hns
namespace ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) :
    ∃ y : Fin (finrank ℝ (VT (X := Y.toData) z ξ)) → VT (X := Y.toData) z ξ,
      LinearIndependent ℝ y ∧ (∀ i, y i ∈ Lat z ξ hξ) ∧
      ∀ i, ‖y i‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 /
        (Y.k0 * Real.sqrt ep0 / Y.NA) := by
  classical
  have := discrete_Lat z hξ ep0 hns hep
  have : IsZLattice ℝ (Lat z ξ hξ) := ⟨span_Lat z ξ hD3 hξ⟩
  have := ZLattice.module_free ℝ (Lat z ξ hξ)
  have := ZLattice.module_finite ℝ (Lat z ξ hξ)
  set n := finrank ℝ (VT (X := Y.toData) z ξ) with hn
  let bZ := Module.Free.chooseBasis ℤ (Lat z ξ hξ)
  let bR := bZ.ofZLatticeBasis ℝ (Lat z ξ hξ)
  have hspanR : Submodule.span ℤ (Set.range bR) = Lat z ξ hξ := bZ.ofZLatticeBasis_span ℝ _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Lat z ξ hξ)) = n :=
    (Module.finrank_eq_card_basis bR).symm
  let bF := bR.reindex (Fintype.equivFinOfCardEq hcard)
  have hspanF : Submodule.span ℤ (Set.range bF) = Lat z ξ hξ := by
    rw [Basis.range_reindex]
    exact hspanR
  let e := (stdOrthonormalBasis ℝ (VT (X := Y.toData) z ξ)).repr
  let b' := (bF.map (Bequiv z ξ)).map e.toLinearEquiv
  have hb'j : ∀ j, b' j = e (Bmap z ξ (bF j)) := fun j => by
    simp only [b', Basis.map_apply]
    rfl
  set lam := Y.k0 * Real.sqrt ep0 / Y.NA with hlam
  have hlam0 : 0 < lam := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  let f : VT (X := Y.toData) z ξ →ₗ[ℤ] EuclideanSpace ℝ (Fin n) :=
    ((e.toLinearEquiv.toLinearMap).comp (Bmap z ξ)).restrictScalars ℤ
  have hfr : f '' Set.range bF = Set.range b' := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (hb'j j).symm)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    rw [← hfr, Submodule.span_image, hspanF] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 (map_zero f)
    have hfa : ‖f a‖ = Y.k0 * ‖a‖ := by
      show ‖e (Bmap z ξ a)‖ = _
      rw [LinearIsometryEquiv.norm_map, norm_Bmap]
    rw [hfa, hlam, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (min_norm z hξ ep0 hns a ha ha0) Y.minWeight_pos.le
  obtain ⟨y, hli, hint, hnorm⟩ := T0.transference_dual b' lam hlam0 hmin
  refine ⟨fun i => e.symm (y i), ?_, ?_, ?_⟩
  · exact hli.map' e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.ker
  · intro i
    apply mem_Lat_of_int z hξ hD3
    intro a ha
    rw [← hspanF] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      obtain ⟨m, hm⟩ := hint i j
      refine ⟨m, ?_⟩
      rw [← hm, hb'j, ← LinearIsometryEquiv.inner_map_map e, LinearIsometryEquiv.apply_symm_apply]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨m1, h1⟩ := iha
      obtain ⟨m2, h2⟩ := ihb
      exact ⟨m1 + m2, by rw [map_add, inner_add_right, h1, h2, Int.cast_add]⟩
    | smul c a _ iha =>
      obtain ⟨m, h⟩ := iha
      refine ⟨c * m, ?_⟩
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, h, Int.cast_mul]
  · intro i
    rw [LinearIsometryEquiv.norm_map]
    exact hnorm i
end ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
