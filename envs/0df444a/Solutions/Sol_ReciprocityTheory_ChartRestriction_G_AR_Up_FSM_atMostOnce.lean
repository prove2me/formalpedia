-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FSM.atMostOnce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:10.811801+00:00
-- url     : https://prove2.me/submissions/d61c8eac-a17c-489d-af08-bc727748d2d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStartPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FSM
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private theorem rmul_rmul' {Ψ : Finset (E →+* ℂ)} (x a b : Frame Ψ r) :
    rmul (rmul x a) b = rmul x (rmul a b) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)
private theorem rmul_mem_bor_upper_bounds {Ψ : Finset (E →+* ℂ)} {a b : Frame Ψ r} (ha : a ∈ Bor Ψ r)
    (hb : b ∈ Bor Ψ r) : rmul a b ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at ha hb ⊢
  intro τ
  obtain ⟨ha1, ha2⟩ := ha τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hA : Matrix.BlockTriangular (mat a τ) id := by
    intro i j h
    exact ha2 i j h
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  refine ⟨?_, fun i j h => hA.mul hB h⟩
  show (mat a τ * mat b τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ha1 hb1
private theorem mem_bor_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : c ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)
  have hI : Matrix.BlockTriangular (mat b τ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨?_, fun i j h => ?_⟩
  · rw [hc τ]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero
  · have h2 := hI h
    rw [← hc τ] at h2
    exact h2
private theorem rmul_rmul_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : rmul (rmul x b) c = x := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  funext τ
  have h := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat x τ * mat b τ * mat c τ = x τ
  rw [hc τ, Matrix.mul_nonsing_inv_cancel_right _ _ h]
  rfl
private theorem lact_rmul_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm
private theorem lact_lact' {Ψ : Finset (E →+* ℂ)} (γ δ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
private theorem lact_inv_lact_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact', inv_mul_cancel]
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  try rfl
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FSM
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FSM
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FSM
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : IsFundSet X x0 FF) (y : Frame X.Ψ r) :
    ∑' γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) ≤ 1 := by
  unfold IsFundSet at hFF
  obtain ⟨_, hFO, hFinj, _⟩ := hFF
  have hS : ∀ w, w ∈ KU.Sset X x0 FF → ∃ z ∈ FF, ∃ b ∈ Bor X.Ψ r, w = rmul (cpt X x0 z) b := by
    intro w hw
    simp only [KU.Sset] at hw
    obtain ⟨⟨z, b⟩, ⟨hz, hb⟩, he⟩ := hw
    exact ⟨z, hz, b, hb, he.symm⟩
  have huniq : ∀ γ γ0 : X.Γ, lact γ.1 y ∈ KU.Sset X x0 FF → lact γ0.1 y ∈ KU.Sset X x0 FF →
      γ = γ0 := by
    intro γ γ0 h1 h2
    obtain ⟨z, hz, b, hb, hzb⟩ := hS _ h1
    obtain ⟨z0, hz0, b0, hb0, hzb0⟩ := hS _ h2
    have hg : γ.1 * γ0.1⁻¹ ∈ X.Γ := X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2)
    have hy : y = lact γ0.1⁻¹ (rmul (cpt X x0 z0) b0) := by
      rw [← hzb0, lact_inv_lact_upper_bounds]
    have hst : rmul (lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0)) b0 = rmul (cpt X x0 z) b := by
      rw [← lact_rmul_upper_bounds, ← lact_lact', ← hy, hzb]
    obtain ⟨bi, hbi⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b τ)⁻¹ :=
      ⟨(fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    obtain ⟨bi0, hbi0⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b0 τ)⁻¹ :=
      ⟨(fun τ => ((mat b0 τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    have hw : cpt X x0 z = lact (γ.1 * γ0.1⁻¹) (rmul (cpt X x0 z0) (rmul b0 bi)) := by
      rw [lact_rmul_upper_bounds, ← rmul_rmul', hst, rmul_rmul_of_mat_eq_inv _ hb hbi]
    have hzz : z0 = z := hFinj z0 hz0 z hz _ hg _ (rmul_mem_bor_upper_bounds hb0 (mem_bor_of_mat_eq_inv hb hbi)) hw
    subst hzz
    have hw0 : cpt X x0 z0 ∈ X.dom := hFO hz0
    have hfix : lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0) = rmul (cpt X x0 z0) (rmul b bi0) := by
      rw [← rmul_rmul', ← hst, rmul_rmul_of_mat_eq_inv _ hb0 hbi0]
    have hg1 : γ.1 * γ0.1⁻¹ = 1 := X.Γ_free _ hg _ hw0 _ (rmul_mem_bor_upper_bounds hb (mem_bor_of_mat_eq_inv hb0 hbi0)) hfix
    exact Subtype.ext (mul_inv_eq_one.mp hg1)
  by_cases hex : ∃ γ0 : X.Γ, lact γ0.1 y ∈ KU.Sset X x0 FF
  · obtain ⟨γ0, hγ0⟩ := hex
    rw [tsum_eq_single γ0]
    · rw [Set.indicator_of_mem hγ0]
      simp
    · intro γ hne
      exact Set.indicator_apply_eq_zero.mpr fun hm => absurd (huniq γ γ0 hm hγ0) hne
  · push_neg at hex
    have h0 : ∀ γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) = 0 :=
      fun γ => Set.indicator_apply_eq_zero.mpr fun hm => absurd hm (hex γ)
    rw [tsum_congr h0, tsum_zero]
    exact zero_le_one
end ReciprocityTheory.ChartRestriction.G.AR.Up.FSM
