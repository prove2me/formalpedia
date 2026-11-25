-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.T_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:46.290203+00:00
-- url     : https://prove2.me/submissions/9210a782-a39c-47ab-9ac5-1299b0083566

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom
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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
private lemma rmul_mem_Bor {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  have h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  have h2' : ∀ τ : X.Ψ, (mat b' τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b' τ a c = 0 := hb'
  show ∀ τ : X.Ψ, (mat (rmul b b') τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → rmul b b' τ a c = 0
  intro τ
  obtain ⟨d1, t1⟩ := h1' τ
  obtain ⟨d2, t2⟩ := h2' τ
  have ht : (mat b τ * mat b' τ).BlockTriangular id :=
    Matrix.BlockTriangular.mul (fun a c h => t1 a c h) (fun a c h => t2 a c h)
  refine ⟨?_, fun a c h => ht h⟩
  show (mat b τ * mat b' τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero d1 d2
private lemma inv_mat_apply_mem_bor {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ a c => (mat b τ)⁻¹ a c) ∈ Bor X.Ψ r := by
  have h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  show ∀ τ : X.Ψ, (mat (fun τ a c => (mat b τ)⁻¹ a c) τ).det ≠ 0 ∧
    ∀ a c : Fin r, c < a → ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) a c = 0
  intro τ
  obtain ⟨d1, t1⟩ := h1' τ
  haveI := (mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr d1)
  have ht : ((mat b τ)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => t1 a c h)
  refine ⟨?_, fun a c h => ht h⟩
  exact ((mat b τ).isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr d1)).ne_zero
private lemma rmul_rmul_assoc (x b b' : Frame X.Ψ r) : rmul (rmul x b) b' = rmul x (rmul b b') := by
  funext τ
  show mat x τ * mat b τ * mat b' τ = mat x τ * (mat b τ * mat b' τ)
  exact Matrix.mul_assoc _ _ _
private lemma rmul_rmul_inv_mat {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    rmul (rmul x b) (fun τ a c => (mat b τ)⁻¹ a c) = x := by
  have h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  funext τ
  show mat x τ * mat b τ * (mat b τ)⁻¹ = mat x τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (h1' τ).1), Matrix.mul_one]
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ T D FF ↔ x ∈ T D FF := by
  simp only [T, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hd, hΔ, hF⟩
    obtain ⟨hzO, hbO, hs⟩ := D.split _ hd hΔ
    have hx' : x = rmul (cpt X x0 (D.zOf (rmul x b)))
        (rmul (D.bOf (rmul x b)) (fun τ a c => (mat b τ)⁻¹ a c)) := by
      rw [← rmul_rmul_assoc (X := X), ← hs, rmul_rmul_inv_mat (X := X) hb]
    obtain ⟨hΔx, hzx, -⟩ := D.uniq _ hzO _ (rmul_mem_Bor (X := X) hbO (inv_mat_apply_mem_bor (X := X) hb))
    rw [← hx'] at hΔx hzx
    exact ⟨hx, hΔx, by rw [hzx]; exact hF⟩
  · rintro ⟨-, hΔ, hF⟩
    obtain ⟨hzO, hbO, hs⟩ := D.split _ hx hΔ
    have hxb : rmul x b = rmul (cpt X x0 (D.zOf x)) (rmul (D.bOf x) b) := by
      rw [← rmul_rmul_assoc (X := X), ← hs]
    obtain ⟨hΔ', hz', -⟩ := D.uniq _ hzO _ (rmul_mem_Bor (X := X) hbO hb)
    rw [← hxb] at hΔ' hz'
    exact ⟨ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb, hΔ', by rw [hz']; exact hF⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
