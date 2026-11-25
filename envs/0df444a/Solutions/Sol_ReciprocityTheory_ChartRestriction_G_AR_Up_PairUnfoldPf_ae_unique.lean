-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.ae_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:04.535272+00:00
-- url     : https://prove2.me/submissions/45ced5aa-640a-45b0-99a5-a493e43c4ab8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_lact_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_lact_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_lact_inv_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_rmul_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_T_rmul_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_T_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_ae_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hFF : IsFundSet X x0 FF) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 ∧ ∃ γ0 ∈ X.Γ, ∀ γ ∈ X.Γ, (lact γ⁻¹ (cpt X x0 z) ∈ T D FF ↔ γ = γ0) := by
  obtain ⟨-, hsub, hinj, hcov⟩ := hFF
  filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0), hcov] with z hz hc
  obtain ⟨z', hz', γ, hγ, b, hb, hcz⟩ := hc
  refine ⟨hz, γ, hγ, fun γ' hγ' => ?_⟩
  have hz'O : z' ∈ OmF X x0 := hsub hz'
  have key : lact γ'⁻¹ (cpt X x0 z) = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z') b) := by
    rw [hcz, lact_lact]
  rw [key]
  constructor
  · intro hT
    obtain ⟨z'', hz'', b'', hb'', hx⟩ := T_split D FF hT
    have hδΓ : γ'⁻¹ * γ ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ

    have h3 : cpt X x0 z'' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z')
        (rmul b (fun τ a c => (mat b'' τ)⁻¹ a c))) := by
      rw [← rmul_rmul_inv_mat (X := X) hb'' (cpt X x0 z''), ← hx, rmul_lact, rmul_rmul_assoc (X := X)]
    have hB := rmul_mem_Bor (X := X) hb (inv_mat_apply_mem_bor (X := X) hb'')
    have hzz := hinj z' hz' z'' hz'' _ hδΓ _ hB h3
    subst hzz

    have h4 : lact (γ'⁻¹ * γ)⁻¹ (cpt X x0 z') = rmul (cpt X x0 z')
        (rmul b (fun τ a c => (mat b'' τ)⁻¹ a c)) := by
      conv_lhs => rw [h3]
      rw [lact_inv_lact]
    have h5 := X.Γ_free _ (X.Γ.inv_mem hδΓ) _ hz'O _ hB h4
    exact inv_mul_eq_one.mp (inv_eq_one.mp h5)
  · rintro rfl
    rw [inv_mul_cancel, lact_one]
    exact (T_rmul_cpt D FF hz'O hb).2 hz'
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
