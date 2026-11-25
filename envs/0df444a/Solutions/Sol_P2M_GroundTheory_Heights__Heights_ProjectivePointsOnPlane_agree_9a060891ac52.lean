-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_agree_9a060891ac52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:03.193798+00:00
-- url     : https://prove2.me/submissions/9140f76d-04ee-4dd6-98ce-cbebd6859e10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_lin_2d6da04684f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_quad_mem_0cdb3f18228b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_eval_quad_8c9d4f136892

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
theorem _root_.solution (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (hz : z ∈ mcPts (projSpaceIdeal K i)) (α : 𝓞 K)
    (σ τ : K →+* ℂ) (j l : Fin i) (hσ : embComp σ (fun q => z ⟨(), q⟩) j ≠ 0)
    (hτ : embComp τ (fun q => z ⟨(), q⟩) l ≠ 0) : σ (α : K) = τ (α : K) := by
  obtain ⟨q0, hq0⟩ := hz.1 ()
  set Z : ProjIdx K i → ℂ := fun q => z ⟨(), q⟩ with hZ
  have hrel : ∀ p q, Z p * lin α Z q = lin α Z p * Z q := by
    intro p q
    have h := hz.2 _ (quad_mem α p q)
    rw [eval_quad] at h
    exact sub_eq_zero.mp h
  have hL : lin α Z = (lin α Z q0 / Z q0) • Z := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hq0]
    linear_combination hrel q0 r
  have key : ∀ ρ : K →+* ℂ, ρ (α : K) • embComp ρ Z = (lin α Z q0 / Z q0) • embComp ρ Z := by
    intro ρ
    rw [← embComp_lin, ← embComp_smul, ← hL]
  have h1 := congrFun (key σ) j
  have h2 := congrFun (key τ) l
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [mul_right_cancel₀ hσ h1, mul_right_cancel₀ hτ h2]
end GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
