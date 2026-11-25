-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eltToLattice_bijective_a2eb0a9320c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:39.202302+00:00
-- url     : https://prove2.me/submissions/f92a5f88-9cba-4296-a489-b0c5339e5473

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (σ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ)
    (hc : c ≠ 0) (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) :
    Function.Bijective (eltToLattice σ J τ c hc himg) := by
  constructor
  · intro x y h
    have h2 := congrArg (fun z : NzLattice τ => (z : ℂ)) h
    simp only [eltToLattice] at h2
    exact Subtype.ext (σ.injective (mul_left_cancel₀ hc h2))
  · rintro ⟨z, hz, hz0⟩
    rw [← himg] at hz
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    refine ⟨⟨x, hx, fun h => hz0 (by simp [h])⟩, rfl⟩
end GroundTheory.Heights₂.Theta.projectiveLineClassData
