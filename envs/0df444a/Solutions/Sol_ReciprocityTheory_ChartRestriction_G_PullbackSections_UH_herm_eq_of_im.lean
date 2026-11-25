-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.herm_eq_of_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:20.967344+00:00
-- url     : https://prove2.me/submissions/e6edca74-9646-4134-b03e-b1c973e0aaea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_UnitHmA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_UH_hermForm_sub_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
theorem _root_.solution {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x y, (hermForm H₁ (P x) (P y)).im = (hermForm H₂ (P x) (P y)).im) : H₁ = H₂ := by
  have hD : ∀ x y, (hermForm (H₁ - H₂) (P x) (P y)).im = 0 := fun x y => by
    rw [hermForm_sub_mat, Complex.sub_im, h, sub_self]
  have h0 : imForm (H₁ - H₂) = 0 := by
    apply LinearMap.ext_on_range hP
    intro x
    apply LinearMap.ext_on_range hP
    intro y
    simpa [imForm] using hD x y
  have hall : ∀ z w, hermForm (H₁ - H₂) z w = 0 := by
    intro z w
    have him : ∀ z' : Fin g → ℂ, (hermForm (H₁ - H₂) z' w).im = 0 := fun z' => by
      simpa [imForm] using LinearMap.congr_fun₂ h0 z' w
    have hre := him (Complex.I • z)
    rw [hermForm_smul_left] at hre
    apply Complex.ext
    · simpa using hre
    · simpa using him z
  have hs : ∀ j : Fin g, star (Pi.single j 1 : Fin g → ℂ) = (Pi.single j 1 : Fin g → ℂ) := fun j => by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  refine sub_eq_zero.1 ?_
  ext i j
  have := hall (Pi.single i 1) (Pi.single j 1)
  simpa [hermForm, hs, Matrix.mulVec_single, single_dotProduct] using this
end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
