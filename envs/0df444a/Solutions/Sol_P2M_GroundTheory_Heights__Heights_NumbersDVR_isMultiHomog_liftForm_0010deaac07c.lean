-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_liftForm_0010deaac07c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:36.518391+00:00
-- url     : https://prove2.me/submissions/c9871736-c5e5-4c6d-9c0e-477079ec292f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {J : Type} {p : MRing ι R} {c : K → ℕ} (h : IsMultiHomog p c) :
    IsMultiHomog (liftForm (J := J) p) (liftMDeg c) := by
  have key : ∀ a : (Σ k, ι k) →₀ ℕ,
      Finsupp.weight (blockWeight (extIdx ι J))
        (a.mapDomain fun v : Σ k, ι k => (⟨some v.1, v.2⟩ : Σ o, extIdx ι J o)) =
      liftMDeg (Finsupp.weight (blockWeight ι) a) := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero => funext o; cases o <;> simp [liftMDeg]
    | add x y hx hy =>
      rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy]
      funext o; cases o <;> simp [liftMDeg]
    | single v n =>
      rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
      funext o; cases o <;> simp [liftMDeg, blockWeight, Pi.single_apply]
  intro a ha
  obtain ⟨a', rfl, ha'⟩ := coeff_rename_ne_zero _ _ _ ha
  rw [key, h ha']
end GroundTheory.Heights₂.Heights.NumbersDVR
