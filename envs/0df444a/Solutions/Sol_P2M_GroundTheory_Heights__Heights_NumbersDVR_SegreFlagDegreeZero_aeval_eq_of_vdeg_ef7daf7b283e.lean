-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_aeval_eq_of_vdeg_ef7daf7b283e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:38.508818+00:00
-- url     : https://prove2.me/submissions/ac7d0092-ee3d-4630-820b-2ad2c71f1e68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalEqOfVdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_le_weight_block_a95d776f8a10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero
theorem _root_.solution {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] {M M' : ℕ}
    {Φ : Type} [Field Φ] [Algebra O Φ] {z z' : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (h : ∀ (k : K) (i : ι k), z ⟨some (some k), i⟩ = z' ⟨some (some k), i⟩)
    {G : MRing (bundleIdx (bundleIdx ι M) M') O} {β : K → ℕ} (hG : IsMultiHomog G (GenericProjClosureDivisor.vdeg β)) :
    aeval z G = aeval z' G := by
  rw [aeval_def, aeval_def]
  apply eval₂_congr
  intro p c' hp hc
  obtain ⟨o, i⟩ := p
  have key := le_weight_block c' hp
  rw [hG hc] at key
  rcases o with _ | _ | k
  · simp [GenericProjClosureDivisor.vdeg] at key
    exact absurd key (Finsupp.mem_support_iff.mp hp)
  · simp [GenericProjClosureDivisor.vdeg] at key
    exact absurd key (Finsupp.mem_support_iff.mp hp)
  · exact h k i
end GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero
