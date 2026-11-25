-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isRatSection_of_map_55aaddf39d7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:54.755511+00:00
-- url     : https://prove2.me/submissions/07caa9e0-f2f5-4e69-8433-b1ae691d21b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_symm_3e327dafea17

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
theorem _root_.solution {V : Ideal (MRingOver F ι)} {A : K' → ℤ} {f g : MRingOver F ι}
    (hs : IsRatSection (V.map (ringEquiv F e h)) A (ringEquiv F e h f) (ringEquiv F e h g)) :
    IsRatSection V (A ∘ e) f g := by
  obtain ⟨α, β, hα, hβ, hf, hg, hd⟩ := hs
  have hα' := isMultiHomog_symm e h hα
  have hβ' := isMultiHomog_symm e h hβ
  rw [RingEquiv.symm_apply_apply] at hα' hβ'
  exact ⟨α ∘ e, β ∘ e, hα', hβ', fun hf' => hf ((mem_map_ringEquiv_iff _ V f).2 hf'),
    fun hg' => hg ((mem_map_ringEquiv_iff _ V g).2 hg'), fun k => hd (e k)⟩
end GroundTheory.Heights₂.Heights.Targets.Relabel
