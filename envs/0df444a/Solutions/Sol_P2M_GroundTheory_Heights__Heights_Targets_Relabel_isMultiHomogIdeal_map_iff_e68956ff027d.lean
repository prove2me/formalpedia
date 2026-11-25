-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomogIdeal_map_iff_e68956ff027d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:34.161353+00:00
-- url     : https://prove2.me/submissions/29096860-01a0-45d9-8da3-8e4f423df042

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_comap_map_91dd5e903145
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_map_ac9cb8581cea
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
theorem _root_.solution (V : Ideal (MRingOver F ι)) :
    IsMultiHomogIdeal (V.map (ringEquiv F e h)) ↔ IsMultiHomogIdeal V := by
  constructor
  · rintro ⟨S, hS, hVS⟩
    refine ⟨(ringEquiv F e h).symm '' S, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨d, hd⟩ := hS g hg
      exact ⟨_, isMultiHomog_symm e h hd⟩
    · rw [← Ideal.map_span, ← hVS, Ideal.map_symm, comap_map]
  · rintro ⟨S, hS, rfl⟩
    refine ⟨ringEquiv F e h '' S, ?_, Ideal.map_span _ _⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨d, hd⟩ := hS f hf
    exact ⟨_, isMultiHomog_map e h hd⟩
end GroundTheory.Heights₂.Heights.Targets.Relabel
