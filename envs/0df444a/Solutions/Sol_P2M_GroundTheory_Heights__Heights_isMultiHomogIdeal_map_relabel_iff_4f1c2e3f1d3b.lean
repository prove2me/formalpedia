-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMultiHomogIdeal_map_relabel_iff_4f1c2e3f1d3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:45.979994+00:00
-- url     : https://prove2.me/submissions/5078528e-1017-4bc9-b016-5cb83e728cfc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_154a322e1b11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_symm_5fefe4430c04

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (V : Ideal (MRing ι)) :
    IsMultiHomogIdeal (V.map (relabelRingEquiv ε h)) ↔ IsMultiHomogIdeal V := by
  constructor
  · rintro ⟨S, hS, hVS⟩
    refine ⟨(relabelRingEquiv ε h).symm '' S, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨d, hd⟩ := hS g hg
      exact ⟨_, isMultiHomog_relabel_symm ε h hd⟩
    · rw [← Ideal.map_span, ← hVS, Ideal.map_symm,
        Ideal.comap_map_of_bijective _ (relabelRingEquiv ε h).bijective]
  · rintro ⟨S, hS, rfl⟩
    refine ⟨relabelRingEquiv ε h '' S, ?_, Ideal.map_span _ _⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨d, hd⟩ := hS f hf
    exact ⟨_, isMultiHomog_relabel ε h hd⟩
end GroundTheory.Heights₂.Heights
