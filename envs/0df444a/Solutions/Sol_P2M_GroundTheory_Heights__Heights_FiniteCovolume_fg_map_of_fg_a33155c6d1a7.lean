-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_map_of_fg_a33155c6d1a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:03:00.202399+00:00
-- url     : https://prove2.me/submissions/7cee0468-aa1d-49ae-b419-9878bc45d322

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
universe u
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {H : AddSubgroup A} (hH : H.FG) (φ : A →+ B) : (H.map φ).FG := by
  rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hH ⊢
  obtain ⟨k, f, rfl⟩ := hH
  exact ⟨k, φ.comp f, by rw [AddMonoidHom.range_comp]⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume
