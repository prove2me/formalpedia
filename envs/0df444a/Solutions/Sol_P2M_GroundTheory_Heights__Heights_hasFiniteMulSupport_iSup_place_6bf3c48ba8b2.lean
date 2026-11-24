-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:20.663807+00:00
-- url     : https://prove2.me/submissions/b3349639-9ef2-4e4a-9ba1-22d03dc43354

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) : Function.HasFiniteMulSupport fun w : FinitePlace F ↦ ⨆ i, w (y i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  have : Nonempty {j // y j ≠ 0} := ⟨⟨i0, hi0⟩⟩
  have h := Function.HasFiniteMulSupport.iSup (ι := {j // y j ≠ 0})
    (f := fun i (w : FinitePlace F) ↦ w (y i)) fun i ↦ FinitePlace.hasFiniteMulSupport i.2
  have e : (fun w : FinitePlace F ↦ ⨆ i, w (y i)) = fun w ↦ ⨆ i : {j // y j ≠ 0}, w (y i) :=
    funext fun w ↦ Finite.iSup_eq_iSup_subtype hy
  rw [e]
  exact h
end GroundTheory.Heights₂.Heights
