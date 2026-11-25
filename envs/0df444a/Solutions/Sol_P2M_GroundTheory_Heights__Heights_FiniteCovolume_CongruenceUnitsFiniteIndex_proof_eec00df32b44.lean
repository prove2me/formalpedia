-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceUnitsFiniteIndex_proof_eec00df32b44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:46:49.223226+00:00
-- url     : https://prove2.me/submissions/07acf44b-3aa8-4d94-9b49-0342db6a0f96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace CongruenceUnitsFiniteIndex
theorem _root_.solution (E : Type*) [Field E] [NumberField E] :
    CongruenceUnitsFiniteIndex.Statement E := by
  intro N hN
  have hI : Ideal.span {(N : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ :=
    Finite.of_injective _ Units.val_injective
  have : (congruenceUnits E N).FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.FiniteIndex.index_ne_zero
end CongruenceUnitsFiniteIndex
end GroundTheory.Heights₂.Heights.FiniteCovolume
