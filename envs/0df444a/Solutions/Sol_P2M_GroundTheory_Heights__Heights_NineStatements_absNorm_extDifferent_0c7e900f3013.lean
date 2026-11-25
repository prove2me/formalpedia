-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_absNorm_extDifferent_0c7e900f3013
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:44.550466+00:00
-- url     : https://prove2.me/submissions/84679ffa-f662-45d3-b19b-d3444999d1bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PDifferentExtNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    letI : Algebra E L := ι.toAlgebra
    Ideal.absNorm (extDifferent ι) = (discr E).natAbs ^ Module.finrank E L := by
  let _ : Algebra E L := ι.toAlgebra
  have h1 : RingOfIntegers.mapRingHom ι = algebraMap (𝓞 E) (𝓞 L) := rfl
  have h3 : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L :=
    (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm
  rw [extDifferent, h1, Ideal.absNorm_algebraMap, absNorm_differentIdeal E (𝓞 E), h3]
end GroundTheory.Heights₂.Heights.NineStatements
