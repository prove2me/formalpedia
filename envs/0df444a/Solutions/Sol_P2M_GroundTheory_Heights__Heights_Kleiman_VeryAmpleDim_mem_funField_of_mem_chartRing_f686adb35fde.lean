-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_funField_of_mem_chartRing_f686adb35fde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:28:28.381995+00:00
-- url     : https://prove2.me/submissions/c0e0cfe0-bec8-44b6-a358-af7a52c3e8b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_ampleBase_le_funField_3c18574d4cd9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AmpleAffineGen
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
theorem _root_.solution {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ chartRing k x (singleChart hi)) : a ∈ funField (k := k) x :=
  ampleBase_le_funField x hi (mem_ampleBase_of_mem_chartRing hi ha)
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
