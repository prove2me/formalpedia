-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_idealLattice_eq_iSup_4b66f2df994c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:47.338289+00:00
-- url     : https://prove2.me/submissions/3c7d44f5-63f8-4e74-96ea-00ab98e15666

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealLatticeFG

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
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
namespace GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
theorem _root_.solution (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice a = ⨆ x, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => K) x)
      (a x : Submodule (𝓞 K) K) :=
  (Submodule.iSup_map_single).symm
end GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
