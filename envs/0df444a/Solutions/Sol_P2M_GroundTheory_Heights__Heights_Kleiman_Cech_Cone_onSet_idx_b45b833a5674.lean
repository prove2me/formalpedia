-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:37.132995+00:00
-- url     : https://prove2.me/submissions/cd9cbd39-37a2-4b02-b5ec-c8aac767d11c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone

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
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
theorem _root_.solution {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) : onSet s I.1.1 = s I := by
  unfold onSet
  rw [dif_pos I.2]
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
