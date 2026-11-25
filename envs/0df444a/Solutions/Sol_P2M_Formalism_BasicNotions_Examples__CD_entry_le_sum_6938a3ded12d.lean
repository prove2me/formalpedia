-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_entry_le_sum_6938a3ded12d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:55.067184+00:00
-- url     : https://prove2.me/submissions/ad4ac034-25fb-480f-b6e3-b69fb234e549

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Set Matrix Formalism.UG.P
open scoped ENNReal NNReal
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (X : MM P Q) (i j : Fin P ⊕ Fin Q) : ‖X i j‖ ≤ ∑ i, ∑ j, ‖X i j‖ :=
  (Finset.single_le_sum (f := fun j => ‖X i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
end Formalism.BasicNotions.Examples₂.CD
