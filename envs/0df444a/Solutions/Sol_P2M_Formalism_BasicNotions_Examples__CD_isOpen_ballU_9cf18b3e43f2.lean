-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_isOpen_ballU_9cf18b3e43f2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:16.257909+00:00
-- url     : https://prove2.me/submissions/7fddb42a-335c-4372-8e05-595a391c094f

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
theorem _root_.solution (r : ℝ) : IsOpen (ballU P Q r) := by
  have : Continuous (fun X : lieU P Q => ∑ i, ∑ j, ‖(X : MM P Q) i j‖) :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_subtype_val.matrix_elem i j).norm
  exact isOpen_lt this continuous_const
end Formalism.BasicNotions.Examples₂.CD
