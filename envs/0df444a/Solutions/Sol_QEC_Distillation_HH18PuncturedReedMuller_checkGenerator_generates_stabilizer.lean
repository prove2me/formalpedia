-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.checkGenerator_generates_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:27:06.61977+00:00
-- url     : https://prove2.me/submissions/7f581b40-2ec0-4220-9a2e-856c7fb4aaee

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18PuncturedReedMuller
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) :
    generatedStabilizerSet (checkGenerator w r m) =
      (stabilizer h).generatedGroup :=
  binaryCSSParityCheckGenerators_generate_generatedGroup
    (zParityCheck w r m) (xParityCheck w r m)
    (parityCheckRows_orthogonal h)
end QEC.Distillation.HH18PuncturedReedMuller
