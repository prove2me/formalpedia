-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.DatL.pL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:57.59249+00:00
-- url     : https://prove2.me/submissions/cfb3b5e1-f716-4900-a9d2-32a7a17eda09

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct
open PI.LevelKSplit.W.NCA.DatL
open PI.LevelKSplit.W.SemiG PI.LevelKSplit.W.SemiG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
  {D : PI.LevelKSplit.W.SemiG.Dat A n r}
namespace PI.LevelKSplit.W.NCA.DatL
theorem _root_.solution (v : n → A) : pL D v = v - D.pX v - D.pXv v := rfl
end PI.LevelKSplit.W.NCA.DatL
