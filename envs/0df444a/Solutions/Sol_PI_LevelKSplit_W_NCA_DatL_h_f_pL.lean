-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.DatL.h_f_pL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:07:01.703202+00:00
-- url     : https://prove2.me/submissions/c50189bc-71c6-4ca6-bc83-8a23a28ee445

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
import Theorems.Thm_PI_LevelKSplit_W_NCA_DatL_h_f_pX
import Theorems.Thm_PI_LevelKSplit_W_NCA_DatL_h_f_pXv
import Theorems.Thm_PI_LevelKSplit_W_NCA_DatL_pL_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_hL_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_hL_apply


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
theorem _root_.solution (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (pL D v) = 0 := by
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h_f_pX H, h_f_pXv H]
  ring
end PI.LevelKSplit.W.NCA.DatL
