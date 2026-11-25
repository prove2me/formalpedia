-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.DatL.h_f_pXv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:14.780818+00:00
-- url     : https://prove2.me/submissions/13b7b309-635e-46ae-98c6-d9f9ea066919

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
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
theorem _root_.solution (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pXv v) = 0 := by
  rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ff, mul_zero,
    Finset.sum_const_zero]
end PI.LevelKSplit.W.NCA.DatL
