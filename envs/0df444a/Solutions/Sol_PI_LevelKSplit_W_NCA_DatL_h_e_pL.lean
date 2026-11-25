-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.DatL.h_e_pL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:14.027581+00:00
-- url     : https://prove2.me/submissions/2f41312c-e1a8-4dd5-a266-6520e75cc7e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
import Theorems.Thm_PI_LevelKSplit_W_NCA_DatL_h_e_pXv
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
theorem _root_.solution (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (pL D v) = 0 := by
  have h0 : D.h (D.e b) (D.pX v) = 0 := by
    rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ee, mul_zero,
      Finset.sum_const_zero]
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h0, h_e_pXv H]
  ring
end PI.LevelKSplit.W.NCA.DatL
