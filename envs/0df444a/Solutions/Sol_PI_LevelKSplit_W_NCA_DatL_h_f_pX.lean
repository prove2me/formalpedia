-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.DatL.h_f_pX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:18.101369+00:00
-- url     : https://prove2.me/submissions/87f48715-7298-4b12-a89e-52befed7f2f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_hL_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_symm
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_hL_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_symm


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
theorem _root_.solution (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pX v) = D.h (D.f b) v := by
  have hfe : ∀ a, D.h (D.f b) (D.e a) = if b = a then 1 else 0 := by
    intro a
    rw [Dat.h_symm H (D.e a) (D.f b), H.ef]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]
  rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, hfe, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end PI.LevelKSplit.W.NCA.DatL
