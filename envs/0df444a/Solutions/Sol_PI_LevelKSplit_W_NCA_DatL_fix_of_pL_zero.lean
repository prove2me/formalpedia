-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.DatL.fix_of_pL_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:03.63329+00:00
-- url     : https://prove2.me/submissions/dd8aad64-cd46-470e-a863-b6d2bc1ef8ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
import Theorems.Thm_PI_LevelKSplit_W_NCA_DatL_pL_apply

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
theorem _root_.solution {S : (n → A) →ₗ[A] (n → A)} (hSe : ∀ a, S (D.e a) = D.e a)
    (hSf : ∀ a, S (D.f a) = D.f a) {u : n → A} (hu : pL D u = 0) : S u = u := by
  have hu' : u = D.pX u + D.pXv u := by
    rw [pL_apply, sub_sub, sub_eq_zero] at hu
    exact hu
  rw [hu', map_add]
  congr 1
  · simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSe]
  · simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSf]
end PI.LevelKSplit.W.NCA.DatL
