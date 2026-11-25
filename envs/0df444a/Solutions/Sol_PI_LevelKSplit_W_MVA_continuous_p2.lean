-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.continuous_p2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:02:19.419691+00:00
-- url     : https://prove2.me/submissions/f6790156-3582-4290-aef1-2a94b7e65401

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_crd
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_crd_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [TopologicalSpace R2] [IsTopologicalRing R2]
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution : Continuous (p2 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p2 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) := by
    intro x
    apply (crd (F := F) (E := E) R2).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p2, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, Prod.snd_add, hx, hy]
  rw [show p2 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) from funext key]
  exact (continuous_crd_symm R2).comp
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))
end PI.LevelKSplit.W.MVA
