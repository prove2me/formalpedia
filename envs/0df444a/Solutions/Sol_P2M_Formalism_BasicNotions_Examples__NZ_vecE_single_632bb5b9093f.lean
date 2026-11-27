-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_vecE_single_632bb5b9093f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:23.274326+00:00
-- url     : https://prove2.me/submissions/936b3678-fa42-491e-9258-f60ba6323b3f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BasisOfBasisF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open scoped TensorProduct nonZeroDivisors
variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]
variable (ι : Type) [Fintype ι] [DecidableEq ι]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (hinj : Function.Injective (algebraMap A B)) (a : ι) :
    vecE A B ι hinj (Pi.single a 1) = (1 : B) ⊗ₜ[A] (Pi.single a 1 : ι → FractionRing A) := by
  unfold vecE
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  funext j
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  show (kap A B hinj).symm ((Pi.single a 1 : ι → FractionRing B) j) = _
  by_cases h : j = a
  · subst h
    rw [Pi.single_eq_same, map_one]
    show (1 : B ⊗[A] FractionRing A) = 1 ⊗ₜ[A] (Pi.single j 1 : ι → FractionRing A) j
    rw [Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne h, map_zero]
    show (0 : B ⊗[A] FractionRing A) = 1 ⊗ₜ[A] (Pi.single a 1 : ι → FractionRing A) j
    rw [Pi.single_eq_of_ne h, TensorProduct.tmul_zero]
end Formalism.BasicNotions.Examples₂.NZ
