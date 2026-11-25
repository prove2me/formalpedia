-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_rename_mul_rename_16588cb6d067
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:50.823925+00:00
-- url     : https://prove2.me/submissions/82ed8111-8025-45e9-a16a-d65b3e12cd80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_alternant_eq_sum_27b6851fc1aa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r s : ℕ}
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution (α : Fin r → ℕ) (β : Fin s → ℕ) :
    rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β) =
      ∑ σ : Equiv.Perm (Fin r), ∑ τ : Equiv.Perm (Fin s),
        sgnP (Equiv.Perm.sumCongr σ τ) * permTerm (Sum.elim α β) (Equiv.Perm.sumCongr σ τ) := by
  rw [alternant_eq_sum, alternant_eq_sum, map_sum, map_sum, sum_mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
  simp only [sgnP, permTerm, map_mul, map_intCast, map_prod, map_pow, rename_X,
    Equiv.Perm.sign_sumCongr, Units.val_mul, Int.cast_mul, Fintype.prod_sum_type,
    Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  ring
end GroundTheory.Heights₂.Heights.KAlt
