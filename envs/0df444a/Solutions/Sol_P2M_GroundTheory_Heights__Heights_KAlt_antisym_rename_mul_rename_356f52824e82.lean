-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_antisym_rename_mul_rename_356f52824e82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:36.368793+00:00
-- url     : https://prove2.me/submissions/e7b33354-407b-415a-81ff-8aa37fe90b54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul_self__1c23ec0bec6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_permTerm_76dab284b23e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_sum_310ba45ee731
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_sign_mul_bb5e29a75a0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_rename_mul_rename_16588cb6d067

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
    antisym (rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β)) =
      ((r.factorial : ℚ) * s.factorial) • alternant (Sum.elim α β) := by
  rw [rename_mul_rename, antisym_sum]
  simp_rw [antisym_sum, antisym_sign_mul, antisym_permTerm, ← mul_assoc, permSign_mul_self₂, one_mul]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
end GroundTheory.Heights₂.Heights.KAlt
