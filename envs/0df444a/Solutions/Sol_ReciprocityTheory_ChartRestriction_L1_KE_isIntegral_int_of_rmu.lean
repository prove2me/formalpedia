-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.isIntegral_int_of_rmu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:08.646798+00:00
-- url     : https://prove2.me/submissions/988608f9-3abc-4716-8229-6e5b3d87a3c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_rmu_isIntegral_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) :
    (Int.castRingHom ℂ_[l]).IsIntegralElem δ := by
  have : Algebra.IsIntegral ℤ (Rmu l) := ⟨fun x => by
    have := rmu_isIntegral_int l x.2
    exact (isIntegral_algebraMap_iff (A := Rmu l) (B := ℂ_[l]) Subtype.val_injective).mp this⟩
  have h : IsIntegral ℤ δ := isIntegral_trans δ hδ
  exact (Subsingleton.elim (algebraMap ℤ ℂ_[l]) (Int.castRingHom ℂ_[l])) ▸ h
end ReciprocityTheory.ChartRestriction.L1.KE
