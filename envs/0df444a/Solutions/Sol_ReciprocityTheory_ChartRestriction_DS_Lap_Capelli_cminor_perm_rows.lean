-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_perm_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:02.57035+00:00
-- url     : https://prove2.me/submissions/8d589c99-d3c5-4d02-b983-b67adec64948

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_sign_mul_sign

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p)) (x : ℂ) :
    cminor E (R ∘ τ) C x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by
  unfold cminor
  rw [Finset.smul_sum]
  refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulLeft τ) _)
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, smul_smul, basic_sign_mul_sign, Function.comp_apply]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
