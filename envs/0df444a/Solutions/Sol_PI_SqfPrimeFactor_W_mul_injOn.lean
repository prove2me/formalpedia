-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.mul_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:31.604604+00:00
-- url     : https://prove2.me/submissions/9446490f-8e66-4750-94cf-6640d2ed3b09

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
import Theorems.Thm_PI_SqfPrimeFactor_W_irr_dvd_of_dvd_mul
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_irrDeg
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_monicDeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (r p : ℕ) (hp : r < 2 * p) :
    Set.InjOn (fun x : (ZMod g)[X] × (ZMod g)[X] => x.1 * x.2)
      ↑(irrDeg g p ×ˢ monicDeg g (r - p)) := by
  rintro ⟨q, h⟩ hx ⟨q', h'⟩ hx' he
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_irrDeg, mem_monicDeg] at hx hx'
  simp only at he
  obtain ⟨⟨⟨hqm, hqd⟩, hqi⟩, hhm, hhd⟩ := hx
  obtain ⟨⟨⟨hqm', hqd'⟩, hqi'⟩, hhm', hhd'⟩ := hx'
  have h1 : q ∣ q' := irr_dvd_of_dvd_mul hqi hhm'.ne_zero (by omega) ⟨h, he.symm⟩
  have hqq : q' = q := eq_of_monic_of_dvd_of_natDegree_le hqm hqm' h1 (by omega)
  subst hqq
  have : h = h' := mul_left_cancel₀ hqm.ne_zero he
  rw [this]
end PI.SqfPrimeFactor.W
