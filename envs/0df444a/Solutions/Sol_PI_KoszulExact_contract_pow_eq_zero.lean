-- Prove2me | solution 1 for PI.KoszulExact.contract_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:59.654036+00:00
-- url     : https://prove2.me/submissions/69307cee-665c-4fdd-9075-83c5c0afc937

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
namespace PI.KoszulExact
theorem _root_.solution (N : Submodule R M) (f : Module.Dual R M) (hf : ∀ m ∈ N, f m = 0) :
    ∀ (j : ℕ) (x : ExteriorAlgebra R M), x ∈ (N.map (ExteriorAlgebra.ι R)) ^ j →
      CliffordAlgebra.contractLeft f x = 0 := by
  intro j
  induction j with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.mem_one] at hx
    obtain ⟨y, rfl⟩ := hx
    exact CliffordAlgebra.contractLeft_algebraMap _ f y
  | succ j ih =>
    intro x hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨m, hm, rfl⟩ := ha
      rw [CliffordAlgebra.contractLeft_ι_mul, hf m hm, ih b hb, zero_smul, mul_zero, sub_zero]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
end PI.KoszulExact
