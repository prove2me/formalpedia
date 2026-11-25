-- Prove2me | solution 1 for PI.CharIdemW.comm_of_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:55.456265+00:00
-- url     : https://prove2.me/submissions/8e271d23-f57b-4c00-848d-dc4ef6ed5087

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (W : FDRep ℂ G) (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) : W.ρ h * (∑ g : G, f g • W.ρ g) = (∑ g : G, f g • W.ρ g) * W.ρ h := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ (fun g => ?_)
  show W.ρ h * (f g • W.ρ g) = f (h * g * h⁻¹) • W.ρ (h * g * h⁻¹) * W.ρ h
  rw [hf g h, smul_mul_assoc, mul_smul_comm, ← map_mul W.ρ h g, ← map_mul W.ρ (h * g * h⁻¹) h,
    inv_mul_cancel_right]
end PI.CharIdemW
