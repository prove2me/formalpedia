-- Prove2me | solution 1 for PI.WhitFunctDualWork.whit_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:26:48.488668+00:00
-- url     : https://prove2.me/submissions/2714e38d-35f2-49e8-90c3-ca1f850106b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible
import Theorems.Thm_PI_WhitFunctDualWork_besselEdge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WhitFunctDualWork
open Formalism.L2.SG.GGMirabolic
namespace PI.WhitFunctDualWork
theorem _root_.solution {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V)
    (ℓ : Module.Dual ℂ V) (hℓ : IsWhit ψ₀ π ℓ) :
    ℓ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := by
  intro u
  beta_reduce
  obtain ⟨hdiag, hlow, -⟩ := u.2
  have huni : IsUni k (u : GL (Fin k) F) := ⟨hdiag, hlow⟩
  have hp : psiU ψ₀ (u : GL (Fin k) F) ≠ 0 := by
    intro h0
    have h3 := AddChar.map_add_eq_mul ψ₀ (superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
      (-superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at h3
    unfold psiU at h0
    rw [h0, zero_mul] at h3
    exact one_ne_zero h3
  have hchar : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar ψ₀⁻¹ 0 0 k (u : GL (Fin k) F) =
      (psiU ψ₀ (u : GL (Fin k) F))⁻¹ := by
    unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar psiU superdiag
    rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
    congr 2
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : (j : ℕ) = (i : ℕ) + 1 <;> simp [hij, besselEdge_zero]
  ext v
  have hinv : π (u : GL (Fin k) F) (π ((u : GL (Fin k) F)⁻¹) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hw := hℓ (u : GL (Fin k) F) huni (π ((u : GL (Fin k) F)⁻¹) v)
  rw [hinv] at hw
  rw [Representation.dual_apply, LinearMap.smul_apply, hchar, smul_eq_mul,
    Module.Dual.transpose_apply, LinearMap.comp_apply, hw, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
end PI.WhitFunctDualWork
