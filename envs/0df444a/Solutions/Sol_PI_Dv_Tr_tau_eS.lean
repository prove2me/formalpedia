-- Prove2me | solution 1 for PI.Dv.Tr.tau_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:58.769617+00:00
-- url     : https://prove2.me/submissions/8ec4c31d-16d2-46ce-8320-14973980040b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_phiS_apply
import Theorems.Thm_PI_Dv_Tr_mul_eS
import Theorems.Thm_PI_Dv_Tr_tau_eS_scalar
import Theorems.Thm_P2M_PI_Dv_Tr_finrank_pos__519d460918af

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) : (T.tau s).asAlgebraHom (eS T s) = 1 := by
  obtain ⟨c, hc⟩ := tau_eS_scalar T s s

  have hcomp : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) = c • LinearMap.id := by
    ext1 X
    obtain ⟨a, rfl⟩ := T.irr s X
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, ← mul_eS, map_mul, hc,
      LinearMap.smul_apply, LinearMap.id_apply, mul_smul_comm, mul_one]
  have hsum : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) =
      ∑ x : G, cf T s • ((LinearMap.trace K (T.W s) ∘ₗ LinearMap.mulLeft K (T.tau s x⁻¹)).smulRight
        (T.tau s x)) := by
    ext1 X
    rw [LinearMap.sum_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, phiS_apply, map_sum,
      map_smul, Representation.asAlgebraHom_of]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [smul_smul]
  have htr := congrArg (LinearMap.trace K (Module.End K (T.W s))) hsum
  rw [hcomp, map_sum] at htr
  simp only [map_smul, LinearMap.trace_smulRight, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, ← map_mul, inv_mul_cancel, map_one, LinearMap.trace_one, LinearMap.trace_id,
    Module.finrank_linearMap, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htr
  have hd : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0 := by
    exact_mod_cast (finrank_pos' T s).ne'
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc1 : c = 1 := by
    simp only [cf, Nat.cast_mul] at htr
    field_simp at htr
    exact htr
  rw [hc, hc1, one_smul]
end PI.Dv.Tr
