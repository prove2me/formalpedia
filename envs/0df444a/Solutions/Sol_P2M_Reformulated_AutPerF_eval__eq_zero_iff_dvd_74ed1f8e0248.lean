-- Prove2me | solution 1 for P2M_Reformulated_AutPerF_eval__eq_zero_iff_dvd_74ed1f8e0248
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:37.946461+00:00
-- url     : https://prove2.me/submissions/b3ce8e28-12f7-4c20-9844-f7811cc80980

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {A : Type u} [CommRing A]
namespace Reformulated.AutPerF
theorem _root_.solution (a : A) (n : ℕ) (x : AdicCompletion (span {a}) A) :
    AdicCompletion.evalₐ (span {a}) n x = 0 ↔
      algebraMap A (AdicCompletion (span {a}) A) a ^ n ∣ x := by
  constructor
  · intro h
    have h1 : AdicCompletion.eval (span {a}) A n x = 0 := by
      rw [← AdicCompletion.factor_evalₐ_eq_eval (span {a}) x (by simp), h, map_zero]
    have h2 : x ∈ (span {a} ^ n • ⊤ : Submodule A (AdicCompletion (span {a}) A)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton a)]
      exact h1
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨y, -, rfl⟩ := h2
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (mem_span_singleton_self _) _), zero_mul]
end Reformulated.AutPerF
