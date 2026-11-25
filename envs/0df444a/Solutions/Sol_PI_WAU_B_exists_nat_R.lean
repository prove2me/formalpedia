-- Prove2me | solution 1 for PI.WAU.B.exists_nat_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:34.871799+00:00
-- url     : https://prove2.me/submissions/2b1d56ae-ec57-42de-8b2d-78585caac5c4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Theorems.Thm_PI_WAU_B_exists_nat_E
import Theorems.Thm_PI_WAU_B_left_mem
import Theorems.Thm_PI_WAU_B_incA_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_B_exists_nat_adele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace PI.WAU.B
theorem _root_.solution (r : E ⊗[F] Af F) : ∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * r ∈ IntAf F E := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by simp⟩
  | tmul e a =>
    obtain ⟨c, hc0, t, ht⟩ := exists_nat_E e
    obtain ⟨N, hN0, hN⟩ := exists_nat_adele a
    refine ⟨c * N, Nat.mul_pos hc0 hN0, ?_⟩
    have e1 : ((c * N : ℕ) : E ⊗[F] Af F) * (e ⊗ₜ[F] a) =
        ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) * incA F E ((N : Af F) * a) := by
      calc ((c * N : ℕ) : E ⊗[F] Af F) * (e ⊗ₜ[F] a) = (c * N) • (e ⊗ₜ[F] a) :=
            (nsmul_eq_mul _ _).symm
        _ = (c • e) ⊗ₜ[F] (N • a) := by
            rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_smul]
        _ = ((c : E) * e) ⊗ₜ[F] ((N : Af F) * a) := by rw [nsmul_eq_mul, nsmul_eq_mul]
        _ = _ := by
            rw [ht]
            simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.includeRight_apply]
    rw [e1]
    exact mul_mem (left_mem t) (incA_mem (fun v => hN v))
  | add x y hx hy =>
    obtain ⟨N1, h1, hx⟩ := hx
    obtain ⟨N2, h2, hy⟩ := hy
    refine ⟨N2 * N1, Nat.mul_pos h2 h1, ?_⟩
    have e1 : ((N2 * N1 : ℕ) : E ⊗[F] Af F) * (x + y) =
        (N2 : E ⊗[F] Af F) * ((N1 : E ⊗[F] Af F) * x) +
          (N1 : E ⊗[F] Af F) * ((N2 : E ⊗[F] Af F) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem (natCast_mem _ _) hx) (mul_mem (natCast_mem _ _) hy)
end PI.WAU.B
