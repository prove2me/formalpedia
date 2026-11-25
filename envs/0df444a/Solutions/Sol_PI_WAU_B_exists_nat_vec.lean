-- Prove2me | solution 1 for PI.WAU.B.exists_nat_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:27.073249+00:00
-- url     : https://prove2.me/submissions/7a2c6ff1-c7d3-4c7b-ae1d-395332108760

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Theorems.Thm_PI_WAU_B_common_nat
import Theorems.Thm_PI_WAU_B_ivec_mem
import Theorems.Thm_PI_WAU_B_smulO_mem
import Theorems.Thm_PI_WAU_B_nsmul_lam
import Theorems.Thm_PI_WAU_B_exists_nat_R
import Theorems.Thm_PI_WAU_B_exists_nat_L
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
theorem _root_.solution {L : Submodule (𝓞 E) (Fin n → E)}
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E ⊗[F] Af F) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ lamAf (F := F) L := by
  classical
  have hi : ∀ i, ∃ N, 0 < N ∧ N • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) ∈
      lamAf (F := F) L := by
    intro i
    obtain ⟨A, hA0, hA⟩ := exists_nat_R (F := F) (E := E) (w i)
    obtain ⟨B, hB0, hB⟩ := exists_nat_L (L := L) (z := Pi.single i 1)
      (by rw [hspan]; exact Submodule.mem_top)
    refine ⟨A * B, Nat.mul_pos hA0 hB0, ?_⟩
    have e1 : ivec (F := F) (B • (Pi.single i 1 : Fin n → E)) =
        (B : E ⊗[F] Af F) • (Pi.single i 1 : Fin n → E ⊗[F] Af F) := by
      funext j
      by_cases h : j = i
      · subst h; simp [ivec]
      · simp [ivec, Pi.single_apply, h]
    have e2 : (A * B) • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) =
        ((A : E ⊗[F] Af F) * w i) • ivec (F := F) (B • (Pi.single i 1 : Fin n → E)) := by
      rw [e1, smul_smul, ← Nat.cast_smul_eq_nsmul (E ⊗[F] Af F), smul_smul]
      congr 1
      push_cast; ring
    rw [e2]
    exact smulO_mem hA (ivec_mem hB)
  obtain ⟨N, hN0, hN⟩ := common_nat
    (fun i N => N • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) ∈ lamAf (F := F) L)
    (fun i N M h => nsmul_lam h M) hi
  refine ⟨N, hN0, ?_⟩
  have ew : w = ∑ i, (w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [ew, Finset.smul_sum]
  exact Submodule.sum_mem _ fun i _ => hN i
end PI.WAU.B
