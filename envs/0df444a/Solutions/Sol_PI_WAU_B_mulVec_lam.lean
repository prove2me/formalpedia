-- Prove2me | solution 1 for PI.WAU.B.mulVec_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:56.787792+00:00
-- url     : https://prove2.me/submissions/f81c99ca-8c63-4719-8dc9-08cb9bd42ecc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Theorems.Thm_PI_WAU_B_incA_mem
import Theorems.Thm_PI_WAU_B_smulO_mem
import Theorems.Thm_PI_WAU_B_lam_sub_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
variable {k : ℕ} {m : Fin k → Fin n → E}
namespace PI.WAU.B
theorem _root_.solution {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    (P : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))
    (hP : ∀ j, P *ᵥ ivec (F := F) (m j) ∈ lamAf (F := F) L) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : P *ᵥ w ∈ lamAf (F := F) L := by
  obtain ⟨a, ha, rfl⟩ := lam_sub_alt hm hgen hw
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Matrix.mulVec_smul]
  exact smulO_mem (incA_mem (ha j)) (hP j)
end PI.WAU.B
