-- Prove2me | solution 1 for PI.WAU.B.T_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:10.409296+00:00
-- url     : https://prove2.me/submissions/52d07809-14ae-4dda-a3e1-2144ec0ef233

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Theorems.Thm_PI_WAU_B_T_smulA
import Theorems.Thm_PI_WAU_B_T_sum
import Theorems.Thm_PI_WAU_B_T_gen
import Theorems.Thm_PI_WAU_B_left_smul_ivec

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
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) (t : 𝓞 E) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ Tset (F := F) m) :
    ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) • w ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  rw [Finset.smul_sum]
  refine T_sum _ _ fun j _ => ?_
  rw [smul_comm, left_smul_ivec]
  exact T_smulA (ha j) (T_gen hgen (L.smul_mem t (hm j)))
end PI.WAU.B
