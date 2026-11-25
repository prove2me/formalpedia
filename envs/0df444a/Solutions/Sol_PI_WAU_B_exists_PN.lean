-- Prove2me | solution 1 for PI.WAU.B.exists_PN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:11.496452+00:00
-- url     : https://prove2.me/submissions/5a01da63-09c2-48a3-a38a-3680dbdba09f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Theorems.Thm_PI_WAU_B_exists_nat_vec
import Theorems.Thm_PI_WAU_B_nsmul_lam


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
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct
variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)
namespace PI.WAU.B
theorem _root_.solution (x : I.Gf) : ∃ N, PN I m N x := by
  classical
  have hA : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  have hB : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  choose A hA0 hA using hA
  choose B hB0 hB using hB
  refine ⟨(∏ j, A j) * ∏ j, B j, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact Nat.mul_pos (Finset.prod_pos fun j _ => hA0 j) (Finset.prod_pos fun j _ => hB0 j)
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem A (Finset.mem_univ j)
    rw [hM, mul_assoc]
    exact nsmul_lam (hA j) _
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem B (Finset.mem_univ j)
    rw [hM, show (∏ j, A j) * (B j * M) = B j * (M * ∏ j, A j) by ring]
    exact nsmul_lam (hB j) _
end PI.WAU.B
