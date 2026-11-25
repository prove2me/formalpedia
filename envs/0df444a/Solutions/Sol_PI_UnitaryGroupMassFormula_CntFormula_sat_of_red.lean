-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.sat_of_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:10.369791+00:00
-- url     : https://prove2.me/submissions/f250df07-c608-4a05-92ed-4f8fd029da2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_key_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]
variable {F}
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : SatF F X := by
  intro u hu hex
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun i => ?_, hc⟩
  by_contra hci
  rw [Valuation.mem_integer_iff, not_le] at hci
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (c i))
    ⟨i, Finset.mem_univ _⟩
  have hj1 : 1 < valuation F (c j) := lt_of_lt_of_le hci (hj i (Finset.mem_univ _))
  have hcj : c j ≠ 0 := by
    intro h
    rw [h, map_zero] at hj1
    exact not_lt.2 zero_le' hj1
  exact key_norm X hX hred c u hc j (fun i => hj i (Finset.mem_univ _)) hcj
    (fun k => lt_of_le_of_lt ((Valuation.mem_integer_iff _ _).1 (hu k)) hj1)
end PI.UnitaryGroupMassFormula.CntFormula
