-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.indep_of_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:06.78959+00:00
-- url     : https://prove2.me/submissions/fe80e007-7011-4086-88ab-864dfc7be900

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
    (hred : LinearIndependent 𝓀[F] (redM F X)) : LinearIndependent F X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (g i))
    ⟨i0, Finset.mem_univ _⟩
  have hcj : g j ≠ 0 := by
    intro h
    have h2 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h2
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h2 zero_le'))
  refine key_norm X hX hred g 0 hg j (fun i => hj i (Finset.mem_univ _)) hcj (fun k => ?_)
  rw [Pi.zero_apply, map_zero]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)
end PI.UnitaryGroupMassFormula.CntFormula
