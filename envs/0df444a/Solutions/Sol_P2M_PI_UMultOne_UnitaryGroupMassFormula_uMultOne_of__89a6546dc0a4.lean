-- Prove2me | solution 1 for P2M_PI_UMultOne_UnitaryGroupMassFormula_uMultOne_of__89a6546dc0a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:08.066322+00:00
-- url     : https://prove2.me/submissions/61be3bad-a674-481b-a355-a8e2bd1b1a4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
import Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_tr_val
import Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_tr_continuous
import Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_tr_mul
import Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_tr_tr
import Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_emb_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set
namespace PI.UMultOne.UnitaryGroupMassFormula
theorem _root_.solution (hCT : ConjTranspose) (hG : GelfandCompact) (hC : CommutantMult) : MultOne := by
  intro n N M ι hι ρ σ hρ hσ _ _ hρirr hσirr Hm hHm
  have hιc : Continuous ι := emb_continuous n ι hι
  have hclosed : IsClosed ((ι.range : Subgroup _) : Set (Matrix.unitaryGroup (Fin (n + 1)) ℂ)) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range hιc).isClosed
  have hconj : ∀ g : Matrix.unitaryGroup (Fin (n + 1)) ℂ, ∃ h ∈ ι.range, tr (n + 1) g = h * g * h⁻¹ := by
    intro g
    obtain ⟨h, hh, hEq⟩ := hCT n g.1 g.2
    refine ⟨ι ⟨h, hh⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [tr_val, Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
      Matrix.star_eq_conjTranspose, hι]
    exact hEq.symm
  have hcomm := hG (Matrix.unitaryGroup (Fin (n + 1)) ℂ) ι.range (tr (n + 1)) hclosed
    (tr_continuous _) (tr_mul _) (tr_tr _) hconj N ρ hρ hρirr
  refine hC (Matrix.unitaryGroup (Fin n) ℂ) N M (ρ.comp ι) σ
    (show Continuous ((fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) ∘ ι) from hρ.comp hιc)
    hσ hσirr ?_ Hm hHm
  intro A B hA hB
  apply hcomm A B
  · intro h hh
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hh
    exact hA g
  · intro h hh
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hh
    exact hB g
end PI.UMultOne.UnitaryGroupMassFormula
