-- Prove2me | solution 1 for PI.Dv.TIW.select_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:02.833078+00:00
-- url     : https://prove2.me/submissions/9b7ba92a-eead-4573-aa53-111629dca805

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace PI.Dv.TIW
theorem _root_.solution {ι : Type} (F : ι → V) (hF : Submodule.span K (Set.range F) = ⊤) :
    ∃ g : Fin (Module.finrank K V) → ι, LinearIndependent K (F ∘ g) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K F
  rw [hF] at hsp
  let b := Module.Basis.mk hli (by rw [hsp])
  letI := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card κ = Module.finrank K V := (Module.finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨a ∘ e.symm, ?_⟩
  have := hli.comp e.symm e.symm.injective
  simpa [Function.comp_assoc] using this
end PI.Dv.TIW
