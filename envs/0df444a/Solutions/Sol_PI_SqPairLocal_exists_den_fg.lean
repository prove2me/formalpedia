-- Prove2me | solution 1 for PI.SqPairLocal.exists_den_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:29:26.33479+00:00
-- url     : https://prove2.me/submissions/c540572c-27b7-41d9-8651-f4f23f52d37b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsDenFg
import Theorems.Thm_PI_SqPairLocal_exists_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (L' L'' : Submodule (𝓞 E) (Fin N → E)) (hfg : L'.FG)
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ y ∈ L', d • y ∈ L'' := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  choose f hf0 hf using fun v => exists_den L'' hsp v
  refine ⟨∏ g ∈ S, f g, Finset.prod_ne_zero_iff.mpr (fun g _ => hf0 g), fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.mul_prod_erase S f (Finset.mem_coe.mp hg), mul_comm, mul_smul]
    exact L''.smul_mem _ (hf g)
  | zero => rw [smul_zero]; exact L''.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact L''.add_mem hy hz
  | smul r y _ h => rw [smul_comm]; exact L''.smul_mem r h
end PI.SqPairLocal
