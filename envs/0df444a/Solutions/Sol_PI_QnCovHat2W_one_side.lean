-- Prove2me | solution 1 for PI.QnCovHat2W.one_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:28.737291+00:00
-- url     : https://prove2.me/submissions/a826bffe-3658-4d66-a474-b5c650efed87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Theorems.Thm_PI_QnCovHat2W_reindex_pairs
import Theorems.Thm_PI_QnCovHat2W_sum_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M)
    (hF : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : Fin (m + 2) → ℂ) :
    ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      (m.factorial : ℂ) • ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  rw [sum_two id F hF, ← reindex_pairs F β β', Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [id, smul_smul]
  congr 1
  ring
end PI.QnCovHat2W
