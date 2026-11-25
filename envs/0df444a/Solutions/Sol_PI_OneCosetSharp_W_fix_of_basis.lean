-- Prove2me | solution 1 for PI.OneCosetSharp.W.fix_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:01:05.490845+00:00
-- url     : https://prove2.me/submissions/b79ad140-a068-49d0-9c93-6f42b937fc9d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
import Theorems.Thm_PI_OneCosetSharp_W_eN_apply
import Theorems.Thm_P2M_PI_OneCosetSharp_W_lowProj_apply__162d0f7a10c7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n c : ℕ}
namespace PI.OneCosetSharp.W
theorem _root_.solution (g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (hga : ∀ i < c, g (eN k (n + c) (n + i)) = eN k (n + c) (n + i)) (w : Fin (n + c) → k)
    (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : g w = w := by
  have hsum : w = ∑ l : Fin (n + c), w l • PI.OneCosetSharp.Loc.eN k (n + c) l.1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · simp [eN_apply]
    · intro b _ hb
      have hx : x.1 ≠ b.1 := fun h => hb (Fin.ext h).symm
      simp [eN_apply, hx]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul]
  by_cases hl : l.1 < n
  · have h0 : w l = 0 := by
      have h1 := congrFun hw l
      rw [lowProj_apply₂, if_pos hl] at h1
      exact h1
    rw [h0, zero_smul, zero_smul]
  · have hlt := l.2
    have hl' : l.1 = n + (l.1 - n) := by omega
    rw [hl', hga (l.1 - n) (by omega)]
end PI.OneCosetSharp.W
