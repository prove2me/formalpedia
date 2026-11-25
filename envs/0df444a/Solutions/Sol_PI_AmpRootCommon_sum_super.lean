-- Prove2me | solution 1 for PI.AmpRootCommon.sum_super
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:13.945417+00:00
-- url     : https://prove2.me/submissions/448debaa-9ecd-4bb4-8a5f-ca151647bbb8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_super_same
import Theorems.Thm_PI_AmpRootCommon_super_diff
import Theorems.Thm_PI_AmpRootCommon_tau_neg
import Theorems.Thm_PI_AmpRootCommon_tau_cs
import Theorems.Thm_PI_AmpRootCommon_tau_succ
import Theorems.Thm_PI_AmpRootCommon_tau_invol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.AmpRootCommon
variable {n : ℕ}
variable {m : ℕ}
namespace PI.AmpRootCommon
theorem _root_.solution {Z u u' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {σ : Fin (m + 1) → Fin (m + 1)}
    {ζ : Fin (m + 1) → ℂ} (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hζ : ∀ i, ζ i ≠ 0)
    (hadj : ∀ i i1 : Fin (m + 1), i1.val = i.val + 1 →
      ((σ i1).val + 1 = (σ i).val ∧ ζ (σ i1) = - ζ (σ i)) ∨ (σ i).val < (σ i1).val)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) :
    ∑ i : Fin m, u' i.castSucc i.succ = star (∑ i : Fin m, u i.castSucc i.succ) := by
  rw [star_sum]
  have hterm : ∀ i : Fin m, u' i.castSucc i.succ = star (u (tau σ i).castSucc (tau σ i).succ) := by
    intro i
    rcases hadj i.castSucc i.succ (by simp) with ⟨h1, h2⟩ | hlt
    · rw [tau_cs h1, tau_succ h1]
      exact super_same hσ hZ hζ hu hud hrel _ _ h1 h2
    · have hn : ¬ (σ i.succ).val + 1 = (σ i.castSucc).val := by omega
      rw [tau_neg hn]
      obtain ⟨e1, e2⟩ := super_diff hσ hZ hζ hu hud hu' hud' hrel _ _ hlt
      rw [e1, e2, star_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact Equiv.sum_comp (Function.Involutive.toPerm (tau σ) (tau_invol hσ))
    (fun i => star (u i.castSucc i.succ))
end PI.AmpRootCommon
