-- Prove2me | solution 1 for PI.GGMirBoundW.mirabolicBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:42.273833+00:00
-- url     : https://prove2.me/submissions/640f0238-a1c9-4fc9-b8c3-f8b5b18ae6e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Theorems.Thm_PI_GGMirBoundW_claim_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace PI.GGMirBoundW
theorem _root_.solution (hb : BaseProp) (hs : StepProp) : MirabolicBound := by
  intro F _ _ k ψ₀ hψ V _ _ _ π _ hgen
  obtain ⟨ℓ, hℓ, hW⟩ := hgen
  cases k with
  | zero =>
    rw [Finset.Ico_eq_empty_of_le (by norm_num), Finset.prod_empty]
    have : Nontrivial V := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hℓ (by ext v; simp [Subsingleton.elim v 0])
    exact Module.finrank_pos
  | succ n =>
    obtain ⟨p, -, hli⟩ := claim_all hb hs F n ψ₀ hψ V π ℓ hℓ hW
    have h1 := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Subspace.dual_finrank_eq] at h1
    exact h1
end PI.GGMirBoundW
