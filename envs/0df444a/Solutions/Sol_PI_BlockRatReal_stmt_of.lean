-- Prove2me | solution 1 for PI.BlockRatReal.stmt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:43.698961+00:00
-- url     : https://prove2.me/submissions/050092fe-7002-4da8-a77b-2bf6ab43a9d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_AntitoneStar
import Theorems.Thm_PI_BlockRatReal_reM_rfl
import Theorems.Thm_PI_BlockRatReal_detShift_eq
import Theorems.Thm_PI_BlockRatReal_natW_eq
import Theorems.Thm_PI_BlockRatReal_antitone_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal
namespace PI.BlockRatReal
theorem _root_.solution (hE : EvenStep) (hO : OddStep) : Stmt := by
  intro nV n' m lam0 Tau _ n LL _ h pos G M embLL lam hanti htie hM
  subst h
  intro v s f hf
  set τ := pos ⟨v, s⟩ with hτ
  have hl : lam0 v s = lam τ := funext fun i => by rw [htie v s i]; rfl
  obtain ⟨M0, hM0⟩ := hM τ
  have hf' : f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lam τ)) := by
    rw [← natW_eq]; exact hf
  by_cases hs : Even s.val
  · have hla : lamAt (lam0 v) s = lam τ := by rw [lamAt, if_pos hs, hl]
    obtain ⟨F, hF, hFe⟩ := hE m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (hanti τ)]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_pos hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1
  · have hla : lamAt (lam0 v) s = fun i => -lam τ i.rev := by rw [lamAt, if_neg hs, hl]
    obtain ⟨F, hF, hFe⟩ := hO m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (antitone_star (hanti τ))]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_neg hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1
end PI.BlockRatReal
