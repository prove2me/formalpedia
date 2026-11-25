-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.iterSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:33.940901+00:00
-- url     : https://prove2.me/submissions/84a7978c-b432-47c7-bf46-a0e2eddaff16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_symm_fix
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_symm_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution : IterSymm := by
  intro V _ _ F Ω hΩ hF
  suffices h : ∀ k : ℕ, ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)),
      iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v from
    fun c hc k v σ => h k c hc v σ
  intro k
  induction k with
  | zero =>
    intro c hc v σ
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    intro c hc v σ
    have key : ∀ (j : Fin (k + 1)) (u : Fin (k + 1) → V),
        iteratedFDeriv ℂ (k + 1) F c (u ∘ Equiv.swap 0 j) = iteratedFDeriv ℂ (k + 1) F c u := by
      intro j u
      by_cases hj0 : j = 0
      · subst hj0
        simp
      · cases k with
        | zero => exact absurd (Fin.fin_one_eq_zero j) hj0
        | succ m =>
          by_cases hj1 : j = 1
          · subst hj1
            exact symm_swap hΩ hF hc u
          · have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
            have hs : Equiv.swap (0 : Fin (m + 2)) j =
                Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j := by
              rw [Equiv.swap_mul_swap_mul_swap h01 (Ne.symm hj0), Equiv.swap_comm]
            have hfix : ∀ w : Fin (m + 2) → V,
                iteratedFDeriv ℂ (m + 2) F c (w ∘ Equiv.swap 1 j) = iteratedFDeriv ℂ (m + 2) F c w :=
              fun w => symm_fix hΩ hF ih hc (Equiv.swap 1 j)
                (Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)) w
            have hcomp : u ∘ ⇑((Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j :
                Equiv.Perm (Fin (m + 2)))) =
                ((u ∘ Equiv.swap 1 j) ∘ Equiv.swap 0 1) ∘ Equiv.swap 1 j := by
              funext i
              simp [Equiv.Perm.mul_apply]
            rw [hs, hcomp, hfix, symm_swap hΩ hF hc, hfix]
    have h0 : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      simp [Equiv.Perm.mul_apply]
    have hv : v ∘ σ = (v ∘ Equiv.swap 0 (σ 0)) ∘ ⇑(Equiv.swap 0 (σ 0) * σ) := by
      funext i
      simp [Equiv.Perm.mul_apply]
    rw [hv, symm_fix hΩ hF ih hc _ h0, key]
end PositivityTheory.Rg.Sw.LVs.TC
