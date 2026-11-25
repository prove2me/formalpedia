-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_proof_f44e3bbd234b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:44.136013+00:00
-- url     : https://prove2.me/submissions/b9f09f2e-8392-4196-abde-fe16ecb45e41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_abs_cf_perm_755c477b2285
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_alternantPsum_cons_28c4eecdeac9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_isAlt_alternantPsum_69aa1f2841c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_bound_nil_68a0da39912e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_eq_zero_of_eq_f9e5a7715b7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_mul_psum_0f698be248eb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Equiv Comb
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
namespace GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
theorem _root_.solution (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombStripSum.Statement) : CombCfBound.Statement := by
  intro m ρ
  induction ρ with
  | nil => intro _ lam hlam; exact bound_nil m lam hlam
  | cons q ρ ih =>
    intro hpos lam hlam
    have hq : 1 ≤ q := hpos q (by simp)
    have ih' := ih (fun r hr => hpos r (List.mem_cons_of_mem _ hr))
    have hterm : ∀ i : Fin m,
        |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| ≤
        (if q ≤ lam i + stair m i then
          |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m (List.replicate ρ.sum 1))| else 0) := by
      intro i
      split_ifs with hqi
      · by_cases hinj :
            Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        · obtain ⟨σ, μ, hμ, -, hσ⟩ := h2 m lam hlam q i hqi hinj
          have hu : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) =
              (fun k => μ k + stair m k) ∘ σ.symm := by
            funext k
            have := hσ (σ.symm k)
            rwa [Equiv.apply_symm_apply] at this
          rw [hu, abs_cf_perm (isAlt_alternantPsum m ρ), abs_cf_perm (isAlt_alternantPsum m _),
            h1 m ρ.sum μ hμ, Nat.abs_cast]
          exact ih' μ hμ
        · simp only [Function.Injective, not_forall] at hinj
          obtain ⟨a, b, hab, hne⟩ := hinj
          rw [cf_eq_zero_of_eq (isAlt_alternantPsum m ρ) hne hab, abs_zero]
          exact abs_nonneg _
      · simp
    rw [alternantPsum_cons, cf_mul_psum]
    calc _ ≤ ∑ i : Fin m, |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ((latticeWords (ρ.sum + q) lam).card : ℚ) := h3 m ρ.sum q lam hlam hq
      _ = ((latticeWords (q :: ρ).sum lam).card : ℚ) := by rw [List.sum_cons, add_comm]
end GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
