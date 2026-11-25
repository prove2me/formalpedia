-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_prod_entry_eq_0ac10606d8ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:24.593851+00:00
-- url     : https://prove2.me/submissions/4542b55f-c238-4def-9906-5bfa53983066

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution {m k : ℕ} (hm : 0 < m) (K r : ℝ) (σ : Equiv.Perm (Fin m)) :
    ∏ i : Fin m, ∏ j : Fin (m + k), K / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
        ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) =
      K ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1) := by
  have hrow : ∀ i : Fin m, ∏ j : Fin (m + k),
      (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
        ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) =
      (1 + r ^ 2) ^ ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1) := by
    intro i
    rw [Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj]; simp)
      (by simp)]
    simp
  have hsum : ∑ i : Fin m,
      ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1) = m + 1 := by
    have h : ∀ i : Fin m, (Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i)) ↔
        (σ.symm ⟨0, hm⟩ = i) := by
      intro i
      rw [(Fin.castAdd_injective _ _).eq_iff, Equiv.symm_apply_eq]
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [add_comm]
  simp_rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hrow,
    Finset.prod_pow_eq_pow_sum, hsum, ← pow_mul]
  ring_nf
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
