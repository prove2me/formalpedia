-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_proof_901599275078
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:19:48.38026+00:00
-- url     : https://prove2.me/submissions/dd927466-e245-4d39-a9c5-f4f5259071a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_mem_span_ab747a8f951f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_mem_sup_8b18db97daef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_step_2ad7e30af467

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace FiltrationHilbSum
theorem _root_.solution : FiltrationHilbSum.Statement.{u, v} := by
  intro F _ K _ _ ι _ M _ _ _ _ piece hM n N x c q h0 hlast hstep m
  classical
  letI : DirectSum.Decomposition piece := hM.internal.chooseDecomposition
  have hgr : ∀ (i : ℕ) (hi : i < n + 1), ∀ y ∈ N ⟨i, hi⟩, ∀ m',
      FiltrationHilbSum.comp (piece := piece) m' y ∈ N ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi y hy m'
      have hN0 : N ⟨0, hi⟩ = ⊥ := h0
      rw [hN0, Submodule.mem_bot] at hy ⊢
      rw [hy, map_zero]
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      obtain ⟨hx, hN', -⟩ := hstep ⟨i, hi'⟩
      have e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩ := rfl
      have e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩ := rfl
      rw [e1, e2] at hN'
      rw [hN']
      exact FiltrationHilbSum.comp_mem_sup (ih _) (fun y hy m' =>
        FiltrationHilbSum.comp_mem_span hM hx hy m')
  have hcount : ∀ (i : ℕ) (hi : i < n + 1),
      FiniteDimensional F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) ∧
        (Module.finrank F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) : ℤ) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i), hilbFn (q j) (m - c j) := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hN0 : N ⟨0, hi⟩ = ⊥ := h0
      rw [hN0, Submodule.restrictScalars_bot, bot_inf_eq]
      refine ⟨inferInstance, ?_⟩
      rw [finrank_bot, Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.sum_empty]
      rfl
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      obtain ⟨hfd, hr⟩ := ih (by omega)
      obtain ⟨hx, hN', hq⟩ := hstep ⟨i, hi'⟩
      have e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩ := rfl
      have e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩ := rfl
      rw [e1, e2] at hN'
      rw [e2] at hq
      obtain ⟨h1, h2⟩ := FiltrationHilbSum.step hM hx hN' hq (hgr i (by omega)) m
      refine ⟨h1, ?_⟩
      rw [h2, hr]
      have hset : Finset.univ.filter (fun j : Fin n => j.val < i + 1) =
          insert ⟨i, hi'⟩ (Finset.univ.filter (fun j : Fin n => j.val < i)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      ring
  obtain ⟨-, h⟩ := hcount n (by omega)
  have hN : N ⟨n, by omega⟩ = ⊤ := hlast
  rw [hN, Submodule.restrictScalars_top, top_inf_eq] at h
  rw [h, Finset.filter_true_of_mem (fun j _ => j.isLt)]
end FiltrationHilbSum
end GroundTheory.Heights₂.Heights.HilbertSamuel
