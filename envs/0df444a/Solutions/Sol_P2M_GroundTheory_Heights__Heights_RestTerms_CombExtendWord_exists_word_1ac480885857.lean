-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_exists_word_1ac480885857
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:48.749907+00:00
-- url     : https://prove2.me/submissions/96f09ff8-9198-4c45-b677-2aefcb770663

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombExtendWord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_snoc_mem_52aadcb06899
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_zero_8589bd36c748
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_update_pred_sub_9997e7a05bb7


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
open Finset Comb
noncomputable section
open scoped Classical
open GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
namespace GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
theorem _root_.solution {m : ℕ} (h1 : CombPcntAppend.Statement) (μ : Fin m → ℕ) (hμ : Antitone μ) :
    ∀ (q : ℕ) (lam : Fin m → ℕ), Antitone lam → (∀ i, μ i ≤ lam i) →
      ∑ i, lam i = ∑ i, μ i + q →
        ∃ s : Fin q → Fin m, ∀ n, ∀ w ∈ latticeWords n μ,
          Fin.append w s ∈ latticeWords (n + q) lam := by
  intro q
  induction q with
  | zero =>
    intro lam _ hle hsum
    have heq : ∀ i, μ i = lam i := by
      have := (Finset.sum_eq_sum_iff_of_le (s := univ) (fun i _ => hle i)).mp (by simpa using hsum.symm)
      exact fun i => this i (mem_univ i)
    refine ⟨Fin.elim0, fun n w hw => ?_⟩
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
    have hp : ∀ t i, pcnt (Fin.append w (Fin.elim0 : Fin 0 → Fin m)) t i = pcnt w t i := by
      intro t i
      rw [h1]
      have : pcnt (Fin.elim0 : Fin 0 → Fin m) (t - n) i = 0 := by unfold pcnt; simp
      omega
    refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
    · rw [hp, hp]; exact hw.1 t ht i j hij
    · rw [hp, Nat.add_zero, hw.2 i, heq i]
  | succ q ih =>
    intro lam hlam hle hsum
    have hne : (univ.filter (fun i => μ i < lam i)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have : ∑ i, lam i ≤ ∑ i, μ i :=
        Finset.sum_le_sum fun i _ => not_lt.mp (hemp (mem_univ i))
      omega
    obtain ⟨k, hk, hkmax⟩ : ∃ k, μ k < lam k ∧ ∀ j, μ j < lam j → j ≤ k :=
      ⟨_, (mem_filter.mp (max'_mem _ hne)).2,
        fun j hj => le_max' _ j (mem_filter.mpr ⟨mem_univ j, hj⟩)⟩
    have hgt : ∀ j, k < j → lam j = μ j := by
      intro j hj
      by_contra hne'
      exact absurd (hkmax j (lt_of_le_of_ne (hle j) (Ne.symm hne'))) (not_le.mpr hj)
    have hanti : Antitone (Function.update lam k (lam k - 1)) := by
      intro i j hij
      by_cases hik : i = k <;> by_cases hjk : j = k
      · rw [hik, hjk]
      · rw [hik, Function.update_self, Function.update_of_ne hjk]
        have hkj : k < j := lt_of_le_of_ne (hik ▸ hij) (Ne.symm hjk)
        rw [hgt j hkj]
        have := hμ (hik ▸ hij)
        omega
      · rw [hjk, Function.update_self, Function.update_of_ne hik]
        have := hlam (hjk ▸ hij)
        omega
      · rw [Function.update_of_ne hik, Function.update_of_ne hjk]
        exact hlam hij
    have hle' : ∀ i, μ i ≤ Function.update lam k (lam k - 1) i := by
      intro i
      by_cases hik : i = k
      · rw [hik, Function.update_self]; omega
      · rw [Function.update_of_ne hik]; exact hle i
    have hsum' : ∑ i, Function.update lam k (lam k - 1) i = ∑ i, μ i + q := by
      have h2 : ∀ i, Function.update lam k (lam k - 1) i + (if k = i then 1 else 0) = lam i :=
        fun i => update_pred_sub lam k i (by omega)
      have : ∑ i, lam i = ∑ i, Function.update lam k (lam k - 1) i + 1 := by
        rw [← Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp
      omega
    obtain ⟨s', hs'⟩ := ih _ hanti hle' hsum'
    refine ⟨Fin.snoc s' k, fun n w hw => ?_⟩
    rw [Fin.append_snoc]
    exact snoc_mem lam hlam k (by omega) _ (hs' n w hw)
end GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
