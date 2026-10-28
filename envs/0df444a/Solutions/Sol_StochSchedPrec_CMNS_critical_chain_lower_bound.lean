-- Prove2me | solution 1 for StochSchedPrec.CMNS.critical_chain_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:11:44.111981+00:00
-- url     : https://prove2.me/submissions/63415da1-18bd-45e9-895d-dc4d398518e0

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace Aux_StochSchedPrec_CMNS_critical_chain_lower_bound

open StochSchedPrec.CMNS

lemma crit_mem {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) (r : V → ℝ)
    (tb : V ≃ Fin (Fintype.card V)) (p S : V → ℝ) (j i : V)
    (h : critPred A r tb p S j = some i) : Relation.TransGen A i j := by
  classical
  unfold critPred at h
  simp only at h
  split_ifs at h with hne
  · have hmem := Finset.min'_mem _ (hne.image tb)
    rw [Finset.mem_image] at hmem
    obtain ⟨i', hi', heq⟩ := hmem
    have : tb.symm ((Finset.image tb _).min' (hne.image tb)) = i' := by
      rw [← heq, Equiv.symm_apply_apply]
    rw [Option.some_inj] at h
    rw [← h, this]
    exact (Finset.mem_filter.1 hi').2.1

lemma trans_le {V : Type*} (A : V → V → Prop) (p S : V → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hA : ∀ i j, A i j → S i + p i ≤ S j) {i j : V} (h : Relation.TransGen A i j) :
    S i + p i ≤ S j := by
  induction h with
  | single hab => exact hA _ _ hab
  | @tail b c _ hbc ih =>
    have h1 := hA _ _ hbc
    have h2 := hp b
    linarith

lemma aux_le {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) (r : V → ℝ)
    (tb : V ≃ Fin (Fintype.card V)) (p S S' : V → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hr : ∀ j, r j ≤ S' j) (hA : ∀ i j, A i j → S' i + p i ≤ S' j) :
    ∀ n j, chainLengthAux A r tb p S n j ≤ S' j + p j := by
  intro n
  induction n with
  | zero => intro j; simp only [chainLengthAux]; linarith [hr j]
  | succ n ih =>
    intro j
    simp only [chainLengthAux]
    cases hc : critPred A r tb p S j with
    | none => simp only; linarith [hr j]
    | some i =>
      simp only
      have h1 := ih i
      have h2 := trans_le A p S' hp hA (crit_mem A r tb p S j i hc)
      linarith

lemma aux_nonneg {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) (r : V → ℝ)
    (tb : V ≃ Fin (Fintype.card V)) (p S : V → ℝ) (hp : ∀ j, 0 ≤ p j) (hr : ∀ j, 0 ≤ r j) :
    ∀ n j, 0 ≤ chainLengthAux A r tb p S n j := by
  intro n
  induction n with
  | zero => intro j; simp only [chainLengthAux]; linarith [hr j, hp j]
  | succ n ih =>
    intro j
    simp only [chainLengthAux]
    cases hc : critPred A r tb p S j with
    | none => simp only; linarith [hr j, hp j]
    | some i => simp only; linarith [ih i, hp j]

end Aux_StochSchedPrec_CMNS_critical_chain_lower_bound

open Aux_StochSchedPrec_CMNS_critical_chain_lower_bound in
open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (tb : V ≃ Fin (Fintype.card V)) :
    (∀ (p S S' : V → ℝ), (∀ j, 0 ≤ p j) → IsFeasible m A r p S' →
        ∀ j, chainLength A r tb p S j ≤ S' j + p j) ∧
      ∀ (P : V → Ω → ℝ), IsStochModel Pr P →
        ∀ (σ : (V → ℝ) → V → ℝ), AEMeasurable (fun ω => σ (fun k => P k ω)) Pr →
        ∀ (pol : (V → ℝ) → V → ℝ), IsAdmissiblePolicy m A r Pr P pol →
        ∀ j, ∫ ω, chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j ∂Pr
          ≤ ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by
  have part1 : ∀ (p S S' : V → ℝ), (∀ j, 0 ≤ p j) → IsFeasible m A r p S' →
      ∀ j, chainLength A r tb p S j ≤ S' j + p j := by
    intro p S S' hp hfeas j
    exact aux_le A r tb p S S' hp hfeas.1 hfeas.2.1 _ j
  refine ⟨part1, ?_⟩
  intro P hP σ _ pol hpol j
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun ω =>
      aux_nonneg A r tb _ _ (fun k => hP.2.1 k ω) hr _ j)
  · exact hpol.2.2 j
  · exact Filter.Eventually.of_forall (fun ω =>
      part1 _ _ _ (fun k => hP.2.1 k ω) (hpol.1 _ (fun k => hP.2.1 k ω)) j)
