-- Prove2me | solution 1 for WeldedPath.verifier_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T16:29:29.560157+00:00
-- url     : https://prove2.me/submissions/362730e5-b46a-4a6d-87c0-bfdb7c953eb2

import Theorems.Thm_WeldedPath_lemma_4_13
import Theorems.Thm_WeldedPath_loop_erasure_acceptance
import Theorems.Thm_WeldedPath_verifier_realization
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false


open QAlgorithms

namespace WeldedPath.VerifierProbability

theorem probEvent_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {P Q : ι → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ z, P z → Q z) : QAlgorithms.probEvent ψ P ≤ QAlgorithms.probEvent ψ Q := by
  unfold QAlgorithms.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hPQ z hz
  · intro z _ _
    exact sq_nonneg _

theorem probEvent_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (P : ι → Prop) [DecidablePred P] :
    0 ≤ QAlgorithms.probEvent ψ P := by
  unfold QAlgorithms.probEvent
  exact Finset.sum_nonneg fun z _ => sq_nonneg _

theorem avgOver_mono {α : Type*} (S : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ S, f x ≤ g x) : avgOver S f ≤ avgOver S g := by
  unfold avgOver
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum hfg) (Nat.cast_nonneg _)

theorem avgOver_nonneg {α : Type*} (S : Finset α) {f : α → ℝ}
    (hf : ∀ x ∈ S, 0 ≤ f x) : 0 ≤ avgOver S f := by
  unfold avgOver
  exact div_nonneg (Finset.sum_nonneg hf) (Nat.cast_nonneg _)

theorem probOver_mono {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (S : Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges))
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    {P Q : Equiv.Perm (Label n) × Equiv.Perm G.edges →
      ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W → Prop}
    (hPQ : ∀ σ ∈ S, ∀ z, P σ z → Q σ z) :
    G.probOver l S A P ≤ G.probOver l S A Q := by
  classical
  unfold WeldedInstance.probOver
  exact avgOver_mono S fun σ hσ => probEvent_mono _ (hPQ σ hσ)

theorem probOver_nonneg {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    (S : Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges))
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (P : Equiv.Perm (Label n) × Equiv.Perm G.edges →
      ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W → Prop) :
    0 ≤ G.probOver l S A P := by
  classical
  unfold WeldedInstance.probOver
  exact avgOver_nonneg S fun σ _ => probEvent_nonneg _ _

theorem pWt_nonneg {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) :
    0 ≤ Supplement.pWt l G A out := by
  exact probOver_nonneg l G _ A _

end WeldedPath.VerifierProbability

open WeldedPath QAlgorithms WeldedPath.Supplement

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      ∃ out' : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1)),
      G.successProb l A out ≤
        C * (pWt l G A out' + (n : ℝ) * (q : ℝ) ^ 2 / (2 : ℝ) ^ n) := by

  classical
  rcases lemma_4_13 with ⟨C, hC, hdist⟩
  refine ⟨100 * C, by positivity, ?_⟩
  intro n l hn hn16 hl hlmax G hG W _ _ q hq A out
  obtain ⟨erase, herase⟩ := loop_erasure_acceptance n l hn hn16 hl hlmax G hG
  let out' := fun z => erase (out z)
  refine ⟨out', ?_⟩
  obtain ⟨W', instF, instD, hB⟩ := verifier_realization n l G W q hq A out'
  letI : Fintype W' := instF
  letI : DecidableEq W' := instD
  obtain ⟨B, acc, heq⟩ := hB
  have hcomplete : G.successProb l A out ≤
      G.probOver l (G.singSupport l) B (fun _ => acc) := by
    rw [heq]
    unfold WeldedInstance.successProb
    apply VerifierProbability.probOver_mono
    intro σ hσ z hz
    exact herase σ hσ (out z) q hq hz
  have hcompare := hdist n l hn hl hlmax G hG W' (7 * q + 3)
    (by omega) B acc
  have hprod : G.probOver l (G.prodSupport l) B (fun _ => acc) =
      Supplement.pWt l G A out' := heq _
  rw [hprod] at hcompare
  have hqueries : ((7 * q + 3 : ℕ) : ℝ) ≤ 10 * (q : ℝ) := by
    exact_mod_cast (show 7 * q + 3 ≤ 10 * q by omega)
  have herr : (n : ℝ) * ((7 * q + 3 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ n ≤
      100 * ((n : ℝ) * (q : ℝ) ^ 2 / (2 : ℝ) ^ n) := by
    calc
      (n : ℝ) * ((7 * q + 3 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ n ≤
          (n : ℝ) * (10 * (q : ℝ)) ^ 2 / (2 : ℝ) ^ n := by gcongr
      _ = 100 * ((n : ℝ) * (q : ℝ) ^ 2 / (2 : ℝ) ^ n) := by ring
  have hp := VerifierProbability.pWt_nonneg l G A out'
  have hscale : Supplement.pWt l G A out' +
      (n : ℝ) * ((7 * q + 3 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ n ≤
      100 * (Supplement.pWt l G A out' +
        (n : ℝ) * (q : ℝ) ^ 2 / (2 : ℝ) ^ n) := by linarith
  calc
    G.successProb l A out ≤ C * (Supplement.pWt l G A out' +
        (n : ℝ) * ((7 * q + 3 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ n) :=
      hcomplete.trans hcompare
    _ ≤ C * (100 * (Supplement.pWt l G A out' +
        (n : ℝ) * (q : ℝ) ^ 2 / (2 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left hscale hC.le
    _ = (100 * C) * (Supplement.pWt l G A out' +
        (n : ℝ) * (q : ℝ) ^ 2 / (2 : ℝ) ^ n) := by ring
