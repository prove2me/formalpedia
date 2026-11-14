-- Prove2me | solution 1 for RvsCert.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T10:05:43.010429+00:00
-- url     : https://prove2.me/submissions/e68b282d-da09-4da6-9d00-721598d43928

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_RvsCert_input_length
import Theorems.Thm_RvsCert_lemma_3
import Theorems.Thm_RvsCert_lemma_4
import Theorems.Thm_RvsCert_lemma_5
import Definitions.Def_RvsCert_C

open RvsCert QAlgorithms

set_option linter.unusedSectionVars false

namespace RvsCertRelabel

/-! ### Certificate complexity under relabeling -/

theorem certAt_spec {ι : Type} [Fintype ι] (f : (ι → Bool) → Bool) (x : ι → Bool) :
    ∃ S : Finset ι, IsCertificate f x S ∧ S.card = certAt f x := by
  have hne : {k : ℕ | ∃ S : Finset ι, IsCertificate f x S ∧ S.card = k}.Nonempty :=
    ⟨Finset.univ.card, Finset.univ, fun y hy => by
      have : y = x := funext fun i => hy i (Finset.mem_univ i)
      rw [this], rfl⟩
  exact Nat.sInf_mem hne

theorem certAt_le {ι : Type} (f : (ι → Bool) → Bool) (x : ι → Bool) (S : Finset ι)
    (h : IsCertificate f x S) : certAt f x ≤ S.card :=
  Nat.sInf_le ⟨S, h, rfl⟩

theorem certAt_comp_le {ι κ : Type} [Fintype κ] (g : (ι → Bool) → Bool) (e : ι ≃ κ)
    (x : ι → Bool) : certAt g x ≤ certAt (fun y : κ → Bool => g (y ∘ e)) (x ∘ e.symm) := by
  obtain ⟨S, hS, hcard⟩ := certAt_spec (fun y : κ → Bool => g (y ∘ e)) (x ∘ e.symm)
  rw [← hcard]
  refine (certAt_le g x (S.map e.symm.toEmbedding) ?_).trans (by simp)
  intro z hz
  have h := hS (z ∘ e.symm) (fun i hi => by
    simpa using hz (e.symm i) (Finset.mem_map_of_mem _ hi))
  have h1 : (z ∘ e.symm) ∘ e = z := by funext i; simp
  have h2 : (x ∘ e.symm) ∘ e = x := by funext i; simp
  simpa [h1, h2] using h

theorem C0_le_C_comp {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : (ι → Bool) → Bool) (e : ι ≃ κ) : C0 g ≤ C (fun y : κ → Bool => g (y ∘ e)) := by
  unfold C0 C
  refine Finset.sup_le fun x _ => ?_
  split_ifs
  · exact (certAt_comp_le g e x).trans (Finset.le_sup (Finset.mem_univ _))
  · exact Nat.zero_le _

/-! ### Randomized query complexity under relabeling -/

def relabelTree {ι κ α : Type} (e : ι → κ) : DecisionTree ι Bool α → DecisionTree κ Bool α
  | .leaf a => .leaf a
  | .node i next => .node (e i) (fun b => relabelTree e (next b))

theorem relabelTree_eval {ι κ α : Type} (e : ι → κ) (t : DecisionTree ι Bool α)
    (y : κ → Bool) : (relabelTree e t).eval y = t.eval (y ∘ e) := by
  induction t with
  | leaf a => rfl
  | node i next ih =>
    simp only [relabelTree, DecisionTree.eval, Function.comp_apply]
    exact ih _

theorem relabelTree_queries {ι κ α : Type} (e : ι → κ) (t : DecisionTree ι Bool α)
    (y : κ → Bool) : (relabelTree e t).queries y = t.queries (y ∘ e) := by
  induction t with
  | leaf a => rfl
  | node i next ih =>
    simp only [relabelTree, DecisionTree.queries, Function.comp_apply]
    rw [ih]

theorem randQC_comp_le {ι κ : Type} (g : (ι → Bool) → Bool) (e : ι ≃ κ) :
    randQC (fun y : κ → Bool => g (y ∘ e)) ≤ randQC g := by
  unfold randQC
  refine le_iInf fun T => le_iInf fun ⟨R, hR, hsucc⟩ => ?_
  refine iInf₂_le T ⟨R.map (relabelTree e), ?_, fun y => ?_⟩
  · intro t ht y
    rw [PMF.support_map] at ht
    obtain ⟨t0, ht0, rfl⟩ := ht
    rw [relabelTree_queries]
    exact hR t0 ht0 _
  · have : (R.map (relabelTree e)).map (fun t => t.eval y) =
        R.map (fun t => t.eval (y ∘ e)) := by
      rw [PMF.map_comp]
      congr 1
      funext t
      exact relabelTree_eval e t y
    unfold successProb
    rw [this]
    exact hsucc (y ∘ e)

/-! ### Quantum query complexity under relabeling -/

section Reindex

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

noncomputable def vecR (σ : Y ≃ X) (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ Y :=
  WithLp.toLp 2 (fun y => v (σ y))

theorem vecR_apply (σ : Y ≃ X) (v : EuclideanSpace ℂ X) (y : Y) : vecR σ v y = v (σ y) := rfl

theorem norm_vecR (σ : Y ≃ X) (v : EuclideanSpace ℂ X) : ‖vecR σ v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [vecR_apply]
  exact Equiv.sum_comp σ (fun x => ‖v x‖ ^ 2)

theorem act_submatrix (σ : Y ≃ X) (M : Matrix X X ℂ) (v : EuclideanSpace ℂ X) :
    act (M.submatrix σ σ) (vecR σ v) = vecR σ (act M v) := by
  ext y
  simp only [act, vecR, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  exact Equiv.sum_comp σ (fun x => M (σ y) x * v x)

theorem prob_eq (ψ : EuclideanSpace ℂ X) (z : X) : prob ψ z = ‖ψ z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

theorem probEvent_vecR (σ : Y ≃ X) (v : EuclideanSpace ℂ X) (P : X → Prop) [DecidablePred P] :
    probEvent (vecR σ v) (fun y => P (σ y)) = probEvent v P := by
  unfold probEvent
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [prob_eq, vecR_apply]
  exact Equiv.sum_comp σ (fun x => if P x then ‖v x‖ ^ 2 else 0)

theorem submatrix_mem_unitary (σ : Y ≃ X) (U : Matrix X X ℂ)
    (hU : U ∈ Matrix.unitaryGroup X ℂ) : U.submatrix σ σ ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  rw [Matrix.star_eq_conjTranspose] at hU ⊢
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv]

end Reindex

section Transport

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def regEquiv (e : ι ≃ κ) (m : ℕ) : ((κ × Bool) × Fin m) ≃ ((ι × Bool) × Fin m) :=
  ((e.symm).prodCongr (Equiv.refl Bool)).prodCongr (Equiv.refl (Fin m))

noncomputable def transAlg (e : ι ≃ κ) {m T : ℕ} (A : QueryAlg ι Bool (Fin m) T) :
    QueryAlg κ Bool (Fin m) T :=
  { start := vecR (regEquiv e m) A.start
    start_unit := (norm_vecR (regEquiv e m) A.start).trans A.start_unit
    U := fun k =>
      ⟨Matrix.submatrix (A.U k : Matrix ((ι × Bool) × Fin m) ((ι × Bool) × Fin m) ℂ)
          (regEquiv e m) (regEquiv e m),
        submatrix_mem_unitary (regEquiv e m)
          (A.U k : Matrix ((ι × Bool) × Fin m) ((ι × Bool) × Fin m) ℂ) (A.U k).2⟩ }

theorem kron_xor (e : ι ≃ κ) (m : ℕ) (y : κ → Bool) :
    Matrix.kronecker (xorOracle y) (1 : Matrix (Fin m) (Fin m) ℂ) =
      (Matrix.kronecker (xorOracle (y ∘ e)) (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix
        (regEquiv e m) (regEquiv e m) := by
  ext ⟨⟨a, b⟩, w⟩ ⟨⟨a', b'⟩, w'⟩
  simp [regEquiv, xorOracle, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem stateAt_trans (e : ι ≃ κ) {m T : ℕ} (A : QueryAlg ι Bool (Fin m) T) (y : κ → Bool)
    (j : Fin (T + 1)) :
    (transAlg e A).stateAt (xorOracle y) j =
      vecR (regEquiv e m) (A.stateAt (xorOracle (y ∘ e)) j) := by
  induction j using Fin.induction with
  | zero =>
    simp only [QueryAlg.stateAt, Fin.induction_zero]
    exact act_submatrix _ _ _
  | succ i ih =>
    simp only [QueryAlg.stateAt, Fin.induction_succ] at ih ⊢
    rw [ih, kron_xor e m y, act_submatrix]
    exact act_submatrix _ _ _

theorem quantQC_comp_le (g : (ι → Bool) → Bool) (e : ι ≃ κ) :
    quantQC (fun y : κ → Bool => g (y ∘ e)) ≤ quantQC g := by
  unfold quantQC
  refine le_iInf fun T => le_iInf fun ⟨m, A, out, hA⟩ => ?_
  refine iInf₂_le T ⟨m, transAlg e A, out ∘ regEquiv e m, fun y _ => ?_⟩
  have h := hA (y ∘ e) (Finset.mem_univ _)
  unfold QueryAlg.outputProb QueryAlg.finalState at h ⊢
  rw [stateAt_trans]
  exact (probEvent_vecR (regEquiv e m) _ (fun x => out x = g (y ∘ e))).symm ▸ h

end Transport

end RvsCertRelabel

open RvsCertRelabel in
theorem solution :
    ∃ (A c : ℝ) (k : ℕ), 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∃ (N : ℕ) (f : (Fin N → Bool) → Bool),
        (N : ℝ) ≤ A * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) ^ k ∧
        c * (n : ℝ) ^ 2 ≤ (C f : ℝ) ∧
        (∃ T : ℕ, randQC f ≤ T ∧ (T : ℝ) ≤ A * (n : ℝ) * (Real.logb 2 n + 1) ^ k) ∧
        (∃ T : ℕ, quantQC f ≤ T ∧ (T : ℝ) ≤ A * Real.sqrt n * (Real.logb 2 n + 1) ^ k) := by
  obtain ⟨-, A1, hA1⟩ := input_length
  obtain ⟨A3, hA3⟩ := lemma_3
  obtain ⟨c, hc, hc4⟩ := lemma_4
  obtain ⟨A5, k5, hA5⟩ := lemma_5
  set A := max (max A1 A3) (max A5 0) with hAdef
  have hA0 : 0 ≤ A := le_trans (le_max_right A5 0) (le_max_right _ _)
  have hA1le : A1 ≤ A := le_trans (le_max_left A1 A3) (le_max_left _ _)
  have hA3le : A3 ≤ A := le_trans (le_max_right A1 A3) (le_max_left _ _)
  have hA5le : A5 ≤ A := le_trans (le_max_left A5 0) (le_max_right _ _)
  refine ⟨A, c, k5 + 1, hc, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : (1 : ℝ) ≤ Real.logb 2 n + 1 := by
    have := Real.logb_nonneg (b := 2) (by norm_num) hn1
    linarith
  have hL0 : (0 : ℝ) ≤ Real.logb 2 n + 1 := by linarith
  have hpow1 : Real.logb 2 n + 1 ≤ (Real.logb 2 n + 1) ^ (k5 + 1) :=
    le_self_pow₀ hL1 (by omega)
  have hpow5 : (Real.logb 2 n + 1) ^ k5 ≤ (Real.logb 2 n + 1) ^ (k5 + 1) :=
    pow_le_pow_right₀ hL1 (by omega)
  let e : Idx n ≃ Fin (Fintype.card (Idx n)) := Fintype.equivFin (Idx n)
  refine ⟨Fintype.card (Idx n), fun y => champion n (y ∘ e), ?_, ?_, ?_, ?_⟩
  · -- input length
    calc (Fintype.card (Idx n) : ℝ) ≤ A1 * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) := hA1 n hn
      _ ≤ A * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) := by gcongr
      _ ≤ A * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) ^ (k5 + 1) := by gcongr
  · -- certificate complexity
    have h1 := hc4 n hn
    have h2 : (C0 (champion n) : ℝ) ≤ (C (fun y => champion n (y ∘ e)) : ℝ) := by
      exact_mod_cast C0_le_C_comp (champion n) e
    linarith
  · -- randomized query complexity
    obtain ⟨T, hT, hTb⟩ := hA3 n hn
    refine ⟨T, (randQC_comp_le (champion n) e).trans hT, ?_⟩
    calc (T : ℝ) ≤ A3 * (n : ℝ) * (Real.logb 2 n + 1) := hTb
      _ ≤ A * (n : ℝ) * (Real.logb 2 n + 1) := by gcongr
      _ ≤ A * (n : ℝ) * (Real.logb 2 n + 1) ^ (k5 + 1) := by gcongr
  · -- quantum query complexity
    obtain ⟨T, hT, hTb⟩ := hA5 n hn
    refine ⟨T, (quantQC_comp_le (champion n) e).trans hT, ?_⟩
    calc (T : ℝ) ≤ A5 * Real.sqrt n * (Real.logb 2 n + 1) ^ k5 := hTb
      _ ≤ A * Real.sqrt n * (Real.logb 2 n + 1) ^ k5 := by gcongr
      _ ≤ A * Real.sqrt n * (Real.logb 2 n + 1) ^ (k5 + 1) := by gcongr
