-- Prove2me | solution 1 for PutermanMDP.Unichain.strict_bias_improvement
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:51:41.849989+00:00
-- url     : https://prove2.me/submissions/51a2712b-0ee6-4be5-a09f-98c68e8384f9

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_Iteration

open MarkovDecisionProcesses Matrix Filter Topology
open PutermanMDP.Unichain

theorem s225_limit_idem {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P * P = P) : BlackwellDiscreteDP.NearOne.limitMatrix P = P := by
  have hpow : ∀ k, P ^ (k + 1) = P := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hP]
  have hsum : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), P ^ k = 1 + (N : ℝ) • P := by
    intro N; induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hpow]
      push_cast; rw [add_smul, one_smul]; abel
  have hc : ∀ N : ℕ, BlackwellDiscreteDP.NearOne.cesaroMean P N =
      (1 / ((N : ℝ) + 1)) • (1 : Matrix n n ℝ) + ((N : ℝ) / ((N : ℝ) + 1)) • P := by
    intro N
    unfold BlackwellDiscreteDP.NearOne.cesaroMean
    rw [hsum, smul_add, smul_smul, one_div, div_eq_inv_mul]
  have ht : Tendsto (BlackwellDiscreteDP.NearOne.cesaroMean P) atTop (𝓝 P) := by
    rw [show BlackwellDiscreteDP.NearOne.cesaroMean P = fun N : ℕ =>
      (1 / ((N : ℝ) + 1)) • (1 : Matrix n n ℝ) + ((N : ℝ) / ((N : ℝ) + 1)) • P from funext hc]
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (1 : Matrix n n ℝ)
    have h2 := (tendsto_natCast_div_add_atTop (1 : ℝ)).smul_const P
    have := h1.add h2
    simpa using this
  exact ht.limUnder_eq

theorem s225_sup2 (t : Finset (Fin 2)) (ht : ∀ a, a ∈ t) (hne : t.Nonempty) (f : Fin 2 → ℝ) :
    t.sup' hne f = max (f 0) (f 1) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    fin_cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' f (ht 0)) (Finset.le_sup' f (ht 1))

noncomputable def s225M : StationaryMDP (Fin 3) (Fin 2) where
  admissible := fun _ => Finset.univ
  admissible_nonempty := fun _ => Finset.univ_nonempty
  reward := fun s a => ![![0, -1], ![2, 1], ![1/2, 0]] s a
  trans := fun _ a j => if a = 0 then (if j = 0 then 1 else 0) else (if j = 2 then 0 else 1/2)
  trans_nonneg := by intro s a j; split_ifs <;> norm_num
  trans_sum := by intro s a; fin_cases a <;> simp [Fin.sum_univ_succ] <;> norm_num

theorem solution : ¬ (∀ {S A : Type} [Fintype S] [Fintype A]
    [DecidableEq S] [Nonempty S] (M : StationaryMDP S A) (hM : IsUnichain M)
    (d d' : Rule M) (g : ℝ) (h : S → ℝ)
    (heval : Evaluates M d g h) (himp : Improves M d d' h)
    (hrec : ∀ s, IsRecurrent (transMatrix M d'.val) s →
      optimalityResidual M g h s = 0)
    (htrans : ∃ s, ¬ IsRecurrent (transMatrix M d'.val) s ∧
      0 < optimalityResidual M g h s),
    ∃ s, ¬ IsRecurrent (transMatrix M d'.val) s ∧
      policyBias M d s < policyBias M d' s) := by
  intro H
  let M := s225M
  have hadm : ∀ s (a : Fin 2), a ∈ M.admissible s := fun _ _ => Finset.mem_univ _
  let d : Rule M := ⟨fun _ => 0, fun s => hadm s 0⟩
  let d' : Rule M := ⟨fun _ => 1, fun s => hadm s 1⟩
  let h : Fin 3 → ℝ := ![0, 2, 1/2]
  -- every state reaches 0 in one step
  have to0 : ∀ (e : Fin 3 → Fin 2) (i : Fin 3), 0 < transMatrix M e i 0 := by
    intro e i
    simp only [transMatrix, M, s225M]
    split_ifs with h1 h2 <;> first | exact absurd h2 (by decide) | norm_num
  have hM : IsUnichain M := by
    intro e _ i j _ hj
    have hi0 : Accessible (transMatrix M e) i 0 := Relation.ReflTransGen.single (to0 e i)
    have hj0 : Accessible (transMatrix M e) j 0 := Relation.ReflTransGen.single (to0 e j)
    exact hi0.trans (hj 0 hj0)
  have P'2 : ∀ i, transMatrix M d'.val i 2 = 0 := by
    intro i; simp [transMatrix, M, s225M, d']
  have notrec2 : ¬ IsRecurrent (transMatrix M d'.val) 2 := by
    intro hr
    have h20 : Accessible (transMatrix M d'.val) 2 0 := Relation.ReflTransGen.single (to0 _ 2)
    have h02 := hr 0 h20
    have key : ∀ j, Accessible (transMatrix M d'.val) 0 j → j ≠ 2 := by
      intro j hj
      induction hj with
      | refl => decide
      | tail _ hbc _ =>
        intro hc; subst hc; rw [P'2] at hbc; exact lt_irrefl _ hbc
    exact key 2 h02 rfl
  have rec01 : ∀ i : Fin 3, i ≠ 2 → IsRecurrent (transMatrix M d'.val) i := by
    intro i hi k _
    have hk0 : Accessible (transMatrix M d'.val) k 0 := Relation.ReflTransGen.single (to0 _ k)
    have h0i : Accessible (transMatrix M d'.val) 0 i := by
      fin_cases i
      · exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        simp [transMatrix, M, s225M, d']
      · exact absurd rfl hi
    exact hk0.trans h0i
  have heval : Evaluates M d 0 h := by
    intro s
    fin_cases s <;> simp [M, s225M, h, d, Fin.sum_univ_succ] <;> norm_num
  have himp : Improves M d d' h := by
    constructor
    · intro s
      refine ⟨hadm s 1, ?_⟩
      rw [s225_sup2 _ (hadm s)]
      fin_cases s <;> simp [M, s225M, h, d', Fin.sum_univ_succ] <;> norm_num
    · intro hI
      have := (hI 2).2
      rw [s225_sup2 _ (hadm 2)] at this
      simp [M, s225M, h, d, Fin.sum_univ_succ] at this
      norm_num at this
  have hres : ∀ s, optimalityResidual M 0 h s =
      max (M.reward s 0 + ∑ j, M.trans s 0 j * h j - h s)
        (M.reward s 1 + ∑ j, M.trans s 1 j * h j - h s) := by
    intro s
    unfold optimalityResidual
    rw [s225_sup2 _ (hadm s)]
    simp
  have hrec : ∀ s, IsRecurrent (transMatrix M d'.val) s → optimalityResidual M 0 h s = 0 := by
    intro s hs
    rw [hres]
    fin_cases s
    · simp [M, s225M, h, Fin.sum_univ_succ]
    · simp [M, s225M, h, Fin.sum_univ_succ]; norm_num
    · exact absurd hs notrec2
  have htrans : ∃ s, ¬ IsRecurrent (transMatrix M d'.val) s ∧ 0 < optimalityResidual M 0 h s := by
    refine ⟨2, notrec2, ?_⟩
    rw [hres]
    simp [M, s225M, h, Fin.sum_univ_succ]; norm_num
  obtain ⟨s, hs, hlt⟩ := H M hM d d' 0 h heval himp hrec htrans
  have hs2 : s = 2 := by
    by_contra hne; exact hs (rec01 s hne)
  subst hs2
  have bias : ∀ e : Rule M, (Matrix.of (transMatrix M e.val) * Matrix.of (transMatrix M e.val) =
      Matrix.of (transMatrix M e.val)) →
      policyBias M e = Matrix.mulVec ((1 : Matrix (Fin 3) (Fin 3) ℝ) - Matrix.of (transMatrix M e.val))
        (policyReward M e) := by
    intro e he
    unfold policyBias policyDeviation BlackwellDiscreteDP.NearOne.deviationMatrix
    have hl : BlackwellDiscreteDP.NearOne.limitMatrix (transMatrix M e.val) = transMatrix M e.val :=
      s225_limit_idem (Matrix.of (transMatrix M e.val)) he
    rw [hl]
    have e1 : @HAdd.hAdd (Matrix (Fin 3) (Fin 3) ℝ) (Matrix (Fin 3) (Fin 3) ℝ) (Matrix (Fin 3) (Fin 3) ℝ) _
        (@HSub.hSub (Matrix (Fin 3) (Fin 3) ℝ) (Matrix (Fin 3) (Fin 3) ℝ) (Matrix (Fin 3) (Fin 3) ℝ) _
          1 (transMatrix M e.val)) (transMatrix M e.val) = 1 :=
      sub_add_cancel _ _
    rw [e1, inv_one]
    rfl
  have idem_d : Matrix.of (transMatrix M d.val) * Matrix.of (transMatrix M d.val) =
      Matrix.of (transMatrix M d.val) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_succ, transMatrix, M, s225M, d]
  have idem_d' : Matrix.of (transMatrix M d'.val) * Matrix.of (transMatrix M d'.val) =
      Matrix.of (transMatrix M d'.val) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_succ, transMatrix, M, s225M, d'] <;> norm_num
  rw [bias d idem_d, bias d' idem_d'] at hlt
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, transMatrix, policyReward, M, s225M, d, d'] at hlt
  norm_num at hlt
