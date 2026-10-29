-- Prove2me | solution 1 for PutermanMDP.Discounted.mpi_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:22:24.150998+00:00
-- url     : https://prove2.me/submissions/f05f209c-fa48-4eef-982a-f7c7e82c4f70

import Mathlib
import Definitions.Def_PutermanMDP_Discounted_Operators

open Filter Topology
open PutermanMDP.Discounted

theorem aux_abs_tsum_le {S : Type} (p : S → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : HasSum p 1)
    (w : S → ℝ) (K : ℝ) (hK : ∀ j, |w j| ≤ K) : |∑' j, p j * w j| ≤ K := by
  have hg : HasSum (fun j => p j * K) K := by simpa using hp.mul_right K
  have := tsum_of_norm_bounded (f := fun j => p j * w j) hg (by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 j)]
    exact mul_le_mul_of_nonneg_left (hK j) (hp0 j))
  simpa [Real.norm_eq_abs] using this

theorem aux_summable {S : Type} (p : S → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : HasSum p 1)
    (w : S → ℝ) (K : ℝ) (hK : ∀ j, |w j| ≤ K) : Summable (fun j => p j * w j) := by
  refine Summable.of_norm_bounded (g := fun j => p j * K) (hp.summable.mul_right K) ?_
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 j)]
  exact mul_le_mul_of_nonneg_left (hK j) (hp0 j)

theorem solution {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)] (M : Model S A)
    (m : ℕ → ℕ) (v : ℕ → S → ℝ) (d : ℕ → DecisionRule A)
    (hv : VB M (v 0)) (hrun : MPIRun M m v d) :
    ∀ n, v (n + 1) = v n + neumann M (d n) (m n) (residual M (v n)) := by
  -- transition preserves boundedness
  have Tbd : ∀ (e : DecisionRule A) (u : S → ℝ), BoundedValue u →
      BoundedValue (transition M e u) := by
    rintro e u ⟨C, hC⟩
    exact ⟨C, fun s => aux_abs_tsum_le _ (M.trans_nonneg s (e s)) (M.trans_sum s (e s)) u C hC⟩
  have Tsub : ∀ (e : DecisionRule A) (u w : S → ℝ), BoundedValue u → BoundedValue w →
      transition M e u - transition M e w = transition M e (u - w) := by
    rintro e u w ⟨Cu, hCu⟩ ⟨Cw, hCw⟩
    funext s
    simp only [transition, Pi.sub_apply]
    rw [← (aux_summable _ (M.trans_nonneg s (e s)) (M.trans_sum s (e s)) u Cu hCu).tsum_sub
      (aux_summable _ (M.trans_nonneg s (e s)) (M.trans_sum s (e s)) w Cw hCw)]
    congr 1; funext j; ring
  have Tsmul : ∀ (e : DecisionRule A) (c : ℝ) (u : S → ℝ),
      transition M e (fun j => c * u j) = fun s => c * transition M e u s := by
    intro e c u; funext s
    simp only [transition]
    rw [← tsum_mul_left]; congr 1; funext j; ring
  have Lbd : ∀ (e : DecisionRule A) (u : S → ℝ), BoundedValue u →
      BoundedValue (policyOperator M e u) := by
    intro e u hu
    obtain ⟨C, hC⟩ := Tbd e u hu
    refine ⟨M.bound + M.discount * C, fun s => ?_⟩
    simp only [policyOperator]
    have h1 := M.reward_bounded s (e s)
    have h2 := hC s
    calc _ ≤ |M.reward s (e s)| + |M.discount * transition M e u s| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg M.discount_nonneg]
        have := mul_le_mul_of_nonneg_left h2 M.discount_nonneg
        linarith
  have Literbd : ∀ (e : DecisionRule A) (k : ℕ) (u : S → ℝ), BoundedValue u →
      BoundedValue ((policyOperator M e)^[k] u) := by
    intro e k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [Function.iterate_succ_apply']
      exact Lbd e _ (ih u hu)
  have Lsub : ∀ (e : DecisionRule A) (u w : S → ℝ), BoundedValue u → BoundedValue w →
      policyOperator M e u - policyOperator M e w =
        fun s => M.discount * transition M e (u - w) s := by
    intro e u w hu hw
    rw [← Tsub e u w hu hw]
    funext s
    simp only [policyOperator, Pi.sub_apply]
    ring
  -- difference of iterates
  have D : ∀ (e : DecisionRule A) (u : S → ℝ), BoundedValue u → ∀ k,
      (policyOperator M e)^[k + 1] u - (policyOperator M e)^[k] u =
        fun s => M.discount ^ k * (transition M e)^[k] (policyOperator M e u - u) s := by
    intro e u hu k
    induction k with
    | zero => funext s; simp
    | succ k ih =>
      have h := Lsub e _ _ (Literbd e (k + 1) u hu) (Literbd e k u hu)
      simp only [← Function.iterate_succ_apply' (policyOperator M e)] at h
      rw [h, ih, Tsmul]
      funext s
      rw [Function.iterate_succ_apply']
      ring
  have vbd : ∀ n, BoundedValue (v n) := by
    intro n
    induction n with
    | zero => exact hv.1
    | succ n ih =>
      rw [(hrun n).2.2]
      exact Literbd _ _ _ ih
  intro n
  obtain ⟨hg, _, hstep⟩ := hrun n
  rw [hstep]
  funext s
  have tele := Finset.sum_range_sub (fun k => (policyOperator M (d n))^[k] (v n) s) (m n + 1)
  simp only [Function.iterate_zero, id_eq] at tele
  have hres : PutermanMDP.Discounted.residual M (v n) = policyOperator M (d n) (v n) - v n := by
    unfold PutermanMDP.Discounted.residual; rw [hg]
  simp only [Pi.add_apply, neumann, hres]
  have : ∀ k, (policyOperator M (d n))^[k + 1] (v n) s - (policyOperator M (d n))^[k] (v n) s
      = M.discount ^ k * (transition M (d n))^[k] (policyOperator M (d n) (v n) - v n) s := by
    intro k
    have := congrFun (D (d n) (v n) (vbd n) k) s
    simpa using this
  rw [Finset.sum_congr rfl (fun k _ => (this k).symm)]
  linarith [tele]
