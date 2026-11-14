-- Prove2me | solution 1 for QuantileMDP.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-13T17:06:17.905684+00:00
-- url     : https://prove2.me/submissions/61775507-10ec-4395-a4c2-624f7211b8e4

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QuantileMDP_optValue

open MeasureTheory QuantileMDP
open scoped ENNReal

namespace QuantileMDP

private theorem pathPrefix_zero {S : Type*} {n : ℕ} (s : S) (g : Fin (n + 1) → S) :
    pathPrefix (Fin.cons s g) (0 : Fin (n + 1)) = fun _ => s := by
  funext j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  rfl

private theorem pathPrefix_succ {S : Type*} {n : ℕ} (s : S) (g : Fin (n + 1) → S)
    (k : Fin n) :
    pathPrefix (Fin.cons s g) k.succ = Fin.cons s (pathPrefix g k) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · rfl

private theorem pathWeight_cons {S A : Type*} {n : ℕ} (M : Model S A) (t : ℕ)
    (π : Policy S A) (s : S) (g : Fin (n + 1) → S) :
    pathWeight (M.shift t) π (Fin.cons s g) =
      M.P t s (π 0 (fun _ => s)) (g 0) *
        pathWeight (M.shift (t + 1)) (π.tail s) g := by
  rw [pathWeight, Fin.prod_univ_succ, pathPrefix_zero, pathWeight]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [pathPrefix_succ]
  simp [Model.shift, Policy.tail, Nat.add_left_comm, Nat.add_comm]

private theorem pathReward_cons {S A : Type*} {n : ℕ} (M : Model S A) (t : ℕ)
    (π : Policy S A) (s : S) (g : Fin (n + 1) → S) :
    pathReward (M.shift t) π (Fin.cons s g) =
      M.r t s (π 0 (fun _ => s)) (g 0) +
        pathReward (M.shift (t + 1)) (π.tail s) g := by
  rw [pathReward, Fin.sum_univ_succ, pathPrefix_zero, pathReward]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pathPrefix_succ]
  simp [Model.shift, Policy.tail, Nat.add_left_comm, Nat.add_comm]

/-- Group the finite path sum by its first transition. Each group is the
shifted reward law of the tail policy, scaled by the first transition weight. -/
private theorem rewardLaw_cons {S A : Type*} [Fintype S] (M : Model S A)
    (n t : ℕ) (π : Policy S A) (s : S) (a : A) (ha : π 0 (fun _ => s) = a) :
    rewardLaw (M.shift t) (n + 1) π s =
      ∑ s' : S, M.P t s a s' •
        (rewardLaw (M.shift (t + 1)) n (π.tail s) s').map
          (fun x => x + M.r t s a s') := by
  classical
  unfold rewardLaw
  calc
    _ = ∑ z : S × (Fin n → S),
        pathWeight (M.shift t) π (Fin.cons s (Fin.cons z.1 z.2)) •
          Measure.dirac (pathReward (M.shift t) π (Fin.cons s (Fin.cons z.1 z.2))) := by
      symm
      exact (Fin.consEquiv (fun _ : Fin (n + 1) => S)).sum_comp
        (fun g => pathWeight (M.shift t) π (Fin.cons s g) •
          Measure.dirac (pathReward (M.shift t) π (Fin.cons s g)))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s' _
      have hm : Measurable (fun x : ℝ => x + M.r t s a s') :=
        measurable_id.add_const _
      rw [Measure.map_finset_sum' hm.aemeasurable, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [pathWeight_cons, pathReward_cons, ha, Fin.cons_zero,
        Measure.map_smul, Measure.map_dirac' hm, smul_smul]
      exact congrArg (fun x : ℝ => _ • Measure.dirac x) (add_comm _ _)

end QuantileMDP

/-- Equation (7) of Li, Zhong and Brandeau, including the reward-law identity
behind the optimization over policies with a fixed first action. -/
theorem solution {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T t : ℕ)
    (ht : t < T) (s : S) (a : A) :
    (∀ π : Policy S A, (M.shift t).Admissible π → π 0 (fun _ => s) = a →
      rewardLaw (M.shift t) (T - t) π s =
        ∑ s' : S, M.P t s a s' •
          (rewardLaw (M.shift (t + 1)) (T - (t + 1)) (π.tail s) s').map
            (fun x => x + M.r t s a s')) ∧
    (∀ τ : ℝ, optValueAct M T t s τ a =
      ⨆ (π : Policy S A) (_ : (M.shift t).Admissible π) (_ : π 0 (fun _ => s) = a),
        quantile (∑ s' : S, M.P t s a s' •
          (rewardLaw (M.shift (t + 1)) (T - (t + 1)) (π.tail s) s').map
            (fun x => x + M.r t s a s')) τ) := by
  have hlength : T - t = (T - (t + 1)) + 1 := by omega
  have hlaw (π : Policy S A) (ha : π 0 (fun _ => s) = a) :
      rewardLaw (M.shift t) (T - t) π s =
        ∑ s' : S, M.P t s a s' •
          (rewardLaw (M.shift (t + 1)) (T - (t + 1)) (π.tail s) s').map
            (fun x => x + M.r t s a s') := by
    conv_lhs => rw [hlength]
    exact rewardLaw_cons M (T - (t + 1)) t π s a ha
  refine ⟨fun π _ ha => hlaw π ha, fun τ => ?_⟩
  unfold optValueAct
  congr 1
  funext π
  congr 1
  funext hπ
  congr 1
  funext ha
  rw [hlaw π ha]
