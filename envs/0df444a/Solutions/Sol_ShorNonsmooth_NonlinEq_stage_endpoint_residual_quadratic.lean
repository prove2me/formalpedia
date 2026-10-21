-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.stage_endpoint_residual_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T14:50:37.507543+00:00
-- url     : https://prove2.me/submissions/176eb8b4-29f0-4a50-b057-244dd11f155a

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_component_residual_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ ε > 0, ∃ C > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε → maxResidual ψ (x n) ≤ C * ‖x 0‖ ^ 2 := by
  classical
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro x hx hx0
    simp [maxResidual]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    choose ε hε C hC hbound using fun k : Fin n =>
      stage_component_residual_quadratic ψ hψ h0 δ L hδ hLip hind k
    let hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
    let η : ℝ := Finset.univ.inf' hne ε
    let c : ℝ := (∑ k, C k) + 1
    have hηpos : 0 < η := by
      dsimp [η]
      exact Iff.mpr
        ((Finset.lt_inf'_iff (s := Finset.univ) (f := ε)) hne)
        (by intro k hk; exact hε k)
    have hcpos : 0 < c := by
      dsimp [c]
      have hsum : 0 ≤ ∑ k, C k :=
        Finset.sum_nonneg (fun k hk => (hC k).le)
      linarith
    refine ⟨η, hηpos, c, hcpos, ?_⟩
    intro x hx hx0
    have hcomp : ∀ k : Fin n, |ψ k (x n)| ≤ c * ‖x 0‖ ^ 2 := by
      intro k
      have hxk : ‖x 0‖ ≤ ε k := by
        exact le_trans hx0 (by dsimp [η]; exact Finset.inf'_le ε (Finset.mem_univ k))
      have hsingle : C k ≤ ∑ j, C j :=
        Finset.single_le_sum (fun j hj => (hC j).le) (Finset.mem_univ k)
      have hCk : C k ≤ c := by
        dsimp [c]
        linarith
      exact (hbound k x hx hxk).trans
        (mul_le_mul_of_nonneg_right hCk (sq_nonneg _))
    simpa [maxResidual] using ciSup_le hcomp
