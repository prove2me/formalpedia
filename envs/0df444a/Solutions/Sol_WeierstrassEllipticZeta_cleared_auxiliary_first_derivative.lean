-- Prove2me | solution 1 for WeierstrassEllipticZeta.cleared_auxiliary_first_derivative
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T00:14:22.032802+00:00
-- url     : https://prove2.me/submissions/3cac74e9-60c3-4170-ad1b-33434c1cda10

import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 800000

open Filter Metric Set
open scoped Topology

open WeierstrassEllipticZeta

/-- The first surviving derivative of a cleared translate retains its exact multiplier. -/
theorem solution
    (L : PeriodPair)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    {ι : Type} [Fintype ι] (v : ℂ) (_hv : v ∉ L.lattice)
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (M : ℕ)
    (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) :
    AnalyticAt ℂ (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z ∧
      ∀ n : ℕ,
        (∀ j < n, iteratedDeriv j (fun w => ∑ i, c i * w ^ l₀ i *
          L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v) = 0) →
        iteratedDeriv n (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z =
          (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) *
            iteratedDeriv n (fun w => ∑ i, c i * w ^ l₀ i *
              L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v) := by
  classical
  let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ l₀ i *
    L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i
  let A : ℂ → ℂ := fun w => (2 * (L.weierstrassP v - L.weierstrassP w)) ^ (3 * M)
  have hZ : AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun w hw => (h_zeta_deriv w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hF : AnalyticAt ℂ F (z + v) := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact ((analyticAt_const.mul (analyticAt_id.pow _)).mul
      ((L.analyticOnNhd_weierstrassP _ hp).pow _)).mul ((hZ _ hp).pow _)
  have hG : AnalyticAt ℂ (fun w => F (w + v)) z :=
    hF.comp (f := fun w : ℂ => w + v) (analyticAt_id.add analyticAt_const)
  have hA : AnalyticAt ℂ A z :=
    (analyticAt_const.mul (analyticAt_const.sub
      (L.analyticOnNhd_weierstrassP z hz))).pow _
  have heq : clearedAuxiliarySum L v c l₀ l₂ l₃ M = fun w => A w * F (w + v) := by
    funext w
    simp only [clearedAuxiliarySum, clearedAdditionMonomial, A, F, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  constructor
  · rw [heq]
    exact hA.mul hG
  · intro n hbefore
    rw [heq, iteratedDeriv_fun_mul hA.contDiffAt hG.contDiffAt, Finset.sum_eq_single 0]
    · simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, one_mul,
        Nat.sub_zero, iteratedDeriv_comp_add_const]
      rfl
    · intro i hi hi0
      have hni : n - i < n := by have := Finset.mem_range.mp hi; omega
      rw [iteratedDeriv_comp_add_const]
      change (n.choose i : ℂ) * iteratedDeriv i A z * iteratedDeriv (n - i) F (z + v) = 0
      rw [show iteratedDeriv (n - i) F (z + v) = 0 from hbefore _ hni, mul_zero]
    · simp
