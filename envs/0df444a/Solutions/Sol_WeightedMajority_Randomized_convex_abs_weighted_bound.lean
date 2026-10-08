-- Prove2me | solution 1 for WeightedMajority.Randomized.convex_abs_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-08T04:26:48.484833+00:00
-- url     : https://prove2.me/submissions/e4c0b3a8-813a-488d-9045-3bcf8ef2e3a1

import Mathlib
set_option autoImplicit false

-- Child A of the WeightedMajority theorem_6_1 decomposition (triage DECOMPOSE
-- 2026-10-07): convex-combination triangle-inequality bound, pure real analysis.
-- Standalone proof: no Theorems.Thm_* citations.
-- Proof idea: multiply rho into the fraction, |a/S - rho| * S = |sum w_i (x_i - rho)|
-- since S > 0, then Finset.abs_sum_le_sum_abs with |w_i| = w_i for w_i >= 0.

theorem solution {n : Nat} (w x : Fin n -> Real) (rho : Real)
    (hw : forall i, 0 <= w i) (hx : forall i, 0 <= x i /\ x i <= 1)
    (hpos : 0 < Finset.sum Finset.univ (fun i => w i)) :
    abs (Finset.sum Finset.univ (fun i => w i * x i)
      / Finset.sum Finset.univ (fun i => w i) - rho)
      * Finset.sum Finset.univ (fun i => w i)
      <= Finset.sum Finset.univ (fun i => w i * abs (x i - rho)) := by
  have hS : 0 < Finset.sum Finset.univ (fun i => w i) := hpos
  have hSne : Finset.sum Finset.univ (fun i => w i) ≠ 0 := ne_of_gt hS
  have habsS : abs (Finset.sum Finset.univ (fun i => w i))
      = Finset.sum Finset.univ (fun i => w i) := abs_of_pos hS
  -- sum w_i * (x_i - rho) = sum w_i * x_i - rho * sum w_i
  have h1 : Finset.sum Finset.univ (fun i => w i * (x i - rho))
      = Finset.sum Finset.univ (fun i => w i * x i)
        - rho * Finset.sum Finset.univ (fun i => w i) := by
    have e : ∀ i ∈ Finset.univ, w i * (x i - rho) = w i * x i - w i * rho :=
      fun i _ => mul_sub _ _ _
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib,
      ← Finset.sum_mul Finset.univ (fun x => w x) rho, mul_comm rho]
  -- the weighted-mean deviation is a single fraction
  have hfrac : Finset.sum Finset.univ (fun i => w i * x i)
        / Finset.sum Finset.univ (fun i => w i) - rho
      = Finset.sum Finset.univ (fun i => w i * (x i - rho))
        / Finset.sum Finset.univ (fun i => w i) := by
    rw [eq_div_iff hSne, sub_mul, div_mul_cancel₀ _ hSne, h1]
  -- |.| * S with S > 0 absorbs the division
  have hstep : abs (Finset.sum Finset.univ (fun i => w i * x i)
        / Finset.sum Finset.univ (fun i => w i) - rho)
        * Finset.sum Finset.univ (fun i => w i)
      = abs (Finset.sum Finset.univ (fun i => w i * (x i - rho))) := by
    rw [hfrac, abs_div, habsS, div_mul_cancel₀ _ hSne]
  rw [hstep]
  calc abs (Finset.sum Finset.univ (fun i => w i * (x i - rho)))
      ≤ Finset.sum Finset.univ (fun i => abs (w i * (x i - rho))) :=
        Finset.abs_sum_le_sum_abs _ _
    _ = Finset.sum Finset.univ (fun i => w i * abs (x i - rho)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]

namespace WeightedMajority.Randomized

theorem convex_abs_weighted_bound {n : Nat} (w x : Fin n -> Real) (rho : Real)
    (hw : forall i, 0 <= w i) (hx : forall i, 0 <= x i /\ x i <= 1)
    (hpos : 0 < Finset.sum Finset.univ (fun i => w i)) :
    abs (Finset.sum Finset.univ (fun i => w i * x i)
      / Finset.sum Finset.univ (fun i => w i) - rho)
      * Finset.sum Finset.univ (fun i => w i)
      <= Finset.sum Finset.univ (fun i => w i * abs (x i - rho)) :=
    solution w x rho hw hx hpos

end WeightedMajority.Randomized
