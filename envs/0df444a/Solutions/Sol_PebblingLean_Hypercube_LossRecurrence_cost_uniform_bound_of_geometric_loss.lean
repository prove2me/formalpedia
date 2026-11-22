-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_geometric_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:34.965349+00:00
-- url     : https://prove2.me/submissions/197d101e-170b-405d-a14a-72cb28f18036

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_exp_lossBound_mul_base
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_exists_terminal_iterate_of_decreasing
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_lossSum_le_geomSum_mul_bound

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence
namespace PebblingLean.Hypercube.LossRecurrence
theorem _root_.solution
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B q M G : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M)
    (hgeom : ∀ k : ℕ, geomSum q k ≤ G) (n : ℕ) :
    R n ≤ Real.exp (G * M) * B := by
  rcases exists_terminal_iterate_of_decreasing
    (next := next) (n0 := n0) hnext n with
    ⟨k, hactive, hterm⟩
  have hsum :
      lossSum next loss k n ≤ geomSum q k * M :=
    lossSum_le_geomSum_mul_bound
      (next := next) (loss := loss) (n0 := n0)
      (q := q) (M := M) hq_nonneg hdecay hbound k n hactive
  have hgeom_mul : geomSum q k * M ≤ G * M :=
    mul_le_mul_of_nonneg_right (hgeom k) hM
  exact cost_le_exp_lossBound_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) (L := G * M)
    hloss hB hstep hactive (hbase _ hterm) (hsum.trans hgeom_mul)
end PebblingLean.Hypercube.LossRecurrence
