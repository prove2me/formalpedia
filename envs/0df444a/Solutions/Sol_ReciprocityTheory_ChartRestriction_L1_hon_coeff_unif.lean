-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hon_coeff_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:22.269464+00:00
-- url     : https://prove2.me/submissions/d84c9796-1874-43e9-b60b-62ec9bb6d668

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_twC_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K) (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M) :
    ‖(l : K) * coeff n lam - ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1)‖ ≤ ‖(l : K)‖ := by
  have h1 : ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)
      = ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold twC
    split_ifs <;> simp
  have h2 : ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1)
      = ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1) := by
    refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
      fun j _ hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [twC_eq_zero hl τ h0 (by omega), mul_zero]
  rw [← h2, ← h1]
  exact E n
end ReciprocityTheory.ChartRestriction.L1
