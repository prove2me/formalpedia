-- Prove2me | solution 1 for PaleyWeil.coeff_finite_weightedEuler
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:30:52.489798+00:00
-- url     : https://prove2.me/submissions/beb8550b-d4aa-46df-ae48-bbd048574e99

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_FiniteWeightedEuler
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_WeightedGeometricSeries
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace PowerSeries
end PowerSeries

section


/-! Weighted geometric factors and their exact formal logarithmic derivatives. -/

open scoped PowerSeries
open PowerSeries Finset

namespace PaleyWeil

noncomputable section



@[simp] theorem coeff_weightedGeometric (w : ℤ) (d n : ℕ) :
    PowerSeries.coeff n (weightedGeometric w d) =
      if d ∣ n then w ^ (n / d) else 0 := by
  simp only [weightedGeometric, coeff_mk]


















end
end PaleyWeil

end

/-!
The coefficient identity for a finite weighted Euler product.  The antidiagonal
bijection follows the finite counting argument in Christian Merten's
`WeilConjectures/EulerProductAux.lean` (Apache-2.0), extended here to arbitrary
integer weights and kept entirely finite.
-/
open scoped PowerSeries
open PowerSeries Finset
open PaleyWeil
variable {ι : Type*}

theorem solution [DecidableEq ι]
    (w : ι → ℤ) (d : ι → ℕ) (T : Finset ι) (n : ℕ)
    (hd : ∀ i, d i ≠ 0) (hT : ∀ i, d i ≤ n → i ∈ T) :
    PowerSeries.coeff n (∏ i ∈ T, weightedGeometric (w i) (d i)) =
      ∑' m : {m : ι →₀ ℕ // (m.sum fun i k ↦ k * d i) = n},
        m.1.prod (fun i k ↦ w i ^ k) := by
  classical
  rw [PowerSeries.coeff_prod]
  simp_rw [coeff_weightedGeometric]
  have hfilter :
      (∑ l ∈ Finset.finsuppAntidiag T n,
        ∏ i ∈ T, if d i ∣ l i then w i ^ (l i / d i) else 0) =
      ∑ l ∈ divisibleAntidiag d T n, ∏ i ∈ T, w i ^ (l i / d i) := by
    rw [divisibleAntidiag, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : ∀ i ∈ T, d i ∣ l i
    · rw [if_pos hl]
      exact Finset.prod_congr rfl fun i hi ↦ if_pos (hl i hi)
    · rw [if_neg hl]
      push_neg at hl
      obtain ⟨i, hi, hdiv⟩ := hl
      exact Finset.prod_eq_zero hi (if_neg hdiv)
  rw [hfilter, ← Finset.tsum_subtype,
    ← (weightedAntidiagEquiv d T n hd hT).tsum_eq]
  apply tsum_congr
  intro l
  change (∏ i ∈ T, w i ^ (l.1 i / d i)) =
    (multiplicityVector d l.1).prod (fun i k ↦ w i ^ k)
  have hm := (weightedAntidiagEquiv d T n hd hT l).2
  have hs : (multiplicityVector d l.1).support ⊆ T :=
    weighted_support_subset d T n hT _ hm
  rw [Finsupp.prod_of_support_subset _ hs _ (fun i _ ↦ pow_zero _)]
  rfl
