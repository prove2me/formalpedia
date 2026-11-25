-- Prove2me | solution 1 for PI.WickFormula.Gen.pderiv_mem_lowDeg_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:31.816816+00:00
-- url     : https://prove2.me/submissions/cfadaf4e-e8a3-4615-b5d8-aad62f8969b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan
import Theorems.Thm_PI_WickFormula_Gen_mem_lowDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
namespace PI.WickFormula.Gen
section
variable {K σ ι : Type} [CommRing K] [Fintype ι]
private lemma monomial_mem_lowDeg_of_weighted_sum_lt {f : ι → σ} {t : ℕ} {m : σ →₀ ℕ} (c : K)
    (h : ∑ i, m (f i) < t) : monomial m c ∈ lowDeg f t := by
  rw [mem_lowDeg]
  intro m' hm'
  rw [Finset.mem_singleton.mp (support_monomial_subset hm')]
  exact h
end
section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
end
end PI.WickFormula.Gen
end

set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]
namespace PI.WickFormula.Gen
theorem _root_.solution {f : ι → σ} {t : ℕ} (i : ι) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f (t + 1)) : pderiv (f i) R ∈ lowDeg f t := by
  classical
  have hR := mem_lowDeg.mp h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases h0 : m (f i) = 0
  · rw [h0, Nat.cast_zero, mul_zero, map_zero]
    exact Submodule.zero_mem _
  apply monomial_mem_lowDeg_of_weighted_sum_lt
  have hm' := hR m hm
  have e1 : m (f i) + ∑ j ∈ Finset.univ.erase i, m (f j) = ∑ j, m (f j) :=
    Finset.add_sum_erase _ (fun j => m (f j)) (Finset.mem_univ i)
  have e2 : (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i) + ∑ j ∈ Finset.univ.erase i, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j) =
      ∑ j, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j) :=
    Finset.add_sum_erase _ (fun j => (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j)) (Finset.mem_univ i)
  have le : ∑ j ∈ Finset.univ.erase i, (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f j) ≤ ∑ j ∈ Finset.univ.erase i, m (f j) :=
    Finset.sum_le_sum fun j _ => (Finsupp.tsub_apply _ _ _).trans_le (Nat.sub_le _ _)
  have gi : (m - Finsupp.single (f i) 1 : σ →₀ ℕ) (f i) = m (f i) - 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
  omega
end PI.WickFormula.Gen
