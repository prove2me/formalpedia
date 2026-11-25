-- Prove2me | solution 1 for PI.WickFormula.Gen.pderiv_mem_lowDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:15.924804+00:00
-- url     : https://prove2.me/submissions/7a9178a5-61b9-4459-90ff-a9f50b3e3480

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
theorem _root_.solution {f : ι → σ} {t : ℕ} (k : σ) {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f t) : pderiv k R ∈ lowDeg f t := by
  have hR := mem_lowDeg.mp h
  rw [R.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  apply monomial_mem_lowDeg_of_weighted_sum_lt
  exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ => (Finsupp.tsub_apply _ _ _).trans_le (Nat.sub_le _ _)) (hR m hm)
end PI.WickFormula.Gen
