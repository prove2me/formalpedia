-- Prove2me | solution 1 for PI.WickFormula.Gen.eq_zero_of_mem_lowDeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:16:12.938514+00:00
-- url     : https://prove2.me/submissions/b726bed9-502f-4315-9823-9fa3849b8b14

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
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]
namespace PI.WickFormula.Gen
theorem _root_.solution {f : ι → σ} {R : MvPolynomial σ K}
    (h : R ∈ lowDeg f 0) : R = 0 := by
  rw [mem_lowDeg] at h
  ext m
  rw [coeff_zero]
  by_contra hne
  exact Nat.not_lt_zero _ (h m (mem_support_iff.mpr hne))
end PI.WickFormula.Gen
