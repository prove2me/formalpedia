-- Prove2me | solution 1 for PI.WickFormula.Gen.mem_lowDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:51.42185+00:00
-- url     : https://prove2.me/submissions/80fadffd-6f4a-45d8-98e8-c8ee0ee1d45f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenVan

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
theorem _root_.solution {f : ι → σ} {t : ℕ} {R : MvPolynomial σ K} :
    R ∈ lowDeg f t ↔ ∀ m ∈ R.support, ∑ i, m (f i) < t := by
  unfold lowDeg
  rw [mem_restrictSupport_iff]
  exact Iff.rfl
end PI.WickFormula.Gen
