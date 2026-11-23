-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.mem_hcompl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:42.64127+00:00
-- url     : https://prove2.me/submissions/2bb6188f-b79f-413a-a446-16535f8a9773

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_hcompl_eq_closure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) (s : 𝓞 K) :
    s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ↔ s ∉ p ∧ s ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  rw [hcompl_eq_closure, mem_conjIdeal_iff]
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
      rw [map_one]
      exact fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h)
    | mul x y _ _ hx hy =>
      refine ⟨fun h => (hp.mem_or_mem h).elim hx.1 hy.1, ?_⟩
      rw [map_mul]
      exact fun h => (hp.mem_or_mem h).elim hx.2 hy.2
  · intro h
    exact Submonoid.subset_closure h
end ReciprocityTheory.ChartRestriction.L3.WA
