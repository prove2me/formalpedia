-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.conjO_mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:44.921041+00:00
-- url     : https://prove2.me/submissions/afac82c7-4e54-446c-8f1e-66ec17d094e2

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_conjO_conjO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_hcompl_eq_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_conjO_conjO


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
theorem _root_.solution {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  rw [hcompl_eq_closure] at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    refine Submonoid.subset_closure ⟨hx.2, ?_⟩
    rw [ReciprocityTheory.ChartRestriction.L3.conjO_conjO]
    exact hx.1
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
end ReciprocityTheory.ChartRestriction.L3.WA
