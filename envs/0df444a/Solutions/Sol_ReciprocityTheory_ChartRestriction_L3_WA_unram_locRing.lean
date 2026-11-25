-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.unram_locRing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:56.885504+00:00
-- url     : https://prove2.me/submissions/1ff7f488-cc4d-422f-834e-0bce1be0398a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_conjO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_conjO_conjO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_hcompl_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_mem_locRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isUnitIn_div_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_conjO_conjO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_exists_sub_conjO_notMem


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ θ ∈ locRing p, IsUnitIn (locRing p) (θ - star θ) := by
  obtain ⟨θ, hθ⟩ := ReciprocityTheory.ChartRestriction.L3.exists_sub_conjO_notMem hK hp
  have hpr := hp.isPrime
  have hx : θ - conjO K θ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hpr, mem_conjIdeal_iff]
    refine ⟨hθ, ?_⟩
    rw [map_sub, ReciprocityTheory.ChartRestriction.L3.conjO_conjO]
    intro h
    exact hθ (by rw [← neg_sub]; exact neg_mem h)
  refine ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_locRing p θ, ?_⟩
  have hu := (isUnitIn_div_iff hpr (θ - conjO K θ) (one_mem _)).2 hx
  rwa [map_one, div_one, map_sub, algebraMap_conjO] at hu
end ReciprocityTheory.ChartRestriction.L3.WA
