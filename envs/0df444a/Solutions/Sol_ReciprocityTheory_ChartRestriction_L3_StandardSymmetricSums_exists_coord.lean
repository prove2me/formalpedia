-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:18.500908+00:00
-- url     : https://prove2.me/submissions/64c9994f-7f14-493c-b3ec-7bd1ccb9ed3b

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums
namespace ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums
theorem _root_.solution {n : ℕ} {e : Fin n → V} (hsp : Submodule.span K (Set.range e) = ⊤) (x : V) :
    ∃ c : Fin n → K, ∑ i, c i • e i = x :=
  (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ Submodule.mem_top)
end ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums
