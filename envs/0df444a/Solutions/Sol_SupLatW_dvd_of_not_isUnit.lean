-- Prove2me | solution 1 for SupLatW.dvd_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:57.236282+00:00
-- url     : https://prove2.me/submissions/3c18890d-8303-4df1-bc39-246f7b03cab8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SupLatW
open Formalism.MainNotions.Ext.CutC
namespace SupLatW
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {s : R} (hs : ¬ IsUnit s) : ϖ ∣ s := by
  have hm : s ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal s).mpr (mem_nonunits_iff.mpr hs)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hm
  exact hm
end SupLatW
