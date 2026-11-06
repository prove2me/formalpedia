-- Prove2me | solution 1 for QEC.Locality.bgklDecayRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:13:12.872981+00:00
-- url     : https://prove2.me/submissions/6c149b97-d77e-428d-a472-41b643adea70

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution {exponent : ℝ} (hexponent : 0 < exponent) :
    bgklDecayRatio exponent < 1 := by
  rw [bgklDecayRatio, ← Real.one_rpow exponent]
  exact Real.rpow_lt_rpow (by norm_num) (by norm_num) hexponent
end QEC.Locality
