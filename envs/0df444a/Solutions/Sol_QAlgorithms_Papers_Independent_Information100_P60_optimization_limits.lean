-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.optimization_limits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:35:02.128833+00:00
-- url     : https://prove2.me/submissions/73a31f62-9995-4995-86c3-607ab50f507d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

end QAlgorithms.Papers.Independent.Information100.P60

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P60 in
theorem solution {Y : Type*} [Nonempty Y] (f : Y → ℕ → ℝ) :
    (⨆ y, liminf (fun n => (f y n : EReal)) atTop) ≤
      liminf (fun n => ⨆ y, (f y n : EReal)) atTop ∧
    (⨆ y, limsup (fun n => (f y n : EReal)) atTop) ≤
      limsup (fun n => ⨆ y, (f y n : EReal)) atTop := by
  constructor
  · exact iSup_le fun y => liminf_le_liminf (Eventually.of_forall fun n =>
      le_iSup (fun y => (f y n : EReal)) y)
  · exact iSup_le fun y => limsup_le_limsup (Eventually.of_forall fun n =>
      le_iSup (fun y => (f y n : EReal)) y)

end
