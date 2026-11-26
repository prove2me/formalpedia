-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_orderedBases_fin_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:02.146892+00:00
-- url     : https://prove2.me/submissions/cfd387ad-26aa-440b-ab03-cd4e72c1fdaa

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_linearIndependentFrames

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p r : ℕ) [Fact p.Prime] :
    Nat.card (LinearIndependentFrames (ZMod p) (Fin r → ZMod p) r) =
      frameProd p r r := by
  simpa using
    (card_linearIndependentFrames
      (K := ZMod p) (V := Fin r → ZMod p) (k := r) (by simp))
end SharpIntermediateSubgroupBounds
