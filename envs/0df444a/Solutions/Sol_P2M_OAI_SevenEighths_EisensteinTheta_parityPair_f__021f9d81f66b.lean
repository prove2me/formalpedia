-- Prove2me | solution 1 for P2M_OAI_SevenEighths_EisensteinTheta_parityPair_f__021f9d81f66b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:23.920367+00:00
-- url     : https://prove2.me/submissions/b77efbd5-3312-43f2-8bca-194f192e5cc6

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.EisensteinTheta
open ThetaProduct
namespace OAI.SevenEighths.EisensteinTheta
theorem _root_.solution (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).f₀ =
      (if (xShift a b L e : UnitAddCircle) = 0 then 1 else 0) *
      (if (yShift b L e : UnitAddCircle) = 0 then 1 else 0) := rfl
end OAI.SevenEighths.EisensteinTheta
