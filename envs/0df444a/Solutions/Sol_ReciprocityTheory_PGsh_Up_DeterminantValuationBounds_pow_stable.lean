-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.pow_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:23.531059+00:00
-- url     : https://prove2.me/submissions/7613474d-4995-4648-966c-2dacdcc239c3

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}
variable {n s : ℕ}
namespace ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
theorem _root_.solution {a : Fin n → C} {M : Lat v (Fin n × Fin s)} (hM : IsLaStable a M) (k : ℕ)
    {w : Fin n × Fin s → C} (hw : w ∈ M.pts) :
    (fun y : Fin n × Fin s => a y.1 ^ k * w y) ∈ M.pts := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    have e : (fun y : Fin n × Fin s => a y.1 ^ (k + 1) * w y) =
        fun y => a y.1 * (a y.1 ^ k * w y) := by
      funext y
      ring
    rw [e]
    exact hM _ ih
end ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
