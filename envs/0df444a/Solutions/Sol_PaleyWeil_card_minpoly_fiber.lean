-- Prove2me | solution 1 for PaleyWeil.card_minpoly_fiber
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:30:25.448336+00:00
-- url     : https://prove2.me/submissions/e528c49d-877e-48a4-bcc2-35920edbd0c9

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil

theorem solution {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L] (x : L) :
    (Finset.univ.filter (fun y : L ↦ minpoly K y = minpoly K x)).card =
      (minpoly K x).natDegree := by
  classical
  let P := minpoly K x
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  have hmonic : P.Monic := minpoly.monic hx
  have hirr : Irreducible P := minpoly.irreducible hx
  have hmap0 : P.map (algebraMap K L) ≠ 0 := (hmonic.map _).ne_zero
  have hsplits : (P.map (algebraMap K L)).Splits :=
    (inferInstance : Normal K L).splits x
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K x
  have hnodup : (P.map (algebraMap K L)).roots.Nodup := Polynomial.nodup_roots hsep.map
  have hfiber :
      Finset.univ.filter (fun y : L ↦ minpoly K y = P) =
        (P.map (algebraMap K L)).roots.toFinset := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      Polynomial.mem_roots hmap0, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    constructor
    · intro h
      rw [← h]
      exact minpoly.aeval K y
    · intro h
      exact (minpoly.eq_of_irreducible_of_monic hirr h hmonic).symm
  rw [hfiber, Multiset.toFinset_card_of_nodup hnodup,
    splits_iff_card_roots.mp hsplits, Polynomial.natDegree_map]
