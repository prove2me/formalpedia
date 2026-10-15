-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:11:48.683983+00:00
-- url     : https://prove2.me/submissions/c50b406a-26a2-4dc6-b2ea-ab132df84f1f

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_partitionWord_length

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Reporting
end ThreeSum.Reporting
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.Reporting
end ThreeSum1960614.Machine.ThreeSum.Reporting
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting

namespace ThreeSum1960614.Machine

/-!
# Executable positive-prefix reporting

The routine enumerates children of the current positive frontier and discards
zero counts. Its correctness interface asks for exact natural prefix counts;
the subset-transform identities supply those counts in the application.
No bound on the cost of obtaining a count is assumed or proved here.
-/

namespace ThreeSum.Reporting
open _root_.ThreeSum.Reporting


open _root_.Finset
open scoped _root_.BigOperators

variable {ι α : Type*} [DecidableEq α]



theorem mass_pos_iff (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) :
    0 < _root_.ThreeSum.Reporting.mass I word weight k pre ↔
      ∃ i ∈ I, (word i).take k = pre ∧ 0 < weight i := by
  unfold _root_.ThreeSum.Reporting.mass _root_.ThreeSum.Subset.fiberMass
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hpre⟩, hw⟩
    exact ⟨i, hi, hpre, hw⟩
  · rintro ⟨i, hi, hpre, hw⟩
    exact ⟨i, ⟨hi, hpre⟩, hw⟩













end ThreeSum.Reporting

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting
open _root_.ThreeSum.StoredReporting


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced





theorem prefixRows_take {J L k : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J)
    (hi : i.val < k) : _root_.ThreeSum.StoredReporting.prefixRows ((List.ofFn u).take k) i = u i := by
  simp only [_root_.ThreeSum.StoredReporting.prefixRows, List.getElem?_take_of_lt hi, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]









section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]























end Indices

end ThreeSum.StoredReporting

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting

set_option maxRecDepth 8000
open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid__implementation_8a232d8606 {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464 * h)))) (hk : k ≤ J)
    (hp : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w k pre) : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre := by
  obtain ⟨r, hr, hpre, _⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.Reporting.mass_pos_iff (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w) _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word (fun _ => 1) k pre).mp hp
  have hw := (Finset.mem_filter.mp hr).2
  have hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput r.2.1 = w.2.2 := congrArg (fun w => w.2.2) hw
  constructor
  · rw [← hpre, List.length_take, _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word, _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord_length, Nat.min_eq_left hk]
  · intro i hi
    have hrows : _root_.ThreeSum.StoredReporting.prefixRows pre i = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (r.2.1 i)).val.1 := by
      rw [← hpre]
      exact _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.prefixRows_take (fun j => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (r.2.1 j)).val.1) i hi
    rw [hrows]
    refine ⟨?_, (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (r.2.1 i))).1⟩
    have he : _root_.ThreeSum.LocalGraph.output (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (r.2.1 i)) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2 i :=
      congrArg (fun q => (q i).2.val) hq
    rw [← he]
    exact Finset.subset_union_left
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid__implementation_8a232d8606.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid__implementation_8a232d8606.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
