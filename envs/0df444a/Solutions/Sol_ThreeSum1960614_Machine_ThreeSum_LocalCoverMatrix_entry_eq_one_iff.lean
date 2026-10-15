-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:13:48.617447+00:00
-- url     : https://prove2.me/submissions/1186e610-52cf-4407-b137-560fc1783a02

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalMaskHashes_indexed_bucket_count
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightTrimTest
end ThreeSum.LightTrimTest
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalCoverMatrix
end ThreeSum.LocalCoverMatrix
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.LocalMaskHashes
end ThreeSum.LocalMaskHashes
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightTrimTest
end ThreeSum1960614.Machine.ThreeSum.LightTrimTest
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
end ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : _root_.ThreeSum.LightResidues.residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp] at h
  exact_mod_cast h















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The exact local retained-edge test -/

namespace ThreeSum.LightTrimTest
open _root_.ThreeSum.LightTrimTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





theorem flag_eq_one (overlap leftCount rightCount cap : ℕ) :
    _root_.ThreeSum.LightTrimTest.flag overlap leftCount rightCount cap=1 ↔ overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap := by
  unfold _root_.ThreeSum.LightTrimTest.flag
  split <;> simp_all





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightTrimTest

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph
open _root_.ThreeSum.LocalGraph


variable {α : Type*} [DecidableEq α]





theorem leftWord_injective : Function.Injective (@_root_.ThreeSum.LocalGraph.leftWord α _) := by
  intro s t he
  ext i
  simpa only [_root_.ThreeSum.LocalGraph.leftWord, decide_eq_decide] using congrFun he i

theorem rightWord_injective : Function.Injective (@_root_.ThreeSum.LocalGraph.rightWord α _) := by
  intro s t he
  ext i
  have hi := congrFun he i
  simpa only [_root_.ThreeSum.LocalGraph.rightWord, decide_eq_decide, not_iff_not] using hi









section ConcreteGraph

open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts



variable {L h : ℕ}

















































end ConcreteGraph

end ThreeSum.LocalGraph

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase
open _root_.ThreeSum.MaskErase


open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress









theorem natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.SubsetAddress.natPositions (s.erase a) = (_root_.ThreeSum.SubsetAddress.natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a

theorem eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) = _root_.ThreeSum.SubsetAddress.subsetMask (s.erase a) := by
  rw [_root_.ThreeSum.SubsetAddress.subsetMask, _root_.ThreeSum.MaskErase.eraseMask_maskOf _ (_root_.ThreeSum.SubsetAddress.natPositions_subset s),
    ← _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.natPositions_erase, ← _root_.ThreeSum.SubsetAddress.subsetMask]

theorem eraseMask_ne_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) ≠ _root_.ThreeSum.SubsetAddress.subsetMask s ↔ a ∈ s := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_subsetMask, (_root_.ThreeSum.SubsetAddress.subsetMask_injective L).ne_iff, Finset.erase_ne_self]





end ThreeSum.MaskErase

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits
open _root_.ThreeSum.LightMaskBits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase





theorem bit_subsetMask {L : ℕ} (s : Finset (Fin L)) (j : Fin L) :
    _root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.SubsetAddress.subsetMask s) j.val = if j ∈ s then 1 else 0 := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff s j
  unfold _root_.ThreeSum.LightMaskBits.bit
  split <;> split <;> simp_all











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightMaskBits

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram
open _root_.ThreeSum.LightResidueHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by
  unfold _root_.ThreeSum.LightResidues.residue
  rw [ZMod.natCast_toNat p (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]

























end ThreeSum.LightResidueHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalHashMoments


open _root_.Finset
open scoped _root_.BigOperators

open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}













































theorem cover_has_edge {B : ℕ} {w : _root_.ThreeSum.LocalHashMoments.Weight L K} {target : K × K}
    (hc : _root_.ThreeSum.LocalHashMoments.Covers L h B w target) :
    ∃ e : _root_.ThreeSum.LocalGraph.Edge L h, _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.left e) = target.1 ∧
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.right e) = target.2 ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices L h) w target.1 ≤ B ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices L h) w target.2 ≤ B := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  have ht := (Finset.mem_filter.mp he).2
  have hp := (Finset.mem_filter.mp ht).1
  have hl := (Finset.mem_filter.mp ht).2
  exact ⟨e, (Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2, hl⟩

/-! ## The selected local prime and its actual finite schedule -/





















end ThreeSum.LocalHashMoments

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments


























theorem rawHash_cast {h L : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Fin L → Bool) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w s : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) = _root_.ThreeSum.HashFamily.hashValue w s := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash, _root_.ThreeSum.HashFamily.hashValue]

































































end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalMaskGraph


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode
open scoped _root_.BigOperators







theorem maskAt_spec {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.IsMask L h (_root_.ThreeSum.LocalMaskGraph.maskAt L h i) := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h _).mp (_root_.ThreeSum.LocalMaskGraph.maskAt_mem hi)



theorem subsetMask_setAt {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.LocalMaskGraph.setAt L h i) = _root_.ThreeSum.LocalMaskGraph.maskAt L h i := _root_.ThreeSum.MaskDecode.subsetMask_decode (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_spec hi).1





theorem setAt_complete {L h : ℕ} (s : Finset (Fin L)) (hs : s.card=h) :
    ∃ i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h, _root_.ThreeSum.LocalMaskGraph.setAt L h i=s := by
  have hm : _root_.ThreeSum.SubsetAddress.subsetMask s ∈ _root_.ThreeSum.SubsetAddress.enumerateLayer L h := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h _).mpr (by
    simpa only [hs] using _root_.ThreeSum.SubsetAddress.subsetMask_isMask s)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,by simpa [_root_.ThreeSum.LocalMaskGraph.vertexCount,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] using hi,?_⟩
  unfold _root_.ThreeSum.LocalMaskGraph.setAt _root_.ThreeSum.LocalMaskGraph.maskAt
  rw [List.getD_eq_getElem _ _ hi,he,_root_.ThreeSum.MaskDecode.decode_subsetMask]

theorem dot_bits {L : ℕ} (s t : Finset (Fin L)) :
    _root_.ThreeSum.LightBooleanDot.dot (_root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.SubsetAddress.subsetMask s))
      (_root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.SubsetAddress.subsetMask t)) L = (s ∩ t).card := by
  unfold _root_.ThreeSum.LightBooleanDot.dot
  rw [← Fin.sum_univ_eq_sum_range]
  have he : (s ∩ t) = (univ : Finset (Fin L)).filter (fun i => i ∈ s ∧ i ∈ t) := by
    ext i
    simp
  rw [he,Finset.card_filter]
  apply sum_congr rfl
  intro i hi
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.bit_subsetMask s i,_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.bit_subsetMask t i]
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs,ht]

theorem dot_zero_iff {L : ℕ} (s t : Finset (Fin L)) :
    _root_.ThreeSum.LightBooleanDot.dot (_root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.SubsetAddress.subsetMask s))
      (_root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.SubsetAddress.subsetMask t)) L = 0 ↔ Disjoint s t := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.dot_bits,Finset.card_eq_zero]
  exact Finset.disjoint_iff_inter_eq_empty.symm

theorem indexed_dot_zero_iff {L h i j : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) (hj : j < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.LightBooleanDot.dot (_root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.LocalMaskGraph.maskAt L h i))
      (_root_.ThreeSum.LightMaskBits.bit L (_root_.ThreeSum.LocalMaskGraph.maskAt L h j)) L = 0 ↔ Disjoint (_root_.ThreeSum.LocalMaskGraph.setAt L h i) (_root_.ThreeSum.LocalMaskGraph.setAt L h j) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hi,← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hj]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.dot_zero_iff _ _



end ThreeSum.LocalMaskGraph

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask
open _root_.ThreeSum.OneHotMask


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    _root_.ThreeSum.OneHotMask.extend f i.val = f i := by simp [_root_.ThreeSum.OneHotMask.extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ _root_.ThreeSum.SubsetAddress.natPositions s ↔ i ∈ s := by
  simp only [_root_.ThreeSum.SubsetAddress.natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    _root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend w0) (_root_.ThreeSum.OneHotMask.extend w1) L (_root_.ThreeSum.SubsetAddress.subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [_root_.ThreeSum.SubsetAddress.subsetMask, _root_.ThreeSum.OneHotMask.eval_maskOf _ (_root_.ThreeSum.SubsetAddress.natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin, _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.mem_natPositions]

theorem eval_rawLeft {h L : ℕ}
    (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Finset (Fin L)) :
    (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,false)).val) (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,true)).val)
      L (_root_.ThreeSum.SubsetAddress.subsetMask s) : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.leftWord s) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_subsetMask]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [_root_.ThreeSum.LocalGraph.leftWord, hi]

theorem eval_rawRight {h L : ℕ}
    (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Finset (Fin L)) :
    (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,true)).val) (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,false)).val)
      L (_root_.ThreeSum.SubsetAddress.subsetMask s) : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.rightWord s) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_subsetMask]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [_root_.ThreeSum.LocalGraph.rightWord, hi]

end ThreeSum.OneHotMask

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes
open _root_.ThreeSum.LocalMaskHashes


open _root_.Finset
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {h L k : ℕ}









theorem leftCode_lt (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k i : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k i < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode _root_.ThreeSum.LightHashHistogram.code
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) 1 _

theorem rightCode_lt (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k i : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k i < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode _root_.ThreeSum.LightHashHistogram.code
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) 1 _

theorem leftCode_cast (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {i : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k i : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) =
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.LocalMaskGraph.setAt L k i)) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode _root_.ThreeSum.LightHashHistogram.code _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h),one_mul,
    ← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hi,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_rawLeft,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast]

theorem rightCode_cast (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {i : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k i : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) =
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.LocalMaskGraph.setAt L k i)) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode _root_.ThreeSum.LightHashHistogram.code _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h),one_mul,
    ← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt hi,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_rawRight,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast]

theorem leftCode_val (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {i : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k i = (_root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.LocalMaskGraph.setAt L k i))).val := by
  have he := congrArg ZMod.val (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_cast w hi)
  simpa only [ZMod.val_natCast_of_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_lt w k i)] using he

theorem rightCode_val (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {i : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k i = (_root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.LocalMaskGraph.setAt L k i))).val := by
  have he := congrArg ZMod.val (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_cast w hi)
  simpa only [ZMod.val_natCast_of_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_lt w k i)] using he



theorem left_count (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k) r (_root_.ThreeSum.LocalMaskGraph.vertexCount L k) =
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices L k) w (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count w _root_.ThreeSum.LocalGraph.leftWord _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph.leftWord_injective
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k) (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_lt w k i) (fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_cast w hi) hr

theorem right_count (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {r : ℕ} (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k) r (_root_.ThreeSum.LocalMaskGraph.vertexCount L k) =
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices L k) w (r : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.indexed_bucket_count w _root_.ThreeSum.LocalGraph.rightWord _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph.rightWord_injective
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k) (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_lt w k i) (fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_cast w hi) hr

end ThreeSum.LocalMaskHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix
open _root_.ThreeSum.LocalCoverMatrix


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes

variable {h L k : ℕ}










theorem radix_div {p a b : ℕ} (hb : b < p) : (a*p+b)/p=a := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb]
  omega

theorem radix_mod {p a b : ℕ} (hb : b < p) : (a*p+b)%p=b := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]

theorem radix_injective {p a b c e : ℕ} (hb : b < p) (he : e < p)
    (hh : a*p+b=c*p+e) : a=c ∧ b=e := by
  exact ⟨by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_div hb,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_div he] using congrArg (fun j => j/p) hh,
    by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_mod hb,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_mod he] using congrArg (fun j => j%p) hh⟩

theorem covers_iff_edge (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k B : ℕ)
    (a b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :
    _root_.ThreeSum.LocalHashMoments.Covers L k B w (a,b) ↔ ∃ e : _root_.ThreeSum.LocalGraph.Edge L k,
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.left e)=a ∧
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.right e)=b ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices L k) w a ≤ B ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices L k) w b ≤ B := by
  constructor
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.cover_has_edge
  · rintro ⟨e,ha,hb,hleft,hright⟩
    apply Nat.ne_of_gt
    apply Finset.card_pos.mpr
    refine ⟨e,?_⟩
    simp only [_root_.ThreeSum.HashFamily.trimmedPairEvent,
      _root_.ThreeSum.HashFamily.pairEvent,mem_filter,mem_univ,true_and]
    exact ⟨⟨ha,hb⟩,hleft,hright⟩

theorem valid_iff (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {B i : ℕ}
    (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L k*_root_.ThreeSum.LocalMaskGraph.vertexCount L k) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.valid w k B i=1 ↔
      Disjoint (_root_.ThreeSum.LocalMaskGraph.setAt L k (i/_root_.ThreeSum.LocalMaskGraph.vertexCount L k))
        (_root_.ThreeSum.LocalMaskGraph.setAt L k (i%_root_.ThreeSum.LocalMaskGraph.vertexCount L k)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.leftCount w k (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k (i/_root_.ThreeSum.LocalMaskGraph.vertexCount L k)) ≤ B ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.rightCount w k (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k (i%_root_.ThreeSum.LocalMaskGraph.vertexCount L k)) ≤ B := by
  have hn : 0 < _root_.ThreeSum.LocalMaskGraph.vertexCount L k := by nlinarith
  have hq : i/_root_.ThreeSum.LocalMaskGraph.vertexCount L k < _root_.ThreeSum.LocalMaskGraph.vertexCount L k :=
    (Nat.div_lt_iff_lt_mul hn).mpr hi
  have hr := Nat.mod_lt i hn
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.valid _root_.ThreeSum.LightPairFlags.pairFlag _root_.ThreeSum.LocalCoverMatrix.bits
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest.flag_eq_one,_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.indexed_dot_zero_iff hq hr]



end ThreeSum.LocalCoverMatrix

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LocalCoverMatrix
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix

open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
variable {h L k : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry_eq_one_iff__implementation_52f5accc01 (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) {B a b : ℕ}
    (ha : a < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (hb : b < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry w k B (a*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+b)=1 ↔
      _root_.ThreeSum.LocalHashMoments.Covers L k B w ((a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h),(b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) := by
  have hbit : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry w k B (a*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+b)=1 ↔
      _root_.ThreeSum.LightSupportMark.Hit (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.key w k) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.valid w k B) (a*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+b)
        (_root_.ThreeSum.LocalMaskGraph.vertexCount L k*_root_.ThreeSum.LocalMaskGraph.vertexCount L k) := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry _root_.ThreeSum.LightSupportMark.bit
    split <;> simp_all
  rw [hbit,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.covers_iff_edge]
  constructor
  · rintro ⟨i,hi,hvalid,hkey⟩
    have hi' := mem_range.mp hi
    have hn : 0 < _root_.ThreeSum.LocalMaskGraph.vertexCount L k := by nlinarith
    have hq : i/_root_.ThreeSum.LocalMaskGraph.vertexCount L k < _root_.ThreeSum.LocalMaskGraph.vertexCount L k :=
      (Nat.div_lt_iff_lt_mul hn).mpr hi'
    have hr := Nat.mod_lt i hn
    obtain ⟨hdisj,hleft,hright⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.valid_iff w hi').mp hvalid
    obtain ⟨hca,hcb⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_injective (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_lt w k _) hb hkey
    let e : _root_.ThreeSum.LocalGraph.Edge L k :=
      ⟨(_root_.ThreeSum.LocalMaskGraph.setAt L k (i/_root_.ThreeSum.LocalMaskGraph.vertexCount L k),
        _root_.ThreeSum.LocalMaskGraph.setAt L k (i%_root_.ThreeSum.LocalMaskGraph.vertexCount L k)),
        _root_.ThreeSum.LayerCounts.mem_edgeSet.mpr ⟨_root_.ThreeSum.LocalMaskGraph.setAt_card hq,_root_.ThreeSum.LocalMaskGraph.setAt_card hr,hdisj⟩⟩
    refine ⟨e,?_,?_,?_,?_⟩
    · exact (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_cast w hq).symm.trans (congrArg (fun n : ℕ => (n : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) hca)
    · exact (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_cast w hr).symm.trans (congrArg (fun n : ℕ => (n : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) hcb)
    · change _root_.ThreeSum.LightHistogram.count _ _ _ ≤ B at hleft
      rw [hca,_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.left_count w ha] at hleft
      exact hleft
    · change _root_.ThreeSum.LightHistogram.count _ _ _ ≤ B at hright
      rw [hcb,_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.right_count w hb] at hright
      exact hright
  · rintro ⟨e,hleftHash,hrightHash,hleft,hright⟩
    obtain ⟨i,hi,hei⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.setAt_complete e.val.1 (_root_.ThreeSum.LocalGraph.edge_data e).1
    obtain ⟨j,hj,hej⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.setAt_complete e.val.2 (_root_.ThreeSum.LocalGraph.edge_data e).2.1
    have hn : 0 < _root_.ThreeSum.LocalMaskGraph.vertexCount L k := by omega
    have hidx : i*_root_.ThreeSum.LocalMaskGraph.vertexCount L k+j <
        _root_.ThreeSum.LocalMaskGraph.vertexCount L k*_root_.ThreeSum.LocalMaskGraph.vertexCount L k := by nlinarith
    have hq := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_div hj (a := i)
    have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.radix_mod hj (a := i)
    have hca : _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode w k i=a := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.leftCode_val w hi,hei]
      change (_root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.left e)).val=a
      rw [hleftHash,ZMod.val_natCast_of_lt ha]
    have hcb : _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode w k j=b := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.rightCode_val w hj,hej]
      change (_root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.right e)).val=b
      rw [hrightHash,ZMod.val_natCast_of_lt hb]
    refine ⟨i*_root_.ThreeSum.LocalMaskGraph.vertexCount L k+j,mem_range.mpr hidx,?_,?_⟩
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.valid_iff w hidx,hq,hr,hei,hej,hca,hcb]
      refine ⟨(_root_.ThreeSum.LocalGraph.edge_data e).2.2,?_,?_⟩
      · simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.leftCount,_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.left_count w ha] using hleft
      · simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.rightCount,_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.right_count w hb] using hright
    · unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.key _root_.ThreeSum.LightPairFlags.pairKey
      rw [hq,hr,hca,hcb]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry_eq_one_iff__implementation_52f5accc01) := (@ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry_eq_one_iff__implementation_52f5accc01)

#print axioms solution
