-- Prove2me | solution 1 for ThreeSum.LocalCoverMatrix.entry_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:37:42.775295+00:00
-- url     : https://prove2.me/submissions/86f65666-4bf1-4bbf-bf13-18036197e9d8

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LocalMaskHashes_indexed_bucket_count
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
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
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph

variable {α : Type*} [DecidableEq α]





theorem leftWord_injective : Function.Injective (@leftWord α _) := by
  intro s t he
  ext i
  simpa only [leftWord, decide_eq_decide] using congrFun he i

theorem rightWord_injective : Function.Injective (@rightWord α _) := by
  intro s t he
  ext i
  have hi := congrFun he i
  simpa only [rightWord, decide_eq_decide, not_iff_not] using hi









































section ConcreteGraph

open LayerCounts




variable {L h : ℕ}






















































































































end ConcreteGraph

end ThreeSum.LocalGraph

end

section


/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments

open Finset
open scoped BigOperators

open LocalGraph LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}


































































































































































































































theorem cover_has_edge {B : ℕ} {w : Weight L K} {target : K × K}
    (hc : Covers L h B w target) :
    ∃ e : Edge L h, HashFamily.hashValue w (left e) = target.1 ∧
      HashFamily.hashValue w (right e) = target.2 ∧
      HashFamily.bucketSize (leftVertices L h) w target.1 ≤ B ∧
      HashFamily.bucketSize (rightVertices L h) w target.2 ≤ B := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  have ht := (Finset.mem_filter.mp he).2
  have hp := (Finset.mem_filter.mp ht).1
  have hl := (Finset.mem_filter.mp ht).2
  exact ⟨e, (Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2, hl⟩

/-! ## The selected local prime and its actual finite schedule -/




































































end ThreeSum.LocalHashMoments

end

section


/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments














































theorem rawHash_cast {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (rawHash w s : LocalField h) = HashFamily.hashValue w s := by
  simp [rawHash, HashFamily.hashValue]











































































































































































































































end ThreeSum.GlobalEncoding

end

section


/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase

open Finset
open scoped BigOperators
open SubsetAddress





























































theorem natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    natPositions (s.erase a) = (natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a

theorem eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) = subsetMask (s.erase a) := by
  rw [subsetMask, eraseMask_maskOf _ (natPositions_subset s),
    ← natPositions_erase, ← subsetMask]

theorem eraseMask_ne_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) ≠ subsetMask s ↔ a ∈ s := by
  rw [eraseMask_subsetMask, (subsetMask_injective L).ne_iff, Finset.erase_ne_self]












end ThreeSum.MaskErase

end

section


/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase





theorem bit_subsetMask {L : ℕ} (s : Finset (Fin L)) (j : Fin L) :
    bit L (SubsetAddress.subsetMask s) j.val = if j ∈ s then 1 else 0 := by
  have h := eraseMask_ne_iff s j
  unfold bit
  split <;> split <;> simp_all





















variable {lim : Limits} {P : Program} {d : ℕ}


























































































end ThreeSum.LightMaskBits

end

section


/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← residue_cast hp] at h
  exact_mod_cast h







































































































end ThreeSum.LightResidues

end

section


/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram

open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba

variable {lim : Limits} {P : Program} {d : ℕ}



















theorem residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by
  unfold residue
  rw [ZMod.natCast_toNat p (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]









































































































































end ThreeSum.LightResidueHistogram

end

section


/-! # The exact local retained-edge test -/

namespace ThreeSum.LightTrimTest

open Light








theorem flag_eq_one (overlap leftCount rightCount cap : ℕ) :
    flag overlap leftCount rightCount cap=1 ↔ overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap := by
  unfold flag
  split <;> simp_all










variable {lim : Limits} {P : Program} {d : ℕ}



























end ThreeSum.LightTrimTest

end

section


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators












theorem maskAt_spec {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)




theorem subsetMask_setAt {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := subsetMask_decode (maskAt_spec hi).1












theorem setAt_complete {L h : ℕ} (s : Finset (Fin L)) (hs : s.card=h) :
    ∃ i < vertexCount L h, setAt L h i=s := by
  have hm : subsetMask s ∈ enumerateLayer L h := (mem_enumerateLayer L h _).mpr (by
    simpa only [hs] using subsetMask_isMask s)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,by simpa [vertexCount,enumerateLayer_length] using hi,?_⟩
  unfold setAt maskAt
  rw [List.getD_eq_getElem _ _ hi,he,decode_subsetMask]

theorem dot_bits {L : ℕ} (s t : Finset (Fin L)) :
    LightBooleanDot.dot (LightMaskBits.bit L (subsetMask s))
      (LightMaskBits.bit L (subsetMask t)) L = (s ∩ t).card := by
  unfold LightBooleanDot.dot
  rw [← Fin.sum_univ_eq_sum_range]
  have he : (s ∩ t) = (univ : Finset (Fin L)).filter (fun i => i ∈ s ∧ i ∈ t) := by
    ext i
    simp
  rw [he,Finset.card_filter]
  apply sum_congr rfl
  intro i hi
  rw [LightMaskBits.bit_subsetMask s i,LightMaskBits.bit_subsetMask t i]
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs,ht]

theorem dot_zero_iff {L : ℕ} (s t : Finset (Fin L)) :
    LightBooleanDot.dot (LightMaskBits.bit L (subsetMask s))
      (LightMaskBits.bit L (subsetMask t)) L = 0 ↔ Disjoint s t := by
  rw [dot_bits,Finset.card_eq_zero]
  exact Finset.disjoint_iff_inter_eq_empty.symm

theorem indexed_dot_zero_iff {L h i j : ℕ}
    (hi : i < vertexCount L h) (hj : j < vertexCount L h) :
    LightBooleanDot.dot (LightMaskBits.bit L (maskAt L h i))
      (LightMaskBits.bit L (maskAt L h j)) L = 0 ↔ Disjoint (setAt L h i) (setAt L h j) := by
  rw [← subsetMask_setAt hi,← subsetMask_setAt hj]
  exact dot_zero_iff _ _









end ThreeSum.LocalMaskGraph

end

section


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

























































@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ natPositions s ↔ i ∈ s := by
  simp only [natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    eval (extend w0) (extend w1) L (subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [subsetMask, eval_maskOf _ (natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [extend_fin, mem_natPositions]

theorem eval_rawLeft {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,false)).val) (extend fun i => (w (i,true)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.leftWord s) := by
  rw [eval_subsetMask]
  unfold GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [LocalGraph.leftWord, hi]

theorem eval_rawRight {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,true)).val) (extend fun i => (w (i,false)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.rightWord s) := by
  rw [eval_subsetMask]
  unfold GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [LocalGraph.rightWord, hi]

end ThreeSum.OneHotMask

end

section


/-!
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes

open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds

variable {h L k : ℕ}















theorem leftCode_lt (w : Weight L (LocalField h)) (k i : ℕ) :
    leftCode w k i < localPrime h := by
  unfold leftCode LightHashHistogram.code
  exact LightResidues.residue_lt (localPrime_pos h) 1 _

theorem rightCode_lt (w : Weight L (LocalField h)) (k i : ℕ) :
    rightCode w k i < localPrime h := by
  unfold rightCode LightHashHistogram.code
  exact LightResidues.residue_lt (localPrime_pos h) 1 _

theorem leftCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (leftCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i)) := by
  unfold leftCode LightHashHistogram.code coeff
  rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
    ← subsetMask_setAt hi,OneHotMask.eval_rawLeft,GlobalEncoding.rawHash_cast]

theorem rightCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (rightCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.rightWord (setAt L k i)) := by
  unfold rightCode LightHashHistogram.code coeff
  rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
    ← subsetMask_setAt hi,OneHotMask.eval_rawRight,GlobalEncoding.rawHash_cast]

theorem leftCode_val (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    leftCode w k i = (HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i))).val := by
  have he := congrArg ZMod.val (leftCode_cast w hi)
  simpa only [ZMod.val_natCast_of_lt (leftCode_lt w k i)] using he

theorem rightCode_val (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    rightCode w k i = (HashFamily.hashValue w (LocalGraph.rightWord (setAt L k i))).val := by
  have he := congrArg ZMod.val (rightCode_cast w hi)
  simpa only [ZMod.val_natCast_of_lt (rightCode_lt w k i)] using he

































theorem left_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.leftWord LocalGraph.leftWord_injective
    (leftCode w k) (fun i _ => leftCode_lt w k i) (fun _ hi => leftCode_cast w hi) hr

theorem right_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.rightWord LocalGraph.rightWord_injective
    (rightCode w k) (fun i _ => rightCode_lt w k i) (fun _ hi => rightCode_cast w hi) hr

end ThreeSum.LocalMaskHashes

end

section


/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix

open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes

variable {h L k : ℕ}




















theorem radix_div {p a b : ℕ} (hb : b < p) : (a*p+b)/p=a := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb]
  omega

theorem radix_mod {p a b : ℕ} (hb : b < p) : (a*p+b)%p=b := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]

theorem radix_injective {p a b c e : ℕ} (hb : b < p) (he : e < p)
    (hh : a*p+b=c*p+e) : a=c ∧ b=e := by
  exact ⟨by simpa only [radix_div hb,radix_div he] using congrArg (fun j => j/p) hh,
    by simpa only [radix_mod hb,radix_mod he] using congrArg (fun j => j%p) hh⟩

theorem covers_iff_edge (w : Weight L (LocalField h)) (k B : ℕ)
    (a b : LocalField h) :
    Covers L k B w (a,b) ↔ ∃ e : LocalGraph.Edge L k,
      HashFamily.hashValue w (LocalGraph.left e)=a ∧
      HashFamily.hashValue w (LocalGraph.right e)=b ∧
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w a ≤ B ∧
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w b ≤ B := by
  constructor
  · exact cover_has_edge
  · rintro ⟨e,ha,hb,hleft,hright⟩
    apply Nat.ne_of_gt
    apply Finset.card_pos.mpr
    refine ⟨e,?_⟩
    simp only [HashFamily.trimmedPairEvent,
      HashFamily.pairEvent,mem_filter,mem_univ,true_and]
    exact ⟨⟨ha,hb⟩,hleft,hright⟩

theorem valid_iff (w : Weight L (LocalField h)) {B i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k) :
    valid w k B i=1 ↔
      Disjoint (setAt L k (i/LocalMaskGraph.vertexCount L k))
        (setAt L k (i%LocalMaskGraph.vertexCount L k)) ∧
      leftCount w k (leftCode w k (i/LocalMaskGraph.vertexCount L k)) ≤ B ∧
      rightCount w k (rightCode w k (i%LocalMaskGraph.vertexCount L k)) ≤ B := by
  have hn : 0 < LocalMaskGraph.vertexCount L k := by nlinarith
  have hq : i/LocalMaskGraph.vertexCount L k < LocalMaskGraph.vertexCount L k :=
    (Nat.div_lt_iff_lt_mul hn).mpr hi
  have hr := Nat.mod_lt i hn
  unfold valid LightPairFlags.pairFlag bits
  rw [LightTrimTest.flag_eq_one,indexed_dot_zero_iff hq hr]

theorem entry_eq_one_iff_sourceProof (w : Weight L (LocalField h)) {B a b : ℕ}
    (ha : a < localPrime h) (hb : b < localPrime h) :
    entry w k B (a*localPrime h+b)=1 ↔
      Covers L k B w ((a : LocalField h),(b : LocalField h)) := by
  have hbit : entry w k B (a*localPrime h+b)=1 ↔
      LightSupportMark.Hit (key w k) (valid w k B) (a*localPrime h+b)
        (LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k) := by
    unfold entry LightSupportMark.bit
    split <;> simp_all
  rw [hbit,covers_iff_edge]
  constructor
  · rintro ⟨i,hi,hvalid,hkey⟩
    have hi' := mem_range.mp hi
    have hn : 0 < LocalMaskGraph.vertexCount L k := by nlinarith
    have hq : i/LocalMaskGraph.vertexCount L k < LocalMaskGraph.vertexCount L k :=
      (Nat.div_lt_iff_lt_mul hn).mpr hi'
    have hr := Nat.mod_lt i hn
    obtain ⟨hdisj,hleft,hright⟩ := (valid_iff w hi').mp hvalid
    obtain ⟨hca,hcb⟩ := radix_injective (rightCode_lt w k _) hb hkey
    let e : LocalGraph.Edge L k :=
      ⟨(setAt L k (i/LocalMaskGraph.vertexCount L k),
        setAt L k (i%LocalMaskGraph.vertexCount L k)),
        LayerCounts.mem_edgeSet.mpr ⟨setAt_card hq,setAt_card hr,hdisj⟩⟩
    refine ⟨e,?_,?_,?_,?_⟩
    · exact (leftCode_cast w hq).symm.trans (congrArg (fun n : ℕ => (n : LocalField h)) hca)
    · exact (rightCode_cast w hr).symm.trans (congrArg (fun n : ℕ => (n : LocalField h)) hcb)
    · change LightHistogram.count _ _ _ ≤ B at hleft
      rw [hca,left_count w ha] at hleft
      exact hleft
    · change LightHistogram.count _ _ _ ≤ B at hright
      rw [hcb,right_count w hb] at hright
      exact hright
  · rintro ⟨e,hleftHash,hrightHash,hleft,hright⟩
    obtain ⟨i,hi,hei⟩ := setAt_complete e.val.1 (LocalGraph.edge_data e).1
    obtain ⟨j,hj,hej⟩ := setAt_complete e.val.2 (LocalGraph.edge_data e).2.1
    have hn : 0 < LocalMaskGraph.vertexCount L k := by omega
    have hidx : i*LocalMaskGraph.vertexCount L k+j <
        LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k := by nlinarith
    have hq := radix_div hj (a := i)
    have hr := radix_mod hj (a := i)
    have hca : leftCode w k i=a := by
      rw [leftCode_val w hi,hei]
      change (HashFamily.hashValue w (LocalGraph.left e)).val=a
      rw [hleftHash,ZMod.val_natCast_of_lt ha]
    have hcb : rightCode w k j=b := by
      rw [rightCode_val w hj,hej]
      change (HashFamily.hashValue w (LocalGraph.right e)).val=b
      rw [hrightHash,ZMod.val_natCast_of_lt hb]
    refine ⟨i*LocalMaskGraph.vertexCount L k+j,mem_range.mpr hidx,?_,?_⟩
    · rw [valid_iff w hidx,hq,hr,hei,hej,hca,hcb]
      refine ⟨(LocalGraph.edge_data e).2.2,?_,?_⟩
      · simpa only [leftCount,left_count w ha] using hleft
      · simpa only [rightCount,right_count w hb] using hright
    · unfold key LightPairFlags.pairKey
      rw [hq,hr,hca,hcb]

end ThreeSum.LocalCoverMatrix

end


theorem solution : ∀ {h L k : Nat} (w : ThreeSum.LocalHashMoments.Weight.{0} L (ThreeSum.LocalHashMoments.LocalField h)) {B a b : Nat},
  @LT.lt.{0} Nat instLTNat a (ThreeSum.LocalCoverBounds.localPrime h) →
    @LT.lt.{0} Nat instLTNat b (ThreeSum.LocalCoverBounds.localPrime h) →
      Iff
        (@Eq.{1} Nat
          (@ThreeSum.LocalCoverMatrix.entry h L w k B
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
                (ThreeSum.LocalCoverBounds.localPrime h))
              b))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@ThreeSum.LocalHashMoments.Covers.{0} (ThreeSum.LocalHashMoments.LocalField h)
          (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h) (ThreeSum.LocalHashMoments.localPrimeFact h))
          (@ZMod.fintype (ThreeSum.LocalCoverBounds.localPrime h)
            (@NeZero.of_gt'.{0} Nat (ThreeSum.LocalCoverBounds.localPrime h)
              (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) Nat.instPreorder
              (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass.{0} Nat Nat.instLinearOrderedCommMonoidWithZero)
              Nat.instOne
              (@Nat.Prime.one_lt' (ThreeSum.LocalCoverBounds.localPrime h)
                (ThreeSum.LocalHashMoments.localPrimeFact h))))
          (ZMod.decidableEq (ThreeSum.LocalCoverBounds.localPrime h)) L k B w
          (@Prod.mk.{0, 0} (ThreeSum.LocalHashMoments.LocalField h) (ThreeSum.LocalHashMoments.LocalField h)
            (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
              (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                  (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                    (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                      (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                        (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                          (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
              a)
            (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
              (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                  (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                    (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                      (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                        (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                          (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
              b))) := by
  exact @ThreeSum.LocalCoverMatrix.entry_eq_one_iff_sourceProof

#print axioms solution
