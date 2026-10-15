-- Prove2me | solution 1 for ThreeSum.ThreeSumWantedHostDecision.accepted_iff_witness
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:28:38.790551+00:00
-- url     : https://prove2.me/submissions/717c19c5-c43e-46ee-a86e-f5f590575b1d

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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle18
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_Arithmetic_small_lift_exists
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_BandRawA_product_values_mem
import Theorems.Thm_ThreeSum_BandRawA_relevant_product_complete
import Theorems.Thm_ThreeSum_Cover_greedy_cover
import Theorems.Thm_ThreeSum_DenseGuardWanted_pair_indices_injective
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul
import Theorems.Thm_ThreeSum_LocalHashMoments_cover_frequency
import Theorems.Thm_ThreeSum_Radix_mem_representations
import Theorems.Thm_ThreeSum_RawIncidences_dense_early_yes
import Theorems.Thm_ThreeSum_ReportingHostFrontier_mem_frontier_iff
import Theorems.Thm_ThreeSum_ReportingHostTerminalBatch_hit_of_compatible
import Theorems.Thm_ThreeSum_StoredReporting_positivePrefix_valid
import Theorems.Thm_ThreeSum_ThreeSumWantedHostConditions_actual_separation
import Theorems.Thm_ThreeSum_WantedRecordCoverage_output_complete
import Theorems.Thm_ThreeSum_WantedRecordOrder_label_injective


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostBlockBucketTest
end ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostTerminalBatch
end ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedPrefix
end ThreeSum.ReportingHostWantedPrefix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder

section


/-!
# The quadratic cardinal bound for relevant sorted-band triples

The proof is an explicit injection.  A relevant A interval either contains
the lower endpoint of a B/C difference interval, or its own lower endpoint
cuts that rectangle.  For a fixed cut, interval intersections inject into
the endpoints of the two families.

This file proves the combinatorial output bound and solution coverage.
It does not assign that bound to a cubic filtering implementation.
-/

namespace ThreeSum.Bands

variable {I J K : Type*}










































































































































/-- Every exact equation in the input interval hulls survives band filtering. -/
theorem exact_equation_relevant
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    {i : I} {j : J} {k : K} {a b c : ℤ}
    (ha : alo i ≤ a ∧ a ≤ ahi i) (hb : blo j ≤ b ∧ b ≤ bhi j)
    (hc : clo k ≤ c ∧ c ≤ chi k) (heq : a + b = c) :
    Relevant alo ahi blo bhi clo chi (i, j, k) := by
  constructor <;> dsimp only <;> omega

end ThreeSum.Bands

end

section


/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts

open Finset


























































































theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm

















end ThreeSum.LayerCounts

end

section


/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators




































theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < outputCount (512 * h) h := by
  have hlo : 256 ^ (2 * h) ≤ outputCount (512 * h) h := by
    simpa [outputCount, show 256 * (2 * h) = 512 * h by omega] using
      pow_le_choose_mul 256 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

theorem degree_le_vertices (L h : ℕ) : degree L h ≤ vertexCount L h :=
  Nat.choose_le_choose h (Nat.sub_le L h)

theorem vertices_mul_degree (L h : ℕ) :
    vertexCount L h * degree L h = outputCount L h * groupSize h :=
  LayerCounts.vertex_degree_identity L h

theorem groupSize_lt_pow {h : ℕ} (hh : 0 < h) : groupSize h < 2 ^ (2 * h) :=
  Nat.choose_lt_two_pow _ _ (by omega)

theorem groupSize_le_pow (h : ℕ) : groupSize h ≤ 2 ^ (2 * h) :=
  Nat.choose_le_two_pow _ _






/-- Exact strict version of the degree-square estimate needed to compare the
degree with the selected prime. -/
theorem degree_sq_lt_output_pow {L h : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L) :
    degree L h ^ 2 < outputCount L h * 2 ^ (2 * h) := by
  have hM : 0 < outputCount L h := Nat.choose_pos hL
  calc
    degree L h ^ 2 = degree L h * degree L h := by rw [pow_two]
    _ ≤ vertexCount L h * degree L h :=
      Nat.mul_le_mul_right _ (degree_le_vertices L h)
    _ = outputCount L h * groupSize h := vertices_mul_degree L h
    _ < outputCount L h * 2 ^ (2 * h) :=
      Nat.mul_lt_mul_of_pos_left (groupSize_lt_pow hh) hM

theorem degree_lt_modulus {L h p : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L)
    (hp : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : degree L h < p := by
  have hs := (degree_sq_lt_output_pow hh hL).trans_le hp
  nlinarith

theorem groupSize_lt_modulus {L h p : ℕ}
    (hM : 2 ^ (2 * h) < outputCount L h)
    (hp : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : groupSize h < p := by
  have hG := groupSize_le_pow h
  have hpow : 0 < (2 : ℕ) ^ (2 * h) := Nat.pow_pos (by decide)
  have hsq : groupSize h ^ 2 < outputCount L h * 2 ^ (2 * h) := by
    calc
      groupSize h ^ 2 ≤ (2 ^ (2 * h)) ^ 2 := Nat.pow_le_pow_left hG _
      _ = 2 ^ (2 * h) * 2 ^ (2 * h) := by rw [pow_two]
      _ < outputCount L h * 2 ^ (2 * h) := Nat.mul_lt_mul_of_pos_right hM hpow
  have hs := hsq.trans_le hp
  nlinarith








































/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/































/-! ## The actual local parameters at `L=512*h` -/






























theorem degree_lt_localPrime {h : ℕ} (hh : 0 < h) :
    degree (512 * h) h < localPrime h :=
  degree_lt_modulus hh (by omega) (localPrime_sq_lower h)

theorem groupSize_lt_localPrime {h : ℕ} (hh : 0 < h) : groupSize h < localPrime h :=
  groupSize_lt_modulus (concrete_output_gt_pow hh) (localPrime_sq_lower h)

theorem edgeCount_le_localPrime_sq (h : ℕ) :
    outputCount (512 * h) h * groupSize h ≤ localPrime h ^ 2 :=
  (Nat.mul_le_mul_left _ (groupSize_le_pow h)).trans (localPrime_sq_lower h)





















end ThreeSum.LocalCoverBounds

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


























































































































































































theorem mem_allWeights (values : List K) (hvalues : ∀ x, x ∈ values)
    (w : Weight L K) : w ∈ allWeights L values := by
  apply List.mem_map.mpr
  refine ⟨(fun i _ => w i), ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (fun i hi => hvalues (w i))















/-- The deterministic, actually defined schedule covers all ordered targets. -/
theorem schedule_covers (values : List K) (hvalues : ∀ x, x ∈ values)
    (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    ∃ w ∈ schedule L h values,
      Covers L h (bucketBound L h (Fintype.card K)) w target := by
  have hfreq : ∀ u ∈ (univ : Finset (K × K)), Fintype.card (Weight L K) ≤
      (320 * (2 * h + 1)) * (univ.filter fun w =>
        Covers L h (bucketBound L h (Fintype.card K)) w u).card := by
    intro u hu
    exact cover_frequency hsep hDelta hG hE hupper u
  have hc := Cover.greedy_cover (allWeights L values) (mem_allWeights values hvalues)
    (Covers L h (bucketBound L h (Fintype.card K)))
    (univ : Finset (K × K)) (320 * (2 * h + 1)) (by omega) hfreq target (mem_univ _)
  simpa only [schedule, scheduleLength, Finset.card_univ, Fintype.card_prod, pow_two] using hc

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









theorem mem_localValues (h : ℕ) (x : LocalField h) : x ∈ localValues h := by
  unfold localValues
  have hv := List.mem_map_of_mem (f := fun n : ℕ => (n : LocalField h))
    (List.mem_range.mpr x.val_lt)
  simpa only [ZMod.natCast_zmod_val] using hv










/-- Main concrete local-cover theorem. There are no moment, probability,
rank, prime-size, or coverage assumptions: the sole premise is `h>0`.
Every ordered residue pair, including an equal pair, is represented by a
retained edge under a member of the specified deterministic schedule. -/
theorem localSchedule_covers {h : ℕ} (hh : 0 < h) (target : LocalField h × LocalField h) :
    ∃ w ∈ localSchedule h, Covers (512 * h) h (localBucketCap h) w target := by
  have hs := schedule_covers (localValues h) (mem_localValues h)
    (L := 512 * h) (h := h) (by omega)
    (by simpa only [ZMod.card] using (degree_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using (groupSize_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using edgeCount_le_localPrime_sq h)
    (by simpa only [ZMod.card] using localPrime_sq_upper h) target
  simpa only [localSchedule, bucketBound, localBucketCap, ZMod.card] using hs

theorem localSchedule_represents {h : ℕ} (hh : 0 < h) (a b : LocalField h) :
    ∃ w ∈ localSchedule h, ∃ e : Edge (512 * h) h,
      HashFamily.hashValue w (left e) = a ∧ HashFamily.hashValue w (right e) = b ∧
      HashFamily.bucketSize (leftVertices (512 * h) h) w a ≤ localBucketCap h ∧
      HashFamily.bucketSize (rightVertices (512 * h) h) w b ≤ localBucketCap h := by
  obtain ⟨w, hw, hc⟩ := localSchedule_covers hh (a, b)
  exact ⟨w, hw, cover_has_edge hc⟩























end ThreeSum.LocalHashMoments

end

section


/-!
# Exact radix composition of finite local covers

The recursion enumerates only representations of one supplied target pair.
The coverage and multiplicity proofs quantify over arbitrary integer targets;
no enumeration of the square of the global modulus is used in the definition.
-/

namespace ThreeSum.Radix

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

































































/-- Every pair is globally covered if every local pair has a choice. -/
theorem representations_nonempty (p : ℤ) (left right : Ω → ℤ)
    (hcover : ∀ a b, (localFiber p left right a b).Nonempty)
    (j : ℕ) (a b : ℤ) : (representations p left right j a b).Nonempty := by
  induction j generalizing a b with
  | zero => exact singleton_nonempty _
  | succ j ih =>
    obtain ⟨ω, hω⟩ := hcover a b
    obtain ⟨xs, hxs⟩ := ih ((a - left ω) / p) ((b - right ω) / p)
    refine ⟨ω :: xs, ?_⟩
    exact mem_biUnion.mpr ⟨ω, hω, mem_image.mpr ⟨xs, hxs, rfl⟩⟩


































end ThreeSum.Radix

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












private theorem exists_list_index {α : Type*} (xs : List α) {n : ℕ}
    (hn : n = xs.length) (x : α) (hx : x ∈ xs) :
    ∃ i : Fin n, xs.get (Fin.cast hn i) = x := by
  subst n
  simpa only [Fin.cast_refl, id_eq] using List.mem_iff_get.mp hx

theorem mapAt_exists {h : ℕ} {w : Weight (512 * h) (LocalField h)}
    (hw : w ∈ localSchedule h) : ∃ i : Occurrence h, mapAt h i = w := by
  exact exists_list_index (localSchedule h) (scheduleSize_eq_length h) w hw

























theorem rawHash_cast {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (rawHash w s : LocalField h) = HashFamily.hashValue w s := by
  simp [rawHash, HashFamily.hashValue]
















theorem dvd_sub_rawHash_iff {h L : ℕ} (a : ℤ)
    (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (localPrime h : ℤ) ∣ a - rawHash w s ↔
      HashFamily.hashValue w s = (a : LocalField h) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, rawHash_cast, sub_eq_zero]
  exact eq_comm







theorem mem_localFiber {h : ℕ} (a b : ℤ) (c : RetainedChoice h) :
    c ∈ Radix.localFiber (localPrime h) rawLeft rawRight a b ↔
      HashFamily.hashValue (mapAt h (occurrence c)) (left (edge c)) = (a : LocalField h) ∧
      HashFamily.hashValue (mapAt h (occurrence c)) (right (edge c)) = (b : LocalField h) := by
  simp only [Radix.localFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rawLeft, rawRight, dvd_sub_rawHash_iff]

theorem localFiber_nonempty {h : ℕ} (hh : 0 < h) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).Nonempty := by
  obtain ⟨w, hw, e, ha, hb, hL, hR⟩ :=
    localSchedule_represents hh (a : LocalField h) (b : LocalField h)
  obtain ⟨i, hmap⟩ := mapAt_exists hw
  have hs : Survives h i e := by
    unfold Survives
    rw [hmap, ha, hb]
    exact ⟨hL, hR⟩
  refine ⟨⟨(i, e), hs⟩, (mem_localFiber a b _).mpr ?_⟩
  change HashFamily.hashValue (mapAt h i) (left e) = (a : LocalField h) ∧
    HashFamily.hashValue (mapAt h i) (right e) = (b : LocalField h)
  rw [hmap]
  exact ⟨ha, hb⟩























































theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (RetainedChoice h)) :
    xs ∈ representations h J a b ↔ xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs := by
  exact Radix.mem_representations (localPrime h)
    (by exact_mod_cast (localPrime_pos h).ne') rawLeft rawRight J a b xs

theorem representations_nonempty {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    (representations h J a b).Nonempty :=
  Radix.representations_nonempty (localPrime h) rawLeft rawRight
    (localFiber_nonempty hh) J a b






















theorem rawHash_difference {h L k : ℕ} (w : Weight L (LocalField h))
    (e : Edge L k) :
    rawHash w (right e) - rawHash w (left e) = rawOutput w (output e) := by
  unfold rawHash rawOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := Finset.disjoint_left.mp (edge_data e).2.2
  by_cases hs : i ∈ e.val.1 <;> by_cases hv : i ∈ e.val.2 <;>
    simp_all [left, right, leftWord, rightWord, output]











theorem blockKey_choice {h : ℕ} (c : RetainedChoice h) :
    blockKey (blockOfChoice c) = rawRight c - rawLeft c :=
  (rawHash_difference (mapAt h (occurrence c)) (edge c)).symm
















theorem positionalHash_difference {h : ℕ} (xs : List (RetainedChoice h)) :
    Radix.positionalHash (localPrime h) rawRight xs -
      Radix.positionalHash (localPrime h) rawLeft xs =
        Radix.positionalHash (localPrime h) blockKey (xs.map blockOfChoice) := by
  induction xs with
  | nil => simp [Radix.positionalHash]
  | cons c xs ih =>
      simp only [List.map_cons, Radix.positionalHash, blockKey_choice]
      rw [← ih]
      ring















































end ThreeSum.GlobalEncoding

end

section


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



















































theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega







theorem index_lt {i j m n : ℕ} (hi : i < m) (hj : j < n) : i*n+j < m*n := by
  have hh := Nat.mul_le_mul_right n (show i+1 ≤ m by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  omega











theorem slot_lt (A B C : Family) (o : Owner A B C) :
    slot A B C o < LightBandEnumeration.count A.size B.size C.size := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · have hh := index_lt j.isLt k.isLt
    simp only [slot,LightBandEnumeration.count]
    omega
  · have hh := index_lt i.isLt j.isLt
    simp only [slot,LightBandEnumeration.count]
    omega
  · have hh := index_lt i.isLt k.isLt
    simp only [slot,LightBandEnumeration.count]
    omega
















































































































end ThreeSum.BandCandidateRows

end

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition


























































theorem index_lt_size {n g i : ℕ} (hi : i < n) : i/g < size n g := by
  have hn : n ≠ 0 := by omega
  have hh := Nat.div_le_div_right (c := g) (show i ≤ n-1 by omega)
  simp only [size,if_neg hn]
  omega

theorem index_bounds {n g i : ℕ} (hg : 0 < g) (hi : i < n) :
    start g (i/g) ≤ i ∧ i < stop n g (i/g) := by
  have hlo := Nat.div_mul_le_self i g
  have hmod := Nat.mod_lt i hg
  have hsum := Nat.mod_add_div i g
  unfold start stop
  constructor
  · exact hlo
  · have hh : i < (i/g+1)*g := by nlinarith
    omega
























theorem covers (f : ℕ → ℤ) (n g : ℕ) (hg : 0 < g)
    (hs : ∀ i j, i < j → j < n → f i < f j) {i : ℕ} (hi : i < n) :
    let A := family f n g hg hs
    A.lower (i/g) ≤ f i ∧ f i ≤ A.upper (i/g) := by
  have hb := index_bounds hg hi
  have hib := index_lt_size (g := g) hi
  exact ⟨monotone_of_strict hs hb.1 hi,
    monotone_of_strict hs (by omega) (stop_sub_one_lt hg hib)⟩

end ThreeSum.BandPartition

end

section


/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light





theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [least]
      | succ n =>
          have h := ih (by omega)
          unfold least
          split <;> omega


































variable {lim : Limits} {P : Program} {d : ℕ}





































end ThreeSum.LightMinimum

end

section


/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice

open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000













theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC g A B C rs < s := LightMinimum.least_lt _ hs
































theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ modulus primes s nA nB nC g A B C rs r ∧
      modulus primes s nA nB nC g A B C rs r ≤ Y^r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    have hidx := chosenIndex_lt (q := modulus primes s nA nB nC g A B C rs r)
      (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs
    constructor
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)

theorem modulus_pos (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < modulus primes s nA nB nC g A B C rs r := by
  have hh := (modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs 1
    (Finset.sup (range s) primes) r
    (fun i hi => (hprime i hi).pos)
    (fun i hi => Finset.le_sup (mem_range.mpr hi))).1
  rw [one_pow] at hh
  omega

























































end ThreeSum.BandPrimeChoice

end

section


/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds












theorem lift_complete {j : ℤ} (hj : Arithmetic.SmallLift j) : ∃ i : Fin 3, lift i = j := by
  rcases hj with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩



















theorem tupleKey_eq {h J : ℕ} (t : ChoiceTuple h J) :
    tupleKey t = tupleRight t - tupleLeft t := by
  rw [tupleKey, globalKey, tupleRight, tupleLeft, positionalHash_difference]
  congr 1
  exact List.map_ofFn.symm

















































theorem ofFn_tupleOfList {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    List.ofFn (tupleOfList xs hlen) = xs := by
  subst J
  exact List.ofFn_get xs

theorem tuple_mem_representations {h J : ℕ} (t : ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ representations h J b c ↔
      globalModulus h J ∣ b - tupleLeft t ∧ globalModulus h J ∣ c - tupleRight t := by
  rw [mem_representations]
  simp only [List.length_ofFn, true_and, tupleLeft, tupleRight]

theorem tuple_difference_congruence {h J : ℕ} {t : ChoiceTuple h J} {b c : ℤ}
    (ht : List.ofFn t ∈ representations h J b c) :
    globalModulus h J ∣ (c - b) - tupleKey t := by
  obtain ⟨hb, hc⟩ := (tuple_mem_representations t b c).mp ht
  rw [tupleKey_eq]
  rw [sub_sub_sub_comm]
  exact dvd_sub hc hb












theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : Witness h J} :
    w ∈ witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
        globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1 := by
  simp only [witnesses, Finset.mem_filter, Finset.mem_univ, true_and]












theorem witnesses_nonempty {h J : ℕ} {P d a b c : ℤ}
    (hh : 0 < h) (hP : 0 < P) (hdiv : P ∣ c - b - a) :
    (witnesses h J P d a b c).Nonempty := by
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  have hnorm : P ∣ c % P - b % P - a % P := heq.dvd_iff.mpr hdiv
  obtain ⟨j, hj, he⟩ := Arithmetic.small_lift_exists hP
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP) hnorm
  obtain ⟨l, hl⟩ := lift_complete hj
  obtain ⟨xs, hxs⟩ := representations_nonempty hh J (b % P) (c % P + d)
  let hlen := ((mem_representations h J (b % P) (c % P + d) xs).mp hxs).1
  let t := tupleOfList xs hlen
  have ht : List.ofFn t ∈ representations h J (b % P) (c % P + d) := by
    simpa only [t, ofFn_tupleOfList] using hxs
  refine ⟨(t, l), mem_witnesses.mpr ⟨ht, ?_⟩⟩
  have hd := tuple_difference_congruence ht
  have htarget : a % P + lift l * P + d = (c % P + d) - b % P := by
    rw [hl]
    linarith
  simpa only [htarget] using hd

































































section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]














theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ} :
    r ∈ rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma







theorem raw_complete {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {t : Original α β γ}
    (hh : 0 < h) (hP : 0 < P) (ht : t ∈ T) (hd : P ∣ difference a b c t) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t := by
  obtain ⟨w, hw⟩ := witnesses_nonempty hh hP hd
  exact ⟨⟨t, w⟩, mem_rawOn.mpr ⟨ht, hw⟩, rfl⟩



























































































































































































end OriginalIndices

end ThreeSum.RawIncidences

end

section


/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool

open Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000






















































































theorem prime_spec {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y :=
  mem_values.mp (prime_mem hi)











theorem values_nonempty {y : ℕ} (hy : 0 < y) : values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ values y := mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < size y :=
  List.length_pos_iff.mpr (values_nonempty hy)


























































variable {lim : Limits} {P : Program} {d : ℕ}
























































































end ThreeSum.LightPrimePool

end

section


/-!
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction

open Light BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000





theorem modulus_bounds {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ modulus y nA nB nC g A B C rs levels ∧
      modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  BandPrimeChoice.modulus_bounds (LightPrimePool.prime y) A B C rs
    (LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (LightPrimePool.prime_spec hi).2.2)







































variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



















































































end ThreeSum.LightBandPrimeConstruction

end

section


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000









































































































theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩
















































end ThreeSum.BandRawA

end

section


/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000



































































theorem at_mem {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) : labelAt n g rs k ∈ items n g rs := by
  rw [labelAt,List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem at_bounds {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    (labelAt n g rs k).owner < rs.length ∧
      (ownerRecord n g rs k).flag=1 ∧
      BandPartition.start g (ownerRecord n g rs k).a ≤ (labelAt n g rs k).position ∧
      (labelAt n g rs k).position < BandPartition.stop n g (ownerRecord n g rs k).a := by
  have hh := mem_firstRows.mp (at_mem hk)
  have hr := mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩

























theorem values_getD {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by
  unfold values labelAt
  rw [List.getD_map_of_lt _ hk default 0]


























end ThreeSum.BandRawA

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



























































theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]






























































































end ThreeSum.BandRawA

end

section


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology

















































































noncomputable section








































































































































































































































































































theorem primeDepth_upper (R : ℕ → ℕ) {n : ℕ} (hR : 4 ≤ R n) :
    4 * (4 * primeWindow n) ^ primeDepth R n ≤ R n := by
  have hr : R n / 4 ≠ 0 := by omega
  have h := Nat.pow_log_le_self (4 * primeWindow n) hr
  have h4 := Nat.mul_le_mul_left 4 h
  have hd := Nat.div_mul_le_self (R n) 4
  simpa [primeDepth, Nat.mul_comm] using h4.trans (by simpa [Nat.mul_comm] using hd)












































































































































































































































































































































































































































































































































end

end ThreeSum.Scales

end

section


/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales

open BandCandidateRows Scales BandScales CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000



















theorem modulus_bounds (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    primeWindow n^primeDepth radix n ≤ modulus n nA nB nC A B C rs ∧
      modulus n nA nB nC A B C rs ≤ (4*primeWindow n)^primeDepth radix n :=
  LightBandPrimeConstruction.modulus_bounds A B C rs _ (by have := primeWindow_ge_two n; omega)

/-- The integer guard used by the three-lift residue construction. -/
theorem modulus_guard {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hR : 4 ≤ radix n) : 4*modulus n nA nB nC A B C rs ≤ radix n :=
  (Nat.mul_le_mul_left 4 (modulus_bounds n nA nB nC A B C rs).2).trans
    (primeDepth_upper radix hR)



















































































end ThreeSum.BandPrimeScales

end

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000


























@[simp] theorem mem_finiteAIndices {n g s : ℕ} {rs : List Record}
    {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ i.val ∈ aIndices n g rs s := by
  simp only [finiteAIndices,mem_filter,mem_univ,true_and]





@[simp] theorem mem_finiteOwnerProduct {nA nB nC g s : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteOwnerProduct nA nB nC g rs s ↔
      coordinates t ∈ ownerProduct nA nB nC g rs s := by
  simp only [finiteOwnerProduct,ownerProduct,mem_product,mem_finiteAIndices,
    mem_finiteBandPositions,coordinates]

@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]

theorem finiteAIndices_owner {n g s : ℕ} {rs : List Record}
    (hs : s < rs.length) {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ (labelAt n g rs i.val).owner=s := by
  rw [mem_finiteAIndices,mem_aIndices_iff_owner hs]
  simp only [i.isLt,true_and]







theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩








theorem finite_lift {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    ∃ u ∈ finiteAllProducts nA nB nC g rs, coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact mem_finiteAllProducts.mpr ht







































































end ThreeSum.BandRawA

end

section


/-!
# Exact original-value membership and equation coverage of the owner catalog

Normalized sorted coordinates remain distinct from original input
positions. The normalization membership equivalence transfers values back
to their original color classes; the color-class bridge can then recover
the required distinct original positions.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000























theorem product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ originalA ∧
      B.getD t.2.1 0 ∈ originalB ∧ C.getD t.2.2 0 ∈ originalC := by
  obtain ⟨ha,hb,hc⟩ := product_values_mem ht
  exact ⟨(hA _).mp ha,(hB _).mp hb,(hC _).mp hc⟩

theorem sorted_equation_complete {A B C : List ℤ} {g : ℕ} {a b c : ℤ}
    (hg : 0 < g) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·))
    (hsC : C.Pairwise (· < ·)) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c := by
  obtain ⟨ia,hia,hA⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨ib,hib,hB⟩ := List.mem_iff_getElem.mp hb
  obtain ⟨ic,hic,hC⟩ := List.mem_iff_getElem.mp hc
  have hAget : A.getD ia 0=a := (List.getD_eq_getElem A 0 hia).trans hA
  have hBget : B.getD ib 0=b := (List.getD_eq_getElem B 0 hib).trans hB
  have hCget : C.getD ic 0=c := (List.getD_eq_getElem C 0 hic).trans hC
  let FA := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let FB := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let FC := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  let band : Triple FA FB FC :=
    (⟨ia/g,index_lt_size hia⟩,⟨ib/g,index_lt_size hib⟩,⟨ic/g,index_lt_size hic⟩)
  have hAband : FA.lo band.1 ≤ a ∧ a ≤ FA.hi band.1 := by
    simpa only [FA,band,Family.lo,Family.hi,hAget] using covers (fun i => A.getD i 0) A.length g hg
      (LightSortedBands.getD_strict hsA) hia
  have hBband : FB.lo band.2.1 ≤ b ∧ b ≤ FB.hi band.2.1 := by
    simpa only [FB,band,Family.lo,Family.hi,hBget] using covers (fun i => B.getD i 0) B.length g hg
      (LightSortedBands.getD_strict hsB) hib
  have hCband : FC.lo band.2.2 ≤ c ∧ c ≤ FC.hi band.2.2 := by
    simpa only [FC,band,Family.lo,Family.hi,hCget] using covers (fun i => C.getD i 0) C.length g hg
      (LightSortedBands.getD_strict hsC) hic
  have hrel : relevant FA FB FC band := Bands.exact_equation_relevant hAband hBband hCband heq
  have hap : start g band.1.val ≤ ia ∧ ia < stop A.length g band.1.val := index_bounds hg hia
  have hbp : start g band.2.1.val ≤ ib ∧ ib < stop B.length g band.2.1.val := index_bounds hg hib
  have hcp : start g band.2.2.val ≤ ic ∧ ic < stop C.length g band.2.2.val := index_bounds hg hic
  obtain ⟨k,hk,hlabel,hproduct⟩ := relevant_product_complete band hrel hap hbp hcp
  have hs : slot FA FB FC (owner FA FB FC band) < (records FA FB FC).length := by
    rw [records_length]
    exact slot_lt FA FB FC _
  have hall : (k,ib,ic) ∈ allProducts A.length B.length C.length g (records FA FB FC) :=
    mem_biUnion.mpr ⟨slot FA FB FC (owner FA FB FC band),mem_range.mpr hs,hproduct⟩
  refine ⟨(k,ib,ic),hall,?_,hBget,hCget⟩
  change valueAt A.length g (records FA FB FC) (fun i => A.getD i 0) k=a
  rw [valueAt,values_getD _ hk,hlabel]
  exact hAget

theorem original_equation_complete {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c :=
  sorted_equation_complete hg hsA hsB hsC ((hA a).mpr ha) ((hB b).mpr hb) ((hC c).mpr hc) heq

theorem original_equation_sound {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ allProducts A.length B.length C.length g rs)
    (heq : valueAt A.length g rs (fun i => A.getD i 0) t.1+B.getD t.2.1 0=C.getD t.2.2 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c := by
  obtain ⟨ha,hb,hc⟩ := product_original_values hA hB hC ht
  exact ⟨_,ha,_,hb,_,hc,heq⟩

end ThreeSum.BandRawA

end

section


/-! # Original-value soundness and completeness on the bounded reporting domain -/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset

set_option maxHeartbeats 1200000
set_option maxRecDepth 7000











theorem finite_original_equation_complete {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ finiteAllProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1.val=a ∧ B.getD t.2.1.val 0=b ∧ C.getD t.2.2.val 0=c := by
  obtain ⟨t,ht,hvalues⟩ := original_equation_complete hg hsA hsB hsC hA hB hC ha hb hc heq
  obtain ⟨u,hu,he⟩ := finite_lift ht
  refine ⟨u,hu,?_⟩
  change valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
    (fun i => A.getD i 0) (coordinates u).1=a ∧
      B.getD (coordinates u).2.1 0=b ∧ C.getD (coordinates u).2.2 0=c
  rw [he]
  exact hvalues

theorem finite_original_equation_sound {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record}
    {t : Fin (items A.length g rs).length × Fin B.length × Fin C.length}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ finiteAllProducts A.length B.length C.length g rs)
    (heq : valueAt A.length g rs (fun i => A.getD i 0) t.1.val+
      B.getD t.2.1.val 0=C.getD t.2.2.val 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c :=
  original_equation_sound hA hB hC (mem_finiteAllProducts.mp ht) heq

end ThreeSum.BandRawA

end

section


/-!
# Distinct original-position semantics of the finite owner catalog

Incidence coordinates remain physical coordinates in the flattened A row.
Original input indices are recovered from retained class membership. Their
different colors prove that the three recovered positions are distinct,
even when the input contains repeated values.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000











































theorem finite_color_iff {n W g : ℕ} {A B C : List ℤ}
    (p : Coloring.Parameter W) (x : Fin n → ℤ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ classList p x 0 1)
    (hB : ∀ z, z ∈ B ↔ z ∈ classList p x 1 1)
    (hC : ∀ z, z ∈ C ↔ z ∈ classList p x 2 (-1)) :
    finiteEquation A B C g (sortedRecords A B C g hg hsA hsB hsC) ↔ witness p x := by
  constructor
  · rintro ⟨t,ht,heq⟩
    exact finite_original_equation_sound hA hB hC ht heq
  · rintro ⟨a,ha,b,hb,c,hc,heq⟩
    obtain ⟨t,ht,hav,hbv,hcv⟩ :=
      finite_original_equation_complete hg hsA hsB hsC hA hB hC ha hb hc heq
    refine ⟨t,ht,?_⟩
    rw [hav,hbv,hcv]
    exact heq
















end ThreeSum.BandRawA

end

section


/-!
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive

open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators

set_option linter.unusedSectionVars false















theorem frontier_positive {α : Type*} (children : ℕ → List α) (query : ℕ → List α → ℕ)
    {k : ℕ} {pre : List α} (hp : pre ∈ Reporting.frontier children query k) :
    0 < query k pre := by
  cases k with
  | zero =>
      simp only [Reporting.frontier] at hp
      split at hp
      · have he : pre = [] := List.mem_singleton.mp hp
        simpa only [he] using ‹0 < query 0 []›
      · cases hp
  | succ k =>
      exact of_decide_eq_true (List.mem_filter.mp hp).2

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
























theorem frontier_valid {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (512*h)))}
    (hp : pre ∈ ReportingHostFrontier.frontier I w k) : ValidPrefix w.2.2 k pre :=
  positivePrefix_valid I w pre hk (frontier_positive _ _ hp)





















end ThreeSum.ReportingHostPositive

end

section


/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting LightBlockQuery ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




theorem rootMass_eq {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w=(domain I w).card := by
  simp [rootMass,prefixQuery,Reporting.mass,Subset.fiberMass]












































































end ThreeSum.ReportingHostFrontierLayout

end

section


/-!
# Sound cumulative dense stopping on visited wanted labels

Distinct wanted labels have disjoint raw-incidence fibers. Therefore any
visited prefix already exceeding the exact representation-times-false-score
threshold certifies an original equation, before proportional traversal.
-/

namespace ThreeSum.DenseGuard

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




@[simp] theorem mass_nil {h J : ℕ} (I : Finset (RawItem h J α β γ)) : mass I []=0 := rfl

theorem mass_append {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) (w : Wanted h J α) :
    mass I (visited++[w])=mass I visited+rootMass I w := by simp [mass]

theorem mass_le_raw_card {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) (hn : visited.Nodup) : mass I visited ≤ I.card := by
  unfold mass
  rw [← List.sum_toFinset _ hn]
  calc
    _ ≤ ∑ w : Wanted h J α, rootMass I w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = I.card := by
      simp only [rootMass_eq]
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

theorem partial_early_yes {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (aux : Finset ℤ)
    (visited : List (Wanted h J α)) (hn : visited.Nodup)
    (hP : 0 < P) (hguard : 4*P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬ l ∣ difference a b c t)
    (hlarge : representationCap h J*Arithmetic.weightedFalseCount T (difference a b c) aux P <
      mass (rawOn h J P d T a b c) visited) :
    ∃ t ∈ T, difference a b c t=0 :=
  RawIncidences.dense_early_yes T a b c aux hP hguard hsep
    (hlarge.trans_le (mass_le_raw_card _ visited hn))

theorem partial_early_yes_of_upper {h J H : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (aux : Finset ℤ)
    (visited : List (Wanted h J α)) (hn : visited.Nodup)
    (hP : 0 < P) (hguard : 4*P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬ l ∣ difference a b c t)
    (hH : Arithmetic.weightedFalseCount T (difference a b c) aux P ≤ H)
    (hlarge : representationCap h J*H < mass (rawOn h J P d T a b c) visited) :
    ∃ t ∈ T, difference a b c t=0 :=
  partial_early_yes T a b c aux visited hn hP hguard hsep
    ((Nat.mul_le_mul_left _ hH).trans_lt hlarge)













end ThreeSum.DenseGuard

end

section


/-!
# Owner queries are the exact fibers of the global physical domain

The A incidence fixes its owner. Restricting to that owner's B/C bands
therefore leaves the entire wanted fiber unchanged. The mass read by the
owner-local query is exactly the mass charged by the global dense guard.
-/

namespace ThreeSum.DenseGuardBands

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

section General

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem domain_eq_of_first_fiber {h J : ℕ} {P shift : ℤ}
    (T U : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α)
    (hf : ∀ t : Original α β γ, t.1=w.1 → (t ∈ T ↔ t ∈ U)) :
    domain (rawOn h J P shift T a b c) w=domain (rawOn h J P shift U a b c) w := by
  ext r
  simp only [domain,mem_filter,mem_rawOn]
  constructor
  · rintro ⟨⟨ht,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mp ht,hr⟩,he⟩
  · rintro ⟨⟨hu,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mpr hu,hr⟩,he⟩

end General

open BandRawA

theorem finite_owner_fiber {nA nB nC g s : ℕ} {rs : List BandCandidateRows.Record}
    (hs : s < rs.length) (i : Fin (items nA g rs).length)
    (hi : (BandRawA.labelAt nA g rs i.val).owner=s)
    (t : Fin (items nA g rs).length × Fin nB × Fin nC) (ht : t.1=i) :
    t ∈ finiteAllProducts nA nB nC g rs ↔ t ∈ finiteOwnerProduct nA nB nC g rs s := by
  have ho : (BandRawA.labelAt nA g rs t.1.val).owner=s := by rw [ht]; exact hi
  simp only [mem_finiteAllProducts,mem_finiteOwnerProduct,mem_allProducts,mem_ownerProduct hs,
    coordinates,ownerRecord,ho,true_and]

theorem domain_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    domain (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      domain (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  domain_eq_of_first_fiber _ _ a b c w (finite_owner_fiber hs w.1 ho)

theorem prefixQuery_global_eq_owner {h J nA nB nC g s k : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s)
    (pre : List (Finset (Fin (512*h)))) :
    prefixQuery (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w k pre=
      prefixQuery (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w k pre := by
  simp only [prefixQuery,domain_global_eq_owner rs hs a b c w ho]

theorem rootMass_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    rootMass (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      rootMass (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  prefixQuery_global_eq_owner rs hs a b c w ho []

end ThreeSum.DenseGuardBands

end

section


/-!
# Distinct wanted labels in the actual emitted array

The join's physical slots decode injectively, even when original integer
values or key values repeat. Consequently every prefix of the actual
array is a valid distinct-label input to the cumulative dense guard.
-/

namespace ThreeSum.DenseGuardWanted

open Light WantedRecordOrder











































theorem labelAt_injective {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift) :
    Function.Injective (labelAt H) := by
  intro k k' he
  have hp := label_injective (output_bounds H k.isLt).1 (output_bounds H k'.isLt).1
    (output_bounds H k.isLt).2 (output_bounds H k'.isLt).2 he
  exact Fin.ext (pair_indices_injective H k.isLt k'.isLt hp.1 hp.2)
































theorem labels_complete {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    {w : RawReporting.Wanted h J (Fin xs.length)}
    (hw : w ∈ RawAKeyLists.wanted M P xs h J shift) : w ∈ labels H := by
  obtain ⟨slot,i,j,hi,hk,_,hL,hR,he⟩ := WantedRecordCoverage.output_complete H hw
  apply List.mem_ofFn.mpr
  refine ⟨⟨slot,hk⟩,?_⟩
  simpa only [labelAt,leftIndex,rightIndex,hL,hR,Int.toNat_natCast] using he

end ThreeSum.DenseGuardWanted

end

section


/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts

open Light Scales BandScales CostLedger ArithmeticStageBounds





























































theorem moduli_pos {A B C : List ℤ} {g y : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hy : 0 < y) (i : ℕ) : 0 < LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y i :=
  BandPrimeChoice.modulus_pos (LightPrimePool.prime y)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (BandRawA.sortedRecords A B C g hg hsA hsB hsC) (LightPrimePool.size_pos hy)
    (fun j hj => (LightPrimePool.prime_spec hj).1) i

theorem scheduled_modulus_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n))=
      BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) := rfl

theorem scheduled_modulus_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) :
    4*LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n)) ≤ radix n := by
  rw [scheduled_modulus_eq]
  exact BandPrimeScales.modulus_guard _ _ _ _ hR

end ThreeSum.EncodedColorPrimeCosts

end

section


/-! # The same normalized finite witnesses and their actually selected prime -/

namespace ThreeSum.EncodedColorPrimeReadyData

open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData





















theorem selected_pos {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < selected n A B C hsA hsB hsC :=
  EncodedColorPrimeCosts.moduli_pos (lt_of_lt_of_le (by decide : 0 < 2) (primeWindow_ge_two n)) _

theorem selected_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : 4*selected n A B C hsA hsB hsC ≤ radix n :=
  EncodedColorPrimeCosts.scheduled_modulus_guard hR

end ThreeSum.EncodedColorPrimeReadyData

end

section


/-!
# Exact original-encoding semantics and cost of the executed terminal batch

This is the specialization of the actual seven-procedure batch to the full
endpoint masks emitted at a valid partial prefix. The precise ordered
candidate sum is charged to raw prefix mass plus the terminal cube term.
-/

namespace ThreeSum.ReportingHostTerminalBatch

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open ReportingHostTerminalChoices ReportingHostBlockBucketTest BlockSourceEncoding LightSourceResidues
open LightReportingTerminalMasks LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false






























































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
















theorem hit_sound {h J k NL NR : ℕ} {av shift : ℤ} {p : ℕ} {left right : ℕ→ℤ}
    {q : GlobalOutput h J} {pre : List (Finset (Fin (512*h)))}
    (H : Hit av p shift left right NL NR q k pre) :
    ∃ i<NL, ∃ j<NR, right j-left i-av=0 := by
  obtain ⟨s,hs,_,_,i,hi,j,hj,_,_,he⟩ := H
  exact ⟨i,hi,j,hj,he⟩
































end ThreeSum.ReportingHostTerminalBatch

end

section


/-!
# Original raw witnesses reach the actually tested terminal prefixes

Every true raw incidence has a stored positive prefix at any chosen partial
depth, and its retained completion appears in the actual terminal batch.
Conversely, every positive terminal result supplies an original finite
owner-domain triple whose integer values satisfy the exact equation.
-/

namespace ThreeSum.ReportingHostTerminalOriginal

open Finset BlockRows BlockEncoding GlobalEncoding RawIncidences RawReporting RawPrefixCounts
open StoredReporting
open ReportingHostTerminalBatch

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem hit_of_raw {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (r : RawItem h J α β γ) (hr : r∈rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c)
    (hw : wantedOf r=w) (hpre : (word r).take k=pre) (hzero : difference a b c r.1=0) :
    Hit (a w.1) p shift left right NL NR w.2.2 k pre := by
  have hq : tupleOutput r.2.1=w.2.2 := congrArg (fun w => w.2.2) hw
  have ha : r.1.1=w.1 := congrArg Prod.fst hw
  have hraw := mem_rawOn.mp hr
  have hrep := (mem_witnesses.mp hraw.2).1
  have hpair := (tuple_mem_representations r.2.1 (b r.1.2.1%(p : ℤ))
    (c r.1.2.2%(p : ℤ)+shift)).mp hrep
  have hcompletion : r.2.1∈completions w.2.2 k pre :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hpre⟩
  have hcompatible : r.1.2∈compatiblePairs (p : ℤ) shift B C b c r.2.1 :=
    Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hraw.1).2,hpair⟩
  exact hit_of_compatible p shift (a w.1) B C b c left right eL eR hvL hvR w.2.2 pre hk hp
    r.2.1 hcompletion r.1.2 hcompatible (by simpa only [difference,ha] using hzero)

theorem hit_sound_original {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (ha : w.1∈A)
    (H : Hit (a w.1) p shift left right NL NR w.2.2 k pre) :
    ∃ t∈A ×ˢ (B ×ˢ C), t.1=w.1 ∧ difference a b c t=0 := by
  obtain ⟨i,hi,j,hj,he⟩ := hit_sound H
  let u := eL ⟨i,hi⟩
  let v := eR ⟨j,hj⟩
  refine ⟨(w.1,u.val,v.val),Finset.mem_product.mpr ⟨ha,Finset.mem_product.mpr ⟨u.property,v.property⟩⟩,rfl,?_⟩
  change c v.val-b u.val-a w.1=0
  rw [← hvL ⟨i,hi⟩,← hvR ⟨j,hj⟩]
  exact he

theorem frontier_hit_of_raw {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (hk : k≤J) (r : RawItem h J α β γ)
    (hr : r∈rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c)
    (hw : wantedOf r=w) (hzero : difference a b c r.1=0) :
    ∃ pre∈ReportingHostFrontier.frontier (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k,
      Hit (a w.1) p shift left right NL NR w.2.2 k pre := by
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hfront : (word r).take k∈ReportingHostFrontier.frontier I w k :=
    (ReportingHostFrontier.mem_frontier_iff I w hk _).mpr ⟨r,hr,hw,rfl⟩
  refine ⟨(word r).take k,hfront,?_⟩
  exact hit_of_raw p shift A B C a b c left right eL eR hvL hvR w _ hk
    (ReportingHostPositive.frontier_valid I w hk hfront) r hr hw rfl hzero






















end ThreeSum.ReportingHostTerminalOriginal

end

section


/-!
# The actual wanted array on physical owner-incidence indices

The key constructor uses the mapped A-value list. The reporter and dense
owner domains use physical positions in the incidence-label list. Their
length-preserving transport keeps every physical position, lift and full
output record, including positions holding equal integer values.
-/

namespace ThreeSum.ReportingHostWantedPhysical

open Light BandRawA BandCandidateRows RawIncidences GlobalEncoding

set_option maxHeartbeats 2100000
set_option maxRecDepth 10000





















theorem transport_injective {α β : Type*} {h J : ℕ} (e : α≃β) :
    Function.Injective (transport (h := h) (J := J) e) := by
  intro w w' he
  exact Prod.ext (e.injective (congrArg (fun z : RawReporting.Wanted h J β => z.1) he))
    (congrArg (fun z : RawReporting.Wanted h J β => z.2) he)

@[simp] theorem transport_symm {α β : Type*} {h J : ℕ} (e : α≃β)
    (w : RawReporting.Wanted h J β) : transport e (transport e.symm w)=w := by
  rcases w with ⟨i,q⟩
  simp only [transport,Equiv.apply_symm_apply]

section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P (values f (items n g rs)))
    (LightGuardedWanted.right h J) (3*(values f (items n g rs)).length)
    (LightGuardedWanted.totalKeys h J) shift)




theorem wantedAt_injective : Function.Injective (wantedAt H) :=
  (transport_injective (incidenceIndices f n g rs)).comp (DenseGuardWanted.labelAt_injective H)


















































/-- Every physical incidence/lift/output satisfying the key equation is an
actual emitted slot. This is the converse needed by the no-hit decision. -/
theorem wantedAt_complete (w : RawReporting.Wanted h J (Fin (items n g rs).length))
    (hk : (M : ℤ) ∣ valueAt n g rs f w.1.val%(P : ℤ)+
      lift w.2.1*(P : ℤ)+shift-globalKey w.2.2) :
    ∃ slot : Fin (μ free).toNat, wantedAt H slot=w := by
  let v := transport (incidenceIndices f n g rs).symm w
  have hv : v∈RawAKeyLists.wanted M P (values f (items n g rs)) h J shift :=
    RawAKeyLists.mem_wanted.mpr hk
  obtain ⟨slot,hs⟩ := List.mem_ofFn.mp (DenseGuardWanted.labels_complete H hv)
  refine ⟨slot,?_⟩
  change transport (incidenceIndices f n g rs) (DenseGuardWanted.labelAt H slot)=w
  rw [hs]
  exact transport_symm _ w

end Actual

end ThreeSum.ReportingHostWantedPhysical

end

section


/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000





































theorem owner_lt {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    owner rs w<rs.length := (at_bounds w.1.isLt).1

theorem mem_owner {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    w.1∈finiteAIndices n g rs (owner rs w) :=
  (finiteAIndices_owner (owner_lt rs w)).mpr rfl







theorem global_local_mass {h J n NB NC g p : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    rootMass (globalItems h J n NB NC g p rs fA fB fC shift) w=
      rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w :=
  DenseGuardBands.rootMass_global_eq_owner rs (owner_lt rs w) _ _ _ w rfl







theorem terminal_sound {h J n NB NC g p k : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs))
    (H : Terminal h J n NB NC g p rs fA fB fC shift w k) :
    ∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  obtain ⟨pre,_,hhit⟩ := H
  obtain ⟨t,ht,ha,hzero⟩ := ReportingHostTerminalOriginal.hit_sound_original p shift
    (finiteAIndices n g rs (owner rs w))
    (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (left rs fB w) (right rs fC w)
    (finiteBandEquiv NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandEquiv NC g (ownerRecord n g rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w pre (mem_owner rs w) hhit
  have hlocal : t∈finiteOwnerProduct n NB NC g rs (owner rs w) := ht
  exact ⟨t,(DenseGuardBands.finite_owner_fiber (owner_lt rs w) w.1 rfl t ha).mpr hlocal,hzero⟩

theorem terminal_of_raw {h J n NB NC g p k : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) (hk : k≤J)
    (r : RawItem h J (AType n g rs) (Fin NB) (Fin NC))
    (hr : r∈globalItems h J n NB NC g p rs fA fB fC shift) (hw : wantedOf r=w)
    (hzero : difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) r.1=0) :
    Terminal h J n NB NC g p rs fA fB fC shift w k := by
  have ha : r.1.1=w.1 := congrArg Prod.fst hw
  have hglobal := mem_rawOn.mp hr
  have hlocal : r.1∈finiteOwnerProduct n NB NC g rs (owner rs w) :=
    (DenseGuardBands.finite_owner_fiber (owner_lt rs w) w.1 rfl r.1 ha).mp hglobal.1
  have hraw : r∈localItems h J n NB NC g p rs fA fB fC shift w := mem_rawOn.mpr ⟨hlocal,hglobal.2⟩
  exact ReportingHostTerminalOriginal.frontier_hit_of_raw p shift
    (finiteAIndices n g rs (owner rs w))
    (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (left rs fB w) (right rs fC w)
    (finiteBandEquiv NB g (ownerRecord n g rs w.1.val).b)
    (finiteBandEquiv NC g (ownerRecord n g rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w hk r hraw hw hzero

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)

theorem raw_emitted {r : RawItem h J (AType n g rs) (Fin NB) (Fin NC)}
    (hr : r∈globalItems h J n NB NC g P rs fA fB fC shift) :
    ∃ slot : Fin (μ free).toNat, wantedAt H slot=wantedOf r := by
  apply wantedAt_complete H
  have hh := (mem_witnesses.mp (mem_rawOn.mp hr).2).2
  simpa only [globalModulus,Nat.cast_pow,wantedOf,tupleKey] using hh

theorem original_zero_iff_emitted_terminal {k : ℕ}
    (hh : 0<h) (hp : 0<P) (hk : k≤J) :
    (∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0) ↔
      ∃ slot : Fin (μ free).toNat, Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H slot) k := by
  constructor
  · rintro ⟨t,ht,hzero⟩
    obtain ⟨r,hr,hrt⟩ := raw_complete (h := h) (J := J) (P := (P : ℤ)) (d := shift)
      (a := fun i => valueAt n g rs fA i.val) (b := fun j => fB j.val) (c := fun j => fC j.val)
      hh (by exact_mod_cast hp) ht (by rw [hzero]; exact dvd_zero _)
    obtain ⟨slot,hslot⟩ := raw_emitted H hr
    exact ⟨slot,terminal_of_raw rs fA fB fC shift (wantedAt H slot) hk r hr hslot.symm
      (by simpa only [hrt] using hzero)⟩
  · rintro ⟨slot,hterminal⟩
    exact terminal_sound rs fA fB fC shift (wantedAt H slot) hterminal

end Actual

end ThreeSum.ReportingHostWantedOriginal

end

section


/-!
# Summing the actual dense-guard branches in physical slot order

The counter at slot i is the mass of slots before i. The expensive branch
is charged only when adding the current mass still fits the threshold.
These charges sum to at most that threshold, including when a later slot
crosses it. No bound on the mass of the crossing slot is required.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset
open scoped BigOperators






theorem prefixMass_zero (mass : ℕ → ℕ) : prefixMass mass 0=0 := by simp [prefixMass]

theorem prefixMass_succ (mass : ℕ → ℕ) (n : ℕ) :
    prefixMass mass (n+1)=prefixMass mass n+mass n := by
  simp only [prefixMass,sum_range_succ]



























































end ThreeSum.SharedTraversalCosts

end

section


/-!
# The exact dense counter of the physical ascending wanted scan

The finite physical labels are injective even when input values repeat.
The sum of the queried owner masses in any prefix is consequently the
mass of a distinct-label prefix in the complete original domain.
-/

namespace ThreeSum.ReportingHostWantedPrefix

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical ReportingHostWantedOriginal
open ReportingHostFrontierLayout SharedTraversalCosts

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)



theorem labels_nodup : (labels H).Nodup :=
  List.nodup_ofFn_ofInjective (wantedAt_injective H)

theorem prefix_nodup (k : ℕ) : ((labels H).take k).Nodup := (labels_nodup H).take

theorem prefix_step (i : Fin (μ free).toNat) :
    (labels H).take (i.val+1)=(labels H).take i.val++[wantedAt H i] := by
  have hi : i.val<(labels H).length := by simpa only [labels,List.length_ofFn] using i.isLt
  rw [List.take_succ_eq_append_getElem hi]
  simp only [labels,List.getElem_ofFn]







theorem slotMass_at (fB fC : ℕ→ℤ) (NB NC : ℕ) (i : Fin (μ free).toNat) :
    slotMass H fB fC NB NC i.val=
      rootMass (globalItems h J n NB NC g P rs fA fB fC shift) (wantedAt H i) := by
  simp only [slotMass,dif_pos i.isLt]
  exact (global_local_mass rs fA fB fC shift (wantedAt H i)).symm

theorem prefix_mass_eq (fB fC : ℕ→ℤ) (NB NC k : ℕ) (hk : k≤(μ free).toNat) :
    prefixMass (slotMass H fB fC NB NC) k=
      DenseGuard.mass (globalItems h J n NB NC g P rs fA fB fC shift) ((labels H).take k) := by
  induction k with
  | zero => simp only [prefixMass_zero,List.take_zero,DenseGuard.mass_nil]
  | succ k ih =>
      let i : Fin (μ free).toNat := ⟨k,by omega⟩
      rw [prefixMass_succ,ih (by omega)]
      rw [show (labels H).take (k+1)=(labels H).take k++[wantedAt H i] from prefix_step H i]
      rw [DenseGuard.mass_append,show slotMass H fB fC NB NC k=
        rootMass (globalItems h J n NB NC g P rs fA fB fC shift) (wantedAt H i) from slotMass_at H fB fC NB NC i]







theorem prefix_dense_yes (fB fC : ℕ→ℤ) (NB NC k F : ℕ) (aux : Finset ℤ)
    (hk : k≤(μ free).toNat) (hp : 0<P) (hg : 4*(P : ℤ)≤globalModulus h J)
    (hsep : ∀ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t≠0 →
        ∃ l∈aux, ¬l∣difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t)
    (hF : Arithmetic.weightedFalseCount (finiteAllProducts n NB NC g rs)
      (difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)) aux (P : ℤ)≤F)
    (hdense : representationCap h J*F<prefixMass (slotMass H fB fC NB NC) k) :
    ∃ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  rw [prefix_mass_eq H fB fC NB NC k hk] at hdense
  exact DenseGuard.partial_early_yes_of_upper (finiteAllProducts n NB NC g rs)
    (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    aux ((labels H).take k) (prefix_nodup H k) (by exact_mod_cast hp) hg hsep hF hdense

end Actual

end ThreeSum.ReportingHostWantedPrefix

end

section


/-!
# Exact whole-scan YES and NO for the original physical domain

Every emitted slot has its own original owner bands. Prefix threshold
crossings are sound by distinct physical labels; if no crossing occurs,
the terminal tests cover every original zero through an actual emitted slot.
-/

namespace ThreeSum.ReportingHostWantedDecision

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting GlobalEncoding
open ReportingHostWantedPhysical ReportingHostWantedOriginal ReportingHostWantedPrefix
open LightReportingWantedScan SharedTraversalCosts

set_option maxHeartbeats 2100000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)






theorem slotHit_at (fB fC : ℕ→ℤ) (NB NC K : ℕ) (i : Fin (μ free).toNat) :
    slotHit H fB fC NB NC K i.val ↔
      Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H i) K := by
  simp only [slotHit,dif_pos i.isLt]

theorem hit_exists_iff (fB fC : ℕ→ℤ) (NB NC K : ℕ) :
    (∃ i<(μ free).toNat, slotHit H fB fC NB NC K i) ↔
      ∃ i : Fin (μ free).toNat, Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H i) K := by
  constructor
  · rintro ⟨i,hi,hhit⟩
    exact ⟨⟨i,hi⟩,(slotHit_at H fB fC NB NC K ⟨i,hi⟩).mp hhit⟩
  · rintro ⟨i,hhit⟩
    exact ⟨i.val,i.isLt,(slotHit_at H fB fC NB NC K i).mpr hhit⟩

theorem accepted_iff_original (fB fC : ℕ→ℤ) (NB NC K F : ℕ) (aux : Finset ℤ)
    (hh : 0<h) (hK : K≤J) (hp : 0<P) (hg : 4*(P : ℤ)≤globalModulus h J)
    (hsep : ∀ t∈finiteAllProducts n NB NC g rs,
      difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t≠0 →
        ∃ l∈aux, ¬l∣difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t)
    (hF : Arithmetic.weightedFalseCount (finiteAllProducts n NB NC g rs)
      (difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)) aux (P : ℤ)≤F) :
    Accepted (slotMass H fB fC NB NC) (slotHit H fB fC NB NC K)
      (representationCap h J*F) (μ free).toNat ↔
      ∃ t∈finiteAllProducts n NB NC g rs,
        difference (fun i => valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  constructor
  · rintro (hdense | hterminal)
    · exact prefix_dense_yes H fB fC NB NC (μ free).toNat F aux le_rfl hp hg hsep hF hdense
    · exact (original_zero_iff_emitted_terminal H hh hp hK).mpr
        ((hit_exists_iff H fB fC NB NC K).mp hterminal)
  · intro hzero
    exact Or.inr ((hit_exists_iff H fB fC NB NC K).mpr
      ((original_zero_iff_emitted_terminal H hh hp hK).mp hzero))




















end Actual

end ThreeSum.ReportingHostWantedDecision

end

section


/-! # Physical mass limits from the retained selected color

The positive common modulus, its guard, every physical incidence count,
and both original sorted-source lengths come from the executed pipeline.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales BandRawA RawReporting GlobalEncoding
open ReportingHostFrontierLayout ReportingHostWantedOriginal
open EncodedColorNormalizedData EncodedColorWantedConsumerData

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}











theorem wanted_selected_guard (hR : 4≤radix n) :
    4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (half n) (blocks n) := by
  have hh : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤(radix n : ℤ) := by
    exact_mod_cast EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
      (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  simpa only [globalModulus,Scales.radix,Scales.localRadix,half,blocks,Nat.cast_pow] using hh



































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Uniform size conditions and original-color semantics for the wanted consumer

The cutoff is chosen before any memory, color, or original array. The
auxiliary-prime separation premise is proved for the actual generated pool.
-/

namespace ThreeSum.ThreeSumWantedHostConditions

open Light Scales BandScales Filter RawIncidences BandRawA ColorClassLists
open scoped Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000































theorem original_zero_iff_witness {μ : ℕ→ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    OriginalZero n A B C hsA hsB hsC ↔ ColorClassLists.witness color x := by
  rw [← finite_color_iff color x (bandSize_pos n) hsA hsB hsC
    H.normalized.2.1.2.2.1 H.normalized.2.2.1.2.2.1 H.normalized.2.2.2.1.2.2.1]
  unfold OriginalZero finiteEquation
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  dsimp only [difference]
  constructor <;> intro he <;> omega







































end ThreeSum.ThreeSumWantedHostConditions

end

section


/-!
# The physical whole-scan decision is exactly an original color witness

The concrete threshold is the retained weighted false score, and the
auxiliary pool separates every original difference in the uniform size
regime. No input-dependent primality or correctness premise is added.
-/

namespace ThreeSum.ThreeSumWantedHostDecision

open Light Scales BandScales BandRawA RawIncidences RawReporting
open ReportingHostWantedConsumerData ThreeSumWantedHostData
open ThreeSumWantedHostConditions SharedReportingBankResourceBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

theorem accepted_iff_witness_sourceProof {μ : ℕ→ℤ} {free n k : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : Ready k n) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    LightReportingWantedScan.Accepted (mass H) (hit H)
      (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC) ↔
        ColorClassLists.witness color x := by
  have hh := ReportingHostWantedDecision.accepted_iff_original H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length
    (LightSwitchDepth.depth (blocks n)) (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC)
    (DenseGuard.actualAux n) hn.half
    (by change 13*blockCount (inputBits n)/20≤blockCount (inputBits n); omega)
    EncodedColorPrimeReadyData.selected_pos (wanted_selected_guard hn.radix)
    (actual_separation H hn hx) (le_refl _)
  change LightReportingWantedScan.Accepted (mass H) (hit H)
      (threshold n A B C hsA hsB hsC)
      (μ (EncodedColorPipelineData.wantedHeader free n
        (EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)).toNat ↔
        OriginalZero n A B C hsA hsB hsC at hh
  rw [count_read H,Int.toNat_natCast] at hh
  exact hh.trans (original_zero_iff_witness H)

end ThreeSum.ThreeSumWantedHostDecision

end


theorem solution : ∀ {μ : Nat → Int} {free n k : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC),
  ThreeSum.ThreeSumWantedHostConditions.Ready k n →
    (∀ (i : Fin n),
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
          (@Nat.cast.{0} Int instNatCastInt
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n k))) →
      Iff
        (ThreeSum.LightReportingWantedScan.Accepted
          (@ThreeSum.ReportingHostWantedConsumerData.mass μ free n color x A B C hsA hsB hsC H)
          (@ThreeSum.ReportingHostWantedConsumerData.hit μ free n color x A B C hsA hsB hsC H)
          (ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
          (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC))
        (@ThreeSum.ColorClassLists.witness n
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          color x) := by
  exact @ThreeSum.ThreeSumWantedHostDecision.accepted_iff_witness_sourceProof

#print axioms solution
