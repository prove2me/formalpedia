-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.cover_frequency
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:16:33.949044+00:00
-- url     : https://prove2.me/submissions/73eeed9a-4726-4cb7-b91d-f4b8e06f7f09

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
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
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Cover_trimmed_support_lower
import Theorems.Thm_ThreeSum_HashFamily_badPartners_card_le
import Theorems.Thm_ThreeSum_HashFamily_raw_second_moment_five
import Theorems.Thm_ThreeSum_HashFamily_trimmedPairEvent_bound
import Theorems.Thm_ThreeSum_LayerCounts_edgeSet_card
import Theorems.Thm_ThreeSum_LayerCounts_leftFiber_card
import Theorems.Thm_ThreeSum_LayerCounts_rightFiber_card
import Theorems.Thm_ThreeSum_LayerCounts_unionFiber_card
import Theorems.Thm_ThreeSum_LocalCoverBounds_mean_lower


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph

section


/-!
# Finite cover bounds

Finite, exact lemmas for the second-moment argument, deterministic averaging,
and composition used in the proposed construction.  A hypothesis about a
particular local hash family is a mathematical obligation, not an asserted
implementation or running-time theorem.
-/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators














































/-- The explicit 1/(320(mu+1)) support fraction used for a microblock. -/
theorem trimmed_support_fraction {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (mu : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hlower : 1 ≤ 16 * (mu + 1 : ℝ) * lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    (Fintype.card Ω : ℝ) ≤
      320 * (mu + 1 : ℝ) * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by
  classical
  have h := trimmed_support_lower f hlam hfirst hsecond
  have h₁ := mul_le_mul_of_nonneg_right hlower
    (show (0 : ℝ) ≤ Fintype.card Ω by positivity)
  have h₂ := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ 16 * (mu + 1 : ℝ) by positivity)
  nlinarith




































end ThreeSum.Cover

end

section


/-!
# The actual one-hot hash family

This file develops the dependence classification of the binary one-hot hash
vectors used in the local cover. Hash weights are independent field elements
at coordinate/symbol pairs. The independence statements concern this concrete
family, not an assumed random oracle.
-/

namespace ThreeSum.HashFamily

open scoped BigOperators

variable {α K : Type*}











section Relations

variable [Ring K]



























































end Relations

section LinearIndependence

variable [Field K]

































end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]































































end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]
















end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]












































































































































end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]





theorem incidenceCount_eq_sum (events : E → Finset Ω) (w : Ω) :
    incidenceCount events w = ∑ e, if w ∈ events e then (1 : ℕ) else 0 := by
  unfold incidenceCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_incidenceCount (events : E → Finset Ω) :
    (∑ w, incidenceCount events w) = ∑ e, (events e).card := by
  simp only [incidenceCount_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp

theorem incidenceCount_mono {events events' : E → Finset Ω}
    (h : ∀ e, events e ⊆ events' e) (w : Ω) :
    incidenceCount events w ≤ incidenceCount events' w := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h e (Finset.mem_filter.mp he).2⟩
































end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]






















































































































































end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]















































































































theorem trimmedPairEvent_subset (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    trimmedPairEvent s t a b leftVertices rightVertices B ⊆ pairEvent s t a b :=
  Finset.filter_subset ..


































end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem trimmed_first_moment (left right : E → α → Bool)
    (hcross : ∀ e f, left e ≠ right f) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool))
    (hL : ∀ e u, u ∈ leftVertices → u ≠ right e)
    (hR : ∀ e u, u ∈ rightVertices → u ≠ left e)
    (B : ℕ)
    (hBL : 4 * (Fintype.card K + leftVertices.card) ≤ B * Fintype.card K)
    (hBR : 4 * (Fintype.card K + rightVertices.card) ≤ B * Fintype.card K) :
    Fintype.card E * Fintype.card (α × Bool → K) ≤
      2 * Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices B) w) := by
  rw [sum_incidenceCount, Finset.mul_sum]
  calc
    _ = ∑ _e : E, Fintype.card (α × Bool → K) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun e he =>
      trimmedPairEvent_bound (hcross e e) a b leftVertices rightVertices (hL e) (hR e) B hBL hBR)

theorem trimmed_second_moment (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (Bbad : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ Bbad)
    (hBp : Bbad ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) (leftVertices rightVertices : Finset (α → Bool)) (Bbucket : ℕ) :
    Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices Bbucket) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  refine (Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun w hw => ?_))).trans
    (raw_second_moment_five left right hinj hcross Bbad hB hBp hEp a b)
  exact Nat.pow_le_pow_left (incidenceCount_mono
    (fun e => trimmedPairEvent_subset (left e) (right e) a b leftVertices rightVertices Bbucket) w) 2

end TrimmedGraphMoments

end ThreeSum.HashFamily

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











theorem vertices_card (L h : ℕ) : (vertices L h).card = L.choose h := by
  simp [vertices, card_powersetCard]


































































































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

































































































theorem mean_positive {L h p : ℕ} (hL : 2 * h ≤ L) (hp : 0 < p) :
    0 < mean L h p := by
  have hM : 0 < outputCount L h := Nat.choose_pos hL
  have hG : 0 < groupSize h := Nat.choose_pos (by omega)
  unfold mean
  positivity




























/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/







theorem bucketCap_le_iff {V p b : ℕ} (hp : 0 < p) :
    bucketCap V p ≤ b ↔ 4 * (p + V) ≤ b * p := by
  simpa only [bucketCap, Nat.mul_comm] using
    (ceilDiv_le_iff_le_mul (b := 4 * (p + V)) (c := b) hp)

theorem bucketCap_threshold {V p : ℕ} (hp : 0 < p) :
    4 * (p + V) ≤ bucketCap V p * p :=
  (bucketCap_le_iff hp).mp le_rfl
















/-! ## The actual local parameters at `L=512*h` -/





























































end ThreeSum.LocalCoverBounds

end

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

theorem leftWord_eq_rightWord_iff [Fintype α] (s v : Finset α) :
    leftWord s = rightWord v ↔ s = Finset.univ \ v := by
  constructor
  · intro he
    ext i
    have hi := congrFun he i
    simpa only [leftWord, rightWord, decide_eq_decide, Finset.mem_sdiff,
      Finset.mem_univ, true_and] using hi
  · intro he
    subst s
    funext i
    simp only [leftWord, rightWord, Finset.mem_sdiff, Finset.mem_univ, true_and]

/-- With `2*h<L`, no left vertex word can equal any right vertex word, even
when the two vertices do not form an edge. -/
theorem leftWord_ne_rightWord {L h : ℕ} {s v : Finset (Fin L)}
    (hs : s.card = h) (hv : v.card = h) (hsep : 2 * h < L) :
    leftWord s ≠ rightWord v := by
  intro he
  have hc := congrArg Finset.card ((leftWord_eq_rightWord_iff s v).mp he)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ v)] at hc
  simp only [Finset.card_univ, Fintype.card_fin, hs, hv] at hc
  omega

/-- The equality mask is true exactly on the union of the disjoint endpoint
subsets. This identifies the exceptional four-word hash fibers. -/
theorem equalityMask_eq_union {s v : Finset α} (hd : Disjoint s v) :
    (fun i => leftWord s i == rightWord v i) = leftWord (s ∪ v) := by
  funext i
  have hnot := Finset.disjoint_left.mp hd
  by_cases hs : i ∈ s <;> by_cases hv : i ∈ v <;>
    simp_all [leftWord, rightWord]








section ConcreteGraph

open LayerCounts




variable {L h : ℕ}


















theorem endpoint_injective :
    Function.Injective (fun e : Edge L h => (left e, right e)) := by
  intro e f he
  apply Subtype.ext
  exact Prod.ext (leftWord_injective (congrArg Prod.fst he))
    (rightWord_injective (congrArg Prod.snd he))

theorem cross_separated (hsep : 2 * h < L) (e f : Edge L h) : left e ≠ right f :=
  leftWord_ne_rightWord (edge_data e).1 (edge_data f).2.1 hsep

theorem equalityMask_eq_output (e : Edge L h) :
    equalityMask e = leftWord (output e) :=
  equalityMask_eq_union (edge_data e).2.2

theorem equalityMask_eq_iff (e f : Edge L h) :
    equalityMask e = equalityMask f ↔ output e = output f := by
  rw [equalityMask_eq_output, equalityMask_eq_output]
  exact leftWord_injective.eq_iff







theorem leftVertices_card (L h : ℕ) : (leftVertices L h).card = L.choose h := by
  rw [leftVertices, Finset.card_image_of_injective _ leftWord_injective, vertices_card]

theorem rightVertices_card (L h : ℕ) : (rightVertices L h).card = L.choose h := by
  rw [rightVertices, Finset.card_image_of_injective _ rightWord_injective, vertices_card]

theorem left_mem_vertices (e : Edge L h) : left e ∈ leftVertices L h :=
  Finset.mem_image.mpr ⟨e.val.1, mem_vertices.mpr (edge_data e).1, rfl⟩

theorem right_mem_vertices (e : Edge L h) : right e ∈ rightVertices L h :=
  Finset.mem_image.mpr ⟨e.val.2, mem_vertices.mpr (edge_data e).2.1, rfl⟩

theorem vertex_sets_separated (hsep : 2 * h < L)
    (s : Fin L → Bool) (hs : s ∈ leftVertices L h)
    (t : Fin L → Bool) (ht : t ∈ rightVertices L h) : s ≠ t := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp ht
  exact leftWord_ne_rightWord (mem_vertices.mp hS) (mem_vertices.mp hV) hsep

/-- Transfer counts in a finite subtype to counts in its actual enumerated
domain. This lemma introduces no larger sample space. -/
theorem subtype_filter_card {β : Type*} [DecidableEq β] (s : Finset β)
    (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun e : s => p e.val)).card = (s.filter p).card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨e.property, (Finset.mem_filter.mp he).2⟩
  · intro e _ f _ he
    exact Subtype.ext he
  · intro x hx
    refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

theorem edge_card (L h : ℕ) :
    Fintype.card (Edge L h) = L.choose (2 * h) * (2 * h).choose h := by
  rw [Fintype.card_coe, edgeSet_card]

/-- Every endpoint has exactly the combinatorial degree, expressed on the
edge subtype used by the finite hash experiment. -/
theorem left_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card =
      (L - h).choose h := by
  simp only [left, leftWord_injective.eq_iff]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.1 = e.val.1)).trans
    (leftFiber_card e.val.1 (edge_data e).1)

theorem right_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => right f = right e)).card =
      (L - h).choose h := by
  simp only [right, rightWord_injective.eq_iff]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.2 = e.val.2)).trans
    (rightFiber_card e.val.2 (edge_data e).2.1)

/-- The exceptional equality-mask group has exactly one edge for each
`h`-subset of its `2*h` output coordinates. -/
theorem equalityMask_fiber_card (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => equalityMask f = equalityMask e)).card =
      (2 * h).choose h := by
  simp only [equalityMask_eq_iff, output]
  exact (subtype_filter_card (edgeSet L h) (fun p => p.1 ∪ p.2 = e.val.1 ∪ e.val.2)).trans
    (unionFiber_card (output e) (output_card e))

theorem endpoint_fiber_bounds (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h => left f = left e)).card ≤
        (L - h).choose h ∧
      (Finset.univ.filter (fun f : Edge L h => right f = right e)).card ≤
        (L - h).choose h := by
  exact ⟨(left_fiber_card e).le, (right_fiber_card e).le⟩

theorem mask_fiber_bound (e : Edge L h) :
    (Finset.univ.filter (fun f : Edge L h =>
      (fun i => left f i == right f i) = (fun i => left e i == right e i))).card ≤
      (2 * h).choose h :=
  (equalityMask_fiber_card e).le

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






theorem bucketBound_threshold (L h p : ℕ) (hp : 0 < p) :
    4 * (p + vertexCount L h) ≤ bucketBound L h p * p := by
  exact bucketCap_threshold hp














theorem bad_partner_bound (e : Edge L h) :
    (HashFamily.badPartners left right e).card ≤ 2 * degree L h + groupSize h := by
  apply HashFamily.badPartners_card_le
  · simpa only [eq_comm, degree] using (endpoint_fiber_bounds e).1
  · simpa only [eq_comm, degree] using (endpoint_fiber_bounds e).2
  · change (univ.filter (fun f : Edge L h =>
      (fun i => left e i == right e i) = (fun i => left f i == right f i))).card ≤
      (2 * h).choose h
    simpa only [eq_comm] using mask_fiber_bound e

theorem first_moment (hsep : 2 * h < L) (target : K × K) :
    Fintype.card (Edge L h) * Fintype.card (Weight L K) ≤
      2 * Fintype.card K ^ 2 *
        ∑ w, hitCount L h (bucketBound L h (Fintype.card K)) w target := by
  apply HashFamily.trimmed_first_moment left right (cross_separated hsep)
  · intro e u hu
    exact vertex_sets_separated hsep u hu (right e) (right_mem_vertices e)
  · intro e u hu
    exact Ne.symm (vertex_sets_separated hsep (left e) (left_mem_vertices e) u hu)
  · simpa only [leftVertices_card, vertexCount] using
      bucketBound_threshold L h (Fintype.card K) Fintype.card_pos
  · simpa only [rightVertices_card, vertexCount] using
      bucketBound_threshold L h (Fintype.card K) Fintype.card_pos

theorem second_moment (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    Fintype.card K ^ 2 * (∑ w, hitCount L h B w target ^ 2) ≤
      5 * Fintype.card (Edge L h) * Fintype.card (Weight L K) := by
  apply HashFamily.trimmed_second_moment left right endpoint_injective
    (cross_separated hsep) (2 * degree L h + groupSize h) bad_partner_bound
  · omega
  · simpa only [edge_card, outputCount, groupSize] using hE

theorem first_moment_real (hsep : 2 * h < L) (target : K × K) :
    mean L h (Fintype.card K) * Fintype.card (Weight L K) / 2 ≤
      ∑ w, (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) := by
  have hm := first_moment (K := K) hsep target
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card (Edge L h) : ℝ) =
      (outputCount L h : ℝ) * groupSize h := by
    exact_mod_cast edge_card L h
  have hmR : (Fintype.card (Edge L h) : ℝ) * Fintype.card (Weight L K) ≤
      2 * (Fintype.card K : ℝ) ^ 2 *
        ∑ w, (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) := by
    exact_mod_cast hm
  rw [he] at hmR
  unfold mean
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hp 2)).mpr
  nlinarith

theorem second_moment_real (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    (∑ w, (hitCount L h B w target : ℝ) ^ 2) ≤
      5 * mean L h (Fintype.card K) * Fintype.card (Weight L K) := by
  have hm := second_moment (K := K) hsep hDelta hG hE target B
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hmR : (Fintype.card K : ℝ) ^ 2 *
        (∑ w, (hitCount L h B w target : ℝ) ^ 2) ≤
      5 * (Fintype.card (Edge L h) : ℝ) * Fintype.card (Weight L K) := by
    exact_mod_cast hm
  have he : (Fintype.card (Edge L h) : ℝ) =
      (outputCount L h : ℝ) * groupSize h := by
    exact_mod_cast edge_card L h
  rw [he] at hmR
  calc
    _ ≤ (5 * ((outputCount L h : ℝ) * groupSize h) *
        Fintype.card (Weight L K)) / (Fintype.card K : ℝ) ^ 2 := by
      apply (le_div_iff₀ (pow_pos hp 2)).mpr
      nlinarith
    _ = _ := by unfold mean; ring

/-- Every target is covered by a polynomial fraction of the actual weight
assignments. All probabilistic premises are discharged by counting the
one-hot hashes on the concrete graph. -/
theorem cover_frequency_sourceProof (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    Fintype.card (Weight L K) ≤ 320 * (2 * h + 1) *
      (univ.filter fun w => Covers L h (bucketBound L h (Fintype.card K)) w target).card := by
  have hl := mean_lower (Nat.le_of_lt hsep) (p := Fintype.card K)
    Fintype.card_pos hupper
  have hm : 0 < mean L h (Fintype.card K) :=
    mean_positive (Nat.le_of_lt hsep) Fintype.card_pos
  have hscale : 1 ≤ 16 * (2 * h + 1 : ℝ) * mean L h (Fintype.card K) := by
    have hd : (0 : ℝ) < 16 * (2 * (h : ℝ) + 1) := by positivity
    have ht := (div_le_iff₀ hd).mp hl
    nlinarith
  have hs := Cover.trimmed_support_fraction
    (fun w => (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ))
    (2 * h) hm (by simpa using hscale)
    (first_moment_real hsep target)
    (second_moment_real hsep hDelta hG hE target _)
  have hf : (univ.filter fun w =>
      (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) ≠ 0) =
      (univ.filter fun w => Covers L h (bucketBound L h (Fintype.card K)) w target) := by
    apply Finset.filter_congr
    intro w hw
    change (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) ≠ 0 ↔
      hitCount L h (bucketBound L h (Fintype.card K)) w target ≠ 0
    exact Nat.cast_ne_zero
  rw [hf] at hs
  exact_mod_cast hs






































































































/-! ## The selected local prime and its actual finite schedule -/




































































end ThreeSum.LocalHashMoments

end

universe u_1

theorem solution : ∀ {K : Type u_1} [inst : Field.{u_1} K] [inst_1 : Fintype.{u_1} K] [inst_2 : DecidableEq.{u_1 + 1} K] {L h : Nat},
  @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
      L →
    @LE.le.{0} Nat instLENat (ThreeSum.LocalCoverBounds.degree L h) (@Fintype.card.{u_1} K inst_1) →
      @LE.le.{0} Nat instLENat (ThreeSum.LocalCoverBounds.groupSize h) (@Fintype.card.{u_1} K inst_1) →
        @LE.le.{0} Nat instLENat
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LocalCoverBounds.outputCount L h)
              (ThreeSum.LocalCoverBounds.groupSize h))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@Fintype.card.{u_1} K inst_1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LE.le.{0} Nat instLENat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@Fintype.card.{u_1} K inst_1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (ThreeSum.LocalCoverBounds.outputCount L h)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))) →
            ∀ (target : Prod.{u_1, u_1} K K),
              @LE.le.{0} Nat instLENat
                (@Fintype.card.{u_1} (ThreeSum.LocalHashMoments.Weight.{u_1} L K)
                  (@Pi.instFintype.{0, u_1} (Prod.{0, 0} (Fin L) Bool) (fun (a : Prod.{0, 0} (Fin L) Bool) => K)
                    (fun (a b : Prod.{0, 0} (Fin L) Bool) =>
                      @instDecidableEqProd.{0, 0} (Fin L) Bool (instDecidableEqFin L) instDecidableEqBool a b)
                    (@instFintypeProd.{0, 0} (Fin L) Bool (Fin.fintype L) Bool.fintype)
                    fun (a : Prod.{0, 0} (Fin L) Bool) => inst_1))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Finset.card.{u_1} (ThreeSum.LocalHashMoments.Weight.{u_1} L K)
                    {w : ThreeSum.LocalHashMoments.Weight.{u_1} L K |
                      @ThreeSum.LocalHashMoments.Covers.{u_1} K inst inst_1 inst_2 L h
                        (ThreeSum.LocalHashMoments.bucketBound L h (@Fintype.card.{u_1} K inst_1)) w target})) := by
  exact @ThreeSum.LocalHashMoments.cover_frequency_sourceProof

#print axioms solution
