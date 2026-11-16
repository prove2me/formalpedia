-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.chain_separation_probability
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T17:01:31.62674+00:00
-- url     : https://prove2.me/submissions/3eddf90b-9798-47de-8278-6c10ba789757

import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- Source: complexity-labelcut/ProductProbability.lean
section
set_option autoImplicit false
open scoped BigOperators

namespace LabelCutCounting

variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]

lemma product_card (s : ι → Finset Ω) :
    (Finset.univ.filter (fun f : ι → Ω => ∀ i, f i ∈ s i)).card =
      ∏ i, (s i).card := by
  classical
  have heq : Finset.univ.filter (fun f : ι → Ω => ∀ i, f i ∈ s i) =
      Fintype.piFinset s := by
    ext f
    simp
  rw [heq, Fintype.card_piFinset]

lemma product_probability (s : ι → Finset Ω) :
    ((Finset.univ.filter (fun f : ι → Ω => ∀ i, f i ∈ s i)).card : ℝ) /
        Fintype.card (ι → Ω) =
      ∏ i, ((s i).card : ℝ) / Fintype.card Ω := by
  simp [product_card, Finset.prod_div_distrib]

lemma product_probability_le [Nonempty Ω] (s : ι → Finset Ω) (active : Finset ι)
    (q : ℝ)
    (hs : ∀ i ∈ active, ((s i).card : ℝ) / Fintype.card Ω ≤ q) :
    ((Finset.univ.filter (fun f : ι → Ω => ∀ i, f i ∈ s i)).card : ℝ) /
        Fintype.card (ι → Ω) ≤ q ^ active.card := by
  rw [product_probability]
  refine le_trans (b := ∏ i : ι, if i ∈ active then q else 1) ?_ ?_
  · apply Finset.prod_le_prod
    · exact fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro i _
      by_cases hi : i ∈ active
      · simpa only [if_pos hi] using hs i hi
      · simpa only [if_neg hi] using
          (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
            (Nat.cast_le.mpr (Finset.card_le_univ (s i)))
  · simp

omit [DecidableEq ι] in
lemma union_probability_le [Nonempty Ω] (s : ι → Finset Ω) (q : ℝ)
    (hs : ∀ i, ((s i).card : ℝ) / Fintype.card Ω ≤ q) :
    ((Finset.univ.biUnion s).card : ℝ) / Fintype.card Ω ≤ Fintype.card ι * q := by
  have hc : ((Finset.univ.biUnion s).card : ℝ) ≤ ∑ i, ((s i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  refine (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)).trans ?_
  simpa only [Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hs i)

end LabelCutCounting
end

-- Source: complexity-labelcut-graph/Connectivity.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2.Graph

/-- Layer coordinate used to prove the constructed route has no repeated vertex. -/
def level {k h : ℕ} (d : ℕ) : ShutterVertex k d h → ℕ
  | .inl false => 0
  | .inl true => 2 * d
  | .inr (_, .inl j) => 2 * (j.val + 1)
  | .inr (_, .inr (j, _)) => 2 * j.val + 1

lemma level_junction {k d h : ℕ} (c : Chain k h) (j : Fin (d + 1)) :
    level d (junction c j) = 2 * j.val := by
  unfold junction
  split_ifs with h0 hd
  all_goals simp_all [level]
  omega

def routeVertex {k d h : ℕ} (c : Chain k h) (b : Fin d → Bool)
    (r : Fin (2 * d + 1)) : ShutterVertex k d h :=
  if he : r.val % 2 = 0 then junction c ⟨r.val / 2, by omega⟩
  else let j : Fin d := ⟨r.val / 2, by omega⟩; middle c j (b j)

def routeEdge {k d h : ℕ} (c : Chain k h) (b : Fin d → Bool)
    (r : Fin (2 * d)) : ShutterEdge k d h :=
  let j : Fin d := ⟨r.val / 2, by omega⟩
  (c, j, b j, decide (r.val % 2 = 1))

lemma level_routeVertex {k d h : ℕ} (c : Chain k h) (b : Fin d → Bool)
    (r : Fin (2 * d + 1)) : level d (routeVertex c b r) = r.val := by
  unfold routeVertex
  split_ifs with he
  · rw [level_junction]
    change 2 * (r.val / 2) = r.val
    omega
  · change 2 * (r.val / 2) + 1 = r.val
    omega

theorem routeVertex_injective {k d h : ℕ} (c : Chain k h) (b : Fin d → Bool) :
    Function.Injective (routeVertex c b) :=
  fun r s heq => Fin.ext ((level_routeVertex c b r).symm.trans
    ((congrArg (level d) heq).trans (level_routeVertex c b s)))

lemma route_tail {k d h : ℕ} (c : Chain k h) (b : Fin d → Bool) (r : Fin (2 * d)) :
    shutterTail (routeEdge c b r) = routeVertex c b r.castSucc := by
  rcases Nat.mod_two_eq_zero_or_one r.val with he | he
  all_goals simp [routeEdge, routeVertex, shutterTail, he]

lemma route_head {k d h : ℕ} (c : Chain k h) (b : Fin d → Bool) (r : Fin (2 * d)) :
    shutterHead (routeEdge c b r) = routeVertex c b r.succ := by
  rcases Nat.mod_two_eq_zero_or_one r.val with he | he
  · simp [routeEdge, routeVertex, shutterHead, he,
      show (r.val + 1) % 2 = 1 by omega,
      show (r.val + 1) / 2 = r.val / 2 by omega]
  · simp [routeEdge, routeVertex, shutterHead, he,
      show (r.val + 1) % 2 = 0 by omega,
      show (r.val + 1) / 2 = r.val / 2 + 1 by omega]

/-- Choose one unbroken two-edge route in every diamond of one chain. -/
def chainPath {k d h : ℕ} (hd : 0 < d) (c : Chain k h) (b : Fin d → Bool)
    (directed : Bool) : Path (shutterGraph k d h directed) (Sum.inl false) (Sum.inl true) where
  length := 2 * d
  vertex := routeVertex c b
  edge := routeEdge c b
  start := by
    simp [routeVertex, junction]
    rfl
  finish := by
    simp [routeVertex, junction, Nat.ne_of_gt hd]
    rfl
  simple := routeVertex_injective c b
  step r := Or.inl ⟨route_tail c b r, route_head c b r⟩

/-- If one of the two labels in every diamond survives, this chain has a surviving simple path. -/
theorem surviving_chain_path {k d h : ℕ} (hd : 0 < d) (directed : Bool)
    (σ : Sample k d h) (S : Finset (Fin k × Fin d)) (c : Chain k h)
    (hfree : ∀ j : Fin d, (c.1.val.1, j) ∉ S ∨ (c.1.val.2, σ c j) ∉ S) :
    ∃ p : Path (shutterInstance k d h directed σ).graph
        (shutterInstance k d h directed σ).s (shutterInstance k d h directed σ).t,
      (∀ r, (p.edge r).1 = c) ∧
      ∀ r, (shutterInstance k d h directed σ).label (p.edge r) ∉ S := by
  classical
  let b : Fin d → Bool := fun j => decide ((c.1.val.1, j) ∈ S)
  refine ⟨chainPath hd c b directed, ?_, ?_⟩
  · intro r
    rfl
  · intro r
    let j : Fin d := ⟨r.val / 2, by have hr : r.val < 2 * d := r.isLt; omega⟩
    change (if b j then (c.1.val.2, σ c j) else (c.1.val.1, j)) ∉ S
    by_cases hl : (c.1.val.1, j) ∈ S
    · simpa [b, hl] using hfree j
    · simp [b, hl]

end ZhangTangLabelCut.LP2.Graph
end

-- Source: complexity-labelcut-graph/Simple.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2.Graph

lemma junction_ne_middle {k d h : ℕ} (c c' : Chain k h) (j : Fin (d + 1))
    (j' : Fin d) (b : Bool) : junction c j ≠ middle c' j' b := by
  unfold junction middle
  split_ifs <;> simp

end ZhangTangLabelCut.LP2.Graph
end

-- Source: complexity-labelcut/Structure.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2.Graph

lemma level_middle {k d h : ℕ} (c : Chain k h) (j : Fin d) (b : Bool) :
    level d (middle c j b) = 2 * j.val + 1 := rfl

lemma level_edge {k d h : ℕ} (e : ShutterEdge k d h) :
    level d (shutterHead e) = level d (shutterTail e) + 1 := by
  rcases e with ⟨c, j, b, f⟩
  cases f <;> simp [shutterHead, shutterTail, level_middle, level_junction,
    Nat.mul_add, Nat.add_assoc]

end ZhangTangLabelCut.LP2.Graph
end

-- Source: complexity-labelcut-graph/ChainCut.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2.Graph

/-- Separating a chain requires deleting both labels of at least one diamond. -/
theorem chainSeparated_imp_hit {k d h : ℕ} (hd : 0 < d) (directed : Bool)
    (S : Finset (Fin k × Fin d)) (c : Chain k h) (σ : Sample k d h)
    (hcut : chainSeparated directed S c σ) :
    ∃ j : Fin d, (c.1.val.1, j) ∈ S ∧ (c.1.val.2, σ c j) ∈ S := by
  by_contra hn
  have hfree : ∀ j : Fin d, (c.1.val.1, j) ∉ S ∨ (c.1.val.2, σ c j) ∉ S := by
    simpa only [not_exists, not_and_or] using hn
  obtain ⟨p, hpc, hpl⟩ := surviving_chain_path hd directed σ S c hfree
  exact Exists.elim (hcut p hpc) (fun r hr => hpl r hr)

theorem good_imp_chainSeparated {k d h : ℕ} (directed : Bool)
    (S : Finset (Fin k × Fin d)) (σ : Sample k d h) (c : Chain k h)
    (hleft : c.1.val.1 ∈ light S) (hright : c.1.val.2 ∈ light S)
    (hgood : good directed S σ) : chainSeparated directed (configuration S) c σ :=
  fun p hp => hgood p (fun r => by simpa only [hp r] using And.intro hleft hright)

theorem cut_imp_chainSeparated {k d h : ℕ} (directed : Bool)
    (S : Finset (Fin k × Fin d)) (σ : Sample k d h) (c : Chain k h)
    (hcut : (shutterInstance k d h directed σ).Cut S) : chainSeparated directed S c σ :=
  fun p _ => hcut p

end ZhangTangLabelCut.LP2.Graph
end

-- Source: complexity-labelcut-probability/Permutation.lean
section
set_option autoImplicit false
open scoped BigOperators

namespace LabelCutProbability

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Transposing two output values gives equal evaluation fibers. -/
theorem permutation_fiber_card_eq (i j k : α) :
    (Finset.univ.filter (fun π : Equiv.Perm α => π i = j)).card =
      (Finset.univ.filter (fun π : Equiv.Perm α => π i = k)).card := by
  classical
  let e : {π : Equiv.Perm α // π i = j} ≃ {π : Equiv.Perm α // π i = k} := {
    toFun := fun π => ⟨π.val.trans (Equiv.swap j k), by simp [π.property]⟩
    invFun := fun π => ⟨π.val.trans (Equiv.swap j k), by simp [π.property]⟩
    left_inv := by intro π; apply Subtype.ext; ext a; simp
    right_inv := by intro π; apply Subtype.ext; ext a; simp }
  simpa only [Fintype.card_subtype] using Fintype.card_congr e

/-- The evaluation preimage of a set is its size times one point fiber. -/
theorem permutation_eval_mem_card (i : α) (B : Finset α) :
    (Finset.univ.filter (fun π : Equiv.Perm α => π i ∈ B)).card =
      B.card * (Finset.univ.filter (fun π : Equiv.Perm α => π i = i)).card := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ B (fun π : Equiv.Perm α => π i)]
  calc
    _ = ∑ _ ∈ B, (Finset.univ.filter (fun π : Equiv.Perm α => π i = i)).card := by
      apply Finset.sum_congr rfl
      intro j hj
      exact permutation_fiber_card_eq i j i
    _ = _ := by simp

/-- Point fibers partition all permutations. -/
theorem permutation_eval_total_card (i : α) :
    Fintype.card (Equiv.Perm α) =
      Fintype.card α * (Finset.univ.filter (fun π : Equiv.Perm α => π i = i)).card := by
  classical
  simpa using permutation_eval_mem_card i (Finset.univ : Finset α)

/-- Finite union bound with the exact uniform-permutation normalization. -/
theorem permutation_hit_card_bound (A B : Finset α) :
    Fintype.card α * (Finset.univ.filter
      (fun π : Equiv.Perm α => ∃ i ∈ A, π i ∈ B)).card ≤
      A.card * B.card * Fintype.card (Equiv.Perm α) := by
  classical
  have heq : (Finset.univ.filter (fun π : Equiv.Perm α => ∃ i ∈ A, π i ∈ B)) =
      A.biUnion (fun i => Finset.univ.filter (fun π : Equiv.Perm α => π i ∈ B)) := by
    ext π
    simp
  have hu := Finset.card_biUnion_le (s := A)
    (t := fun i => Finset.univ.filter (fun π : Equiv.Perm α => π i ∈ B))
  rw [← heq] at hu
  calc
    _ ≤ Fintype.card α * (∑ i ∈ A, (Finset.univ.filter (fun π : Equiv.Perm α => π i ∈ B)).card) :=
      Nat.mul_le_mul_left _ hu
    _ = ∑ i ∈ A, Fintype.card α * (Finset.univ.filter (fun π : Equiv.Perm α => π i ∈ B)).card := by
      rw [Finset.mul_sum]
    _ = ∑ _ ∈ A, B.card * Fintype.card (Equiv.Perm α) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [permutation_eval_mem_card]
      calc
        _ = B.card * (Fintype.card α * (Finset.univ.filter (fun π : Equiv.Perm α => π i = i)).card) := by ac_rfl
        _ = _ := by rw [← permutation_eval_total_card i]
    _ = _ := by simp [Nat.mul_assoc]

/-- A uniform random permutation maps one selected set into the other with
probability at most the product of their cardinalities divided by the universe size. -/
theorem permutation_hit_probability_bound (A B : Finset α) (hd : 0 < Fintype.card α) :
    ((Finset.univ.filter (fun π : Equiv.Perm α => ∃ i ∈ A, π i ∈ B)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ (A.card : ℝ) * B.card / Fintype.card α := by
  classical
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm α) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty (Equiv.Perm α) from ⟨Equiv.refl α⟩))
  have hdr : (0 : ℝ) < Fintype.card α := by exact_mod_cast hd
  apply (div_le_div_iff₀ hp hdr).2
  rw [mul_comm ((Finset.univ.filter (fun π : Equiv.Perm α => ∃ i ∈ A, π i ∈ B)).card : ℝ)]
  exact_mod_cast permutation_hit_card_bound A B

end LabelCutProbability
end

-- Source: complexity-labelcut-probability/ChainBound.lean
section
set_option autoImplicit false
open scoped BigOperators
open ZhangTangLabelCut.LP2

namespace LabelCutProbability

/-- Restricting a candidate set to one ground element gives exactly its row count. -/
theorem row_card {k d : ℕ} (S : Finset (Fin k × Fin d)) (μ : Fin k) :
    (Finset.univ.filter (fun j : Fin d => (μ, j) ∈ S)).card = counts S μ := by
  classical
  unfold counts
  refine Finset.card_bij (fun j _ => (μ, j)) ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩
  · intro i hi j hj hij
    exact (Prod.mk.inj hij).2
  · rintro ⟨ν, j⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hν⟩
    dsimp at hν
    subst ν
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩

theorem light_row_card_le {k d : ℕ} (S : Finset (Fin k × Fin d)) (μ : Fin k)
    (hμ : μ ∈ light S) :
    ((Finset.univ.filter (fun j : Fin d => (μ, j) ∈ S)).card : ℝ) ≤
      4 * average k S.card := by
  classical
  rw [row_card]
  simpa only [light, Finset.mem_filter, Finset.mem_univ, true_and] using hμ

/-- The direct half bound at the construction's exact dimension. -/
theorem permutation_hit_half_bound {d : ℕ} (A B : Finset (Fin d)) (a : ℝ)
    (ha : 0 < a) (hA : (A.card : ℝ) ≤ 4 * a) (hB : (B.card : ℝ) ≤ 4 * a)
    (hd : (d : ℝ) = 32 * a^2) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin d) => ∃ i ∈ A, π i ∈ B)).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin d)) ≤ 1 / 2 := by
  have hdpos : (0 : ℝ) < d := by nlinarith [sq_pos_of_pos ha]
  have hdNat : 0 < d := by exact_mod_cast hdpos
  have hp := permutation_hit_probability_bound A B (by simpa using hdNat)
  have hprod : (A.card : ℝ) * B.card ≤ (4 * a) * (4 * a) :=
    mul_le_mul hA hB (Nat.cast_nonneg _) (by linarith)
  calc
    _ ≤ (A.card : ℝ) * B.card / d := by
      convert hp using 1 <;> simp
      congr 1
      ext π
      simp
    _ ≤ 1 / 2 := by
      apply (div_le_iff₀ hdpos).2
      nlinarith

/-- The half bound in the integral form useful for product counting. -/
theorem permutation_hit_card_half_bound {d : ℕ} (A B : Finset (Fin d)) (a : ℝ)
    (ha : 0 < a) (hA : (A.card : ℝ) ≤ 4 * a) (hB : (B.card : ℝ) ≤ 4 * a)
    (hd : (d : ℝ) = 32 * a^2) :
    2 * (Finset.univ.filter (fun π : Equiv.Perm (Fin d) => ∃ i ∈ A, π i ∈ B)).card ≤
      Fintype.card (Equiv.Perm (Fin d)) := by
  have hp := permutation_hit_half_bound A B a ha hA hB hd
  have hpos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin d)) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin d)))
  have hm := (div_le_iff₀ hpos).mp hp
  have hr : (2 : ℝ) * (Finset.univ.filter
      (fun π : Equiv.Perm (Fin d) => ∃ i ∈ A, π i ∈ B)).card ≤
        Fintype.card (Equiv.Perm (Fin d)) := by linarith
  exact_mod_cast hr

/-- A fixed light pair has matching selected labels with probability at most one half. -/
theorem light_pair_hit_half {k d : ℕ} (S : Finset (Fin k × Fin d)) (μ ν : Fin k)
    (hμ : μ ∈ light S) (hν : ν ∈ light S)
    (ha : 0 < average k S.card) (hd : (d : ℝ) = 32 * (average k S.card)^2) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin d) =>
      ∃ j : Fin d, (μ, j) ∈ S ∧ (ν, π j) ∈ S)).card : ℝ) /
      Fintype.card (Equiv.Perm (Fin d)) ≤ 1 / 2 := by
  classical
  let A := Finset.univ.filter (fun j : Fin d => (μ, j) ∈ S)
  let B := Finset.univ.filter (fun j : Fin d => (ν, j) ∈ S)
  have hp := permutation_hit_half_bound A B (average k S.card) ha
    (light_row_card_le S μ hμ) (light_row_card_le S ν hν) hd
  simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using hp

/-- A nonempty candidate and an actual ground element have positive average. -/
theorem average_pos_of_card_pos {k d : ℕ} (S : Finset (Fin k × Fin d))
    (hc : 0 < S.card) (μ : Fin k) : 0 < average k S.card := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le μ.val) μ.isLt
  exact div_pos (Nat.cast_pos.mpr hc) (Nat.cast_pos.mpr hk)

/-- Cardinal form for the exact selected-label hit event of a light pair. -/
theorem light_pair_hit_card_half {k d : ℕ} (S : Finset (Fin k × Fin d)) (μ ν : Fin k)
    (hμ : μ ∈ light S) (hν : ν ∈ light S) (hc : 0 < S.card)
    (hd : (d : ℝ) = 32 * (average k S.card)^2) :
    2 * (Finset.univ.filter (fun π : Equiv.Perm (Fin d) =>
      ∃ j : Fin d, (μ, j) ∈ S ∧ (ν, π j) ∈ S)).card ≤
      Fintype.card (Equiv.Perm (Fin d)) := by
  classical
  let A := Finset.univ.filter (fun j : Fin d => (μ, j) ∈ S)
  let B := Finset.univ.filter (fun j : Fin d => (ν, j) ∈ S)
  have hp := permutation_hit_card_half_bound A B (average k S.card)
    (average_pos_of_card_pos S hc μ) (light_row_card_le S μ hμ) (light_row_card_le S ν hν) hd
  simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using hp

end LabelCutProbability
end


section
open scoped BigOperators
namespace LabelCutExact
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma map_trans (A : Finset α) (π σ : Equiv.Perm α) :
    A.map (π.trans σ).toEmbedding = (A.map π.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

lemma fiber_card (A U V : Finset α) (h : U.card = V.card) :
    (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding = U)).card =
    (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding = V)).card := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq U V h
  let e : Equiv.Perm α ≃ Equiv.Perm α := {
    toFun := fun π => π.trans σ
    invFun := fun π => π.trans σ.symm
    left_inv := by intro π; ext x; simp
    right_inv := by intro π; ext x; simp }
  apply Finset.card_equiv e
  intro π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change A.map π.toEmbedding = U ↔ A.map (π.trans σ).toEmbedding = V
  rw [map_trans, ← hσ]
  exact ⟨fun h => congrArg (Finset.map σ.toEmbedding) h,
    fun h => Finset.map_injective σ.toEmbedding h⟩

lemma collection_card (A : Finset α) (C : Finset (Finset α))
    (hC : ∀ U ∈ C, U.card = A.card) :
    (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding ∈ C)).card =
      C.card * (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding = A)).card := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ C (fun π : Equiv.Perm α => A.map π.toEmbedding)]
  calc
    _ = ∑ _ ∈ C, (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding = A)).card := by
      apply Finset.sum_congr rfl
      intro U hU
      exact fiber_card A U A (hC U hU)
    _ = _ := by simp

lemma avoidance_card (A B : Finset α) :
    (Finset.univ.filter (fun π : Equiv.Perm α => Disjoint (A.map π.toEmbedding) B)).card =
      (Fintype.card α - B.card).choose A.card *
      (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding = A)).card := by
  classical
  have h := collection_card A (Bᶜ.powersetCard A.card) (by
    intro U hU
    exact (Finset.mem_powersetCard.mp hU).2)
  simpa only [Finset.mem_powersetCard, Finset.card_map, and_true,
    Finset.subset_compl_iff_disjoint_left, disjoint_comm, Finset.card_powersetCard, Finset.card_compl] using h

lemma total_card (A : Finset α) :
    Fintype.card (Equiv.Perm α) =
      (Fintype.card α).choose A.card *
      (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding = A)).card := by
  simpa using avoidance_card A ∅

lemma avoidance_probability (A B : Finset α) :
    ((Finset.univ.filter (fun π : Equiv.Perm α => Disjoint (A.map π.toEmbedding) B)).card : ℝ) /
      Fintype.card (Equiv.Perm α) =
      ((Fintype.card α - B.card).choose A.card : ℝ) / (Fintype.card α).choose A.card := by
  classical
  have hf : 0 < (Finset.univ.filter (fun π : Equiv.Perm α => A.map π.toEmbedding = A)).card := by
    apply Finset.card_pos.mpr
    refine ⟨Equiv.refl α, ?_⟩
    simp
  rw [avoidance_card, total_card A, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast (ne_of_gt hf))

lemma choose_ratio_product (N s r : ℕ) :
    ((N-s).choose r : ℝ) / N.choose r =
      ∏ i ∈ Finset.range r, ((N-s-i : ℕ) : ℝ) / (N-i : ℕ) := by
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hr : ((N-s).choose r : ℝ) / N.choose r =
      ((N-s).descFactorial r : ℝ) / N.descFactorial r := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    exact (mul_div_mul_left _ _ hf).symm
  rw [hr, Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

lemma choose_ratio_lower (N s r : ℕ) (a : ℝ) (ha : 0 < a)
    (hr : (r : ℝ) ≤ 4*a) (hs : (s : ℝ) ≤ 4*a) (hN : 8*a < N) :
    (1-8*a/N) ^ (4*a) ≤ ((N-s).choose r : ℝ) / N.choose r := by
  have hNp : (0 : ℝ) < N := by linarith
  have hb : 0 < 1-8*a/N := by apply sub_pos.mpr; exact (div_lt_one hNp).mpr hN
  have hb1 : 1-8*a/N ≤ 1 := by
    have : 0 ≤ 8*a/N := by positivity
    linarith
  calc
    _ ≤ (1-8*a/N) ^ (r : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb hb1 hr
    _ = ∏ _i ∈ Finset.range r, (1-8*a/N) := by simp
    _ ≤ _ := by
      rw [choose_ratio_product]
      apply Finset.prod_le_prod (fun _ _ => le_of_lt hb)
      intro i hi
      have hir : i < r := Finset.mem_range.mp hi
      have hirR : (i : ℝ) < r := by exact_mod_cast hir
      have hi4 : (i : ℝ) < 4*a := lt_of_lt_of_le hirR hr
      have hsum : s+i ≤ N := by exact_mod_cast (show (s : ℝ)+(i : ℝ) ≤ N by linarith)
      have hsN : s ≤ N := by omega
      have hiNs : i ≤ N-s := by omega
      have hiN : i ≤ N := by omega
      have hden : (0 : ℝ) < (N : ℝ)-i := by linarith
      rw [Nat.cast_sub hiNs, Nat.cast_sub hsN, Nat.cast_sub hiN]
      apply (le_div_iff₀ hden).mpr
      apply (mul_le_mul_iff_left₀ hNp).mp
      have hc : 8*a/N*N = 8*a := div_mul_cancel₀ _ (ne_of_gt hNp)
      nlinarith [mul_nonneg (show 0 ≤ 4*a-s by linarith) (le_of_lt hNp),
        mul_nonneg (show 0 ≤ 4*a-i by linarith) (show 0 ≤ 8*a by positivity),
        mul_nonneg (show 0 ≤ N-8*a by linarith) (show 0 ≤ 4*a by positivity)]

lemma hit_probability (A B : Finset α) (a : ℝ) (ha : 0 < a)
    (hA : (A.card : ℝ) ≤ 4*a) (hB : (B.card : ℝ) ≤ 4*a)
    (hN : 8*a < Fintype.card α) :
    ((Finset.univ.filter (fun π : Equiv.Perm α => ∃ i ∈ A, π i ∈ B)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ 1 - (1-8*a/Fintype.card α) ^ (4*a) := by
  classical
  have hp := choose_ratio_lower (Fintype.card α) B.card A.card a ha hA hB hN
  rw [← avoidance_probability A B] at hp
  have hnot (π : Equiv.Perm α) :
      (¬ Disjoint (A.map π.toEmbedding) B) ↔ ∃ i ∈ A, π i ∈ B := by
    simp only [Finset.disjoint_left, Finset.mem_map, Equiv.coe_toEmbedding]
    push_neg
    aesop
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Equiv.Perm α))) (fun π => Disjoint (A.map π.toEmbedding) B)
  simp only [hnot, Finset.card_univ] at hc
  have hcR : ((Finset.univ.filter (fun π : Equiv.Perm α => Disjoint (A.map π.toEmbedding) B)).card : ℝ) +
      ((Finset.univ.filter (fun π : Equiv.Perm α => ∃ i ∈ A, π i ∈ B)).card : ℝ) =
      Fintype.card (Equiv.Perm α) := by exact_mod_cast hc
  have hP : (Fintype.card (Equiv.Perm α) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm α)))
  have hs := congrArg (fun x : ℝ => x / Fintype.card (Equiv.Perm α)) hcR
  rw [add_div, div_self hP] at hs
  linarith
end LabelCutExact

end

open ZhangTangLabelCut.LP2

theorem solution (k d h : ℕ)
    (directed : Bool) (S : Finset (Fin k × Fin d)) (hc : 0 < S.card)
    (hreg : 8 * average k S.card < (d : ℝ)) (c : Chain k h)
    (hμ : c.1.val.1 ∈ light S) (hν : c.1.val.2 ∈ light S) :
    probability k d h (chainSeparated directed S c) ≤ chainBound (average k S.card) d := by
  classical
  let A : Finset (Fin d) := Finset.univ.filter (fun j => (c.1.val.1,j) ∈ S)
  let B : Finset (Fin d) := Finset.univ.filter (fun j => (c.1.val.2,j) ∈ S)
  let q := chainBound (average k S.card) d
  have ha := LabelCutProbability.average_pos_of_card_pos S hc c.1.val.1
  have hdR : (0 : ℝ) < d := by linarith
  have hd : 0 < d := by exact_mod_cast hdR
  have hp : ((Finset.univ.filter (fun π : Equiv.Perm (Fin d) =>
        ∃ j ∈ A, π j ∈ B)).card : ℝ) / Fintype.card (Equiv.Perm (Fin d)) ≤ q := by
    have hx := LabelCutExact.hit_probability A B (average k S.card) ha
        (LabelCutProbability.light_row_card_le S c.1.val.1 hμ)
        (LabelCutProbability.light_row_card_le S c.1.val.2 hν)
        (by simpa using hreg)
    convert hx using 1
    · congr 3
      ext π
      simp
    · simp only [Fintype.card_fin, q, chainBound]
  let T : Chain k h → Finset (Equiv.Perm (Fin d)) := fun i =>
    if i = c then Finset.univ.filter (fun π => ∃ j ∈ A, π j ∈ B) else Finset.univ
  have hsub : Finset.univ.filter (chainSeparated directed S c) ⊆
      Finset.univ.filter (fun σ : Sample k d h => ∀ i, σ i ∈ T i) := by
    intro σ hσ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun i => ?_⟩
    by_cases hi : i = c
    · subst i
      obtain ⟨j,hj,hj'⟩ := Graph.chainSeparated_imp_hit hd directed S c σ (Finset.mem_filter.mp hσ).2
      simp only [T, if_pos rfl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨j, by simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hj,
        by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hj'⟩
    · simp only [T, if_neg hi, Finset.mem_univ]
  have hprod := LabelCutCounting.product_probability_le T {c} q (by
    intro i hi
    have hi' : i = c := Finset.mem_singleton.mp hi
    subst i
    simpa only [T, if_pos rfl] using hp)
  calc
    probability k d h (chainSeparated directed S c) ≤
        ((Finset.univ.filter (fun σ : Sample k d h => ∀ i, σ i ∈ T i)).card : ℝ) /
          Fintype.card (Sample k d h) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ q := by simpa using hprod
