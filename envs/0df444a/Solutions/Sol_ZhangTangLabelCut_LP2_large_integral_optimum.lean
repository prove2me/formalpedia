-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.large_integral_optimum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:01:07.956273+00:00
-- url     : https://prove2.me/submissions/7da030d6-9809-40bd-83f6-260196a0019b

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

-- Source: complexity-labelcut-scout/Helpers.lean
section
set_option autoImplicit false
open scoped BigOperators

namespace ZhangTangLabelCut.LP2

lemma counts_sum {k d : ℕ} (S : Finset (Fin k × Fin d)) :
    ∑ μ : Fin k, counts S μ = S.card := by
  classical
  simpa only [counts, Finset.sum_filter, Finset.mem_univ, Finset.filter_true] using
    (Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ)
      (f := Prod.fst) (fun _ _ => Finset.mem_univ _)).symm

lemma light_card_lower {k d : ℕ} (S : Finset (Fin k × Fin d)) (hk : 0 < k) :
    3 * (k : ℝ) / 4 ≤ ((light S).card : ℝ) := by
  classical
  by_cases hS : S.card = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hS
    simp only [hSe, light, counts, Finset.card_empty, average, Nat.cast_zero,
      zero_div, mul_zero, Finset.filter_empty, le_refl, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  · have ha0 : 0 < average k S.card :=
      div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)) (Nat.cast_pos.mpr hk)
    have hsum : ∑ μ : Fin k, (counts S μ : ℝ) = (S.card : ℝ) := by
      exact_mod_cast counts_sum S
    have hheavy : ∑ μ ∈ (light S)ᶜ, 4 * average k S.card ≤
        ∑ μ ∈ (light S)ᶜ, (counts S μ : ℝ) := by
      apply Finset.sum_le_sum
      intro μ hμ
      exact (lt_of_not_ge (by simpa only [light, Finset.mem_filter, Finset.mem_univ,
        true_and] using (Finset.mem_compl.mp hμ))).le
    have hsumle : ∑ μ ∈ (light S)ᶜ, (counts S μ : ℝ) ≤ ∑ μ : Fin k, (counts S μ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    have hcard : ((light S).card : ℝ) + ((light S)ᶜ.card : ℝ) = k := by
      exact_mod_cast (show (light S).card + (light S)ᶜ.card = k by
        simpa only [Fintype.card_fin] using Finset.card_add_card_compl (light S))
    have havg : average k S.card * k = (S.card : ℝ) :=
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))
    simp only [Finset.sum_const, nsmul_eq_mul] at hheavy
    nlinarith

lemma pair_filter_card {k : ℕ} (L : Finset (Fin k)) :
    ((Finset.univ : Finset (Pair k)).filter
      (fun p => p.val.1 ∈ L ∧ p.val.2 ∈ L)).card = L.card.choose 2 := by
  classical
  calc
    _ = ((L ×ˢ L).filter (fun p => p.1 < p.2)).card := by
      apply Finset.card_bij (fun p _ => p.val)
      · exact fun p hp => Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr (Finset.mem_filter.mp hp).2, p.property⟩
      · exact fun _ _ _ _ h => Subtype.ext h
      · exact fun p hp => ⟨⟨p, (Finset.mem_filter.mp hp).2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Finset.mem_product.mp (Finset.mem_filter.mp hp).1⟩, rfl⟩
    _ = _ := Finset.card_product_filter_lt

lemma chain_filter_card {k h : ℕ} (L : Finset (Fin k)) :
    ((Finset.univ : Finset (Chain k h)).filter
      (fun c => c.1.val.1 ∈ L ∧ c.1.val.2 ∈ L)).card = L.card.choose 2 * h := by
  classical
  have hs : (Finset.univ : Finset (Chain k h)).filter
        (fun c => c.1.val.1 ∈ L ∧ c.1.val.2 ∈ L) =
      ((Finset.univ : Finset (Pair k)).filter
        (fun p => p.val.1 ∈ L ∧ p.val.2 ∈ L)) ×ˢ (Finset.univ : Finset (Fin h)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
  rw [hs, Finset.card_product, Finset.card_univ, Fintype.card_fin, pair_filter_card]

lemma light_chain_card_lower {k d h : ℕ} (S : Finset (Fin k × Fin d)) (hk : 2 ≤ k) :
    ((h : ℝ) / 2) * (3 * (k : ℝ) / 4) * (3 * (k : ℝ) / 4 - 1) ≤
      (((Finset.univ : Finset (Chain k h)).filter
        (fun c => c.1.val.1 ∈ light S ∧ c.1.val.2 ∈ light S)).card : ℝ) := by
  rw [chain_filter_card, Nat.cast_mul, Nat.cast_choose_two]
  have hL := light_card_lower S (by omega : 0 < k)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul : (3 * (k : ℝ) / 4) * (3 * (k : ℝ) / 4 - 1) ≤
      ((light S).card : ℝ) * ((light S).card - 1) :=
    mul_le_mul hL (sub_le_sub_right hL 1) (by linarith) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hmul (Nat.cast_nonneg (α := ℝ) h)]

lemma chainBound_half (a : ℕ) (ha : 0 < a) :
    (1 / 2 : ℝ) ≤ chainBound (a : ℝ) (32 * (a : ℝ) ^ 2) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have heq : 8 * (a : ℝ) / (32 * (a : ℝ) ^ 2) = 1 / (4 * (a : ℝ)) := by
    field_simp
    norm_num
  have hb0 : 0 < 1 - 1 / (4 * (a : ℝ)) :=
    sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  have hx : (1 / (4 * (a : ℝ))) * (4 * a) = 1 :=
    one_div_mul_cancel (by positivity : 4 * (a : ℝ) ≠ 0)
  have hlog : Real.log (1 - 1 / (4 * (a : ℝ))) * (4 * a) ≤ -1 := by
    nlinarith [mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hb0)
      (show 0 ≤ 4 * (a : ℝ) by positivity)]
  have hpow : (1 - 1 / (4 * (a : ℝ))) ^ (4 * (a : ℝ)) ≤ Real.exp (-1) := by
    rw [Real.rpow_def_of_pos hb0]
    exact Real.exp_le_exp.mpr hlog
  have hexp : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    simpa only [Real.exp_neg, one_div] using
      (one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp (1 : ℝ)]))
  rw [chainBound, heq]
  linarith

lemma chainBound_lt_one (a : ℕ) (ha : 0 < a) :
    chainBound (a : ℝ) (32 * (a : ℝ) ^ 2) < 1 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb : 0 < 1 - 8 * (a : ℝ) / (32 * (a : ℝ) ^ 2) :=
    sub_pos.mpr ((div_lt_one (by positivity)).mpr (by nlinarith))
  exact sub_lt_self _ (Real.rpow_pos_of_pos hb _)

lemma chainBound_range (a : ℕ) (ha : 0 < a) :
    0 ≤ chainBound (a : ℝ) (32 * (a : ℝ) ^ 2) ∧
      chainBound (a : ℝ) (32 * (a : ℝ) ^ 2) < 1 := by
  exact ⟨le_trans (by norm_num) (chainBound_half a ha), chainBound_lt_one a ha⟩

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/Feasibility.lean
section
set_option autoImplicit false
open scoped BigOperators
namespace ZhangTangLabelCut.LP2

/-- Every terminal path has a nonempty label set because its endpoints differ. -/
lemma lp_ones_feasible (I : LabelCut) : I.lp.Feasible (fun _ => 1) := by
  classical
  have hlen (p : Path I.graph I.s I.t) : 0 < p.length := by
    by_contra hn
    have hl : p.length = 0 := by omega
    have hv : (0 : Fin (p.length + 1)) = Fin.last p.length := by
      apply Fin.ext
      simp [hl]
    apply I.distinct
    calc
      I.s = p.vertex 0 := p.start.symm
      _ = p.vertex (Fin.last p.length) := congrArg p.vertex hv
      _ = I.t := p.finish
  have hnon (p : Path I.graph I.s I.t) : (I.pathLabels p).Nonempty := by
    refine ⟨I.label (p.edge ⟨0, hlen p⟩), ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, hlen p⟩, Finset.mem_univ _, rfl⟩
  constructor
  · intro l
    norm_num
  · intro R hR
    simp only [LabelCut.lp, Finset.mem_filter, Finset.mem_univ, true_and] at hR
    rcases hR with ⟨p, rfl⟩
    have hc : (1 : ℝ) ≤ ((I.pathLabels p).card : ℝ) := by
      exact_mod_cast (Finset.one_le_card.mpr (hnon p))
    simpa [LabelCut.lp] using hc

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut/LP.lean
section
set_option autoImplicit false
open scoped BigOperators
namespace ZhangTangLabelCut.LP2

lemma lp_value_ge_one (I : LabelCut) (p : Path I.graph I.s I.t) :
    (1 : EReal) ≤ I.lp.value := by
  classical
  apply le_sInf
  rintro z ⟨x, hx, rfl⟩
  have hr : I.pathLabels p ∈ I.lp.rows := by simp [LabelCut.lp]
  have hrow : (1 : ℝ) ≤ ∑ l ∈ I.pathLabels p, x l := hx.2 _ hr
  have hsum : (∑ l ∈ I.pathLabels p, x l) ≤ ∑ l, x l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun l _ _ => hx.1 l)
  have hcost : (1 : ℝ) ≤ I.lp.objective x := by
    simpa [CoveringLP.objective, LabelCut.lp] using hrow.trans hsum
  exact_mod_cast hcost

lemma lp_value_positive_finite (I : LabelCut) (p : Path I.graph I.s I.t) :
    ∃ v : ℝ, 0 < v ∧ I.lp.value = (v : EReal) := by
  have hl := lp_value_ge_one I p
  have hu : I.lp.value ≤ (I.lp.objective (fun _ => 1) : EReal) :=
    sInf_le ⟨(fun _ => 1), lp_ones_feasible I, rfl⟩
  have htop : I.lp.value ≠ ⊤ := ne_of_lt (hu.trans_lt (EReal.coe_lt_top _))
  have hpos : 0 < I.lp.value := lt_of_lt_of_le (by norm_num : (0 : EReal) < 1) hl
  have hbot : I.lp.value ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe 0).trans hpos)
  exact ⟨I.lp.value.toReal, EReal.toReal_pos hpos htop, (EReal.coe_toReal htop hbot).symm⟩

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/Counts.lean
section
set_option autoImplicit false
open ZhangTangLabelCut.LP2
namespace LabelCutCounting

private lemma candidates_card_le_pow {L : Type} [Fintype L] [DecidableEq L] (c : ℕ) :
    (Finset.univ.powersetCard c : Finset (Finset L)).card ≤ (Fintype.card L)^c := by
  simpa only [Finset.card_powersetCard, Finset.card_univ] using
    Nat.choose_le_pow (Fintype.card L) c

/-- The supervisor has fixed the counting argument; complete only its formalization. -/
lemma candidates_le_countBound (k a d : ℕ) (hkd : k ≤ d) (hd : 1 ≤ d) :
    ((Finset.univ.powersetCard (k * a) : Finset (Finset (Fin k × Fin d))).card : ℝ) ≤
      countBound k a d := by
  unfold countBound
  have h : ((4 * a + 1 : ℕ) : ℝ) = 4 * (a : ℝ) + 1 := by push_cast; rfl
  rw [← h, ← Nat.cast_mul, Real.rpow_natCast, Real.rpow_natCast,
    ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_le]
  calc
    _ ≤ (k * d) ^ (k * a) := by
      simpa using (candidates_card_le_pow (L := Fin k × Fin d) (k * a))
    _ ≤ d ^ (2 * (k * a)) := by
      simpa only [pow_mul, pow_two] using
        Nat.pow_le_pow_left (Nat.mul_le_mul_right d hkd) (k * a)
    _ ≤ d ^ ((4 * a + 1) * k) := by
      apply Nat.pow_le_pow_right hd
      nlinarith
    _ ≤ (4 * a + 1) ^ k * d ^ ((4 * a + 1) * k) := by
      exact Nat.le_mul_of_pos_left _ (Nat.one_le_pow k (4 * a + 1) (by omega))

end LabelCutCounting
end

-- Source: complexity-labelcut-terra-count/Cardinalities.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

/-- Exact size formulas, with the pair count left explicit. -/
lemma shutter_cardinalities (k d h : ℕ) (directed : Bool) :
    Fintype.card (shutterGraph k d h directed).V =
        2 + (Fintype.card (Pair k) * h) * ((d - 1) + d * 2) ∧
    Fintype.card (shutterGraph k d h directed).E =
        (Fintype.card (Pair k) * h) * (d * 2 * 2) := by
  change Fintype.card (ShutterVertex k d h) =
      2 + (Fintype.card (Pair k) * h) * ((d - 1) + d * 2) ∧
    Fintype.card (ShutterEdge k d h) = (Fintype.card (Pair k) * h) * (d * 2 * 2)
  simp [ShutterVertex, ShutterEdge, Chain, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  omega

private lemma shutter_generic_sizes (k d h : ℕ) (directed : Bool)
    (hk : 2 ≤ k) (hd : 1 ≤ d) (hh : 1 ≤ h) :
    2 * Fintype.card (shutterGraph k d h directed).V ≤ 3 * d * h * k ^ 2 ∧
    Fintype.card (shutterGraph k d h directed).E ≤ 2 * d * h * k ^ 2 := by
  have hc : Fintype.card (Pair k) = k.choose 2 := by
    classical
    simpa using (pair_filter_card (Finset.univ : Finset (Fin k)))
  have hpair : 2 * Fintype.card (Pair k) + k = k ^ 2 := by
    have hr : (2 : ℝ) * Fintype.card (Pair k) + k = (k : ℝ) ^ 2 := by
      rw [hc, Nat.cast_choose_two]
      nlinarith
    exact_mod_cast hr
  obtain ⟨hv, he⟩ := shutter_cardinalities k d h directed
  rw [hv, he]
  have hleft : d - 1 + d * 2 ≤ 3 * d := by omega
  have h4 : 4 ≤ 3 * d * h * k := by
    have hdh : 1 ≤ d * h := by nlinarith
    have hdhk := Nat.mul_le_mul hdh hk
    nlinarith
  constructor
  · nlinarith [Nat.mul_le_mul_left (Fintype.card (Pair k) * h) hleft,
      congrArg (fun x : ℕ => 3 * d * h * x) hpair]
  · nlinarith [congrArg (fun x : ℕ => 2 * d * h * x) hpair]

/-- The supervisor fixed the construction parameters and final constants. -/
lemma shutter_size_bounds (k D : ℕ) (hk : 2 ≤ k) (_hD : 0 < D) (directed : Bool)
    (σ : Sample k (32 * k ^ (2 * D)) (k ^ D)) :
    Fintype.card (shutterInstance k (32 * k ^ (2 * D)) (k ^ D) directed σ).graph.V ≤
        48 * k ^ (2 + 3 * D) ∧
    Fintype.card (shutterInstance k (32 * k ^ (2 * D)) (k ^ D) directed σ).graph.E ≤
        64 * k ^ (2 + 3 * D) := by
  have hp : (32 * k ^ (2 * D)) * k ^ D * k ^ 2 = 32 * k ^ (2 + 3 * D) := by
    calc
      _ = 32 * (k ^ (2 * D) * k ^ D * k ^ 2) := by ring
      _ = 32 * k ^ (2 * D + D + 2) := by rw [pow_add, pow_add]
      _ = _ := by congr 2; omega
  have hg := shutter_generic_sizes k (32 * k ^ (2 * D)) (k ^ D) directed hk
    (by
      have hk0 : 0 < k := by omega
      have hx : 0 < 32 * k ^ (2 * D) := by positivity
      omega)
    (Nat.one_le_pow D k (by omega))
  dsimp only [shutterInstance]
  have hv : 3 * (32 * k ^ (2 * D)) * k ^ D * k ^ 2 = 96 * k ^ (2 + 3 * D) := by
    calc
      _ = 3 * ((32 * k ^ (2 * D)) * k ^ D * k ^ 2) := by ring
      _ = _ := by rw [hp]; ring
  have he : 2 * (32 * k ^ (2 * D)) * k ^ D * k ^ 2 = 64 * k ^ (2 + 3 * D) := by
    calc
      _ = 2 * ((32 * k ^ (2 * D)) * k ^ D * k ^ 2) := by ring
      _ = _ := by rw [hp]; ring
  rw [hv, he] at hg
  refine ⟨?_, ?_⟩
  · have hv_le : Fintype.card (shutterGraph k (32 * k ^ (2 * D)) (k ^ D) directed).V ≤
        48 * k ^ (2 + 3 * D) := by omega
    exact hv_le
  · exact hg.2

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/GraphSimplicity.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2.Graph

lemma edge_endpoints_injective {k d h : ℕ} :
    Function.Injective (fun e : ShutterEdge k d h => (shutterTail e, shutterHead e)) := by
  intro e e' heq
  rcases e with ⟨c, j, b, f⟩
  rcases e' with ⟨c', j', b', f'⟩
  cases f <;> cases f'
  · have hm := congrArg Prod.snd heq
    change middle c j b = middle c' j' b' at hm
    simp only [middle, Sum.inr.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩
    rfl
  · have ht := congrArg Prod.fst heq
    change junction c j.castSucc = middle c' j' b' at ht
    exact False.elim ((junction_ne_middle c c' j.castSucc j' b') ht)
  · have ht := congrArg Prod.fst heq
    change middle c j b = junction c' j'.castSucc at ht
    exact False.elim ((junction_ne_middle c' c j'.castSucc j b) ht.symm)
  · have hm := congrArg Prod.fst heq
    change middle c j b = middle c' j' b' at hm
    simp only [middle, Sum.inr.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩
    rfl

lemma shutterGraph_simple (k d h : ℕ) (directed : Bool) :
    (shutterGraph k d h directed).Simple := by
  simp only [FiniteGraph.Simple, shutterGraph]
  constructor
  · intro e heq
    have he := congrArg (level d) heq
    have hlevel := level_edge e
    omega
  · intro e f hx
    rcases hx with h | ⟨_, htail, hhead⟩
    · exact edge_endpoints_injective (Prod.ext h.1 h.2)
    · have h1 := level_edge e
      have h2 := level_edge f
      have h3 := congrArg (level d) htail
      have h4 := congrArg (level d) hhead
      omega

end ZhangTangLabelCut.LP2.Graph
end

-- Source: complexity-labelcut-terra-count/Admissibility.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma shutter_admissible (k d h : ℕ) (hk : 2 ≤ k) (hd : 0 < d) (hh : 0 < h)
    (directed : Bool) (σ : Sample k d h) :
    (shutterInstance k d h directed σ).Admissible := by
  let c : Chain k h := (⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change 0 < 1; omega⟩, ⟨0, hh⟩)
  let p : Path (shutterInstance k d h directed σ).graph
      (shutterInstance k d h directed σ).s (shutterInstance k d h directed σ).t :=
    Graph.chainPath hd c (fun _ => false) directed
  exact ⟨Graph.shutterGraph_simple k d h directed, ⟨p⟩,
    lp_value_positive_finite (shutterInstance k d h directed σ) p⟩

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut/SampleBound.lean
section
set_option autoImplicit false
open scoped BigOperators
namespace ZhangTangLabelCut.LP2

noncomputable def lightChains {k d h : ℕ} (S : Finset (Fin k × Fin d)) : Finset (Chain k h) := by
  classical
  exact Finset.univ.filter (fun c => c.1.val.1 ∈ light S ∧ c.1.val.2 ∈ light S)

noncomputable def matchingPerms {k d h : ℕ} (S : Finset (Fin k × Fin d)) (c : Chain k h) :
    Finset (Equiv.Perm (Fin d)) := by
  classical
  exact Finset.univ.filter (fun π => ∃ j : Fin d, (c.1.val.1, j) ∈ S ∧ (c.1.val.2, π j) ∈ S)

noncomputable def chainEvents {k d h : ℕ} (S : Finset (Fin k × Fin d)) (c : Chain k h) :
    Finset (Equiv.Perm (Fin d)) := by
  classical
  exact if c ∈ lightChains S then matchingPerms S c else Finset.univ

lemma cut_probability_half {k d h : ℕ} (directed : Bool) (S : Finset (Fin k × Fin d))
    (hd : 0 < d) (hc : 0 < S.card) (hdim : (d : ℝ) = 32 * (average k S.card)^2) :
    probability k d h (fun σ => (shutterInstance k d h directed σ).Cut S) ≤
      (1 / 2 : ℝ) ^ (lightChains (h := h) S).card := by
  classical
  have hcoord : ∀ c ∈ lightChains (h := h) S,
      ((chainEvents S c).card : ℝ) / Fintype.card (Equiv.Perm (Fin d)) ≤ 1 / 2 := by
    intro c hactive
    have hends : c.1.val.1 ∈ light S ∧ c.1.val.2 ∈ light S := by
      simpa only [lightChains, Finset.mem_filter, Finset.mem_univ, true_and] using hactive
    have hp := LabelCutProbability.light_pair_hit_half S c.1.val.1 c.1.val.2
      hends.1 hends.2 (LabelCutProbability.average_pos_of_card_pos S hc c.1.val.1) hdim
    simpa only [chainEvents, if_pos hactive, matchingPerms] using hp
  have hprod := LabelCutCounting.product_probability_le (chainEvents (h := h) S)
    (lightChains S) (1 / 2) hcoord
  have hsub : (Finset.univ.filter (fun σ : Sample k d h =>
      (shutterInstance k d h directed σ).Cut S)) ⊆
      Finset.univ.filter (fun σ : Sample k d h => ∀ c, σ c ∈ chainEvents S c) := by
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => ?_⟩
    by_cases hactive : c ∈ lightChains S
    · simpa only [chainEvents, if_pos hactive, matchingPerms, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        Graph.chainSeparated_imp_hit hd directed S c σ
          (Graph.cut_imp_chainSeparated directed S σ c (Finset.mem_filter.mp hσ).2)
    · simp [chainEvents, hactive]
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
    (Nat.cast_nonneg _)).trans hprod

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/ProbabilityConversion.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma cut_probability_bound (k a h : ℕ) (hk : 2 ≤ k) (ha : 0 < a)
    (directed : Bool) (S : Finset (Fin k × Fin (32 * a^2))) (hS : S.card = k * a) :
    probability k (32 * a^2) h (fun σ => (shutterInstance k (32 * a^2) h directed σ).Cut S) ≤
      configurationBound (k : ℝ) (h : ℝ) (a : ℝ) ((32 * a^2 : ℕ) : ℝ) := by
  have havg : average k S.card = (a : ℝ) := by
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    simp [average, hS, Nat.cast_mul, hk0]
  have hd : 0 < 32 * a ^ 2 := by positivity
  have hc : 0 < S.card := by
    rw [hS]
    have hk0 : 0 < k := by omega
    positivity
  have hdim : ((32 * a ^ 2 : ℕ) : ℝ) = 32 * (average k S.card) ^ 2 := by
    rw [havg]
    push_cast
    rfl
  have hbase := chainBound_half a ha
  have hrange := chainBound_range a ha
  have hexp : (h : ℝ) / 2 * (3 * (k : ℝ) / 4) * (3 * (k : ℝ) / 4 - 1) ≤
      ((lightChains (h := h) S).card : ℝ) := by
    simpa only [lightChains] using (light_chain_card_lower (h := h) S hk)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, configurationBound]
  calc
    _ ≤ (1 / 2 : ℝ) ^ (lightChains (h := h) S).card := by
      exact cut_probability_half directed S hd hc hdim
    _ ≤ chainBound (a : ℝ) (32 * (a : ℝ) ^ 2) ^ (lightChains (h := h) S).card := by
      exact pow_le_pow_left₀ (by norm_num) hbase _
    _ ≤ _ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (by linarith [hbase]) hrange.2.le hexp

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut/Existence.lean
section
set_option autoImplicit false
namespace LabelCutCounting

lemma exists_avoiding {ι Ω : Type} [Fintype ι] [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (s : ι → Finset Ω) (q : ℝ)
    (hs : ∀ i, ((s i).card : ℝ) / Fintype.card Ω ≤ q)
    (hlt : (Fintype.card ι : ℝ) * q < 1) : ∃ ω, ∀ i, ω ∉ s i := by
  classical
  by_contra hn
  have hall : ∀ ω, ∃ i, ω ∈ s i := by
    simpa only [not_exists, not_forall, not_not] using hn
  have hwhole : Finset.univ.biUnion s = Finset.univ :=
    Finset.eq_univ_of_forall (fun ω => Exists.elim (hall ω)
      (fun i hi => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩))
  have hd : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hb : (1 : ℝ) ≤ Fintype.card ι * q := by
    simpa only [hwhole, Finset.card_univ, div_self hd]
      using union_probability_le s q hs
  exact (not_lt_of_ge hb) hlt

end LabelCutCounting
end

-- Source: complexity-labelcut-terra-count/AnalyticProof.lean
section
set_option autoImplicit false
open Filter Topology

namespace ZhangTangLabelCut.LP2

lemma zt_chain (a : ℝ) (ha : 1 ≤ a) :
    0 ≤ chainBound a (32 * a ^ 2) ∧ chainBound a (32 * a ^ 2) ≤ 1 - Real.exp (-(4/3)) := by
  have ha0 : 0 < a := by linarith
  have e1 : 8 * a / (32 * a ^ 2) = 1 / (4 * a) := by field_simp; ring
  set x : ℝ := 1 / (4 * a) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 4 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h1x : 0 < 1 - x := by linarith
  have hlog : -(4 / 3) * x ≤ Real.log (1 - x) := by
    have h := Real.one_sub_inv_le_log_of_pos h1x
    have : -(4 / 3) * x ≤ 1 - (1 - x)⁻¹ := by
      have : (1 - x)⁻¹ ≤ 1 + 4 / 3 * x := by
        rw [inv_eq_one_div, div_le_iff₀ h1x]
        nlinarith [mul_nonneg hx0.le (by linarith : (0:ℝ) ≤ 1 / 4 - x)]
      linarith
    linarith
  have hxa : x * (4 * a) = 1 := by rw [hx]; field_simp
  have hp : (1 - x) ^ (4 * a) = Real.exp (Real.log (1 - x) * (4 * a)) := by
    rw [Real.rpow_def_of_pos h1x]
  unfold chainBound
  rw [e1, hp]
  constructor
  · have : Real.exp (Real.log (1 - x) * (4 * a)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.log_nonpos h1x.le (by linarith)
      nlinarith
    linarith
  · have : -(4 / 3) ≤ Real.log (1 - x) * (4 * a) := by
      have := mul_le_mul_of_nonneg_right hlog (by positivity : (0:ℝ) ≤ 4 * a)
      nlinarith
    have := Real.exp_le_exp.mpr this
    linarith

lemma zt_conf (k β : ℝ) (hk : 4 ≤ k) (a : ℝ) (ha : 1 ≤ a) :
    configurationBound k (k ^ β) a (32 * a ^ 2) ≤
      Real.exp (-(3 * Real.exp (-(4/3)) / 16) * (k ^ β * k ^ 2)) := by
  have hk0 : 0 < k := by linarith
  obtain ⟨hc0, hc1⟩ := zt_chain a ha
  set e : ℝ := Real.exp (-(4/3)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hcb : chainBound a (32 * a ^ 2) ≤ Real.exp (-e) := by
    have := Real.add_one_le_exp (-e)
    linarith
  have hh : 0 < k ^ β := Real.rpow_pos_of_pos hk0 β
  set E : ℝ := k ^ β / 2 * (3 * k / 4) * (3 * k / 4 - 1) with hE
  have hE1 : 3 * (k ^ β * k ^ 2) / 16 ≤ E := by
    have h1 : k / 2 ≤ 3 * k / 4 - 1 := by linarith
    have h2 : 0 ≤ k ^ β / 2 * (3 * k / 4) := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    rw [hE]
    nlinarith
  have hE0 : 0 ≤ E := le_trans (by positivity) hE1
  unfold configurationBound
  rw [← hE]
  calc chainBound a (32 * a ^ 2) ^ E ≤ (Real.exp (-e)) ^ E :=
        Real.rpow_le_rpow hc0 hcb hE0
    _ = Real.exp (-e * E) := (Real.exp_mul (-e) E).symm
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have : 3 * (k ^ β * k ^ 2) / 16 * e ≤ E * e := mul_le_mul_of_nonneg_right hE1 he0.le
        nlinarith

lemma zt_count (k a : ℝ) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    countBound k a (32 * a ^ 2) ≤ Real.exp (6 * a * k * Real.log (32 * a ^ 2)) := by
  have hk0 : 0 < k := by linarith
  have ha0 : 0 < a := by linarith
  set d : ℝ := 32 * a ^ 2 with hd
  have hd1 : 1 ≤ d := by rw [hd]; nlinarith
  have hd0 : 0 < d := by linarith
  have h4 : 4 * a + 1 ≤ d := by rw [hd]; nlinarith
  unfold countBound
  calc (4 * a + 1) ^ k * d ^ ((4 * a + 1) * k)
      ≤ d ^ k * d ^ ((4 * a + 1) * k) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.rpow_le_rpow (by positivity) h4 hk0.le
        · exact (Real.rpow_pos_of_pos hd0 _).le
    _ = d ^ (k + (4 * a + 1) * k) := (Real.rpow_add hd0 _ _).symm
    _ ≤ d ^ (6 * a * k) := by
        apply Real.rpow_le_rpow_of_exponent_le hd1
        nlinarith
    _ = Real.exp (6 * a * k * Real.log d) := by
        rw [Real.rpow_def_of_pos hd0]; ring_nf

lemma zt_eps (δ ε γ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, 6 * (Real.log 32 + 2 * δ * Real.log x) < γ * x ^ ε := by
  have h1 := (isLittleO_log_rpow_atTop hε).def' (c := γ / (48 * δ)) (by positivity)
  have h2 : ∀ᶠ x : ℝ in atTop, 2 * (6 * Real.log 32) / γ < x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_gt_atTop _
  filter_upwards [h1.bound, h2, eventually_gt_atTop 1] with x hx1 hx2 hx3
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxe] at hx1
  have hl : Real.log x ≤ γ / (48 * δ) * x ^ ε := le_trans (le_abs_self _) hx1
  have h3 : 2 * δ * Real.log x ≤ 2 * δ * (γ / (48 * δ) * x ^ ε) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  have h4 : 2 * δ * (γ / (48 * δ) * x ^ ε) = γ / 24 * x ^ ε := by field_simp; ring
  have h5 : 6 * Real.log 32 < γ / 2 * x ^ ε := by
    rw [div_lt_iff₀ hγ] at hx2
    nlinarith
  nlinarith

theorem zt_main (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hgap : δ - 1 < β) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → analyticZ k β δ < 1 := by
  set γ : ℝ := 3 * Real.exp (-(4/3)) / 16 with hγ
  have hγ0 : 0 < γ := by positivity
  have hε : 0 < β + 1 - δ := by linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (zt_eps δ (β + 1 - δ) γ hδ hε hγ0)
  refine ⟨max 4 ⌈N⌉₊, le_trans (by norm_num) (le_max_left _ _), fun k hk => ?_⟩
  have hk4 : (4:ℝ) ≤ k := by
    have : 4 ≤ k := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hkN : N ≤ (k:ℝ) := by
    have : ⌈N⌉₊ ≤ k := le_trans (le_max_right _ _) hk
    exact le_trans (Nat.le_ceil N) (by exact_mod_cast this)
  have hk0 : 0 < (k:ℝ) := by linarith
  have hE := hN k hkN
  set x : ℝ := (k:ℝ) with hx
  set a : ℝ := x ^ δ with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow (by linarith) hδ.le
  have ha0 : 0 < a := by linarith
  have hd : x ^ (2 * δ) = a ^ 2 := by
    rw [ha, mul_comm, Real.rpow_mul hk0.le, Real.rpow_two]
  unfold analyticZ z
  rw [hd]
  have hc := zt_conf x β hk4 a ha1
  have hn := zt_count x a (by linarith) ha1
  have hcb0 : 0 ≤ countBound x a (32 * a ^ 2) := by
    unfold countBound; positivity
  have hcf0 : 0 ≤ configurationBound x (x ^ β) a (32 * a ^ 2) := by
    unfold configurationBound
    apply Real.rpow_nonneg (zt_chain a ha1).1
  have hlog : Real.log (32 * a ^ 2) = Real.log 32 + 2 * δ * Real.log x := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, ha, Real.log_rpow hk0]
    push_cast; ring
  have hkb : x ^ β * x ^ 2 = a * x * x ^ (β + 1 - δ) := by
    rw [ha, ← Real.rpow_natCast x 2, Real.rpow_natCast]
    have : x ^ δ * x * x ^ (β + 1 - δ) = x ^ δ * (x ^ (1:ℝ) * x ^ (β + 1 - δ)) := by
      rw [Real.rpow_one]; ring
    rw [this, ← Real.rpow_add hk0, ← Real.rpow_add hk0]
    have h2 : x ^ 2 = x ^ (2:ℝ) := (Real.rpow_two x).symm
    rw [h2, ← Real.rpow_add hk0]
    congr 1; ring
  have hzle : countBound x a (32 * a ^ 2) * configurationBound x (x ^ β) a (32 * a ^ 2) ≤
      Real.exp (6 * a * x * Real.log (32 * a ^ 2)) * Real.exp (-γ * (x ^ β * x ^ 2)) :=
    mul_le_mul hn hc hcf0 (Real.exp_pos _).le
  rw [← Real.exp_add] at hzle
  refine lt_of_le_of_lt hzle ?_
  rw [Real.exp_lt_one_iff]
  rw [hlog, hkb]
  have hax : 0 < a * x := by positivity
  have := mul_lt_mul_of_pos_left hE hax
  nlinarith

end ZhangTangLabelCut.LP2

set_option autoImplicit false

theorem ZhangTangLabelCut.LP2.eventually_z_lt_one (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hgap : δ - 1 < β) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ZhangTangLabelCut.LP2.analyticZ k β δ < 1 :=
  ZhangTangLabelCut.LP2.zt_main β δ hβ hδ hgap
end

-- Source: complexity-labelcut-terra-count/Cuts.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma terminal_path_length_pos (I : LabelCut) (p : Path I.graph I.s I.t) : 0 < p.length := by
  by_contra hn
  have hl : p.length = 0 := by omega
  have hv : (0 : Fin (p.length + 1)) = Fin.last p.length := by
    apply Fin.ext
    simp [hl]
  apply I.distinct
  calc
    I.s = p.vertex 0 := p.start.symm
    _ = p.vertex (Fin.last p.length) := congrArg p.vertex hv
    _ = I.t := p.finish

lemma all_labels_cut (I : LabelCut) : I.Cut Finset.univ := by
  classical
  intro p
  exact ⟨⟨0, terminal_path_length_pos I p⟩, Finset.mem_univ _⟩

lemma cut_mono (I : LabelCut) {S T : Finset I.L} (hST : S ⊆ T) (hcut : I.Cut S) : I.Cut T := by
  intro p
  obtain ⟨j, hj⟩ := hcut p
  exact ⟨j, hST hj⟩

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut/Minimum.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma opt_lower_of_no_card_cut (I : LabelCut) (c : ℕ) (hc : c ≤ Fintype.card I.L)
    (hno : ∀ S : Finset I.L, S.card = c → ¬ I.Cut S) : c ≤ I.opt := by
  classical
  unfold LabelCut.opt
  apply le_csInf
  · exact ⟨Fintype.card I.L, Finset.univ, all_labels_cut I, Finset.card_univ⟩
  · rintro n ⟨S, hcut, hcard⟩
    by_contra hn
    obtain ⟨T, hST, hTc⟩ := Finset.exists_superset_card_eq (by omega : S.card ≤ c) hc
    exact hno T hTc (cut_mono I hST hcut)

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/Realization.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

/-- The hard independent-event and finite-union arguments are checked prerequisites. -/
lemma exists_no_card_cut (k a h : ℕ) (hk : 2 ≤ k) (ha : 0 < a)
    (hkd : k ≤ 32 * a^2)
    (hz : z (k : ℝ) ((32 * a^2 : ℕ) : ℝ) (h : ℝ) (a : ℝ) < 1)
    (directed : Bool) :
    ∃ σ : Sample k (32 * a^2) h,
      ∀ S : Finset (Fin k × Fin (32 * a^2)), S.card = k * a →
        ¬ (shutterInstance k (32 * a^2) h directed σ).Cut S := by
  classical
  let C : Finset (Finset (Fin k × Fin (32 * a ^ 2))) :=
    Finset.univ.powersetCard (k * a)
  let B := {S : Finset (Fin k × Fin (32 * a ^ 2)) // S ∈ C}
  let E : B → Finset (Sample k (32 * a ^ 2) h) := fun S =>
    Finset.univ.filter (fun σ => (shutterInstance k (32 * a ^ 2) h directed σ).Cut S.val)
  let q : ℝ := configurationBound k h a (32 * a ^ 2 : ℕ)
  have hd : 1 ≤ 32 * a ^ 2 := by
    have hp : 0 < 32 * a ^ 2 := by positivity
    omega
  have hcard : (Fintype.card B : ℝ) ≤ countBound k a (32 * a ^ 2 : ℕ) := by
    simpa only [B, Fintype.card_coe, C] using
      (LabelCutCounting.candidates_le_countBound k a (32 * a ^ 2) hkd hd)
  have hq : 0 ≤ q := by
    dsimp only [q, configurationBound]
    apply Real.rpow_nonneg
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using (chainBound_range a ha).1
  have hlt : (Fintype.card B : ℝ) * q < 1 :=
    (mul_le_mul_of_nonneg_right hcard hq).trans_lt hz
  have hs (i : B) : ((E i).card : ℝ) / Fintype.card (Sample k (32 * a ^ 2) h) ≤ q := by
    have hi : i.val.card = k * a := (Finset.mem_powersetCard.mp i.property).2
    exact cut_probability_bound k a h hk ha directed i.val hi
  obtain ⟨σ, hσ⟩ := LabelCutCounting.exists_avoiding E q hs hlt
  refine ⟨σ, ?_⟩
  intro S hS
  have hm : S ∈ C := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩
  simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hσ ⟨S, hm⟩

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut/Optimum.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma exists_optimum_lower (k a h : ℕ) (hk : 2 ≤ k) (ha : 0 < a)
    (hkd : k ≤ 32 * a^2)
    (hz : z (k : ℝ) ((32 * a^2 : ℕ) : ℝ) (h : ℝ) (a : ℝ) < 1)
    (directed : Bool) :
    ∃ σ : Sample k (32 * a^2) h,
      k * a ≤ (shutterInstance k (32 * a^2) h directed σ).opt := by
  obtain ⟨σ, hσ⟩ := exists_no_card_cut k a h hk ha hkd hz directed
  have haDim : a ≤ 32 * a^2 :=
    (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) a).trans
      (Nat.le_mul_of_pos_left (a^2) (by decide : (0 : ℕ) < 32))
  refine ⟨σ, opt_lower_of_no_card_cut (shutterInstance k (32 * a^2) h directed σ) (k * a) ?_ hσ⟩
  change k * a ≤ Fintype.card (Fin k × Fin (32 * a^2))
  simpa only [Fintype.card_prod, Fintype.card_fin] using Nat.mul_le_mul_left k haDim

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut/Exponent.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma exists_integer_exponent (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ (((2 + 3 * D : ℕ) : ℝ) * (1 / 3 - ε) ≤ (D : ℝ)) := by
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / ε)
  have hDpos : 0 < D := Nat.cast_pos.mp ((one_div_pos.mpr hε).trans hD)
  have hlarge : (1 : ℝ) < D * ε := (div_lt_iff₀ hε).mp hD
  refine ⟨D, hDpos, ?_⟩
  push_cast
  nlinarith

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/PowerBounds.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma scaled_vertex_bound (γ : ℝ) (D : ℕ) (hγ : 0 ≤ γ)
    (hExp : (((2 + 3 * D : ℕ) : ℝ) * γ) ≤ (D : ℝ))
    (k v : ℕ) (hk : 2 ≤ k) (hv : 0 < v) (hV : v ≤ 48 * k ^ (2 + 3 * D)) :
    (48 : ℝ) ^ (-γ) * (k : ℝ) * (v : ℝ) ^ γ ≤ (k : ℝ) * ((k ^ D : ℕ) : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hV' : (v : ℝ) ≤ 48 * (k : ℝ) ^ (2 + 3 * D) := by exact_mod_cast hV
  have hkpow : (k : ℝ) ^ (((2 + 3 * D : ℕ) : ℝ) * γ) ≤ (k : ℝ) ^ (D : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hk1 hExp
  have hbound : (v : ℝ) ^ γ ≤ (48 : ℝ) ^ γ * (k : ℝ) ^ (D : ℝ) := by
    calc
      _ ≤ (48 * (k : ℝ) ^ (2 + 3 * D)) ^ γ :=
        Real.rpow_le_rpow (le_of_lt (by exact_mod_cast hv)) hV' hγ
      _ = (48 : ℝ) ^ γ * (k : ℝ) ^ (((2 + 3 * D : ℕ) : ℝ) * γ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_natCast (k : ℝ) (2 + 3 * D), ← Real.rpow_mul (by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hkpow (Real.rpow_nonneg (by norm_num) _)
  have hcancel : (48 : ℝ) ^ (-γ) * (48 : ℝ) ^ γ = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 48), neg_add_cancel, Real.rpow_zero]
  calc
    _ ≤ ((48 : ℝ) ^ (-γ) * k) * ((48 : ℝ) ^ γ * (k : ℝ) ^ (D : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (k : ℝ) * (k : ℝ) ^ (D : ℝ) := by
      calc
        _ = ((48 : ℝ) ^ (-γ) * (48 : ℝ) ^ γ) * ((k : ℝ) * (k : ℝ) ^ (D : ℝ)) := by ring
        _ = _ := by rw [hcancel, one_mul]
    _ = _ := by rw [Real.rpow_natCast, Nat.cast_pow]

lemma analyticZ_nat (k D : ℕ) :
    analyticZ (k : ℝ) (D : ℝ) (D : ℝ) =
      z (k : ℝ) ((32 * (k ^ D)^2 : ℕ) : ℝ) ((k ^ D : ℕ) : ℝ) ((k ^ D : ℕ) : ℝ) := by
  unfold analyticZ
  have h2 : (2 : ℝ) * D = ((2 * D : ℕ) : ℝ) := by push_cast; rfl
  rw [h2, Real.rpow_natCast (k : ℝ) (2 * D)]
  simp only [Real.rpow_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show 2 * D = D * 2 by omega, pow_mul]

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/Budget.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma integer_vertex_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧
      ∀ k v : ℕ, 2 ≤ k → 0 < v → v ≤ 48 * k ^ (2 + 3 * D) →
        C * (k : ℝ) * (v : ℝ) ^ (1 / 3 - ε) ≤ (k : ℝ) * ((k ^ D : ℕ) : ℝ) := by
  by_cases hγ : 0 ≤ (1 / 3 - ε : ℝ)
  · obtain ⟨D, hD, hExp⟩ := exists_integer_exponent ε hε
    refine ⟨D, hD, (48 : ℝ) ^ (-(1 / 3 - ε)), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
    intro k v hk hv hV
    exact scaled_vertex_bound (1 / 3 - ε) D hγ hExp k v hk hv hV
  · refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro k v hk hv _
    have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hp : (v : ℝ) ^ (1 / 3 - ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hv1 (le_of_not_ge hγ)
    simpa only [one_mul, pow_one] using
      (mul_le_mul_of_nonneg_left hp hk0).trans (mul_le_mul_of_nonneg_left hk1 hk0)

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut/Construction.lean
section
set_option autoImplicit false
namespace ZhangTangLabelCut.LP2

lemma construction_from_budget (ε : ℝ) (D : ℕ) (hD : 0 < D) (C : ℝ)
    (hbudget : ∀ k v : ℕ, 2 ≤ k → 0 < v → v ≤ 48 * k ^ (2 + 3 * D) →
      C * (k : ℝ) * (v : ℝ) ^ (1 / 3 - ε) ≤ (k : ℝ) * ((k ^ D : ℕ) : ℝ)) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ directed : Bool,
      ∃ σ : Sample k (32 * k ^ (2 * D)) (k ^ D),
        let I := shutterInstance k (32 * k ^ (2 * D)) (k ^ D) directed σ
        I.Admissible ∧
        C * k * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε) ≤ (I.opt : ℝ) ∧
        Fintype.card I.graph.V ≤ 48 * k ^ (2 + 3 * D) ∧
        Fintype.card I.graph.E ≤ 64 * k ^ (2 + 3 * D) := by
  obtain ⟨k₀, hk₀, hz⟩ := eventually_z_lt_one (D : ℝ) (D : ℝ)
    (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hD) (by linarith)
  refine ⟨k₀, hk₀, fun k hk directed => ?_⟩
  have hk2 : 2 ≤ k := hk₀.trans hk
  have ha : 0 < k^D := pow_pos (by omega : 0 < k) D
  have hkd : k ≤ 32 * (k^D)^2 :=
    (Nat.le_self_pow (Nat.ne_of_gt hD) k).trans
      ((Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) (k^D)).trans
        (Nat.le_mul_of_pos_left ((k^D)^2) (by decide : (0 : ℕ) < 32)))
  have hzSquare : z (k : ℝ) ((32 * (k^D)^2 : ℕ) : ℝ)
      ((k^D : ℕ) : ℝ) ((k^D : ℕ) : ℝ) < 1 := by
    simpa only [analyticZ_nat] using hz k hk
  have hexSquare := exists_optimum_lower k (k^D) (k^D) hk2 ha hkd hzSquare directed
  have hdim : 32 * (k^D)^2 = 32 * k^(2 * D) := by
    rw [← pow_mul, Nat.mul_comm D 2]
  rw [hdim] at hexSquare
  obtain ⟨σ, hopt⟩ := hexSquare
  let I := shutterInstance k (32 * k^(2 * D)) (k^D) directed σ
  have hsizes : Fintype.card I.graph.V ≤ 48 * k^(2 + 3 * D) ∧
      Fintype.card I.graph.E ≤ 64 * k^(2 + 3 * D) :=
    shutter_size_bounds k D hk2 hD directed σ
  have hv : 0 < Fintype.card I.graph.V := Fintype.card_pos_iff.mpr ⟨I.s⟩
  have hbound := hbudget k (Fintype.card I.graph.V) hk2 hv hsizes.1
  have hoptr : (k : ℝ) * ((k^D : ℕ) : ℝ) ≤ (I.opt : ℝ) := by
    exact_mod_cast hopt
  refine ⟨σ, ?_, hbound.trans hoptr, hsizes.1, hsizes.2⟩
  exact shutter_admissible k (32 * k^(2 * D)) (k^D) hk2
    (Nat.mul_pos (by decide) (pow_pos (by omega : 0 < k) _)) ha directed σ

end ZhangTangLabelCut.LP2
end

-- Source: complexity-labelcut-terra-count/Leaf.lean
section
set_option autoImplicit false
open ZhangTangLabelCut.LP2

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ directed : Bool,
        ∃ σ : Sample k (32 * k ^ (2 * D)) (k ^ D),
          let I := shutterInstance k (32 * k ^ (2 * D)) (k ^ D) directed σ
          I.Admissible ∧
          C * k * (Fintype.card I.graph.V : ℝ) ^ (1 / 3 - ε) ≤ (I.opt : ℝ) ∧
          Fintype.card I.graph.V ≤ 48 * k ^ (2 + 3 * D) ∧
          Fintype.card I.graph.E ≤ 64 * k ^ (2 + 3 * D) := by
  obtain ⟨D, hD, C, hC, hbudget⟩ := integer_vertex_budget ε hε
  exact ⟨D, hD, C, hC, construction_from_budget ε D hD C hbudget⟩
end

