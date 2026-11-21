-- Prove2me | solution 1 for TenChallenges.challenge_10_overlappingComponentInterfaces
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T05:05:52.785068+00:00
-- url     : https://prove2.me/submissions/be387e25-1a4d-4760-a0c7-64ccce48283c

import Definitions.Def_TenChallenges_Challenge_10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Finset
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.WellFounded
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order

set_option linter.style.haveILetI false
universe u v w

/- Inlined from Continuation/UnfriendlyBlockAssembly.lean. -/
/-!
# Well-founded assembly of block actions

Each block reads the colours of finitely many vertices in earlier blocks and
outputs a colouring of its own vertices. A prescribed override is applied
before a colour becomes available to later blocks.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.BlockAssembly

/-- A well-founded network of blocks with finitely many parent vertices per block. -/
structure Network (V : Type u) (ι : Type v) where
  owner : V → ι
  parents : ι → Finset V
  lt : ι → ι → Prop
  wf : WellFounded lt
  parent_lt : ∀ i (p : parents i), lt (owner p.val) i

namespace Network

variable {V : Type u} {ι : Type v} (N : Network V ι)

abbrev Vertices (i : ι) := {v : V // N.owner v = i}

abbrev Action (i : ι) := (N.parents i → Bool) → (N.Vertices i → Bool)

abbrev Assignment := (i : ι) → N.Action i

private noncomputable def output (actions : N.Assignment) (override : V → Option Bool) :
    (i : ι) → N.Vertices i → Bool :=
  N.wf.fix fun i previous v =>
    (override v.val).getD (actions i
      (fun p => previous (N.owner p.val) (N.parent_lt i p) ⟨p.val, rfl⟩) v)

/-- Evaluate each action on the assembled colours of its parents and apply any override. -/
noncomputable def assemble (actions : N.Assignment) (override : V → Option Bool) : V → Bool :=
  fun v => N.output actions override (N.owner v) ⟨v, rfl⟩

theorem assemble_eq (actions : N.Assignment) (override : V → Option Bool) (v : V) :
    N.assemble actions override v =
      (override v).getD
        (actions (N.owner v) (fun p => N.assemble actions override p.val) ⟨v, rfl⟩) := by
  unfold assemble output
  rw [WellFounded.fix_eq]

/-- A set of blocks is forward-closed if it contains every block that reads one of its colours. -/
def ForwardClosed (C : Set ι) : Prop :=
  ∀ i (p : N.parents i), N.owner p.val ∈ C → i ∈ C

/-- Changing actions only in a forward-closed set cannot change any colour outside it. -/
theorem assemble_eqOn_outside (actions other : N.Assignment) (override : V → Option Bool)
    {C : Set ι} (hC : N.ForwardClosed C) (hact : ∀ i ∉ C, actions i = other i) :
    Set.EqOn (N.assemble actions override) (N.assemble other override)
      {v | N.owner v ∉ C} := by
  intro v hv
  suffices h : ∀ i v, N.owner v = i → i ∉ C →
      N.assemble actions override v = N.assemble other override v from h _ _ rfl hv
  intro i
  refine N.wf.induction (C := fun i => ∀ (v : V), N.owner v = i → i ∉ C →
    N.assemble actions override v = N.assemble other override v) i ?_
  intro i ih v howner hi
  subst i
  have hparents :
      (fun p : N.parents (N.owner v) => N.assemble actions override p.val) =
        (fun p : N.parents (N.owner v) => N.assemble other override p.val) :=
    funext fun p => ih (N.owner p.val) (N.parent_lt _ p) p.val rfl
      (fun hp => hi (hC (N.owner v) p hp))
  rw [N.assemble_eq actions override v, N.assemble_eq other override v, hact _ hi, hparents]

/-- Prescribing colours already used by the unoverridden assembly preserves that assembly. -/
theorem assemble_override_eq (actions : N.Assignment) (override : V → Option Bool)
    (h : ∀ v b, override v = some b → N.assemble actions (fun _ => none) v = b) :
    N.assemble actions override = N.assemble actions (fun _ => none) := by
  funext v
  suffices hEq : ∀ i v, N.owner v = i →
      N.assemble actions override v = N.assemble actions (fun _ => none) v from hEq _ _ rfl
  intro i
  refine N.wf.induction (C := fun i => ∀ (v : V), N.owner v = i →
    N.assemble actions override v = N.assemble actions (fun _ => none) v) i ?_
  intro i ih v howner
  subst i
  cases hov : override v
  · have hparents :
        (fun p : N.parents (N.owner v) => N.assemble actions override p.val) =
          (fun p : N.parents (N.owner v) => N.assemble actions (fun _ => none) p.val) :=
      funext fun p => ih (N.owner p.val) (N.parent_lt _ p) p.val rfl
    rw [N.assemble_eq actions override v, N.assemble_eq actions (fun _ => none) v, hov,
      hparents]
  · rename_i b
    rw [N.assemble_eq actions override v, hov]
    exact (h v b hov).symm

/-- For fixed overrides, assembly is continuous in the discrete block actions. -/
theorem continuous_assemble [TopologicalSpace Bool] [DiscreteTopology Bool]
    [∀ i, TopologicalSpace (N.Action i)] [∀ i, DiscreteTopology (N.Action i)]
    (override : V → Option Bool) :
    Continuous (fun actions : N.Assignment => N.assemble actions override) := by
  refine continuous_pi fun v => ?_
  suffices h : ∀ i v, N.owner v = i →
      Continuous (fun a : N.Assignment => N.assemble a override v) from h _ _ rfl
  intro i
  refine N.wf.induction (C := fun i => ∀ (v : V), N.owner v = i →
    Continuous (fun a : N.Assignment => N.assemble a override v)) i ?_
  intro i ih v hv
  subst i
  let readParents (a : N.Assignment) : N.parents (N.owner v) → Bool :=
    fun p => N.assemble a override p.val
  have hread : Continuous readParents :=
    continuous_pi fun p => ih (N.owner p.val) (N.parent_lt _ p) p.val rfl
  let evaluate (z : N.Action (N.owner v) × (N.parents (N.owner v) → Bool)) : Bool :=
    (override v).getD (z.1 z.2 ⟨v, rfl⟩)
  have heval : Continuous evaluate := continuous_of_discreteTopology
  have hpair : Continuous (fun a : N.Assignment => (a (N.owner v), readParents a)) :=
    (continuous_apply (N.owner v)).prodMk hread
  convert heval.comp hpair using 1
  funext a
  exact N.assemble_eq a override v

end Network

end TenChallenges.Continuation.BlockAssembly

/- Inlined from Continuation/UnfriendlyBlockOwnership.lean. -/
/-!
# Ownership of blocks in a well-founded schedule

Assign each vertex to the earliest member of a covering family that contains it.
Any other member containing it reads its colour from an earlier block.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.BlockOwnership

/-- A well-founded order on a covering family determines an owner for each
vertex if sets that intersect are comparable. -/
theorem exists_owner {V : Type u} {I : Type v} (A : I → Set V)
    (hfinite : ∀ i, (A i).Finite) (hcover : ∀ x, ∃ i, x ∈ A i)
    (before : I → I → Prop) (hwf : WellFounded before)
    (hcompare : ∀ i j, i ≠ j → ∀ x ∈ A i, x ∈ A j → before i j ∨ before j i) :
    ∃ owner : V → I, (∀ x, x ∈ A (owner x)) ∧ (∀ i, {x | owner x = i}.Finite) ∧
      ∀ i x, x ∈ A i → owner x ≠ i → before (owner x) i := by
  choose owner howner hmin using fun x => hwf.has_min {i | x ∈ A i} (hcover x)
  exact ⟨owner, howner, fun i => (hfinite i).subset fun x (hx : owner x = i) => hx ▸ howner x,
    fun i x hx hne => (hcompare _ _ hne x (howner x) hx).resolve_right (hmin x i hx)⟩

/-- Inside a round colours can influence other blocks at the same level.
Between rounds only an even level can influence an adjacent odd level. -/
def BandInfluence (m n : ℕ) : Prop :=
  m = n ∨ (m % 2 = 0 ∧ n % 2 = 1 ∧ m ≤ n + 1 ∧ n ≤ m + 1)

/-- Influence cannot pass through two changes of round. -/
theorem BandInfluence.trans {a b c : ℕ} (hab : BandInfluence a b)
    (hbc : BandInfluence b c) : BandInfluence a c := by
  rcases hab with hab | hab
  · exact hab ▸ hbc
  rcases hbc with hbc | hbc
  · exact hbc ▸ Or.inr hab
  · exact (Nat.one_ne_zero (hab.2.1.symm.trans hbc.1)).elim

/-- If each level in each component has finitely many blocks, any one block
lies in a finite set closed under the permitted influence relation. -/
theorem finite_influence_closure {I : Type u} {K : Type v}
    (component : I → K) (level : I → ℕ)
    (hfinite : ∀ k n, {j | component j = k ∧ level j = n}.Finite)
    (i : I) :
    ∃ S : Set I, S.Finite ∧ i ∈ S ∧
      ∀ j ∈ S, ∀ k, component j = component k →
        BandInfluence (level j) (level k) → k ∈ S := by
  let S := {j | component i = component j ∧ BandInfluence (level i) (level j)}
  have hS : S.Finite := by
    refine (((hfinite (component i) (level i - 1)).union (hfinite (component i) (level i))).union
      (hfinite (component i) (level i + 1))).subset ?_
    intro j hj
    have hc : component j = component i := hj.1.symm
    rcases hj.2 with he | he
    · exact Or.inl (Or.inr ⟨hc, he.symm⟩)
    have hlevel : level j = level i - 1 ∨ level j = level i ∨ level j = level i + 1 := by
      have := he.2.2.1
      have := he.2.2.2
      omega
    exact hlevel.elim (fun hm => Or.inl (Or.inl ⟨hc, hm⟩)) fun h =>
      h.elim (fun hm => Or.inl (Or.inr ⟨hc, hm⟩)) (fun hm => Or.inr ⟨hc, hm⟩)
  exact ⟨S, hS, ⟨rfl, Or.inl rfl⟩, fun j hj k hc hk => ⟨hj.1.trans hc, hj.2.trans hk⟩⟩

end TenChallenges.Continuation.BlockOwnership

/- Inlined from Continuation/UnfriendlyEnergy.lean. -/
/-!
# Directed cut energy for finite color flips

The energy counts both orientations of each edge. Its sign agrees with ordinary
cut improvement, while a singleton perturbation has the uniform bound `4 * k`.
All identities involving sums assume that the flipped vertices have finite degree.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators symmDiff

variable {V : Type u}

open Classical in
/-- Reverse the colors on a finite vertex set. -/
noncomputable def flip (c : V → Bool) (S : Finset V) : V → Bool :=
  fun x => if x ∈ S then !(c x) else c x

/-- The indicator that a directed pair crosses the color classes. -/
def cutIndicator (c : V → Bool) (e : V × V) : ℤ :=
  if c e.1 ≠ c e.2 then 1 else 0

open Classical in
/-- Change in the directed cut indicator along one adjacent pair. -/
noncomputable def edgeDelta (G : SimpleGraph V) (c d : V → Bool) (e : V × V) : ℤ :=
  if G.Adj e.1 e.2 then cutIndicator d e - cutIndicator c e else 0

/-- Directed cut gain from a finite color flip; finite-degree hypotheses ensure finite support. -/
noncomputable def gain (G : SimpleGraph V) (c : V → Bool) (S : Finset V) : ℤ :=
  ∑ᶠ e, edgeDelta G c (flip c S) e

/-- Directed edges that become crossing edges after the flip. -/
def gained (G : SimpleGraph V) (c : V → Bool) (S : Finset V) : Set (V × V) :=
  {e | edgeDelta G c (flip c S) e = 1}

/-- Directed edges that cease to be crossing edges after the flip. -/
def lost (G : SimpleGraph V) (c : V → Bool) (S : Finset V) : Set (V × V) :=
  {e | edgeDelta G c (flip c S) e = -1}

/-- No finite flip of finite-degree vertices in `A` improves the cut. -/
def StrongMaximal (G : SimpleGraph V) (A : Set V) (c : V → Bool) : Prop :=
  ∀ S : Finset V, (S : Set V) ⊆ A →
    (∀ x ∈ S, (G.neighborSet x).Finite) → gain G c S ≤ 0

/-- Adjacent directed pairs with at least one endpoint in `S`. -/
def incident (G : SimpleGraph V) (S : Finset V) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧ (e.1 ∈ S ∨ e.2 ∈ S)}

@[simp] theorem flip_empty (c : V → Bool) : flip c ∅ = c :=
  funext fun x => if_neg (Finset.notMem_empty x)

@[simp] theorem gain_empty (G : SimpleGraph V) (c : V → Bool) : gain G c ∅ = 0 := by
  simp [gain, edgeDelta]

open Classical in
/-- Two finite flips compose by symmetric difference. -/
theorem flip_symmDiff (c : V → Bool) (S T : Finset V) :
    flip c (S ∆ T) = flip (flip c S) T := by
  funext x
  by_cases hxS : x ∈ S
  all_goals by_cases hxT : x ∈ T
  all_goals simp_all [flip, Finset.mem_symmDiff]

/-- Finite sets of finite-degree vertices meet only finitely many directed edges. -/
theorem incident_finite (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) : (incident G S).Finite := by
  exact (S.finite_toSet.biUnion (fun x hx =>
    ((hS x hx).image (fun y => (x, y))).union
      ((hS x hx).image (fun y => (y, x))))).subset
    (fun e he => he.2.elim
      (fun hx => Set.mem_iUnion.mpr ⟨e.1, Set.mem_iUnion.mpr
        ⟨hx, Or.inl ⟨e.2, he.1, rfl⟩⟩⟩)
      (fun hy => Set.mem_iUnion.mpr ⟨e.2, Set.mem_iUnion.mpr
        ⟨hy, Or.inr ⟨e.1, he.1.symm, rfl⟩⟩⟩))

private theorem edgeDelta_flip_zero (G : SimpleGraph V) (c : V → Bool)
    (S : Finset V) (e : V × V) (h : e ∉ incident G S) :
    edgeDelta G c (flip c S) e = 0 := by
  classical
  by_cases ha : G.Adj e.1 e.2
  · simp [edgeDelta, cutIndicator, flip, ha,
      (show e.1 ∉ S from fun hx => h ⟨ha, Or.inl hx⟩),
      (show e.2 ∉ S from fun hy => h ⟨ha, Or.inr hy⟩)]
  · simp [edgeDelta, ha]

/-- A finite flip changes only incident directed edges. -/
theorem support_edgeDelta_flip_subset (G : SimpleGraph V) (c : V → Bool) (S : Finset V) :
    Function.support (edgeDelta G c (flip c S)) ⊆ incident G S :=
  fun e he => Classical.byContradiction
    (fun hn => he (edgeDelta_flip_zero G c S e hn))

/-- The directed gain function has finite support for a flip of finite-degree vertices. -/
theorem gain_hasFiniteSupport (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) :
    (edgeDelta G c (flip c S)).HasFiniteSupport :=
  (incident_finite G S hS).subset (support_edgeDelta_flip_subset G c S)

/-- A flip of finite-degree vertices gains only finitely many directed edges. -/
theorem gained_finite (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) : (gained G c S).Finite :=
  (gain_hasFiniteSupport G c S hS).subset
    (fun _ he => ne_of_eq_of_ne he (by decide : (1 : ℤ) ≠ 0))

/-- A flip of finite-degree vertices loses only finitely many directed edges. -/
theorem lost_finite (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) : (lost G c S).Finite :=
  (gain_hasFiniteSupport G c S hS).subset
    (fun _ he => ne_of_eq_of_ne he (by decide : (-1 : ℤ) ≠ 0))

private theorem edgeDelta_add (G : SimpleGraph V) (c d q : V → Bool) (e : V × V) :
    edgeDelta G c q e = edgeDelta G c d e + edgeDelta G d q e := by
  unfold edgeDelta
  split_ifs
  all_goals omega

open Classical in
/-- Cut gains add along successive finite flips. -/
theorem gain_symmDiff (G : SimpleGraph V) (c : V → Bool) (S T : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite)
    (hT : ∀ x ∈ T, (G.neighborSet x).Finite) :
    gain G c (S ∆ T) = gain G c S + gain G (flip c S) T := by
  unfold gain
  rw [flip_symmDiff]
  rw [show edgeDelta G c (flip (flip c S) T) =
      (fun e => edgeDelta G c (flip c S) e +
        edgeDelta G (flip c S) (flip (flip c S) T) e) from
    funext (edgeDelta_add G c (flip c S) (flip (flip c S) T))]
  exact finsum_add_distrib (gain_hasFiniteSupport G c S hS)
    (gain_hasFiniteSupport G (flip c S) T hT)

/-- Gain depends only on colors at endpoints of incident edges. -/
theorem gain_congr_of_incident_eq (G : SimpleGraph V) (c d : V → Bool) (S : Finset V)
    (h : ∀ e ∈ incident G S, c e.1 = d e.1 ∧ c e.2 = d e.2) :
    gain G c S = gain G d S := by
  classical
  apply finsum_congr
  intro e
  by_cases he : e ∈ incident G S
  · simp only [edgeDelta, cutIndicator, flip, (h e he).1, (h e he).2]
    rfl
  · exact (edgeDelta_flip_zero G c S e he).trans (edgeDelta_flip_zero G d S e he).symm

/-- Every admissible finite-flip energy depends on finitely many color coordinates. -/
theorem gain_finite_dependence (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) :
    ∃ W : Finset V, ∀ c d : V → Bool,
      (∀ x ∈ W, c x = d x) → gain G c S = gain G d S := by
  classical
  let E := (incident_finite G S hS).toFinset
  exact ⟨E.image Prod.fst ∪ E.image Prod.snd, fun c d h =>
    gain_congr_of_incident_eq G c d S (fun e he =>
      let hE : e ∈ E := (incident_finite G S hS).mem_toFinset.mpr he
      ⟨h e.1 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, hE, rfl⟩)),
        h e.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, hE, rfl⟩))⟩)⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyEnergyBound.lean. -/
/-!
# A uniform bound after changing one boundary color

Only finite-degree repair supports enter the energy sums. The singleton boundary
vertex may have infinite degree; no energy identity is applied to its singleton.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators symmDiff

variable {V : Type u}

open Classical in
/-- Both orientations of pairs joining `v` to the finite opposite-neighbor cover. -/
noncomputable def oppositePairs (v : V) (O : Finset V) : Finset (V × V) :=
  O.image (fun w => (v, w)) ∪ O.image (fun w => (w, v))

open Classical in
/-- A pointwise allowance for the positive effect of a boundary singleton flip. -/
noncomputable def pairAllowance (v : V) (O : Finset V) (e : V × V) : ℤ :=
  if e ∈ oppositePairs v O then 2 else 0

private theorem edgeDelta_bounds (G : SimpleGraph V) (c d : V → Bool) (e : V × V) :
    -1 ≤ edgeDelta G c d e ∧ edgeDelta G c d e ≤ 1 := by
  unfold edgeDelta cutIndicator
  split_ifs
  all_goals omega

open Classical in
private theorem same_of_not_oppositePairs (G : SimpleGraph V) (c : V → Bool)
    (v : V) (O : Finset V)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O)
    (x y : V) (ha : G.Adj x y) (hr : (x, y) ∉ oppositePairs v O)
    (ht : x = v ∨ y = v) : c x = c y :=
  Classical.byContradiction (fun hn => ht.elim
    (fun hx => hr (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨y, hO y (hx ▸ ha) (fun hc => hn ((congrArg c hx).trans hc.symm)),
        Prod.ext hx.symm rfl⟩)))
    (fun hy => hr (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨x, hO x (hy ▸ ha.symm) (fun hc => hn (hc.trans (congrArg c hy).symm)),
        Prod.ext rfl hy.symm⟩))))

private theorem edgeDelta_singleton_le_of_same (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S : Finset V) (hvS : v ∉ S) (x y : V)
    (hsame : G.Adj x y → (x = v ∨ y = v) → c x = c y) :
    edgeDelta G (flip c {v}) (flip (flip c {v}) S) (x, y) ≤
      edgeDelta G c (flip c S) (x, y) := by
  classical
  by_cases ha : G.Adj x y
  all_goals by_cases hx : x = v
  all_goals by_cases hy : y = v
  all_goals by_cases hxS : x ∈ S
  all_goals by_cases hyS : y ∈ S
  all_goals simp_all [edgeDelta, cutIndicator, flip]

/-- Only pairs to original opposite-colored neighbors can contribute positive perturbation. -/
theorem edgeDelta_singleton_le (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S O : Finset V) (hvS : v ∉ S)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O) (e : V × V) :
    edgeDelta G (flip c {v}) (flip (flip c {v}) S) e ≤
      edgeDelta G c (flip c S) e + pairAllowance v O e := by
  classical
  by_cases he : e ∈ oppositePairs v O
  · have hb := And.intro (edgeDelta_bounds G (flip c {v}) (flip (flip c {v}) S) e).2
        (edgeDelta_bounds G c (flip c S) e).1
    simp only [pairAllowance, if_pos he]
    omega
  · simpa only [pairAllowance, if_neg he, add_zero] using
      edgeDelta_singleton_le_of_same G c v S hvS e.1 e.2
        (fun ha ht => same_of_not_oppositePairs G c v O hO e.1 e.2 ha he ht)

private theorem pairAllowance_sum (v : V) (O : Finset V) (U : Finset (V × V))
    (hRU : oppositePairs v O ⊆ U) :
    (∑ e ∈ U, pairAllowance v O e) = 2 * ((oppositePairs v O).card : ℤ) := by
  classical
  simp [pairAllowance, Finset.inter_eq_right.mpr hRU, mul_comm]

open Classical in
private theorem oppositePairs_card_le (v : V) (O : Finset V) :
    (oppositePairs v O).card ≤ 2 * O.card :=
  (Finset.card_union_le ..).trans
    ((Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans_eq (two_mul O.card).symm)

/-- Changing an external boundary vertex raises any admissible repair gain by at most `4|O|`. -/
theorem gain_singleton_perturbation_le (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S O : Finset V) (hvS : v ∉ S)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O) :
    gain G (flip c {v}) S ≤ gain G c S + 4 * (O.card : ℤ) := by
  classical
  let U := (incident_finite G S hS).toFinset ∪ oppositePairs v O
  have hsum (d : V → Bool) : gain G d S = ∑ e ∈ U, edgeDelta G d (flip d S) e :=
    finsum_eq_sum_of_support_subset _ (fun e he => Finset.mem_union_left _
      ((incident_finite G S hS).mem_toFinset.mpr (support_edgeDelta_flip_subset G d S he)))
  have hle := Finset.sum_le_sum (s := U)
    (fun e (_ : e ∈ U) => edgeDelta_singleton_le G c v S O hvS hO e)
  rw [Finset.sum_add_distrib, pairAllowance_sum v O U Finset.subset_union_right,
    ← hsum (flip c {v}), ← hsum c] at hle
  have hcard := oppositePairs_card_le v O
  omega

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyFiniteRepair.lean. -/
set_option autoImplicit false


namespace TenChallenges.Continuation.FiniteRepair

open scoped symmDiff

/-- A bounded integer cut gain attains a finite flip after which no allowed flip improves it. -/
theorem exists_stable_flip {V : Type u} [DecidableEq V] {C : Type v}
    (allowed : Finset V → Prop) (hempty : allowed ∅)
    (hclosed : ∀ s t, allowed s → allowed t → allowed (s ∆ t))
    (flip : C → Finset V → C) (gain : C → Finset V → ℤ)
    (hcocycle : ∀ c s t, allowed s → allowed t →
      gain c (s ∆ t) = gain c s + gain (flip c s) t)
    (c : C) (B : ℤ) (hbound : ∀ s, allowed s → gain c s ≤ B) :
    ∃ s, allowed s ∧ ∀ t, allowed t → gain (flip c s) t ≤ 0 := by
  obtain ⟨m, ⟨s, hs, hsm⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ s, allowed s ∧ gain c s = z)
    ⟨B, fun z ⟨s, hs, hz⟩ => hz ▸ hbound s hs⟩
    ⟨gain c ∅, ∅, hempty, rfl⟩
  refine ⟨s, hs, ?_⟩
  intro t ht
  have hle := hmax (gain c (s ∆ t)) ⟨s ∆ t, hclosed s t hs ht, rfl⟩
  rw [hcocycle c s t hs ht, hsm] at hle
  exact (add_le_iff_nonpos_right _).mp hle

end TenChallenges.Continuation.FiniteRepair

/- Inlined from Continuation/UnfriendlyRepair.lean. -/
/-!
# Finite repair of strong cut maximality after a boundary flip

A strongly maximal coloring can be repaired within its maximality domain after
changing an external vertex with only finitely many original opposite neighbors.
The result uses neither countability nor finite degree of the changed vertex.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped symmDiff

variable {V : Type u}

/-- A finite opposite-neighbor cover bounds the repair needed after an external singleton flip. -/
theorem exists_strongMaximal_repair (G : SimpleGraph V) (A : Set V) (c : V → Bool)
    (hc : StrongMaximal G A c) (v : V) (hv : v ∉ A) (O : Finset V)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O) :
    ∃ S : Finset V, (S : Set V) ⊆ A ∧
      (∀ x ∈ S, (G.neighborSet x).Finite) ∧
      StrongMaximal G A (flip (flip c {v}) S) := by
  classical
  let allowed : Finset V → Prop := fun S =>
    (S : Set V) ⊆ A ∧ ∀ x ∈ S, (G.neighborSet x).Finite
  have hempty : allowed ∅ := by simp [allowed]
  have hclosed : ∀ S T, allowed S → allowed T → allowed (S ∆ T) :=
    fun S T hS hT =>
      ⟨fun x hx => (Finset.mem_symmDiff.mp hx).elim
        (fun h => hS.1 h.1) (fun h => hT.1 h.1),
        fun x hx => (Finset.mem_symmDiff.mp hx).elim
          (fun h => hS.2 x h.1) (fun h => hT.2 x h.1)⟩
  have hbound : ∀ S, allowed S → gain G (flip c {v}) S ≤ 4 * (O.card : ℤ) :=
    fun S hS => (gain_singleton_perturbation_le G c v S O
      (fun hvin => hv (hS.1 hvin)) hS.2 hO).trans
        ((Int.add_le_add_right (hc S hS.1 hS.2) (4 * (O.card : ℤ))).trans_eq (zero_add _))
  obtain ⟨S, hS, hstable⟩ :=
    TenChallenges.Continuation.FiniteRepair.exists_stable_flip allowed hempty hclosed
      flip (gain G) (fun d S T hS hT => gain_symmDiff G d S T hS.2 hT.2)
      (flip c {v}) (4 * (O.card : ℤ)) hbound
  exact ⟨S, hS.1, hS.2, fun T hTA hTN => hstable T ⟨hTA, hTN⟩⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyFiniteBoundaryRepair.lean. -/
/-!
# Repair with a finite interface

For a change outside a strongly maximal domain, only neighbours inside the
domain need to be counted. A finite set of such boundary changes can be
repaired using finitely many changes of finite-degree vertices.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

variable {V : Type u}

private def incidentGraph (G : SimpleGraph V) (A : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∈ A ∨ y ∈ A)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

private theorem gain_incidentGraph (G : SimpleGraph V) (A : Set V) (c : V → Bool)
    (S : Finset V) (hS : (S : Set V) ⊆ A) :
    gain (incidentGraph G A) c S = gain G c S := by
  classical
  apply finsum_congr
  intro e
  by_cases h : e.1 ∈ S ∨ e.2 ∈ S
  · have he : (incidentGraph G A).Adj e.1 e.2 ↔ G.Adj e.1 e.2 :=
      ⟨fun h => h.1, fun he => ⟨he, h.imp (fun hx => hS hx) (fun hx => hS hx)⟩⟩
    simp only [edgeDelta, he]
  have hx : e.1 ∉ S := fun hx => h (Or.inl hx)
  have hy : e.2 ∉ S := fun hy => h (Or.inr hy)
  simp [edgeDelta, cutIndicator, flip, hx, hy]

/-- Boundary repair needs only a finite supply of opposite neighbours within
the repair domain. Neighbours outside the domain impose no finiteness premise. -/
theorem exists_strongMaximal_repair_inside (G : SimpleGraph V) (A : Set V) (c : V → Bool)
    (hA : ∀ x ∈ A, (G.neighborSet x).Finite) (hc : StrongMaximal G A c)
    (v : V) (hv : v ∉ A)
    (hOpp : {x | x ∈ A ∧ G.Adj v x ∧ c x ≠ c v}.Finite) :
    ∃ S : Finset V, (S : Set V) ⊆ A ∧ StrongMaximal G A (flip (flip c {v}) S) := by
  let P := incidentGraph G A
  have hP : StrongMaximal P A c := fun S hSA _ =>
    (gain_incidentGraph G A c S hSA).trans_le (hc S hSA (fun x hx => hA x (hSA hx)))
  obtain ⟨S, hSA, _, hs⟩ := exists_strongMaximal_repair P A c hP v hv hOpp.toFinset
    (fun x ha hn => hOpp.mem_toFinset.mpr ⟨ha.2.resolve_left hv, ha.1, hn⟩)
  refine ⟨S, hSA, fun Q hQA hQ => ?_⟩
  have hQP (x : V) (hx : x ∈ Q) : (P.neighborSet x).Finite :=
    (hQ x hx).subset fun _ h => h.1
  exact (gain_incidentGraph G A (flip (flip c {v}) S) Q hQA).symm.trans_le (hs Q hQA hQP)

/-- Finitely many prescribed colours outside `A` can be changed while preserving
strong cut maximality in `A` by a finite repair. Each prescribed vertex has
only finitely many neighbours in `A`. -/
theorem exists_strongMaximal_of_finite_boundary (G : SimpleGraph V) (A : Set V)
    (c₀ d : V → Bool) (hA : ∀ x ∈ A, (G.neighborSet x).Finite) (hc₀ : StrongMaximal G A c₀)
    (B : Finset V) (hB : ∀ x ∈ B, x ∉ A ∧ (G.neighborSet x ∩ A).Finite) :
    ∃ c : V → Bool, Set.EqOn c d B ∧ Set.EqOn c c₀ (A ∪ (B : Set V))ᶜ ∧
      StrongMaximal G A c ∧ {x | c x ≠ c₀ x}.Finite := by
  classical
  revert hB
  induction B using Finset.induction_on
  case insert v B hvB ih =>
    intro hB
    obtain ⟨c, hcd, hcc₀, hmax, hdiff⟩ := ih (fun x hx => hB x (Finset.mem_insert_of_mem hx))
    have hv := hB v (Finset.mem_insert_self v B)
    by_cases hcv : c v = d v
    · exact ⟨c, fun x hx => (Finset.mem_insert.mp hx).elim (fun h => h ▸ hcv) (fun h => hcd h),
        fun x hx => hcc₀ (fun h => h.elim (fun hA => hx (Or.inl hA))
          (fun hB => hx (Or.inr (Finset.mem_insert_of_mem hB)))), hmax, hdiff⟩
    have hOpp : {x | x ∈ A ∧ G.Adj v x ∧ c x ≠ c v}.Finite :=
      hv.2.subset fun _ h => ⟨h.2.1, h.1⟩
    obtain ⟨S, hSA, hnew⟩ := exists_strongMaximal_repair_inside G A c hA hmax v hv.1 hOpp
    let c' := flip (flip c {v}) S
    have hvd : (!c v) = d v := by
      cases hc : c v <;> cases hd : d v <;> simp_all
    have keep (y : V) (hyv : y ≠ v) (hyS : y ∉ S) : c' y = c y := by
      simp [c', flip, hyS, hyv]
    have atv : c' v = d v := by
      simpa [c', flip, show v ∉ S from fun h => hv.1 (hSA h)] using hvd
    refine ⟨c', ?_, ?_, hnew, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with e | hxB
      · exact e ▸ atv
      · exact (keep x (fun e => hvB (e ▸ hxB))
          (fun hxS => (hB x (Finset.mem_insert_of_mem hxB)).1 (hSA hxS))).trans (hcd hxB)
    · intro x hx
      exact (keep x (fun e => hx (Or.inr (e.symm ▸ Finset.mem_insert_self v B)))
        (fun h => hx (Or.inl (hSA h)))).trans
        (hcc₀ (fun h => h.elim (fun hA => hx (Or.inl hA))
          (fun hB => hx (Or.inr (Finset.mem_insert_of_mem hB)))))
    · refine (hdiff.union (S ∪ {v}).finite_toSet).subset ?_
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inr (Finset.mem_union_left _ hxS)
      by_cases hxv : x = v
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_singleton.mpr hxv))
      exact Or.inl (fun e => hx ((keep x hxv hxS).trans e))
  case empty =>
    exact fun _ => ⟨c₀, by simp, fun _ _ => rfl, hc₀, Set.finite_empty.subset (fun _ h => h rfl)⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyInfiniteStability.lean. -/
/-!
# Infinite opposite neighborhoods and finite perturbations

On countable graphs, an infinite opposite-colored neighborhood guarantees the
canonical unfriendly inequality. At an infinite-degree vertex this condition is
also necessary. Finite flips away from the vertex preserve it.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped Cardinal

variable {V : Type u}

/-- Neighbors whose Boolean color is opposite to the vertex's color. -/
def oppositeSet (G : SimpleGraph V) (c : V → Bool) (v : V) : Set V :=
  {w | G.Adj v w ∧ c w ≠ c v}

lemma oppositeSet_eq_colored (G : SimpleGraph V) (c : V → Bool) (v : V) :
    oppositeSet G c v =
      G.neighborSet v ∩ (fun w => some (c w)) ⁻¹' {some (!(c v))} := by
  ext w
  simp [oppositeSet, Bool.eq_not]

/-- Infinitely many opponents ensure the unfriendly inequality on a countable graph. -/
theorem unfriendly_of_infinite_opposite [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (v : V) (hO : (oppositeSet G c v).Infinite) :
    UnfriendlyAt G (fun w => some (c w)) v := by
  haveI : Infinite (NeighColored G (fun w => some (c w)) v (some (!(c v)))) :=
    Set.infinite_coe_iff.mpr ((oppositeSet_eq_colored G c v) ▸ hO)
  haveI : Countable (NeighColored G (fun w => some (c w)) v (some (c v))) :=
    inferInstanceAs (Countable {w : V // G.Adj v w ∧ some (c w) = some (c v)})
  exact ⟨c v, rfl, Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_mk _)⟩

/-- At any infinite-degree vertex, the unfriendly inequality forces infinitely many opponents. -/
theorem infinite_opposite_of_unfriendly (G : SimpleGraph V) (c : V → Bool) (v : V)
    (hN : (G.neighborSet v).Infinite) (hUF : UnfriendlyAt G (fun w => some (c w)) v) :
    (oppositeSet G c v).Infinite := by
  classical
  obtain ⟨b, hv, hcard⟩ := hUF
  obtain rfl : b = c v := (Option.some.inj hv).symm
  by_contra hO
  have hOfin : (oppositeSet G c v).Finite := Set.not_infinite.mp hO
  haveI : Finite (NeighColored G (fun w => some (c w)) v (some (!(c v)))) :=
    Set.finite_coe_iff.mpr ((oppositeSet_eq_colored G c v) ▸ hOfin)
  obtain ⟨e⟩ := (Cardinal.le_def ..).mp hcard
  haveI : Finite (NeighColored G (fun w => some (c w)) v (some (c v))) :=
    Finite.of_injective e e.injective
  have hSfin : (G.neighborSet v ∩ (fun w => some (c w)) ⁻¹' {some (c v)}).Finite :=
    Set.finite_coe_iff.mp
      (inferInstance : Finite (NeighColored G (fun w => some (c w)) v (some (c v))))
  exact hN ((hSfin.union hOfin).subset (fun w hw => (Classical.em (c w = c v)).elim
    (fun hc => Or.inl ⟨hw, congrArg some hc⟩) (fun hc => Or.inr ⟨hw, hc⟩)))

/-- A bad vertex in a countable graph has only finitely many opposite-colored neighbors. -/
theorem opposite_finite_of_not_unfriendly [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (v : V) (hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v) :
    (oppositeSet G c v).Finite :=
  Set.not_infinite.mp (fun hO => hbad (unfriendly_of_infinite_opposite G c v hO))

/-- A finite flip away from a vertex preserves its infinite opposite neighborhood. -/
theorem infinite_opposite_flip (G : SimpleGraph V) (c : V → Bool) (v : V)
    (S : Finset V) (hvS : v ∉ S) (hO : (oppositeSet G c v).Infinite) :
    (oppositeSet G (flip c S) v).Infinite := by
  classical
  have hsub : oppositeSet G c v \ (S : Set V) ⊆ oppositeSet G (flip c S) v :=
    fun w hw => ⟨hw.1.1, fun heq => hw.1.2
      ((if_neg hw.2).symm.trans (heq.trans (if_neg hvS)))⟩
  exact Set.Infinite.mono hsub (hO.sdiff S.finite_toSet)

/-- Unfriendliness at an infinite-degree vertex survives finite flips away from that vertex. -/
theorem unfriendly_infinite_flip [Countable V] (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S : Finset V) (hvS : v ∉ S) (hN : (G.neighborSet v).Infinite)
    (hUF : UnfriendlyAt G (fun w => some (c w)) v) :
    UnfriendlyAt G (fun w => some (flip c S w)) v :=
  unfriendly_of_infinite_opposite G (flip c S) v
    (infinite_opposite_flip G c v S hvS (infinite_opposite_of_unfriendly G c v hN hUF))

private theorem neighbor_sdiff_opposite_subset_flip (G : SimpleGraph V) (c : V → Bool)
    (v : V) : G.neighborSet v \ oppositeSet G c v ⊆ oppositeSet G (flip c {v}) v := by
  classical
  intro w hw
  have hcw : c w = c v := Classical.byContradiction (fun hc => hw.2 ⟨hw.1, hc⟩)
  simpa [oppositeSet, flip, (G.ne_of_adj hw.1).symm, hcw] using hw.1

/-- Flipping a bad infinite-degree vertex gives it infinitely many opponents. -/
theorem infinite_opposite_flip_bad [Countable V] (G : SimpleGraph V) (c : V → Bool)
    (v : V) (hN : (G.neighborSet v).Infinite)
    (hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v) :
    (oppositeSet G (flip c {v}) v).Infinite :=
  Set.Infinite.mono (neighbor_sdiff_opposite_subset_flip G c v)
    (hN.sdiff (opposite_finite_of_not_unfriendly G c v hbad))

/-- The newly repaired infinite-degree vertex stays unfriendly after finite-degree repairs. -/
theorem unfriendly_flip_bad_after_finite_degree_repair [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (v : V) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) (hN : (G.neighborSet v).Infinite)
    (hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v) :
    UnfriendlyAt G (fun w => some (flip (flip c {v}) S w)) v :=
  unfriendly_of_infinite_opposite G (flip (flip c {v}) S) v
    (infinite_opposite_flip G (flip c {v}) v S (fun hvS => hN (hS v hvS))
      (infinite_opposite_flip_bad G c v hN hbad))

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyInfiniteComponentSupport.lean. -/
/-!
# Requests for infinitely many opponents inside one region

Finitely many exterior vertices with infinite neighbourhoods in a region
can be served at once. Only these vertices and the interior are recoloured.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

variable {V : Type u}

open Classical in
private theorem infinite_opposite_inside_flip (G : SimpleGraph V) (A : Set V)
    (c : V → Bool) (v : V) (S : Finset V) (hvS : v ∉ S)
    (hO : (oppositeSet G c v ∩ A).Infinite) :
    (oppositeSet G (flip c S) v ∩ A).Infinite :=
  (hO.sdiff S.finite_toSet).mono fun _ hw =>
    ⟨⟨hw.1.1.1, fun e => hw.1.1.2 ((if_neg hw.2).symm.trans (e.trans (if_neg hvS)))⟩, hw.1.2⟩

/-- Strong maximality can be kept while serving finitely many exterior vertices
that each have infinitely many neighbours in the repair domain. -/
theorem exists_strongMaximal_component_opponents [Countable V] (G : SimpleGraph V)
    (A : Set V) (c₀ : V → Bool)
    (hA : ∀ x ∈ A, (G.neighborSet x).Finite) (hc₀ : StrongMaximal G A c₀)
    (F : Finset V) (hF : ∀ x ∈ F, x ∉ A ∧ (G.neighborSet x ∩ A).Infinite) :
    ∃ c, Set.EqOn c c₀ (A ∪ (F : Set V))ᶜ ∧ StrongMaximal G A c ∧
      ∀ x ∈ F, (oppositeSet G c x ∩ A).Infinite := by
  classical
  revert hF
  induction F using Finset.induction_on
  case empty =>
    exact fun _ => ⟨c₀, fun _ _ => rfl, hc₀, fun x hx => (Finset.notMem_empty x hx).elim⟩
  case insert v F hvF ih =>
    intro hF
    obtain ⟨c, hfixed, hmax, hopponents⟩ := ih (fun x hx => hF x (Finset.mem_insert_of_mem hx))
    obtain ⟨hvA, hvInf⟩ := hF v (Finset.mem_insert_self v F)
    have hfix : Set.EqOn c c₀ (A ∪ ((insert v F : Finset V) : Set V))ᶜ := fun _ hw =>
      hfixed (fun h => hw (h.imp id Finset.mem_insert_of_mem))
    by_cases hv : (oppositeSet G c v ∩ A).Infinite
    · exact ⟨c, hfix, hmax, fun x hx => (Finset.mem_insert.mp hx).elim
        (fun hxv => hxv.symm ▸ hv) (hopponents x)⟩
    · have hO := Set.not_infinite.mp hv
      obtain ⟨S, hSA, hstable⟩ := exists_strongMaximal_repair_inside G A c hA hmax v hvA
        (hO.subset fun _ h => ⟨h.2, h.1⟩)
      let d := flip (flip c {v}) S
      have keep (w : V) (hwv : w ≠ v) (hwS : w ∉ S) : d w = c w := by
        simp [d, flip, hwv, hwS]
      have hdFix : Set.EqOn d c₀ (A ∪ ((insert v F : Finset V) : Set V))ᶜ := fun w hw =>
        (keep w (fun e => hw (Or.inr (e.symm ▸ Finset.mem_insert_self v F)))
          (fun hwS => hw (Or.inl (hSA hwS)))).trans (hfix hw)
      have hbefore : (oppositeSet G (flip c {v}) v ∩ A).Infinite :=
        (hvInf.sdiff hO).mono fun w hw =>
          let ha : G.Adj v w := hw.1.1
          let he : c w = c v := Classical.byContradiction fun hn => hw.2 ⟨⟨ha, hn⟩, hw.1.2⟩
          ⟨⟨ha, by simp [flip, (G.ne_of_adj ha).symm, he]⟩, hw.1.2⟩
      have hnew : (oppositeSet G d v ∩ A).Infinite :=
        infinite_opposite_inside_flip G A (flip c {v}) v S (fun h => hvA (hSA h)) hbefore
      exact ⟨d, hdFix, hstable, fun x hx => (Finset.mem_insert.mp hx).elim
        (fun hxv => hxv.symm ▸ hnew) (fun hxF =>
          infinite_opposite_inside_flip G A (flip c {v}) x S
            (fun hxS => (hF x (Finset.mem_insert_of_mem hxF)).1 (hSA hxS))
            (infinite_opposite_inside_flip G A c x {v}
              (fun hxv => hvF ((Finset.mem_singleton.mp hxv) ▸ hxF)) (hopponents x hxF)))⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyStrongMaximal.lean. -/
/-!
# Strong maximality on finite-degree vertices with a fixed boundary

Finite flip inequalities depend on finitely many color coordinates. Their
finite satisfiability therefore gives a global coloring by compactness.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.StrongMaximalCompactness

open scoped symmDiff

variable {V : Type u}

private theorem isClosed_of_finite_dependence [TopologicalSpace Bool] [DiscreteTopology Bool]
    (P : (V → Bool) → Prop) (W : Finset V)
    (hP : ∀ c d, Set.EqOn c d (W : Set V) → (P c ↔ P d)) :
    IsClosed {c | P c} := by
  classical
  let res : (V → Bool) → (W → Bool) := fun c x => c x.1
  let ext : (W → Bool) → (V → Bool) := fun c x => if hx : x ∈ W then c ⟨x, hx⟩ else false
  have hres : Continuous res := continuous_pi fun x => continuous_apply x.1
  have heq : {c | P c} = res ⁻¹' {d | P (ext d)} :=
    Set.ext fun c => hP c (ext (res c))
      (fun x hx => by simp only [ext, res, dif_pos (show x ∈ W from hx)])
  rw [heq]
  exact (isClosed_discrete _).preimage hres

private theorem exists_boolean_coloring {ι : Type v} (D : Set V) (p : V → Bool)
    (P : ι → (V → Bool) → Prop)
    (hlocal : ∀ i, ∃ W : Finset V,
      ∀ c d, Set.EqOn c d (W : Set V) → (P i c ↔ P i d))
    (hfinite : ∀ F : Finset ι, ∃ c, Set.EqOn c p D ∧ ∀ i ∈ F, P i c) :
    ∃ c, Set.EqOn c p D ∧ ∀ i, P i c := by
  classical
  letI : TopologicalSpace Bool := ⊥
  letI : DiscreteTopology Bool := ⟨rfl⟩
  letI : CompactSpace (V → Bool) := inferInstance
  let B : Set (V → Bool) := {c | Set.EqOn c p D}
  have hB : IsClosed B := by
    simpa only [B, Set.EqOn, Set.ofPred_forall] using
      (isClosed_biInter fun x (_ : x ∈ D) =>
        isClosed_eq (continuous_apply x) (continuous_const (y := p x)))
  have hPc : ∀ i, IsClosed {c | P i c} := fun i =>
    let ⟨W, hW⟩ := hlocal i
    isClosed_of_finite_dependence (P i) W hW
  have hF : ∀ F : Finset ι, (B ∩ ⋂ i ∈ F, {c | P i c}).Nonempty := fun F => by
    simpa only [B, Set.Nonempty, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      using hfinite F
  obtain ⟨c, hc⟩ := hB.isCompact.inter_iInter_nonempty (fun i => {c | P i c}) hPc hF
  exact ⟨c, hc.1, fun i => Set.mem_iInter.mp hc.2 i⟩

private theorem exists_maximal_flip_subset [DecidableEq V] {C : Type v}
    (flip : C → Finset V → C) (gain : C → Finset V → ℤ) (p : C) (U : Finset V)
    (hcocycle : ∀ c S T, S ⊆ U → T ⊆ U →
      gain c (S ∆ T) = gain c S + gain (flip c S) T) :
    ∃ T, T ⊆ U ∧ ∀ S, S ⊆ U → gain (flip p T) S ≤ 0 := by
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image U.powerset (gain p) U.powerset_nonempty
  refine ⟨T, Finset.mem_powerset.mp hT, ?_⟩
  intro S hS
  have hTS : T ∆ S ⊆ U := Finset.symmDiff_subset_union.trans
    (Finset.union_subset (Finset.mem_powerset.mp hT) hS)
  have hle := hmax (T ∆ S) (Finset.mem_powerset.mpr hTS)
  rw [hcocycle p T S (Finset.mem_powerset.mp hT) hS] at hle
  exact (add_le_iff_nonpos_right _).mp hle

/-- Every prescribed boundary coloring extends to a coloring admitting no improving
finite flip of finite-degree vertices outside the boundary. -/
theorem exists_strongMaximal_eqOn (G : SimpleGraph V) (D : Set V) (p : V → Bool) :
    ∃ c, Set.EqOn c p D ∧ Energy.StrongMaximal G Dᶜ c := by
  classical
  let ι : Type u := {S : Finset V // (S : Set V) ⊆ Dᶜ ∧
    ∀ x ∈ S, (G.neighborSet x).Finite}
  let P : ι → (V → Bool) → Prop := fun S c => Energy.gain G c S.1 ≤ 0
  have hlocal : ∀ i, ∃ W : Finset V,
      ∀ c d, Set.EqOn c d (W : Set V) → (P i c ↔ P i d) := by
    intro i
    obtain ⟨W, hW⟩ := Energy.gain_finite_dependence G i.1 i.2.2
    exact ⟨W, fun c d hcd => Iff.of_eq
      (congrArg (fun z : ℤ => z ≤ 0) (hW c d (fun x hx => hcd hx)))⟩
  have hfinite : ∀ F : Finset ι, ∃ c, Set.EqOn c p D ∧ ∀ i ∈ F, P i c := by
    intro F
    let U : Finset V := F.biUnion fun i => i.1
    have hU : ∀ x ∈ U, (G.neighborSet x).Finite := fun x hx =>
      let ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      i.2.2 x hxi
    have hUD : (U : Set V) ⊆ Dᶜ := fun x hx =>
      let ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      i.2.1 hxi
    obtain ⟨T, hTU, hstable⟩ := exists_maximal_flip_subset Energy.flip (Energy.gain G) p U
      (fun c S T hSU hTU => Energy.gain_symmDiff G c S T
        (fun x hx => hU x (hSU hx)) (fun x hx => hU x (hTU hx)))
    refine ⟨Energy.flip p T, ?_, fun i hi =>
      hstable i.1 (fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)⟩
    exact fun x hx => if_neg (fun hxt => hUD (hTU hxt) hx)
  obtain ⟨c, hcD, hc⟩ := exists_boolean_coloring D p P hlocal hfinite
  exact ⟨c, hcD, fun S hS hfin => hc ⟨S, hS, hfin⟩⟩

end TenChallenges.Continuation.StrongMaximalCompactness

/- Inlined from Continuation/UnfriendlyInfiniteInterfaceAssignment.lean. -/
/-!
# Assigning hubs to regions with infinite incidence

A hub can request support from several regions. Its earliest such region
chooses its colour. Each later region reads the colours of its earlier
requests as parent inputs and serves its own requests.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.InfiniteInterfaceAssignment

open Energy

variable {V : Type u} {I : Type v}

/-- Target hubs with infinitely many neighbours in the indicated region. -/
def demanding (G : SimpleGraph V) (T : Set V) (A : I → Set V) (i : I) : Set V :=
  {x | x ∈ T ∧ (G.neighborSet x ∩ A i).Infinite}

/-- The target hubs that can request support from at least one region. -/
def requested (G : SimpleGraph V) (T : Set V) (A : I → Set V) : Set V :=
  ⋃ i, demanding G T A i

/-- Choose colours for all requests and strongly maximal regional colourings
agreeing with those choices. Each request has infinitely many opponents in
at least one of its regions. -/
theorem exists_assignments [Countable I] [Countable V] (G : SimpleGraph V)
    (T : Set V) (A : I → Set V) (c₀ : V → Bool) (hdisj : ∀ i, Disjoint T (A i))
    (hA : ∀ i x, x ∈ A i → (G.neighborSet x).Finite)
    (hf : ∀ i, (demanding G T A i).Finite) :
    ∃ (q : V → Bool) (d : I → V → Bool),
      Set.EqOn q c₀ (requested G T A)ᶜ ∧
      (∀ i, Energy.StrongMaximal G (A i) (d i)) ∧
      (∀ i, Set.EqOn (d i) q (demanding G T A i)) ∧
      (∀ i, Set.EqOn (d i) c₀ (A i ∪ demanding G T A i)ᶜ) ∧
      (∀ x ∈ requested G T A, ∃ i, x ∈ demanding G T A i ∧
        (Energy.oppositeSet G (d i) x ∩ A i).Infinite) := by
  classical
  let U := requested G T A
  let demands (i : I) : Set U := Subtype.val ⁻¹' demanding G T A i
  have hfinite (i : I) : (demands i).Finite := (hf i).preimage Subtype.val_injective.injOn
  have hcover (x : U) : ∃ i, x ∈ demands i :=
    let ⟨i, hi⟩ := Set.mem_iUnion.mp (show x.val ∈ ⋃ i, demanding G T A i from x.property)
    ⟨i, hi⟩
  obtain ⟨index, hindex⟩ := exists_injective_nat I
  let before (i j : I) := index i < index j
  have hwf : WellFounded before := InvImage.wf index Nat.lt_wfRel.wf
  obtain ⟨owner, howner, hblock, hparent⟩ := BlockOwnership.exists_owner demands hfinite hcover before hwf
    (fun i j h _ _ _ => lt_or_gt_of_ne (fun e => h (hindex e)))
  let parents (i : I) : Set U := demands i \ {x | owner x = i}
  have hparents (i : I) : (parents i).Finite := (hfinite i).subset Set.sdiff_subset
  let N : BlockAssembly.Network U I :=
    { owner := owner
      parents := fun i => (hparents i).toFinset
      lt := before
      wf := hwf
      parent_lt := fun i p =>
        let hp : p.val ∈ parents i := (hparents i).mem_toFinset.mp p.property
        hparent i p.val hp.1 hp.2 }
  have parent_spec (i : I) (p : N.parents i) : p.val ∈ demands i ∧ N.owner p.val ≠ i :=
    (hparents i).mem_toFinset.mp p.property
  have reply (i : I) (b : N.parents i → Bool) : ∃ c : V → Bool,
      StrongMaximal G (A i) c ∧
      (∀ p : N.parents i, c p.val.val = b p) ∧
      Set.EqOn c c₀ (A i ∪ demanding G T A i)ᶜ ∧
      ∀ x : N.Vertices i, (oppositeSet G c x.val.val ∩ A i).Infinite := by
    let owned : Set V := Subtype.val '' {x : U | N.owner x = i}
    have ho : owned.Finite := (hblock i).image Subtype.val
    have hdemand : owned ⊆ demanding G T A i := by
      rintro _ ⟨x, hx, rfl⟩
      exact (show N.owner x = i from hx) ▸ howner x
    let F := ho.toFinset
    have hF (x : V) (hx : x ∈ F) : x ∉ A i ∧ (G.neighborSet x ∩ A i).Infinite :=
      let hxD : x ∈ demanding G T A i := hdemand (ho.mem_toFinset.mp hx)
      ⟨Set.disjoint_left.mp (hdisj i) hxD.1, hxD.2⟩
    have hpD (p : N.parents i) : p.val.val ∈ demanding G T A i := (parent_spec i p).1
    have hpA (p : N.parents i) : p.val.val ∉ A i := Set.disjoint_left.mp (hdisj i) (hpD p).1
    have hpF (p : N.parents i) : p.val.val ∉ F := fun h =>
      let ⟨x, hx, hxp⟩ := ho.mem_toFinset.mp h
      (parent_spec i p).2 ((Subtype.ext hxp : x = p.val) ▸ hx)
    let prescribed (x : V) := if hx : ∃ p : N.parents i, p.val.val = x then
      b (Classical.choose hx) else c₀ x
    have hpread (p : N.parents i) : prescribed p.val.val = b p :=
      let hp : ∃ t : N.parents i, t.val.val = p.val.val := ⟨p, rfl⟩
      (dif_pos hp).trans (congrArg b (Subtype.ext (Subtype.ext (Classical.choose_spec hp))))
    obtain ⟨base, hbaseFix, hbaseMax⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G (A i)ᶜ prescribed
    obtain ⟨c, hkeep, hstable, hop⟩ := exists_strongMaximal_component_opponents G (A i) base
      (hA i) (by simpa only [compl_compl] using hbaseMax) F hF
    refine ⟨c, hstable, ?_, ?_, ?_⟩
    · intro p
      exact (hkeep (fun hp => hp.elim (hpA p) (hpF p))).trans
        ((hbaseFix (hpA p)).trans (hpread p))
    · intro x hx
      have hxA : x ∉ A i := fun h => hx (Or.inl h)
      have hxD : x ∉ demanding G T A i := fun h => hx (Or.inr h)
      have hxF : x ∉ F := fun h => hxD (hdemand (ho.mem_toFinset.mp h))
      have hxP : ¬ ∃ p : N.parents i, p.val.val = x :=
        fun ⟨p, hp⟩ => hxD (hp ▸ hpD p)
      exact (hkeep (fun h => h.elim hxA hxF)).trans ((hbaseFix hxA).trans (dif_neg hxP))
    · intro x
      exact hop _ (ho.mem_toFinset.mpr ⟨x.val, x.property, rfl⟩)
  choose regional hmax hread hfix hopponents using reply
  let actions : N.Assignment := fun i b x => regional i b x.val.val
  let colours : U → Bool := N.assemble actions (fun _ => none)
  let q : V → Bool := fun x => if hx : x ∈ U then colours ⟨x, hx⟩ else c₀ x
  let d (i : I) : V → Bool := regional i (fun p => colours p.val)
  have hq (x : U) : q x.val = colours x := dif_pos x.property
  have howned (x : U) : colours x = d (N.owner x) x.val := by
    simpa only [colours, actions, d, Option.getD_none] using
      N.assemble_eq actions (fun _ => none) x
  refine ⟨q, d, fun _ hx => dif_neg hx, fun i => hmax i _, ?_, fun i => hfix i _, ?_⟩
  · intro i x hx
    let u : U := ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩⟩
    have hqu : q x = colours u := hq u
    by_cases hi : N.owner u = i
    · exact (hi ▸ howned u : colours u = d i x).symm.trans hqu.symm
    · have hp : u ∈ N.parents i := (hparents i).mem_toFinset.mpr ⟨hx, hi⟩
      exact (hread i _ ⟨u, hp⟩).trans hqu.symm
  · intro x hx
    let u : U := ⟨x, hx⟩
    exact ⟨N.owner u, howner u, hopponents (N.owner u) _ ⟨u, rfl⟩⟩

end TenChallenges.Continuation.InfiniteInterfaceAssignment

/- Inlined from Continuation/UnfriendlyEnergyUF.lean. -/
/-!
# Strong maximality implies unfriendliness at finite-degree vertices

A singleton flip changes the directed cut by twice the excess of same-colored
neighbors. Thus a strongly maximal coloring is unfriendly wherever the vertex
has finite degree and lies outside the prescribed boundary.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators Cardinal

variable {V : Type u}

private theorem neighColored_card_eq (G : SimpleGraph V) (c : V → Bool) (v : V)
    (hN : (G.neighborSet v).Finite) (b : Bool) :
    #(NeighColored G (fun x => some (c x)) v (some b)) =
      ((hN.toFinset.filter fun w => c w = b).card : Cardinal) := by
  classical
  have heq : G.neighborSet v ∩ (fun x => some (c x)) ⁻¹' {some b} =
      ((hN.toFinset.filter fun w => c w = b) : Set V) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Option.some.injEq, Finset.mem_coe, Finset.mem_filter, hN.mem_toFinset]
  unfold NeighColored
  rw [heq, Cardinal.mk_fintype]
  simp

private theorem edgeDelta_swap (G : SimpleGraph V) (c d : V → Bool) (x y : V) :
    edgeDelta G c d (x, y) = edgeDelta G c d (y, x) := by
  simp only [edgeDelta, cutIndicator, ne_comm]
  rw [G.adj_comm x y]

private theorem bool_flip_indicator : ∀ a b : Bool,
    (if (!a) ≠ b then (1 : ℤ) else 0) - (if a ≠ b then 1 else 0) =
      (if b = a then 1 else -1) := by decide

/-- The directed cut gain of a singleton flip is twice the local color imbalance. -/
theorem gain_singleton (G : SimpleGraph V) (c : V → Bool) (v : V)
    (hN : (G.neighborSet v).Finite) :
    gain G c {v} = 2 *
      (((hN.toFinset.filter fun w => c w = c v).card : ℤ) -
        ((hN.toFinset.filter fun w => c w ≠ c v).card : ℤ)) := by
  classical
  let N : Finset V := hN.toFinset
  let R : Finset (V × V) := N.image fun w => (v, w)
  let C : Finset (V × V) := N.image fun w => (w, v)
  have hE : incident G {v} ⊆ ((R ∪ C : Finset (V × V)) : Set (V × V)) :=
    fun e he => he.2.elim
      (fun hx =>
        let hxv : e.1 = v := Finset.mem_singleton.mp hx
        Finset.mem_union_left C (Finset.mem_image.mpr
          ⟨e.2, hN.mem_toFinset.mpr (hxv ▸ he.1), Prod.ext hxv.symm rfl⟩))
      (fun hy =>
        let hyv : e.2 = v := Finset.mem_singleton.mp hy
        Finset.mem_union_right R (Finset.mem_image.mpr
          ⟨e.1, hN.mem_toFinset.mpr (hyv ▸ he.1.symm), Prod.ext rfl hyv.symm⟩))
  have hsum : gain G c {v} = ∑ e ∈ R ∪ C, edgeDelta G c (flip c {v}) e :=
    finsum_eq_sum_of_support_subset _ ((support_edgeDelta_flip_subset G c {v}).trans hE)
  have hRC : Disjoint R C := Finset.disjoint_left.mpr fun e heR heC =>
    let ⟨w, hw, hwe⟩ := Finset.mem_image.mp heR
    let ⟨_, _, hze⟩ := Finset.mem_image.mp heC
    G.ne_of_adj (hN.mem_toFinset.mp hw)
      (congrArg Prod.snd (hwe.trans hze.symm)).symm
  have hR : (∑ e ∈ R, edgeDelta G c (flip c {v}) e) =
      ∑ w ∈ N, edgeDelta G c (flip c {v}) (v, w) :=
    Finset.sum_image (fun a _ b _ h => congrArg Prod.snd h)
  have hC : (∑ e ∈ C, edgeDelta G c (flip c {v}) e) =
      ∑ w ∈ N, edgeDelta G c (flip c {v}) (w, v) :=
    Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h)
  rw [hsum, Finset.sum_union hRC, hR, hC]
  have hsymm : (∑ w ∈ N, edgeDelta G c (flip c {v}) (w, v)) =
      ∑ w ∈ N, edgeDelta G c (flip c {v}) (v, w) :=
    Finset.sum_congr rfl (fun w _ => edgeDelta_swap G c (flip c {v}) w v)
  have hdelta : ∀ w ∈ N, edgeDelta G c (flip c {v}) (v, w) =
      (if c w = c v then 1 else -1) := fun w hw =>
    let ha : G.Adj v w := hN.mem_toFinset.mp hw
    by simpa only [edgeDelta, cutIndicator, flip, Finset.mem_singleton,
      if_pos ha, if_pos rfl, if_pos True.intro, if_neg (G.ne_of_adj ha).symm]
      using bool_flip_indicator (c v) (c w)
  have hrow : (∑ w ∈ N, edgeDelta G c (flip c {v}) (v, w)) =
      ((N.filter fun w => c w = c v).card : ℤ) -
        ((N.filter fun w => c w ≠ c v).card : ℤ) := by
    rw [Finset.sum_congr rfl hdelta, Finset.sum_ite]
    simp [sub_eq_add_neg]
  rw [hsymm, hrow, two_mul]

/-- A strongly maximal coloring is canonically unfriendly at each allowed finite-degree vertex. -/
theorem unfriendlyAt_of_strongMaximal (G : SimpleGraph V) (A : Set V) (c : V → Bool)
    (hmax : StrongMaximal G A c) (v : V) (hv : v ∈ A)
    (hN : (G.neighborSet v).Finite) :
    UnfriendlyAt G (fun x => some (c x)) v := by
  classical
  have hg : gain G c {v} ≤ 0 := hmax {v}
    (fun x hx => (Finset.mem_singleton.mp hx).symm ▸ hv)
    (fun x hx => (Finset.mem_singleton.mp hx).symm ▸ hN)
  have hformula := gain_singleton G c v hN
  have hcounts : (hN.toFinset.filter fun w => c w = c v).card ≤
      (hN.toFinset.filter fun w => c w ≠ c v).card := by omega
  refine ⟨c v, rfl, ?_⟩
  rw [neighColored_card_eq G c v hN (c v), neighColored_card_eq G c v hN (!c v)]
  simp only [Bool.eq_not]
  exact Nat.cast_le.mpr hcounts

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyRecurrentBlocks.lean. -/
/-!
# Recurrent finite blocks give robust colourings of infinite-degree vertices

A *piece* is a finite set of finite-degree vertices. If infinitely many pairwise
disjoint pieces have all their outside neighbours in a common finite set `A`
together with an already frozen set `D`, and each piece meets every vertex of `A`,
then `A` can be coloured so that every strongly maximal completion gives each
vertex of `A` an opposite-coloured neighbour in infinitely many of the pieces.

The witnesses are permanent: they depend only on the colours on `A ∪ D` and on
strong maximality, so they survive any later colouring of other vertices. Zorn's
lemma then assembles these blocks without any limit-stage loss.

This is a special case of the countable unfriendly partition problem. It does
not prove the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators

variable {V : Type u}

/-- Directed crossing count over a finite set of directed pairs. -/
def cutOn (E : Finset (V × V)) (c : V → Bool) : ℤ :=
  ∑ e ∈ E, cutIndicator c e

theorem cutIndicator_nonneg (c : V → Bool) (e : V × V) : 0 ≤ cutIndicator c e := by
  unfold cutIndicator
  split_ifs <;> omega

theorem cutIndicator_le_one (c : V → Bool) (e : V × V) : cutIndicator c e ≤ 1 := by
  unfold cutIndicator
  split_ifs <;> omega

theorem cutOn_le_card (E : Finset (V × V)) (c : V → Bool) : cutOn E c ≤ E.card := by
  have h := Finset.sum_le_card_nsmul E (cutIndicator c) 1
    (fun e _ => cutIndicator_le_one c e)
  simpa [cutOn] using h

/-- The crossing count depends only on the colours at endpoints of the listed pairs. -/
theorem cutOn_congr (E : Finset (V × V)) (c d : V → Bool)
    (h : ∀ e ∈ E, c e.1 = d e.1 ∧ c e.2 = d e.2) : cutOn E c = cutOn E d :=
  Finset.sum_congr rfl fun e he => by
    simp only [cutIndicator, (h e he).1, (h e he).2]

/-- The gain of a finite flip is the change of the crossing count on any finite set of
adjacent pairs containing all pairs incident with the flipped set. -/
theorem gain_eq_cutOn_sub (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (E : Finset (V × V)) (hE : incident G S ⊆ (E : Set (V × V)))
    (hadj : ∀ e ∈ E, G.Adj e.1 e.2) :
    gain G c S = cutOn E (flip c S) - cutOn E c := by
  unfold gain cutOn
  rw [finsum_eq_sum_of_support_subset _ ((support_edgeDelta_flip_subset G c S).trans hE),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e he => by simp only [edgeDelta, if_pos (hadj e he)]

open Classical in
/-- Recolouring an outside vertex that has no opponent inside the piece, but at least one
neighbour there, strictly increases the crossing count of the piece. -/
theorem cutOn_lt_cutOn_update (G : SimpleGraph V) (C : Finset V) (E : Finset (V × V))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2 ∧ (e.1 ∈ C ∨ e.2 ∈ C))
    (c : V → Bool) (v : V) (hv : v ∉ C)
    (hsame : ∀ w ∈ C, G.Adj v w → c w = c v)
    (w : V) (hw : w ∈ C) (hvw : (v, w) ∈ E) :
    cutOn E c < cutOn E (Function.update c v (!c v)) := by
  refine Finset.sum_lt_sum (fun e he => ?_) ⟨(v, w), hvw, ?_⟩
  · obtain ⟨hadj, hC⟩ := hE e he
    by_cases h1 : e.1 = v
    · have h2 : e.2 ∈ C := hC.resolve_left (h1 ▸ hv)
      have h3 : c e.2 = c e.1 := h1 ▸ hsame e.2 h2 (h1 ▸ hadj)
      have h4 : cutIndicator c e = 0 := by simp [cutIndicator, h3]
      exact h4 ▸ cutIndicator_nonneg _ e
    · by_cases h2 : e.2 = v
      · have h3 : e.1 ∈ C := hC.resolve_right (h2 ▸ hv)
        have h4 : c e.1 = c e.2 := h2 ▸ hsame e.1 h3 (h2 ▸ hadj.symm)
        have h5 : cutIndicator c e = 0 := by simp [cutIndicator, h4]
        exact h5 ▸ cutIndicator_nonneg _ e
      · simp [cutIndicator, Function.update_of_ne h1, Function.update_of_ne h2]
  · have hwv : w ≠ v := fun h => hv (h ▸ hw)
    have hcw : c w = c v := hsame w hw (hE _ hvw).1
    simp [cutIndicator, Function.update_of_ne hwv, hcw]

/-- **Block selection.** Infinitely many pairwise disjoint finite pieces of finite-degree
vertices have all outside neighbours in `A ∪ D`, and every piece meets every vertex of the
finite set `A`. Then the colours on `A` can be chosen (keeping `p` elsewhere) so that every
strongly maximal colouring agreeing with the choice on `A ∪ D` gives each vertex of `A`
infinitely many opposite-coloured neighbours. -/
theorem exists_block_assignment (G : SimpleGraph V) (p : V → Bool) (A : Finset V) (D : Set V)
    {ι : Type*} [Infinite ι] (C : ι → Finset V)
    (hdisj : Pairwise (Function.onFun Disjoint C))
    (hfin : ∀ i, ∀ x ∈ C i, (G.neighborSet x).Finite)
    (hbdry : ∀ i, ∀ x ∈ C i, ∀ y, G.Adj x y → y ∈ C i ∨ y ∈ A ∨ y ∈ D)
    (hA : ∀ i, ∀ v ∈ A, v ∉ C i)
    (htouch : ∀ i, ∀ v ∈ A, ∃ x ∈ C i, G.Adj v x) :
    ∃ q : V → Bool, (∀ y, y ∉ A → q y = p y) ∧
      ∀ (M : Set V) (c : V → Bool), (∀ i, (C i : Set V) ⊆ M) → StrongMaximal G M c →
        (∀ y, y ∈ A ∨ y ∈ D → c y = q y) → ∀ v ∈ A, (oppositeSet G c v).Infinite := by
  classical
  let E : ι → Finset (V × V) := fun i => (incident_finite G (C i) (hfin i)).toFinset
  have hEmem : ∀ i e, e ∈ E i ↔ G.Adj e.1 e.2 ∧ (e.1 ∈ C i ∨ e.2 ∈ C i) := fun i e =>
    (incident_finite G (C i) (hfin i)).mem_toFinset
  have hend : ∀ i, ∀ e ∈ E i,
      (e.1 ∈ C i ∨ e.1 ∈ A ∨ e.1 ∈ D) ∧ (e.2 ∈ C i ∨ e.2 ∈ A ∨ e.2 ∈ D) := by
    intro i e he
    obtain ⟨hadj, h1 | h2⟩ := (hEmem i e).mp he
    · exact ⟨Or.inl h1, hbdry i e.1 h1 e.2 hadj⟩
    · exact ⟨hbdry i e.2 h2 e.1 hadj.symm, Or.inl h2⟩
  let K : ι → (V → Bool) → Prop := fun i d => ∀ y, y ∉ C i → y ∉ A → d y = p y
  have hmax : ∀ i, ∃ d, K i d ∧ ∀ d', K i d' → cutOn (E i) d' ≤ cutOn (E i) d := by
    intro i
    obtain ⟨m, ⟨d, hd, hdm⟩, hm⟩ := Int.exists_greatest_of_bdd
      (P := fun z => ∃ d, K i d ∧ cutOn (E i) d = z)
      ⟨(E i).card, fun z ⟨d, _, hz⟩ => hz ▸ cutOn_le_card (E i) d⟩
      ⟨cutOn (E i) p, p, fun _ _ _ => rfl, rfl⟩
    exact ⟨d, hd, fun d' hd' => hdm ▸ hm _ ⟨d', hd', rfl⟩⟩
  choose dsel hdK hdmax using hmax
  obtain ⟨t, ht⟩ := Finite.exists_infinite_fiber (fun i (a : A) => dsel i a.1)
  let q : V → Bool := fun y => if hy : y ∈ A then t ⟨y, hy⟩ else p y
  refine ⟨q, fun y hy => dif_neg hy, ?_⟩
  intro M c hCM hc hcq v hvA
  have key : ∀ i, (fun (a : A) => dsel i a.1) = t → ∃ w ∈ C i, G.Adj v w ∧ c w ≠ c v := by
    intro i hfib
    by_contra hno
    have hsame : ∀ w ∈ C i, G.Adj v w → c w = c v := fun w hw hvw =>
      Classical.byContradiction fun hne => hno ⟨w, hw, hvw, hne⟩
    obtain ⟨w, hwC, hvw⟩ := htouch i v hvA
    -- outside the piece, `c` agrees with the selected maximiser on `A ∪ D`
    have hout : ∀ y, y ∉ C i → (y ∈ A ∨ y ∈ D) → c y = dsel i y := by
      intro y hyC hy
      rw [hcq y hy]
      by_cases hyA : y ∈ A
      · exact (dif_pos hyA).trans (congrFun hfib ⟨y, hyA⟩).symm
      · exact (dif_neg hyA).trans (hdK i y hyC hyA).symm
    -- strong maximality: the interior of `c` is at least as good as the maximiser's interior
    let S : Finset V := (C i).filter fun y => dsel i y ≠ c y
    have hSC : S ⊆ C i := Finset.filter_subset _ _
    have hgain : gain G c S ≤ 0 := hc S (fun x hx => hCM i (hSC hx))
      (fun x hx => hfin i x (hSC hx))
    have hF1 : gain G c S = cutOn (E i) (flip c S) - cutOn (E i) c :=
      gain_eq_cutOn_sub G c S (E i)
        (fun e he => (hEmem i e).mpr ⟨he.1, he.2.imp (fun h => hSC h) (fun h => hSC h)⟩)
        (fun e he => ((hEmem i e).mp he).1)
    have hflip : ∀ y, (y ∈ C i ∨ y ∈ A ∨ y ∈ D) → flip c S y = dsel i y := by
      intro y hy
      by_cases hyC : y ∈ C i
      · by_cases hyd : dsel i y = c y
        · have hyS : y ∉ S := fun h => (Finset.mem_filter.mp h).2 hyd
          exact (if_neg hyS).trans hyd.symm
        · have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hyC, hyd⟩
          refine (if_pos hyS).trans ?_
          revert hyd
          cases dsel i y <;> cases c y <;> simp
      · have hyS : y ∉ S := fun h => hyC (hSC h)
        exact (if_neg hyS).trans (hout y hyC (hy.resolve_left hyC))
    have h1 : cutOn (E i) (flip c S) = cutOn (E i) (dsel i) :=
      cutOn_congr _ _ _ fun e he => ⟨hflip e.1 (hend i e he).1, hflip e.2 (hend i e he).2⟩
    -- recolouring `v` strictly improves the piece
    have hlt : cutOn (E i) c < cutOn (E i) (Function.update c v (!c v)) :=
      cutOn_lt_cutOn_update G (C i) (E i) (fun e he => (hEmem i e).mp he) c v (hA i v hvA)
        hsame w hwC ((hEmem i (v, w)).mpr ⟨hvw, Or.inr hwC⟩)
    -- but the recoloured state is admissible for the maximisation
    let d' : V → Bool := fun y =>
      if y ∈ C i ∨ y ∈ A then Function.update c v (!c v) y else p y
    have hd'K : K i d' := fun y hyC hyA => if_neg (fun h => h.elim hyC hyA)
    have h2 : cutOn (E i) (Function.update c v (!c v)) = cutOn (E i) d' := by
      have hpt : ∀ y, (y ∈ C i ∨ y ∈ A ∨ y ∈ D) → Function.update c v (!c v) y = d' y := by
        intro y hy
        by_cases hyCA : y ∈ C i ∨ y ∈ A
        · exact (if_pos hyCA).symm
        · have hyC : y ∉ C i := fun h => hyCA (Or.inl h)
          have hyA : y ∉ A := fun h => hyCA (Or.inr h)
          have hyD : y ∈ D := (hy.resolve_left hyC).resolve_left hyA
          have hyv : y ≠ v := fun h => hyA (h ▸ hvA)
          rw [Function.update_of_ne hyv, hcq y (Or.inr hyD)]
          exact (dif_neg hyA).trans (if_neg hyCA).symm
      exact cutOn_congr _ _ _ fun e he => ⟨hpt e.1 (hend i e he).1, hpt e.2 (hend i e he).2⟩
    have h3 := hdmax i d' hd'K
    omega
  haveI : Infinite ((fun i (a : A) => dsel i a.1) ⁻¹' {t}) := ht
  choose w hwC hvw hne using key
  refine Set.infinite_of_injective_forall_mem
    (f := fun i : ((fun i (a : A) => dsel i a.1) ⁻¹' {t}) => w i.1 i.2) ?_ ?_
  · intro i j hij
    by_contra hne'
    have hd : Disjoint (C i.1) (C j.1) := hdisj fun h => hne' (Subtype.ext h)
    have hij' : w i.1 i.2 = w j.1 j.2 := hij
    have hj : w i.1 i.2 ∈ C j.1 := hij' ▸ hwC j.1 j.2
    exact Finset.disjoint_left.mp hd (hwC i.1 i.2) hj
  · intro i
    exact ⟨hvw i.1 i.2, hne i.1 i.2⟩

/-- A colouring `q`, frozen on `S`, is *robust* for strong maximality on `M` if every
colouring that is strongly maximal on `M` and agrees with `q` on `S` gives each vertex of
`S` infinitely many opposite-coloured neighbours. The property is closed under unions of
chains, since it quantifies over all strongly maximal completions. -/
def Robust (G : SimpleGraph V) (M S : Set V) (q : V → Bool) : Prop :=
  ∀ c : V → Bool, StrongMaximal G M c → Set.EqOn c q S →
    ∀ v ∈ S, (oppositeSet G c v).Infinite

/-- `A` is a *recurrent block over* `S`: infinitely many pairwise disjoint finite pieces of
finite-degree vertices have all their outside neighbours in `A ∪ S`, and each piece meets
every vertex of `A`. When `A ∪ S` consists of infinite-degree vertices, a piece is a finite
union of components of the graph induced on the finite-degree vertices, and the condition
says that the part of its boundary outside `S` is exactly `A`. -/
def RecurrentBlock (G : SimpleGraph V) (S : Set V) (A : Finset V) : Prop :=
  ∃ C : ℕ → Finset V, Pairwise (Function.onFun Disjoint C) ∧
    (∀ i, ∀ x ∈ C i, (G.neighborSet x).Finite) ∧
    (∀ i, ∀ x ∈ C i, ∀ y, G.Adj x y → y ∈ C i ∨ y ∈ A ∨ y ∈ S) ∧
    (∀ i, ∀ v ∈ A, ∃ x ∈ C i, G.Adj v x)

/-- A robust frozen colouring extends across a recurrent block of infinite-degree vertices. -/
theorem Robust.extend_block (G : SimpleGraph V) (M S : Set V) (q : V → Bool)
    (hq : Robust G M S q) (A : Finset V) (hAS : ∀ v ∈ A, v ∉ S)
    (hAinf : ∀ v ∈ A, (G.neighborSet v).Infinite)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M)
    (hblock : RecurrentBlock G S A) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ (A : Set V)) q' := by
  obtain ⟨C, hdisj, hfin, hbdry, htouch⟩ := hblock
  obtain ⟨q', hq'p, hq'⟩ := exists_block_assignment G q A S C hdisj hfin hbdry
    (fun i v hv hvC => hAinf v hv (hfin i v hvC)) htouch
  have hq'S : Set.EqOn q' q S := fun y hy => hq'p y (fun hyA => hAS y hyA hy)
  refine ⟨q', hq'S, ?_⟩
  intro c hc hcq v hv
  rcases hv with hvS | hvA
  · exact hq c hc (fun y hy => (hcq (Or.inl hy)).trans (hq'S hy)) v hvS
  · exact hq' M c (fun i x hx => hM x (hfin i x hx)) hc
      (fun y hy => hcq (hy.elim (fun h => Or.inr h) (fun h => Or.inl h))) v hvA

/-- Maximal robust frozen colourings exist inside any target set `H`. No countability,
enumeration, or limit-stage argument is needed. -/
theorem exists_maximal_robust (G : SimpleGraph V) (M H : Set V) :
    ∃ (S : Set V) (q : V → Bool), S ⊆ H ∧ Robust G M S q ∧
      ∀ (S' : Set V) (q' : V → Bool), S' ⊆ H → Robust G M S' q' → S ⊆ S' →
        Set.EqOn q' q S → S' ⊆ S := by
  classical
  let T : Type u := {P : Set V × (V → Bool) // P.1 ⊆ H ∧ Robust G M P.1 P.2}
  let r : T → T → Prop := fun P Q => P.1.1 ⊆ Q.1.1 ∧ Set.EqOn Q.1.2 P.1.2 P.1.1
  have htrans : ∀ {a b c : T}, r a b → r b c → r a c := fun {a b c} hab hbc =>
    ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 (hab.1 hy)).trans (hab.2 hy)⟩
  have hchain : ∀ c : Set T, IsChain r c → ∃ ub, ∀ a ∈ c, r a ub := by
    intro c hc
    let dom : Set V := ⋃ P ∈ c, P.1.1
    let col : V → Bool := fun y =>
      if h : ∃ P ∈ c, y ∈ P.1.1 then (Classical.choose h).1.2 y else false
    have hcol : ∀ P ∈ c, Set.EqOn col P.1.2 P.1.1 := by
      intro P hP y hy
      have h : ∃ P ∈ c, y ∈ P.1.1 := ⟨P, hP, hy⟩
      have hspec := Classical.choose_spec h
      have hval : col y = (Classical.choose h).1.2 y := dif_pos h
      rw [hval]
      by_cases hPQ : Classical.choose h = P
      · rw [hPQ]
      · rcases hc hspec.1 hP hPQ with hle | hle
        · exact (hle.2 hspec.2).symm
        · exact hle.2 hy
    have hdomH : dom ⊆ H := Set.iUnion₂_subset fun P _ => P.2.1
    have hrob : Robust G M dom col := by
      intro cc hcc heq v hv
      obtain ⟨P, hP, hvP⟩ := Set.mem_iUnion₂.mp hv
      exact P.2.2 cc hcc
        (fun y hy => (heq (Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩)).trans (hcol P hP hy)) v hvP
    exact ⟨⟨(dom, col), hdomH, hrob⟩, fun P hP =>
      ⟨fun y hy => Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩, hcol P hP⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  refine ⟨m.1.1, m.1.2, m.2.1, m.2.2, fun S' q' hS'H hrob hSS' heq => ?_⟩
  exact (hm ⟨(S', q'), hS'H, hrob⟩ ⟨hSS', heq⟩).1

/-- **Relative recurrence.** Suppose that every proper subset `S` of the infinite-degree
vertices admits a nonempty recurrent block of further infinite-degree vertices. Then the
infinite-degree vertices have a robust colouring: every colouring extending it that is
strongly maximal on the finite-degree vertices gives every infinite-degree vertex
infinitely many opposite-coloured neighbours. -/
theorem exists_robust_of_recurrent_blocks (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      S ≠ {v | (G.neighborSet v).Infinite} →
      ∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) :
    ∃ q : V → Bool, Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} q := by
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {v | (G.neighborSet v).Infinite}ᶜ {v | (G.neighborSet v).Infinite}
  by_cases hS : S = {v | (G.neighborSet v).Infinite}
  · exact ⟨q, hS ▸ hrob⟩
  · obtain ⟨A, ⟨a, ha⟩, hA, hblock⟩ := h S hSH hS
    obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob A (fun v hv => (hA v hv).2)
      (fun v hv => (hA v hv).1) (fun x hx hinf => hinf hx) hblock
    have hsub : S ∪ (A : Set V) ⊆ S := hmax (S ∪ (A : Set V)) q'
      (Set.union_subset hSH (fun v hv => (hA v hv).1)) hq' Set.subset_union_left hq'q
    exact ((hA a ha).2 (hsub (Or.inr ha))).elim

/-- A countable graph has an unfriendly partition whenever every proper subset of its
infinite-degree vertices admits a nonempty recurrent block of further such vertices. -/
theorem exists_unfriendly_of_recurrent_blocks [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      S ≠ {v | (G.neighborSet v).Infinite} →
      ∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨q, hq⟩ := exists_robust_of_recurrent_blocks G h
  obtain ⟨c, hcq, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {v | (G.neighborSet v).Infinite} q
  refine ⟨fun v => some (c v), fun v => ?_⟩
  exact (Classical.em (G.neighborSet v).Finite).elim
    (fun hN => unfriendlyAt_of_strongMaximal G _ c hc v (fun hInf => hInf hN) hN)
    (fun hN => unfriendly_of_infinite_opposite G c v (hq c hc hcq v (Set.not_finite.mp hN)))

/-- **Recurrent full boundaries.** If every infinite-degree vertex lies in a finite set `B`
of infinite-degree vertices that is the exact outside neighbourhood of infinitely many
pairwise disjoint finite pieces of finite-degree vertices, then the countable graph has
an unfriendly partition. Different boundaries may overlap arbitrarily. -/
theorem exists_unfriendly_of_recurrent_boundaries [Countable V] (G : SimpleGraph V)
    (h : ∀ v, (G.neighborSet v).Infinite →
      ∃ B : Finset V, v ∈ B ∧ (∀ u ∈ B, (G.neighborSet u).Infinite) ∧
        RecurrentBlock G ∅ B) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  refine exists_unfriendly_of_recurrent_blocks G fun S hSH hS => ?_
  obtain ⟨v, hvI, hvS⟩ : ∃ v, (G.neighborSet v).Infinite ∧ v ∉ S := by
    by_contra hno
    exact hS (Set.Subset.antisymm hSH fun v hv =>
      Classical.byContradiction fun hvS => hno ⟨v, hv, hvS⟩)
  obtain ⟨B, hvB, hBI, C, hdisj, hfin, hbdry, htouch⟩ := h v hvI
  refine ⟨B.filter (· ∉ S), ⟨v, Finset.mem_filter.mpr ⟨hvB, hvS⟩⟩,
    fun u hu => ⟨hBI u (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩,
    C, hdisj, hfin, ?_, fun i u hu => htouch i u (Finset.mem_filter.mp hu).1⟩
  intro i x hx y hxy
  rcases hbdry i x hx y hxy with hC | hB | hE
  · exact Or.inl hC
  · by_cases hyS : y ∈ S
    · exact Or.inr (Or.inr hyS)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hB, hyS⟩))
  · exact hE.elim

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyPairProfile.lean. -/
/-!
# Universal opponent certificates for pair profiles

The matrix stores twice the undirected interaction coefficient. Both matrix
orientations are summed, so the representation is for four times the profile.
No bound on the finite boundary size is used in the certificate.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PairProfile

open scoped BigOperators

variable {B : Type u} [Fintype B]

def quadratic (a : B → B → ℤ) (b : B → Bool) : ℤ :=
  ∑ u, ∑ v, if b u ≠ b v then a u v else 0

open Classical in
noncomputable def toggle (b : B → Bool) (v : B) : B → Bool :=
  Function.update b v (!b v)

def row (a : B → B → ℤ) (b : B → Bool) (v : B) : ℤ :=
  ∑ u, if b v ≠ b u then a v u else -a v u

def weight (a : B → B → ℤ) (v : B) : ℤ := ∑ u, |a v u|

def Favoured (a : ℤ) (x y : Bool) : Prop :=
  (0 < a ∧ x ≠ y) ∨ (a < 0 ∧ x = y)

open Classical in
noncomputable def favouredWeight (a : B → B → ℤ) (b : B → Bool) (v : B) : ℤ :=
  ∑ u, if Favoured (a v u) (b v) (b u) then |a v u| else 0

def Represents (Q : (B → Bool) → ℤ) (K : ℤ) (a : B → B → ℤ) : Prop :=
  (∀ u v, a u v = a v u) ∧ (∀ v, a v v = 0) ∧
    ∀ b, 4 * Q b = K + quadratic a b

omit [Fintype B] in
open Classical in
private theorem term_toggle (a : B → B → ℤ) (hdiag : ∀ v, a v v = 0)
    (b : B → Bool) (v u w : B) :
    (if b u ≠ b w then a u w else 0) -
        (if toggle b v u ≠ toggle b v w then a u w else 0) =
      (if u = v then (if b v ≠ b w then a v w else -a v w) else 0) +
      (if w = v then (if b u ≠ b v then a u v else -a u v) else 0) := by
  classical
  by_cases hu : u = v <;> by_cases hw : w = v
  all_goals cases hv : b v <;> cases hbu : b u <;> cases hbw : b w
  all_goals simp_all [toggle]

private theorem quadratic_difference (a : B → B → ℤ)
    (hsym : ∀ u v, a u v = a v u) (hdiag : ∀ v, a v v = 0)
    (b : B → Bool) (v : B) :
    quadratic a b - quadratic a (toggle b v) = 2 * row a b v := by
  classical
  unfold quadratic
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, term_toggle a hdiag b v]
  simp_rw [Finset.sum_add_distrib]
  have hA : (∑ u, ∑ w,
      if u = v then (if b v ≠ b w then a v w else -a v w) else 0) = row a b v := by
    simp [Finset.sum_ite_irrel, row]
  rw [hA]
  simp [row, hsym, ne_comm, two_mul]

theorem profile_difference (Q : (B → Bool) → ℤ) (K : ℤ) (a : B → B → ℤ)
    (hrep : Represents Q K a) (b : B → Bool) (v : B) :
    2 * (Q b - Q (toggle b v)) = row a b v := by
  have h := quadratic_difference a hrep.1 hrep.2.1 b v
  have h₁ := hrep.2.2 b
  have h₂ := hrep.2.2 (toggle b v)
  omega

private theorem row_star (a : B → B → ℤ) (hdiag : ∀ v, a v v = 0) (v : B) :
    row a (fun u => decide (0 < a v u)) v = weight a v := by
  classical
  unfold row weight
  simp only [hdiag, lt_self_iff_false, decide_false]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases ha : 0 < a v u
  · simp [ha, abs_of_pos ha]
  · simp [ha, abs_of_nonpos (le_of_not_gt ha)]

open Classical in
private theorem signed_term (a : ℤ) (x y : Bool) :
    (if x ≠ y then a else -a) =
      2 * (if Favoured a x y then |a| else 0) - |a| := by
  rcases lt_trichotomy a 0 with hn | rfl | hp
  · cases x <;> cases y <;> simp [Favoured, hn, not_lt_of_ge hn.le, abs_of_neg hn, two_mul]
  · cases x <;> cases y <;> simp [Favoured]
  · cases x <;> cases y <;> simp [Favoured, hp, not_lt_of_ge hp.le, abs_of_pos hp, two_mul]

private theorem row_favoured (a : B → B → ℤ) (b : B → Bool) (v : B) :
    row a b v = 2 * favouredWeight a b v - weight a v := by
  classical
  unfold row favouredWeight weight
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun u _ => signed_term (a v u) (b v) (b u)

theorem weight_budget (Q : (B → Bool) → ℤ) (K : ℤ) (a : B → B → ℤ)
    (hrep : Represents Q K a) (d : B → ℤ)
    (hflip : ∀ b v, Q b - Q (toggle b v) ≤ d v) (v : B) :
    weight a v ≤ 2 * d v := by
  have h := profile_difference Q K a hrep (fun u => decide (0 < a v u)) v
  rw [row_star a hrep.2.1 v] at h
  linarith [hflip (fun u => decide (0 < a v u)) v]

/-- The integer-scaled universal opponent certificate. The response inequality
holds separately for every maximizing completion, so the conclusion does too. -/
theorem universal_opponent_certificate (Q : (B → Bool) → ℤ) (K : ℤ)
    (a : B → B → ℤ) (hrep : Represents Q K a) (d : B → ℤ)
    (hflip : ∀ b v, Q b - Q (toggle b v) ≤ d v)
    (b : B → Bool) (v : B) (o : ℤ)
    (hresponse : d v + Q b - Q (toggle b v) ≤ 2 * o) :
    weight a v ≤ 2 * d v ∧
      2 * d v - weight a v + 2 * favouredWeight a b v ≤ 4 * o := by
  refine ⟨weight_budget Q K a hrep d hflip v, ?_⟩
  have hdiff := profile_difference Q K a hrep b v
  have hrow := row_favoured a b v
  linarith

end TenChallenges.Continuation.PairProfile

/- Inlined from Continuation/UnfriendlyPairRepresentation.lean. -/
/-!
# Complement-invariant profiles on boundaries of size at most three

The coefficients are integers representing twice the undirected interaction
weight. This file provides pair representations for every even integer profile
on a finite boundary with at most three vertices.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PairProfile

open scoped BigOperators

private theorem vec_one_eta (b : Fin 1 → Bool) : ![b 0] = b := by
  funext i
  fin_cases i
  rfl

private theorem vec_two_eta (b : Fin 2 → Bool) : ![b 0, b 1] = b := by
  funext i
  fin_cases i <;> rfl

private theorem vec_three_eta (b : Fin 3 → Bool) : ![b 0, b 1, b 2] = b := by
  funext i
  fin_cases i <;> rfl

private theorem quadratic_two (p : ℤ) (b : Fin 2 → Bool) :
    quadratic ![![0, p], ![p, 0]] b = 2 * (if b 0 ≠ b 1 then p else 0) := by
  cases h₀ : b 0 <;> cases h₁ : b 1
  all_goals simp [quadratic, Fin.sum_univ_succ, h₀, h₁, two_mul]

private theorem quadratic_three (p q r : ℤ) (b : Fin 3 → Bool) :
    quadratic ![![0, p, q], ![p, 0, r], ![q, r, 0]] b =
      2 * (if b 0 ≠ b 1 then p else 0) +
      2 * (if b 0 ≠ b 2 then q else 0) +
      2 * (if b 1 ≠ b 2 then r else 0) := by
  cases h₀ : b 0 <;> cases h₁ : b 1 <;> cases h₂ : b 2
  all_goals simp [quadratic, Fin.sum_univ_succ, h₀, h₁, h₂, two_mul,
    add_left_comm, add_comm]

private def triple01 (f : Bool → Bool → Bool → ℤ) : ℤ :=
  f true false false + f false true false - f false false true - f false false false

private def triple02 (f : Bool → Bool → Bool → ℤ) : ℤ :=
  f true false false + f false false true - f false true false - f false false false

private def triple12 (f : Bool → Bool → Bool → ℤ) : ℤ :=
  f false true false + f false false true - f true false false - f false false false

private theorem even_three_identity (f : Bool → Bool → Bool → ℤ)
    (heven : ∀ x y z, f (!x) (!y) (!z) = f x y z) (x y z : Bool) :
    2 * f x y z = 2 * f false false false +
      (if x ≠ y then triple01 f else 0) +
      (if x ≠ z then triple02 f else 0) +
      (if y ≠ z then triple12 f else 0) := by
  simp only [Bool.forall_bool, Bool.not_true, Bool.not_false] at heven
  cases x <;> cases y <;> cases z
  all_goals simp only [triple01, triple02, triple12, ne_eq,
    Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
    ite_true, ite_false]
  all_goals omega

private theorem even_two_identity (f : Bool → Bool → ℤ)
    (heven : ∀ x y, f (!x) (!y) = f x y) (x y : Bool) :
    2 * f x y = 2 * f false false +
      (if x ≠ y then 2 * (f false true - f false false) else 0) := by
  simp only [Bool.forall_bool, Bool.not_true, Bool.not_false] at heven
  cases x <;> cases y
  all_goals simp only [ne_eq, Bool.false_eq_true, Bool.true_eq_false,
    not_false_eq_true, not_true_eq_false, ite_true, ite_false]
  all_goals omega

private theorem represents_zero (Q : (Fin 0 → Bool) → ℤ) :
    ∃ K a, Represents Q K a := by
  refine ⟨4 * Q ![], fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun b => ?_⟩
  have hb : b = ![] := Subsingleton.elim _ _
  simp [quadratic, hb]

private theorem represents_one (Q : (Fin 1 → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  have hf : Q ![true] = Q ![false] :=
    (congrArg Q (vec_one_eta (fun i => !(![false] i)))).trans (heven ![false])
  refine ⟨4 * Q ![false], fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun b => ?_⟩
  have hQ : Q b = Q ![false] := by
    rw [← vec_one_eta b]
    cases b 0
    · rfl
    · exact hf
  simp [quadratic, hQ]

private theorem represents_two (Q : (Fin 2 → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  let f : Bool → Bool → ℤ := fun x y => Q ![x, y]
  have hf : ∀ x y, f (!x) (!y) = f x y := fun x y =>
    (congrArg Q (vec_two_eta (fun i => !(![x, y] i)))).trans (heven ![x, y])
  let t : ℤ := 2 * (f false true - f false false)
  refine ⟨4 * f false false, ![![0, t], ![t, 0]], ?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl
  · intro v
    fin_cases v <;> rfl
  · intro b
    have h := even_two_identity f hf (b 0) (b 1)
    have hQ : Q b = f (b 0) (b 1) := (congrArg Q (vec_two_eta b)).symm
    rw [hQ, quadratic_two]
    dsimp only [t]
    omega

private theorem represents_three (Q : (Fin 3 → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  let f : Bool → Bool → Bool → ℤ := fun x y z => Q ![x, y, z]
  have hf : ∀ x y z, f (!x) (!y) (!z) = f x y z := fun x y z =>
    (congrArg Q (vec_three_eta (fun i => !(![x, y, z] i)))).trans (heven ![x, y, z])
  let a : Fin 3 → Fin 3 → ℤ :=
    ![![0, triple01 f, triple02 f], ![triple01 f, 0, triple12 f],
      ![triple02 f, triple12 f, 0]]
  refine ⟨4 * f false false false, a, ?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl
  · intro v
    fin_cases v <;> rfl
  · intro b
    have h := even_three_identity f hf (b 0) (b 1) (b 2)
    have hQ : Q b = f (b 0) (b 1) (b 2) := (congrArg Q (vec_three_eta b)).symm
    rw [hQ, quadratic_three]
    omega

private theorem represents_fin (n : ℕ) (hn : n ≤ 3)
    (Q : (Fin n → Bool) → ℤ) (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn' with rfl | rfl | rfl | rfl
  · exact represents_zero Q
  · exact represents_one Q heven
  · exact represents_two Q heven
  · exact represents_three Q heven

/-- Every complement-invariant integer profile on at most three boundary
vertices has a constant-plus-pair representation, with integer-scaled weights. -/
theorem exists_representation_of_card_le_three {B : Type u} [Fintype B]
    (hB : Fintype.card B ≤ 3) (Q : (B → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  classical
  let e := Fintype.equivFin B
  let Q' : (Fin (Fintype.card B) → Bool) → ℤ := fun b => Q (fun v => b (e v))
  have heven' : ∀ b, Q' (fun i => !b i) = Q' b :=
    fun b => heven (fun v => b (e v))
  obtain ⟨K, a, hrep⟩ := represents_fin (Fintype.card B) hB Q' heven'
  refine ⟨K, fun u v => a (e u) (e v), fun u v => hrep.1 (e u) (e v),
    fun v => hrep.2.1 (e v), fun b => ?_⟩
  have h := hrep.2.2 (fun i => b (e.symm i))
  simp only [quadratic] at h ⊢
  simpa only [← e.sum_comp, e.symm_apply_apply, Q'] using h

end TenChallenges.Continuation.PairProfile

/- Inlined from Continuation/UnfriendlyComponentProfile.lean. -/
/-!
# Full-boundary profiles of finite pieces

Scores and incidence counts include both orientations, as in `Energy.gain`.
This common factor of two preserves all opponent-positivity certificates.
The full outside boundary is fixed before any colours on hubs are prescribed.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators

variable {V : Type u}

open Classical in
noncomputable def pieceDegree (E : Finset (V × V)) (v : V) : ℤ :=
  ∑ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else 0

open Classical in
noncomputable def pieceOpponents (E : Finset (V × V)) (c : V → Bool) (v : V) : ℤ :=
  ∑ e ∈ E, if e.1 = v ∨ e.2 = v then cutIndicator c e else 0

theorem pieceOpponents_nonneg (E : Finset (V × V)) (c : V → Bool) (v : V) :
    0 ≤ pieceOpponents E c v := by
  classical
  apply Finset.sum_nonneg
  intro e he
  split_ifs
  · exact cutIndicator_nonneg c e
  · exact le_rfl

theorem pieceOpponents_le_degree (E : Finset (V × V)) (c : V → Bool) (v : V) :
    pieceOpponents E c v ≤ pieceDegree E v := by
  classical
  apply Finset.sum_le_sum
  intro e he
  split_ifs
  · exact cutIndicator_le_one c e
  · exact le_rfl

open Classical in
private theorem cutIndicator_update_boundary (c : V → Bool) (v : V) (e : V × V)
    (hne : e.1 ≠ e.2) :
    cutIndicator (Function.update c v (!c v)) e =
      cutIndicator c e + (if e.1 = v ∨ e.2 = v then 1 else 0) -
        2 * (if e.1 = v ∨ e.2 = v then cutIndicator c e else 0) := by
  classical
  by_cases h₁ : e.1 = v <;> by_cases h₂ : e.2 = v
  all_goals cases hc₁ : c e.1 <;> cases hc₂ : c e.2 <;> cases hcv : c v
  all_goals simp_all [cutIndicator]

open Classical in
theorem cutOn_update_boundary (G : SimpleGraph V) (E : Finset (V × V))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2) (c : V → Bool) (v : V) :
    cutOn E (Function.update c v (!c v)) =
      cutOn E c + pieceDegree E v - 2 * pieceOpponents E c v := by
  classical
  unfold cutOn pieceDegree pieceOpponents
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e he =>
    cutIndicator_update_boundary c v e (G.ne_of_adj (hE e he))

/-- A finite set of finite-degree vertices, with its full outside boundary. -/
structure FinitePiece (G : SimpleGraph V) where
  verts : Finset V
  finite_degree : ∀ x ∈ verts, (G.neighborSet x).Finite

namespace FinitePiece

variable {G : SimpleGraph V} (P : FinitePiece G)

noncomputable def edges : Finset (V × V) :=
  (incident_finite G P.verts P.finite_degree).toFinset

open Classical in
noncomputable def boundary : Finset V :=
  (P.edges.image Prod.fst ∪ P.edges.image Prod.snd).filter (· ∉ P.verts)

noncomputable def score (c : V → Bool) : ℤ := cutOn P.edges c

def Respects (b : P.boundary → Bool) (c : V → Bool) : Prop :=
  ∀ v : P.boundary, c v.val = b v

theorem edge_mem (e : V × V) :
    e ∈ P.edges ↔ G.Adj e.1 e.2 ∧ (e.1 ∈ P.verts ∨ e.2 ∈ P.verts) :=
  (incident_finite G P.verts P.finite_degree).mem_toFinset

theorem boundary_not_mem {v : V} (hv : v ∈ P.boundary) : v ∉ P.verts := by
  classical
  exact (Finset.mem_filter.mp hv).2

theorem endpoints {e : V × V} (he : e ∈ P.edges) :
    (e.1 ∈ P.verts ∨ e.1 ∈ P.boundary) ∧
      (e.2 ∈ P.verts ∨ e.2 ∈ P.boundary) := by
  classical
  exact ⟨if h : e.1 ∈ P.verts then Or.inl h else Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), h⟩),
    if h : e.2 ∈ P.verts then Or.inl h else Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), h⟩)⟩

private theorem exists_maximum (b : P.boundary → Bool) :
    ∃ c : V → Bool, P.Respects b c ∧
      ∀ d : V → Bool, P.Respects b d → P.score d ≤ P.score c := by
  classical
  let c₀ : V → Bool := fun x => if hx : x ∈ P.boundary then b ⟨x, hx⟩ else false
  have hc₀ : P.Respects b c₀ := fun v => dif_pos v.property
  obtain ⟨m, ⟨c, hc, hcm⟩, hm⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ c, P.Respects b c ∧ P.score c = z)
    ⟨P.edges.card, fun z ⟨c, _, hz⟩ => hz ▸ cutOn_le_card P.edges c⟩
    ⟨P.score c₀, c₀, hc₀, rfl⟩
  exact ⟨c, hc, fun d hd => hcm ▸ hm _ ⟨d, hd, rfl⟩⟩

noncomputable def profile (b : P.boundary → Bool) : ℤ :=
  P.score (Classical.choose (P.exists_maximum b))

theorem profile_attained (b : P.boundary → Bool) :
    ∃ c : V → Bool, P.Respects b c ∧ P.score c = P.profile b :=
  ⟨Classical.choose (P.exists_maximum b), (Classical.choose_spec (P.exists_maximum b)).1, rfl⟩

theorem le_profile (b : P.boundary → Bool) (c : V → Bool) (hc : P.Respects b c) :
    P.score c ≤ P.profile b :=
  (Classical.choose_spec (P.exists_maximum b)).2 c hc

private theorem score_not (c : V → Bool) : P.score (fun x => !c x) = P.score c := by
  unfold score cutOn
  refine Finset.sum_congr rfl fun e _ => ?_
  cases h₁ : c e.1 <;> cases h₂ : c e.2 <;> simp [cutIndicator, h₁, h₂]

theorem profile_even (b : P.boundary → Bool) :
    P.profile (fun v => !b v) = P.profile b := by
  have hle : ∀ b, P.profile b ≤ P.profile (fun v => !b v) := by
    intro b
    obtain ⟨c, hc, hmax⟩ := P.profile_attained b
    have hres : P.Respects (fun v => !b v) (fun x => !c x) :=
      fun v => congrArg Bool.not (hc v)
    have h := P.le_profile _ _ hres
    rw [P.score_not c] at h
    omega
  exact le_antisymm (by simpa only [Bool.not_not] using hle (fun v => !b v)) (hle b)

open Classical in
private theorem respects_update (b : P.boundary → Bool) (c : V → Bool)
    (hc : P.Respects b c) (v : P.boundary) :
    P.Respects (PairProfile.toggle b v) (Function.update c v.val (!c v.val)) := by
  classical
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [PairProfile.toggle, Function.update_self] using congrArg Bool.not (hc v)
  · have hval : w.val ≠ v.val := fun h => hw (Subtype.ext h)
    simpa only [PairProfile.toggle, Function.update, dif_neg hval, dif_neg hw] using hc w

theorem profile_response (b : P.boundary → Bool) (c : V → Bool)
    (hc : P.Respects b c) (hmax : P.score c = P.profile b) (v : P.boundary) :
    pieceDegree P.edges v.val + P.profile b - P.profile (PairProfile.toggle b v) ≤
      2 * pieceOpponents P.edges c v.val := by
  classical
  have h := P.le_profile _ _ (P.respects_update b c hc v)
  have heq := cutOn_update_boundary G P.edges
    (fun e he => ((P.edge_mem e).mp he).1) c v.val
  change cutOn P.edges (Function.update c v.val (!c v.val)) ≤
    P.profile (PairProfile.toggle b v) at h
  rw [heq] at h
  change P.score c + pieceDegree P.edges v.val -
    2 * pieceOpponents P.edges c v.val ≤ P.profile (PairProfile.toggle b v) at h
  omega

theorem profile_flip_bound (b : P.boundary → Bool) (v : P.boundary) :
    P.profile b - P.profile (PairProfile.toggle b v) ≤ pieceDegree P.edges v.val := by
  obtain ⟨c, hc, hmax⟩ := P.profile_attained b
  have h := P.profile_response b c hc hmax v
  linarith [pieceOpponents_le_degree P.edges c v.val]

theorem eq_profile_of_strongMaximal (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c) :
    P.score c = P.profile b := by
  classical
  obtain ⟨d, hd, hdmax⟩ := P.profile_attained b
  let S : Finset V := P.verts.filter (fun y => d y ≠ c y)
  have hSC : S ⊆ P.verts := Finset.filter_subset _ _
  have hgain := hc S (fun x hx => hPM (hSC hx))
    (fun x hx => P.finite_degree x (hSC hx))
  have hdiff : gain G c S = cutOn P.edges (flip c S) - cutOn P.edges c :=
    gain_eq_cutOn_sub G c S P.edges
      (fun e he => (P.edge_mem e).mpr
        ⟨he.1, he.2.imp (fun h => hSC h) (fun h => hSC h)⟩)
      (fun e he => ((P.edge_mem e).mp he).1)
  have hflip : ∀ y, y ∈ P.verts ∨ y ∈ P.boundary → flip c S y = d y := by
    intro y hy
    by_cases hyC : y ∈ P.verts
    · by_cases hyd : d y = c y
      · have hyS : y ∉ S := fun h => (Finset.mem_filter.mp h).2 hyd
        exact (if_neg hyS).trans hyd.symm
      · have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hyC, hyd⟩
        refine (if_pos hyS).trans ?_
        revert hyd
        cases d y <;> cases c y <;> simp
    · have hyS : y ∉ S := fun h => hyC (hSC h)
      exact (if_neg hyS).trans
        ((hcb ⟨y, hy.resolve_left hyC⟩).trans (hd ⟨y, hy.resolve_left hyC⟩).symm)
  have hF : cutOn P.edges (flip c S) = P.score d :=
    cutOn_congr _ _ _ fun e he =>
      ⟨hflip e.1 (P.endpoints he).1, hflip e.2 (P.endpoints he).2⟩
  rw [hdiff, hF] at hgain
  change P.score d - P.score c ≤ 0 at hgain
  exact le_antisymm (P.le_profile b c hcb) (by omega)

/-- Strong maximality supplies the universal, completion-independent opponent certificate. -/
theorem opponent_certificate (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c)
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v : P.boundary) :
    PairProfile.weight a v ≤ 2 * pieceDegree P.edges v.val ∧
      2 * pieceDegree P.edges v.val - PairProfile.weight a v +
        2 * PairProfile.favouredWeight a b v ≤ 4 * pieceOpponents P.edges c v.val := by
  exact PairProfile.universal_opponent_certificate P.profile K a hrep
    (fun v => pieceDegree P.edges v.val) P.profile_flip_bound b v
    (pieceOpponents P.edges c v.val)
    (P.profile_response b c hcb (P.eq_profile_of_strongMaximal M c hPM hc b hcb) v)

theorem exists_opponent_of_pos (c : V → Bool) (v : P.boundary)
    (hop : 0 < pieceOpponents P.edges c v.val) :
    ∃ w ∈ P.verts, G.Adj v.val w ∧ c w ≠ c v.val := by
  classical
  have hnon : ∀ e ∈ P.edges, 0 ≤
      (if e.1 = v.val ∨ e.2 = v.val then cutIndicator c e else 0) := by
    intro e he
    split_ifs
    · exact cutIndicator_nonneg c e
    · exact le_rfl
  obtain ⟨e, he, hpos⟩ := (Finset.sum_pos_iff_of_nonneg hnon).mp hop
  have hi : e.1 = v.val ∨ e.2 = v.val := by
    by_contra hn
    simp only [if_neg hn, lt_self_iff_false] at hpos
  have hpc : 0 < cutIndicator c e := by simpa only [if_pos hi] using hpos
  have hne : c e.1 ≠ c e.2 := by
    intro h
    have hz : cutIndicator c e = 0 := by simp [cutIndicator, h]
    omega
  obtain ⟨hadj, hC⟩ := (P.edge_mem e).mp he
  have hv : v.val ∉ P.verts := P.boundary_not_mem v.property
  rcases hi with hL | hR
  · exact ⟨e.2, hC.resolve_left (fun h => hv (hL ▸ h)), hL ▸ hadj, (hL ▸ hne).symm⟩
  · exact ⟨e.1, hC.resolve_right (fun h => hv (hR ▸ h)), hR ▸ hadj.symm, hR ▸ hne⟩

theorem exists_pair_representation (hB : P.boundary.card ≤ 3) :
    ∃ K a, PairProfile.Represents P.profile K a := by
  apply PairProfile.exists_representation_of_card_le_three _ P.profile P.profile_even
  simpa only [Fintype.card_coe] using hB

theorem boundary_touch (v : P.boundary) :
    ∃ w ∈ P.verts, G.Adj v.val w := by
  classical
  obtain ⟨hends, hv⟩ := Finset.mem_filter.mp v.property
  rcases Finset.mem_union.mp hends with hL | hR
  · obtain ⟨e, he, hval⟩ := Finset.mem_image.mp hL
    have h := (P.edge_mem e).mp he
    exact ⟨e.2, h.2.resolve_left (fun he => hv (hval ▸ he)), hval ▸ h.1⟩
  · obtain ⟨e, he, hval⟩ := Finset.mem_image.mp hR
    have h := (P.edge_mem e).mp he
    exact ⟨e.1, h.2.resolve_right (fun he => hv (hval ▸ he)), hval ▸ h.1.symm⟩

theorem degree_pos (v : P.boundary) : 0 < pieceDegree P.edges v.val := by
  classical
  obtain ⟨w, hw, hvw⟩ := P.boundary_touch v
  have he : (v.val, w) ∈ P.edges := (P.edge_mem _).mpr ⟨hvw, Or.inr hw⟩
  have hs := Finset.single_le_sum (s := P.edges)
    (f := fun e => if e.1 = v.val ∨ e.2 = v.val then (1 : ℤ) else 0)
    (fun e _ => by split_ifs <;> omega) he
  rw [if_pos (Or.inl rfl)] at hs
  change 1 ≤ pieceDegree P.edges v.val at hs
  omega

open Classical in
private theorem favoured_term_nonneg (a : ℤ) (x y : Bool) :
    0 ≤ (if PairProfile.Favoured a x y then |a| else 0) := by
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

private theorem favoured_nonneg
    (a : P.boundary → P.boundary → ℤ) (b : P.boundary → Bool) (v : P.boundary) :
    0 ≤ PairProfile.favouredWeight a b v :=
  Finset.sum_nonneg fun u _ => favoured_term_nonneg (a v u) (b v) (b u)

private theorem favoured_pos
    (a : P.boundary → P.boundary → ℤ) (b : P.boundary → Bool) (v u : P.boundary)
    (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    0 < PairProfile.favouredWeight a b v := by
  classical
  have hpos : 0 < |a v u| := abs_pos.mpr
    (hfav.elim (fun h => ne_of_gt h.1) (fun h => ne_of_lt h.1))
  apply (Finset.sum_pos_iff_of_nonneg
    (fun w _ => favoured_term_nonneg (a v w) (b v) (b w))).mpr
  exact ⟨u, Finset.mem_univ u, by simpa only [if_pos hfav] using hpos⟩

theorem opponent_of_slack (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c)
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v : P.boundary)
    (hslack : PairProfile.weight a v < 2 * pieceDegree P.edges v.val) :
    ∃ w ∈ P.verts, G.Adj v.val w ∧ c w ≠ c v.val := by
  have hcert := P.opponent_certificate M c hPM hc b hcb K a hrep v
  apply P.exists_opponent_of_pos c v
  linarith [hcert.2, P.favoured_nonneg a b v]

theorem opponent_of_favoured (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c)
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v u : P.boundary)
    (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    ∃ w ∈ P.verts, G.Adj v.val w ∧ c w ≠ c v.val := by
  have hcert := P.opponent_certificate M c hPM hc b hcb K a hrep v
  apply P.exists_opponent_of_pos c v
  linarith [hcert.1, hcert.2, P.favoured_pos a b v u hfav]

theorem exists_interaction_of_not_slack
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v : P.boundary)
    (hn : ¬ PairProfile.weight a v < 2 * pieceDegree P.edges v.val) :
    ∃ u, v ≠ u ∧ a v u ≠ 0 := by
  classical
  by_contra hno
  have hz : ∀ u, a v u = 0 := by
    intro u
    by_cases hu : v = u
    · subst u
      exact hrep.2.1 v
    · exact Classical.byContradiction (fun hnu => hno ⟨u, hu, hnu⟩)
  have hw : PairProfile.weight a v = 0 := by simp [PairProfile.weight, hz]
  have hd := P.degree_pos v
  omega

theorem mem_boundary_of_adj {v w : V} (hv : v ∉ P.verts) (hw : w ∈ P.verts)
    (hvw : G.Adj v w) : v ∈ P.boundary := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(v, w), (P.edge_mem _).mpr ⟨hvw, Or.inr hw⟩, rfl⟩), hv⟩

end FinitePiece
end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlySignedSelection.lean. -/
/-!
# Permanent witnesses for signed constraints

The countable construction below assigns each vertex infinitely many distinct
neighbours meeting a prescribed Boolean response. Every witness is fixed when
it is selected, so the construction does not use preservation of an infinite
neighbourhood under a limit of recolourings.

This supplies the distinct-neighbour step used by `UnfriendlySignedMultigraph`.
The application to full-boundary cut profiles is formalized in
`UnfriendlyThreeBoundaryGraph`. No unrestricted unfriendly partition theorem
is proved here.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.SignedSelection

variable {V : Type u}

/-- Countably many vertices with infinitely many available neighbours allow
infinitely many permanent witnesses for any prescribed Boolean response. -/
theorem exists_response_coloring [Countable V] (R : V → V → Prop)
    (response : V → V → Bool → Bool)
    (hR : ∀ x, {y | R x y}.Infinite) :
    ∃ c : V → Bool, ∀ x, {y | R x y ∧ c y = response x y (c x)}.Infinite := by
  classical
  cases isEmpty_or_nonempty V
  · exact ⟨fun _ => false, fun x => isEmptyElim x⟩
  · have hfresh : ∀ (D F : Finset V) (x : V),
        ∃ y, R x y ∧ y ∉ D ∧ y ≠ x ∧ y ∉ F := fun D F x =>
      let ⟨y, hy, hyK⟩ := (hR x).exists_notMem_finset (D ∪ insert x F)
      ⟨y, hy, fun hyD => hyK (Finset.mem_union_left _ hyD),
        fun h => hyK (Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl h))),
        fun hyF => hyK (Finset.mem_union_right _ (Finset.mem_insert_of_mem hyF))⟩
    choose w hw using hfresh
    letI : Encodable V := Encodable.ofCountable V
    -- Schedule every vertex together with every finite forbidden witness set.
    obtain ⟨e, he⟩ := exists_surjective_nat (V × Finset V)
    let s : ℕ → Finset V × (V → Bool) :=
      Nat.rec (∅, fun _ => false) (fun n state =>
        let x := (e n).1
        let y := w state.1 (e n).2 x
        (insert x (insert y state.1),
          Function.update state.2 y (response x y (state.2 x))))
    have hDstep : ∀ n, (s n).1 ⊆ (s (n + 1)).1 := fun n y hy =>
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)
    have hDmono : Monotone (fun n => (s n).1) := monotone_nat_of_le_succ hDstep
    -- Once a vertex enters the domain, its colour never changes.
    have hcolstep : ∀ n y, y ∈ (s n).1 → (s (n + 1)).2 y = (s n).2 y :=
      fun n y hy => Function.update_of_ne
        (show y ≠ w (s n).1 (e n).2 (e n).1 from
          fun h => (hw (s n).1 (e n).2 (e n).1).2.1 (h ▸ hy)) _ _
    have hcoh : ∀ {m n : ℕ}, m ≤ n →
        ∀ y ∈ (s m).1, (s n).2 y = (s m).2 y := fun {m n} hmn =>
      Nat.le_induction
        (P := fun n _ => ∀ y ∈ (s m).1, (s n).2 y = (s m).2 y)
        (fun _ _ => rfl)
        (fun k hmk ih y hy => (hcolstep k y (hDmono hmk hy)).trans (ih y hy)) n hmn
    have htask : ∀ n, (e n).1 ∈ (s (n + 1)).1 := fun n => Finset.mem_insert_self _ _
    have hcover : ∀ x, ∃ n, x ∈ (s n).1 := fun x =>
      let ⟨n, hn⟩ := he (x, ∅)
      ⟨n + 1, Eq.mp (congrArg (fun x => x ∈ (s (n + 1)).1)
        (congrArg Prod.fst hn)) (htask n)⟩
    choose index hindom using hcover
    let c : V → Bool := fun x => (s (index x)).2 x
    have hc : ∀ n, ∀ x ∈ (s n).1, c x = (s n).2 x := fun n x hx =>
      (hcoh (Nat.le_max_right n (index x)) x (hindom x)).symm.trans
        (hcoh (Nat.le_max_left n (index x)) x hx)
    have hnewdom : ∀ n, w (s n).1 (e n).2 (e n).1 ∈ (s (n + 1)).1 :=
      fun n => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hquery : ∀ n, c (e n).1 = (s n).2 (e n).1 := fun n =>
      (hc (n + 1) (e n).1 (htask n)).trans
        (Function.update_of_ne (hw (s n).1 (e n).2 (e n).1).2.2.1.symm _ _)
    have hnew : ∀ n, c (w (s n).1 (e n).2 (e n).1) =
        response (e n).1 (w (s n).1 (e n).2 (e n).1) (c (e n).1) := fun n =>
      ((hc (n + 1) _ (hnewdom n)).trans
        (Function.update_self (w (s n).1 (e n).2 (e n).1)
          (response (e n).1 (w (s n).1 (e n).2 (e n).1) ((s n).2 (e n).1))
          (s n).2)).trans
        (congrArg (response (e n).1 (w (s n).1 (e n).2 (e n).1)) (hquery n).symm)
    have hrequest : ∀ n, ∃ y, R (e n).1 y ∧
        c y = response (e n).1 y (c (e n).1) ∧ y ∉ (e n).2 := fun n =>
      ⟨w (s n).1 (e n).2 (e n).1, (hw (s n).1 (e n).2 (e n).1).1,
        hnew n, (hw (s n).1 (e n).2 (e n).1).2.2.2⟩
    have hreq : ∀ (x : V) (F : Finset V),
        ∃ y, R x y ∧ c y = response x y (c x) ∧ y ∉ F := fun x F =>
      let ⟨n, hn⟩ := he (x, F)
      Eq.mp (congrArg (fun t : V × Finset V =>
        ∃ y, R t.1 y ∧ c y = response t.1 y (c t.1) ∧ y ∉ t.2) hn) (hrequest n)
    -- A finite witness set is contradicted by the request forbidding that set.
    exact ⟨c, fun x hfin =>
      let ⟨y, hyR, hyc, hyF⟩ := hreq x hfin.toFinset
      hyF (hfin.mem_toFinset.mpr ⟨hyR, hyc⟩)⟩

/-- Prescribed colours can be retained when every other vertex has infinitely
many available neighbours outside the prescribed set. -/
theorem exists_response_coloring_eqOn [Countable V] (R : V → V → Prop)
    (response : V → V → Bool → Bool) (P : Set V) (p : V → Bool)
    (hR : ∀ x, x ∉ P → {y | R x y ∧ y ∉ P}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {y | R x y ∧ c y = response x y (c x)}.Infinite := by
  classical
  have hU : ∀ x : {x : V // x ∉ P}, {y : {y : V // y ∉ P} | R x.val y.val}.Infinite := by
    intro x
    apply Set.Infinite.of_image (Subtype.val : {x : V // x ∉ P} → V)
    exact (hR x.val x.property).mono fun y hy => ⟨⟨y, hy.2⟩, hy.1, rfl⟩
  obtain ⟨d, hd⟩ := exists_response_coloring
    (fun x y : {x : V // x ∉ P} => R x.val y.val)
    (fun x y b => response x.val y.val b) hU
  let c : V → Bool := fun x => if hx : x ∈ P then p x else d ⟨x, hx⟩
  have hc : ∀ x : {x : V // x ∉ P}, c x.val = d x := fun x => dif_neg x.property
  refine ⟨c, fun x hx => dif_pos hx, fun x hx => ?_⟩
  refine ((hd ⟨x, hx⟩).image (f := Subtype.val) (fun _ _ _ _ h => Subtype.ext h)).mono ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨hy.1, (hc y).trans (hy.2.trans
    (congrArg (response x y.val) (hc ⟨x, hx⟩).symm))⟩

private theorem signed_response_iff (a b s : Bool) :
    b = (a == s) ↔ (a == b) = s := by
  cases a <;> cases b <;> cases s <;> decide

/-- A signed relation with infinitely many distinct neighbours outside `P`
admits a colouring extending `p` with infinitely many satisfied requests at
each vertex outside `P`. A true sign asks for equal colours; false asks for
opposite colours. Parallel requests to the same neighbour are not counted
as distinct neighbours in this hypothesis or conclusion. -/
theorem exists_signed_coloring_eqOn [Countable V] (R : V → V → Prop)
    (sign : V → V → Bool) (P : Set V) (p : V → Bool)
    (hR : ∀ x, x ∉ P → {y | R x y ∧ y ∉ P}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {y | R x y ∧ (c x == c y) = sign x y}.Infinite := by
  obtain ⟨c, hcp, hc⟩ := exists_response_coloring_eqOn R (fun x y b => b == sign x y) P p hR
  exact ⟨c, hcp, fun x hx => (hc x hx).mono fun y hy =>
    ⟨hy.1, (signed_response_iff _ _ _).mp hy.2⟩⟩

end TenChallenges.Continuation.SignedSelection

/- Inlined from Continuation/UnfriendlySignedMultigraph.lean. -/
/-!
# Infinite satisfied degree in signed multigraphs

Edge identities are retained, and only the vertex type is assumed countable.
A parity of `false` requests equality; `true` requests opposite colours.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.SignedSelection

/-- A loopless multigraph whose edges request equality or opposition. -/
structure SignedMultiGraph (V : Type u) (E : Type v) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e
  parity : E → Bool

variable {V : Type u} {E : Type v}

/-- Toggle a colour exactly when the edge requests opposition. -/
def twist (b s : Bool) : Bool := if s then !b else b

private theorem twist_symm (a b s : Bool) : a = twist b s ↔ b = twist a s := by
  cases a <;> cases b <;> cases s <;> decide

private theorem twist_self (b : Bool) : twist b b = false := by
  cases b <;> rfl

private theorem infinite_bool_fiber {α : Type*} (s : Set α) (hs : s.Infinite)
    (f : α → Bool) : ∃ b, {e | e ∈ s ∧ f e = b}.Infinite := by
  haveI : Infinite s := Set.infinite_coe_iff.mpr hs
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber (fun e : s => f e.val)
  haveI := hb
  refine ⟨b, Set.infinite_of_injective_forall_mem
    (f := fun e : ((fun e : s => f e.val) ⁻¹' {b}) => e.val.val) ?_ ?_⟩
  · exact fun i j h => Subtype.ext (Subtype.ext h)
  · exact fun e => ⟨e.val.property, e.property⟩

namespace SignedMultiGraph

variable (M : SignedMultiGraph V E)

def Incident (x : V) (e : E) : Prop := M.left e = x ∨ M.right e = x

def Between (x y : V) : Set E :=
  {e | (M.left e = x ∧ M.right e = y) ∨ (M.left e = y ∧ M.right e = x)}

open Classical in
noncomputable def other (x : V) (e : E) : V :=
  if M.left e = x then M.right e else M.left e

def Satisfied (c : V → Bool) (e : E) : Prop :=
  c (M.left e) = twist (c (M.right e)) (M.parity e)

/-- Satisfied edges with both endpoints already frozen. -/
def witnesses (S : Set V) (c : V → Bool) (x : V) : Set E :=
  {e | M.Incident x e ∧ M.left e ∈ S ∧ M.right e ∈ S ∧ M.Satisfied c e}

def Admissible (P : Set V) (p : V → Bool) (S : Set V) (c : V → Bool) : Prop :=
  P ⊆ S ∧ Set.EqOn c p P ∧
    ∀ x ∈ S, x ∉ P → (M.witnesses S c x).Infinite

theorem incident_of_between {x y : V} {e : E} (he : e ∈ M.Between x y) :
    M.Incident x e :=
  he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)

theorem other_of_between {x y : V} {e : E} (he : e ∈ M.Between x y) :
    M.other x e = y := by
  classical
  rcases he with h | h
  · exact (if_pos h.1).trans h.2
  · exact (if_neg (fun hn => M.loopless e (hn.trans h.2.symm))).trans h.1

theorem between_other {x : V} {e : E} (he : M.Incident x e) :
    e ∈ M.Between x (M.other x e) := by
  classical
  rcases he with h | h
  · exact Or.inl ⟨h, (if_pos h).symm⟩
  · exact Or.inr ⟨(if_neg (fun hn => M.loopless e (hn.trans h.symm))).symm, h⟩

theorem endpoints_mem {S : Set V} {x : V} {e : E}
    (he : M.Incident x e) (hx : x ∈ S) (ho : M.other x e ∈ S) :
    M.left e ∈ S ∧ M.right e ∈ S := by
  classical
  rcases he with h | h
  · exact ⟨h.symm ▸ hx, (if_pos h : M.other x e = M.right e) ▸ ho⟩
  · exact ⟨(if_neg (fun hn => M.loopless e (hn.trans h.symm)) :
      M.other x e = M.left e) ▸ ho, h.symm ▸ hx⟩

theorem satisfied_iff_at (c : V → Bool) {x : V} {e : E} (he : M.Incident x e) :
    M.Satisfied c e ↔ c x = twist (c (M.other x e)) (M.parity e) := by
  classical
  rcases he with h | h
  · simp [Satisfied, other, h]
  · have hn : M.left e ≠ x := fun hn => M.loopless e (hn.trans h.symm)
    simpa only [Satisfied, other, if_neg hn, h] using
      twist_symm (c (M.left e)) (c x) (M.parity e)

theorem witnesses_mono {S T : Set V} {c d : V → Bool}
    (hST : S ⊆ T) (hdc : Set.EqOn d c S) (x : V) :
    M.witnesses S c x ⊆ M.witnesses T d x := by
  rintro e ⟨he, hL, hR, hs⟩
  refine ⟨he, hST hL, hST hR, ?_⟩
  simpa only [Satisfied, hdc hL, hdc hR] using hs

private theorem admissible_extend {P S T : Set V} {p q d : V → Bool}
    (hq : M.Admissible P p S q) (hST : S ⊆ T) (hdq : Set.EqOn d q S)
    (hnew : ∀ x ∈ T, x ∉ S → (M.witnesses T d x).Infinite) :
    M.Admissible P p T d := by
  refine ⟨hq.1.trans hST, fun x hx => (hdq (hq.1 hx)).trans (hq.2.1 hx), ?_⟩
  intro x hx hxP
  by_cases hxS : x ∈ S
  · exact (hq.2.2 x hxS hxP).mono (M.witnesses_mono hST hdq x)
  · exact hnew x hx hxS

private theorem exists_maximal_admissible (P : Set V) (p : V → Bool) :
    ∃ (S : Set V) (q : V → Bool), M.Admissible P p S q ∧
      ∀ (T : Set V) (q' : V → Bool), M.Admissible P p T q' → S ⊆ T →
        Set.EqOn q' q S → T ⊆ S := by
  classical
  let T : Type u := {a : Set V × (V → Bool) // M.Admissible P p a.1 a.2}
  let r : T → T → Prop := fun a b =>
    a.1.1 ⊆ b.1.1 ∧ Set.EqOn b.1.2 a.1.2 a.1.1
  have htrans : ∀ {a b c : T}, r a b → r b c → r a c := fun {a b c} hab hbc =>
    ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 (hab.1 hy)).trans (hab.2 hy)⟩
  have hchain : ∀ C : Set T, IsChain r C → ∃ ub, ∀ a ∈ C, r a ub := by
    intro C hC
    let dom : Set V := P ∪ ⋃ a ∈ C, a.1.1
    let col : V → Bool := fun y =>
      if h : ∃ a ∈ C, y ∈ a.1.1 then (Classical.choose h).1.2 y else p y
    have hcol : ∀ a ∈ C, Set.EqOn col a.1.2 a.1.1 := by
      intro a ha y hy
      have h : ∃ a ∈ C, y ∈ a.1.1 := ⟨a, ha, hy⟩
      have hs := Classical.choose_spec h
      have hv : col y = (Classical.choose h).1.2 y := dif_pos h
      rw [hv]
      by_cases heq : Classical.choose h = a
      · rw [heq]
      · rcases hC hs.1 ha heq with hle | hle
        · exact (hle.2 hs.2).symm
        · exact hle.2 hy
    have hP : Set.EqOn col p P := fun y hy =>
      if h : ∃ a ∈ C, y ∈ a.1.1 then
        (dif_pos h).trans ((Classical.choose h).property.2.1 hy)
      else dif_neg h
    have hAdm : M.Admissible P p dom col := by
      refine ⟨Set.subset_union_left, hP, ?_⟩
      intro x hx hxP
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hx.resolve_left hxP)
      exact (a.property.2.2 x hxa hxP).mono (M.witnesses_mono (T := dom)
        (fun y hy => Or.inr (Set.mem_iUnion₂.mpr ⟨a, ha, hy⟩)) (hcol a ha) x)
    exact ⟨⟨(dom, col), hAdm⟩, fun a ha =>
      ⟨fun y hy => Or.inr (Set.mem_iUnion₂.mpr ⟨a, ha, hy⟩), hcol a ha⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  exact ⟨m.1.1, m.1.2, m.property, fun S q' hAdm hsub hfix =>
    (hm ⟨(S, q'), hAdm⟩ ⟨hsub, hfix⟩).1⟩

private theorem extend_to_frozen (P S : Set V) (p q : V → Bool)
    (hq : M.Admissible P p S q) (x : V) (hx : x ∉ S)
    (hi : {e | M.Incident x e ∧ M.other x e ∈ S}.Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ M.Admissible P p (S ∪ {x}) q' := by
  classical
  obtain ⟨b, hb⟩ := infinite_bool_fiber _ hi
    (fun e => twist (q (M.other x e)) (M.parity e))
  let q' : V → Bool := Function.update q x b
  have hfix : Set.EqOn q' q S := fun y hy =>
    Function.update_of_ne (show y ≠ x from fun h => hx (h ▸ hy)) _ _
  have hxval : q' x = b := Function.update_self ..
  have hnew : (M.witnesses (S ∪ {x}) q' x).Infinite := hb.mono fun e he =>
    let hends := M.endpoints_mem he.1.1 (Or.inr rfl) (Or.inl he.1.2 :
      M.other x e ∈ S ∪ {x})
    ⟨he.1.1, hends.1, hends.2, (M.satisfied_iff_at q' he.1.1).mpr
      (hxval.trans (he.2.symm.trans
        (congrArg (fun b => twist b (M.parity e)) (hfix he.1.2)).symm))⟩
  refine ⟨q', hfix, M.admissible_extend hq Set.subset_union_left hfix ?_⟩
  rintro v (hv | rfl) hnot
  · exact (hnot hv).elim
  · exact hnew

private theorem extend_parallel (P S : Set V) (p q : V → Bool)
    (hq : M.Admissible P p S q) (x y : V) (hx : x ∉ S) (hy : y ∉ S)
    (hi : (M.Between x y).Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ M.Admissible P p (S ∪ {x, y}) q' := by
  classical
  have hxy : x ≠ y := fun h =>
    let ⟨e, he⟩ := hi.nonempty
    he.elim (fun he => M.loopless e (he.1.trans (h.trans he.2.symm)))
      (fun he => M.loopless e (he.1.trans (h.symm.trans he.2.symm)))
  obtain ⟨b, hb⟩ := infinite_bool_fiber _ hi M.parity
  let q' : V → Bool := Function.update (Function.update q x false) y b
  let T : Set V := S ∪ {x, y}
  have hfix : Set.EqOn q' q S := fun v hv =>
    (Function.update_of_ne (show v ≠ y from fun h => hy (h ▸ hv)) _ _).trans
      (Function.update_of_ne (show v ≠ x from fun h => hx (h ▸ hv)) _ _)
  have hqx : q' x = false := (Function.update_of_ne hxy _ _).trans (Function.update_self ..)
  have hqy : q' y = b := Function.update_self ..
  have hends : ∀ e, e ∈ M.Between x y → M.left e ∈ T ∧ M.right e ∈ T :=
    fun e he => M.endpoints_mem (M.incident_of_between he)
      (show x ∈ T from Or.inr (Or.inl rfl))
      (Eq.mp (congrArg (fun v => v ∈ T) (M.other_of_between he).symm)
        (show y ∈ T from Or.inr (Or.inr rfl)))
  have hsat : ∀ e, e ∈ M.Between x y ∧ M.parity e = b → M.Satisfied q' e :=
    fun e he => (M.satisfied_iff_at q' (M.incident_of_between he.1)).mpr
      (hqx.trans ((twist_self b).symm.trans (congrArg₂ twist
        ((congrArg q' (M.other_of_between he.1)).trans hqy).symm he.2.symm)))
  have hnewx : (M.witnesses T q' x).Infinite := hb.mono fun e he =>
    ⟨M.incident_of_between he.1, (hends e he.1).1, (hends e he.1).2, hsat e he⟩
  have hnewy : (M.witnesses T q' y).Infinite := hb.mono fun e he =>
    ⟨he.1.elim (fun he => Or.inr he.2) (fun he => Or.inl he.1),
      (hends e he.1).1, (hends e he.1).2, hsat e he⟩
  refine ⟨q', hfix, M.admissible_extend hq Set.subset_union_left hfix ?_⟩
  rintro v (hv | rfl | rfl) hnot
  · exact (hnot hv).elim
  · exact hnewx
  · exact hnewy

private theorem residual_neighbors (S : Set V)
    (hdeg : ∀ x, x ∉ S → {e | M.Incident x e}.Infinite)
    (hinto : ∀ x, x ∉ S → {e | M.Incident x e ∧ M.other x e ∈ S}.Finite)
    (hpair : ∀ x, x ∉ S → ∀ y, y ∉ S → (M.Between x y).Finite) :
    ∀ x, x ∉ S → {y | y ∉ S ∧ (M.Between x y).Nonempty}.Infinite := by
  intro x hx hfin
  have hi := (hdeg x hx).sdiff (hinto x hx)
  have hf := hfin.biUnion (fun y hy => hpair x hx y hy.1)
  exact hi (hf.subset fun e he => Set.mem_iUnion₂.mpr
    ⟨M.other x e, ⟨(fun ho => he.2 ⟨he.1, ho⟩), e, M.between_other he.1⟩,
      M.between_other he.1⟩)

private theorem complete_residual [Countable V] (P S : Set V) (p q : V → Bool)
    (hq : M.Admissible P p S q)
    (hres : ∀ x, x ∉ S → {y | y ∉ S ∧ (M.Between x y).Nonempty}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {e | M.Incident x e ∧ M.Satisfied c e}.Infinite := by
  classical
  let response : V → V → Bool → Bool := fun x y b =>
    if h : (M.Between x y).Nonempty then twist b (M.parity (Classical.choose h)) else b
  obtain ⟨c, hcS, hc⟩ := exists_response_coloring_eqOn
    (fun x y => (M.Between x y).Nonempty) response S q
    (fun x hx => (hres x hx).mono fun y hy => ⟨hy.2, hy.1⟩)
  refine ⟨c, fun x hx => (hcS (hq.1 hx)).trans (hq.2.1 hx), fun x hxP => ?_⟩
  by_cases hxS : x ∈ S
  · exact ((hq.2.2 x hxS hxP).mono
      (M.witnesses_mono (Set.subset_univ S) hcS x)).mono fun e he =>
        ⟨he.1, he.2.2.2⟩
  · let Y : Set V := {y | (M.Between x y).Nonempty ∧ c y = response x y (c x)}
    haveI : Infinite Y := Set.infinite_coe_iff.mpr (hc x hxS)
    have hinj : Function.Injective (fun y : Y => Classical.choose y.property.1) :=
      fun y z heq => Subtype.ext
        ((M.other_of_between (Classical.choose_spec y.property.1)).symm.trans
          ((congrArg (M.other x) heq).trans
            (M.other_of_between (Classical.choose_spec z.property.1))))
    have hresponse : ∀ y : Y, c y.val =
        twist (c x) (M.parity (Classical.choose y.property.1)) := fun y =>
      y.property.2.trans (dif_pos y.property.1)
    have hsat : ∀ y : Y, M.Satisfied c (Classical.choose y.property.1) := fun y =>
      (M.satisfied_iff_at c (M.incident_of_between
        (Classical.choose_spec y.property.1))).mpr
        ((twist_symm _ _ _).mpr
          ((congrArg c (M.other_of_between
            (Classical.choose_spec y.property.1))).trans (hresponse y)))
    exact Set.infinite_of_injective_forall_mem hinj fun y =>
      ⟨M.incident_of_between (Classical.choose_spec y.property.1), hsat y⟩

/-- Prescribed colours extend so that every other vertex satisfies infinitely
many incident edge identities. No countability assumption on the edge type is needed. -/
theorem exists_infinitely_satisfied_extension [Countable V]
    (P : Set V) (p : V → Bool)
    (hdeg : ∀ x, x ∉ P → {e | M.Incident x e}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {e | M.Incident x e ∧ M.Satisfied c e}.Infinite := by
  classical
  obtain ⟨S, q, hq, hmax⟩ := M.exists_maximal_admissible P p
  have hinto : ∀ x, x ∉ S →
      {e | M.Incident x e ∧ M.other x e ∈ S}.Finite := fun x hx =>
    Set.not_infinite.mp fun hi =>
      let ⟨q', hfix, hnew⟩ := M.extend_to_frozen P S p q hq x hx hi
      hx (hmax (S ∪ {x}) q' hnew Set.subset_union_left hfix (Or.inr rfl))
  have hpair : ∀ x, x ∉ S → ∀ y, y ∉ S → (M.Between x y).Finite :=
    fun x hx y hy => Set.not_infinite.mp fun hi =>
      let ⟨q', hfix, hnew⟩ := M.extend_parallel P S p q hq x y hx hy hi
      hx (hmax (S ∪ {x, y}) q' hnew Set.subset_union_left hfix (Or.inr (Or.inl rfl)))
  exact M.complete_residual P S p q hq
    (M.residual_neighbors S
      (fun x hx => hdeg x (fun hxP => hx (hq.1 hxP))) hinto hpair)

end SignedMultiGraph
end TenChallenges.Continuation.SignedSelection

/- Inlined from Continuation/UnfriendlyFromGlobal.lean. -/
set_option autoImplicit false


namespace TenChallenges.Continuation

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- An extension unfriendly at the queried vertex admits a finite consistent response. -/
theorem finite_response_of_unfriendly_partition (p : V → Option Bool)
    (f : V → Option Bool) (hf : HasFiniteDomain f) (hfp : Extends f p)
    (v : V) (hp : UnfriendlyAt G p v) :
    ∃ g, IsLegalResponse G f g v ∧ Extends g p := by
  classical
  obtain ⟨b, hpv, hcard⟩ := hp
  let S : Set V := G.neighborSet v ∩ f ⁻¹' {some b}
  have hS : S.Finite := hf.subset
    (fun _ hx => Option.ne_none_iff_exists'.mpr ⟨b, hx.2⟩)
  have hsub : S ⊆ G.neighborSet v ∩ p ⁻¹' {some b} :=
    fun x hx => ⟨hx.1, hfp x b hx.2⟩
  obtain ⟨e⟩ := (Cardinal.le_def S (NeighColored G p v (some (!b)))).mp
    ((Cardinal.mk_le_mk_of_subset hsub).trans hcard)
  letI : Finite S := hS.to_subtype
  let T : Set V := Set.range fun x : S => (e x).1
  have hT : T.Finite := Set.finite_range _
  have hTc : ∀ x ∈ T, p x = some (!b) :=
    fun _ ⟨y, hy⟩ => hy ▸ (e y).2.2
  let g : V → Option Bool := fun x => if x = v ∨ x ∈ T then p x else f x
  have hfg : Extends f g := fun x c hc =>
    if h : x = v ∨ x ∈ T then (if_pos h).trans (hfp x c hc)
    else (if_neg h).trans hc
  have hgp : Extends g p := fun x c hc =>
    if h : x = v ∨ x ∈ T then (if_pos h).symm.trans hc
    else hfp x c ((if_neg h).symm.trans hc)
  have hgf : HasFiniteDomain g := (hf.union ((Set.finite_singleton v).union hT)).subset
    fun x hx => if h : x = v ∨ x ∈ T then Or.inr h else Or.inl
      (fun hn => hx ((if_neg h).trans hn))
  have hsame : (G.neighborSet v ∩ g ⁻¹' {some b}) ⊆ S := fun x hx =>
    ⟨hx.1, if h : x = v ∨ x ∈ T then h.elim
      (fun hv => False.elim (G.irrefl (hv ▸ hx.1)))
      (fun ht => False.elim ((Bool.not_eq_self b).mp (Option.some.inj
        ((hTc x ht).symm.trans ((if_pos h).symm.trans hx.2)))))
    else (if_neg h).symm.trans hx.2⟩
  let E : S ↪ NeighColored G g v (some (!b)) :=
    ⟨fun s => ⟨(e s).1, (e s).2.1,
      (if_pos (Or.inr ⟨s, rfl⟩)).trans (e s).2.2⟩,
      fun s t h => e.injective (Subtype.ext
        (congrArg (fun z : NeighColored G g v (some (!b)) => z.val) h))⟩
  exact ⟨g, ⟨hfg, hgf, b, (if_pos (Or.inl rfl)).trans hpv,
    (Cardinal.mk_le_mk_of_subset hsame).trans ((Cardinal.le_def ..).mpr ⟨E⟩)⟩, hgp⟩

/-- Finite partial partitions consistent with a global unfriendly partition
win at every clock. -/
theorem wins_from_unfriendly_partition (p : V → Option Bool)
    (hp : ∀ v, UnfriendlyAt G p v) :
    ∀ (α : Ordinal.{v}) (f : V → Option Bool),
      HasFiniteDomain f → Extends f p → PartitionerWins G f α := by
  intro α
  induction α using WellFoundedLT.induction
  rename_i α ih
  intro f hf hfp
  rw [PartitionerWins]
  exact fun x β hβ =>
    let ⟨g, hg, hgp⟩ := finite_response_of_unfriendly_partition G p f hf hfp x (hp x)
    ⟨g, hg, ih β hβ g hg.2.1 hgp⟩

/-- A global unfriendly partition gives Partitioner a winning strategy at every ordinal clock. -/
theorem partitionerWins_of_unfriendly_partition (p : V → Option Bool)
    (hp : ∀ v, UnfriendlyAt G p v) (α : Ordinal.{v}) :
    PartitionerWins G (emptyPartition V) α := by
  have hf : HasFiniteDomain (emptyPartition V) := by simp [HasFiniteDomain, emptyPartition]
  exact wins_from_unfriendly_partition G p hp α (emptyPartition V) hf
    (fun _ b h => False.elim (Option.some_ne_none b h.symm))

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyLimit.lean. -/
set_option autoImplicit false


namespace TenChallenges.Continuation

open scoped Cardinal

variable {V : Type u} [Countable V] (G : SimpleGraph V)

/-- Finite witnesses suffice for the cardinal majority inequality on a countable graph. -/
theorem unfriendlyAt_of_finite_approximations (p : V → Option Bool) (v : V) (b : Bool)
    (hpv : p v = some b)
    (ha : ∀ s : Finset V,
      (∀ x ∈ s, G.Adj v x ∧ p x = some b) →
      ∃ f : V → Option Bool, Extends f p ∧ UnfriendlyAt G f v ∧
        ∀ x ∈ s, f x = some b) :
    UnfriendlyAt G p v := by
  classical
  refine ⟨b, hpv, ?_⟩
  by_cases hO : (G.neighborSet v ∩ p ⁻¹' {some (!b)}).Finite
  · letI : Fintype (NeighColored G p v (some (!b))) := hO.fintype
    rw [Cardinal.mk_fintype (NeighColored G p v (some (!b)))]
    apply Cardinal.mk_le_iff_forall_finset_subset_card_le.mpr
    intro s hs
    obtain ⟨f, hfp, ⟨c, hfv, hc⟩, hsf⟩ := ha s (fun x hx => hs hx)
    have hcb : c = b := Option.some.inj ((hfp v c hfv).symm.trans hpv)
    subst c
    have hle : #(s : Set V) ≤ #(NeighColored G p v (some (!b))) :=
      (Cardinal.mk_le_mk_of_subset (show (s : Set V) ⊆
        G.neighborSet v ∩ f ⁻¹' {some b} from
          fun x hx => ⟨(hs hx).1, hsf x hx⟩)).trans
        (hc.trans (Cardinal.mk_le_mk_of_subset
          (fun x hx => ⟨hx.1, hfp x (!b) hx.2⟩)))
    change (#↥s : Cardinal.{u}) ≤ #(NeighColored G p v (some (!b))) at hle
    rw [Cardinal.mk_coe_finset] at hle
    simpa only [Cardinal.mk_fintype, Nat.cast_le] using hle
  · haveI : Infinite (NeighColored G p v (some (!b))) := Set.infinite_coe_iff.mpr hO
    haveI : Countable (NeighColored G p v (some b)) :=
      inferInstanceAs (Countable {x : V // G.Adj v x ∧ p x = some b})
    exact Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_mk _)

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyPersistent.lean. -/
/-!
# Persistent winning states in the unfriendly partition game

A state winning at every ordinal clock in the vertex universe admits, for every
query, a finite legal response that is again winning at every clock. This is a
structural consequence of the supremum of the losing clocks of all responses.
It does not assert that the empty coloring is a persistent state.
-/


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- A winning state at every clock in the universe of its vertex type. -/
def Persistent (f : V → Option Bool) : Prop :=
  ∀ α : Ordinal.{u}, PartitionerWins G f α

private theorem wins_mono {f : V → Option Bool} {α β : Ordinal.{v}}
    (hβα : β ≤ α) (h : PartitionerWins G f α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)

/-- Every query from a persistent state has a persistent finite legal response. -/
theorem persistent_response {f : V → Option Bool} (hf : Persistent G f) (x : V) :
    ∃ g, IsLegalResponse G f g x ∧ Persistent G g := by
  classical
  by_contra h
  have hbad : ∀ g : {g : V → Option Bool // IsLegalResponse G f g x},
      ∃ α : Ordinal.{u}, ¬ PartitionerWins G g.val α := fun g =>
    not_forall.mp (show ¬ Persistent G g.val from fun hg => h ⟨g.val, g.property, hg⟩)
  choose α hα using hbad
  let β : Ordinal.{u} := ⨆ g, α g
  have hw : PartitionerWins G f (Order.succ β) := hf _
  rw [PartitionerWins] at hw
  obtain ⟨g, hg, hwin⟩ := hw x β (Order.lt_succ β)
  exact hα ⟨g, hg⟩ (wins_mono G (Ordinal.le_iSup α ⟨g, hg⟩) hwin)

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyPlay.lean. -/
/-!
# Fair play from a persistent unfriendly-partition state

On a countable graph, persistence of the empty state supplies an increasing chain
of partial colorings that covers every vertex and makes each vertex unfriendly
at arbitrarily late stages.
-/


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- A persistent empty state admits a fair infinite legal play on a countable graph. -/
theorem persistent_fair_play [Countable V] (h : Persistent G (emptyPartition V)) :
    ∃ f : ℕ → (V → Option Bool),
      (∀ n, Extends (f n) (f (n + 1))) ∧
      (∀ v, ∃ n b, f n v = some b) ∧
      (∀ v N, ∃ n, N ≤ n ∧ UnfriendlyAt G (f n) v) := by
  classical
  cases isEmpty_or_nonempty V
  · exact ⟨fun _ => emptyPartition V, fun _ _ _ hx => hx,
      fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  · obtain ⟨e, he⟩ := exists_surjective_nat V
    let q : ℕ → V := fun n => e (Nat.unpair n).1
    have hfair : ∀ v N, ∃ n, N ≤ n ∧ q n = v := fun v N =>
      let ⟨k, hk⟩ := he v
      ⟨Nat.pair k N, Nat.right_le_pair k N,
        by simpa only [q, Nat.unpair_pair] using hk⟩
    choose R hR using fun (s : {f : V → Option Bool // Persistent G f}) (x : V) =>
      persistent_response G s.property x
    let s : ℕ → {f : V → Option Bool // Persistent G f} :=
      Nat.rec ⟨emptyPartition V, h⟩
        (fun n state => ⟨R state (q n), (hR state (q n)).2⟩)
    have hlegal : ∀ n, IsLegalResponse G (s n).val (s (n + 1)).val (q n) :=
      fun n => (hR (s n) (q n)).1
    have hUF : ∀ v N, ∃ n, N ≤ n ∧ UnfriendlyAt G (s n).val v := fun v N =>
      let ⟨n, hn, hq⟩ := hfair v N
      ⟨n + 1, hn.trans (Nat.le_succ n), hq ▸ (hlegal n).2.2⟩
    have hcover : ∀ v, ∃ n b, (s n).val v = some b := fun v =>
      let ⟨n, _, b, hb, _⟩ := hUF v 0
      ⟨n, b, hb⟩
    exact ⟨fun n => (s n).val, fun n => (hlegal n).1, hcover, hUF⟩

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyChain.lean. -/
/-!
# Finite approximation data from an increasing fair play

An increasing sequence that colors every vertex and makes each vertex unfriendly
at arbitrarily late stages determines a total coloring with compatible unfriendly
approximations for every finite set of same-colored neighbors.
-/


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- Fair increasing play supplies finite approximation witnesses for its total coloring. -/
theorem chain_data (f : ℕ → (V → Option Bool))
    (hext : ∀ n, Extends (f n) (f (n + 1)))
    (hcover : ∀ v, ∃ n b, f n v = some b)
    (huf : ∀ v N, ∃ n, N ≤ n ∧ UnfriendlyAt G (f n) v) :
    ∃ p : V → Option Bool, ∀ v, ∃ b, p v = some b ∧
      ∀ s : Finset V, (∀ x ∈ s, G.Adj v x ∧ p x = some b) →
        ∃ g, Extends g p ∧ UnfriendlyAt G g v ∧ ∀ x ∈ s, g x = some b := by
  classical
  have hmono : ∀ {m n}, m ≤ n → Extends (f m) (f n) := fun {m n} hmn =>
    Nat.le_induction (P := fun n _ => Extends (f m) (f n))
      (fun _ _ hx => hx) (fun n _ ih x b hx => hext n x b (ih x b hx)) n hmn
  choose index color hcolor using hcover
  let p : V → Option Bool := fun v => some (color v)
  have hFp : ∀ n, Extends (f n) p := fun n v b hv =>
    (hmono (Nat.le_max_right n (index v)) v (color v) (hcolor v)).symm.trans
      (hmono (Nat.le_max_left n (index v)) v b hv)
  refine ⟨p, fun v => ⟨color v, rfl, ?_⟩⟩
  intro s hs
  obtain ⟨n, hn, hu⟩ := huf v (s.sup index)
  exact ⟨f n, hFp n, hu, fun x hx =>
    (hmono ((Finset.le_sup hx).trans hn) x (color x) (hcolor x)).trans (hs x hx).2⟩

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyEquivalence.lean. -/
/-!
# Global unfriendly partitions and all ordinal game clocks

For a countable graph, existence of a global unfriendly partition is equivalent
to winning the game at every ordinal clock in the vertex universe. A global
partition also gives winning strategies for clocks in any independent universe.

This equivalence does not prove either existence statement for all countable
graphs. In particular, it does not prove that the empty state is persistent.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- The all-clock game and the global unfriendly-partition assertion are equivalent. -/
theorem unfriendly_partition_iff_persistent [Countable V] :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ↔
      Persistent G (emptyPartition V) := by
  exact ⟨fun ⟨p, hp⟩ α => partitionerWins_of_unfriendly_partition G p hp α,
    fun h =>
      let ⟨f, hext, hcover, huf⟩ := persistent_fair_play G h
      let ⟨p, hp⟩ := chain_data G f hext hcover huf
      ⟨p, fun x => let ⟨b, hpx, ha⟩ := hp x
        unfriendlyAt_of_finite_approximations G p x b hpx ha⟩⟩

/-- The equivalence with the clock quantifier written explicitly. -/
theorem unfriendly_partition_iff_all_clocks [Countable V] :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ↔
      ∀ α : Ordinal.{u}, PartitionerWins G (emptyPartition V) α :=
  unfriendly_partition_iff_persistent G

/-- A global partition supplies all clocks in an independent universe, without countability. -/
theorem all_clocks_of_global
    (h : ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  fun α => let ⟨p, hp⟩ := h
    partitionerWins_of_unfriendly_partition G p hp α

/-- All clocks in the vertex universe imply all clocks in any other universe. -/
theorem all_clocks_transfer_universe [Countable V]
    (h : ∀ α : Ordinal.{u}, PartitionerWins G (emptyPartition V) α) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G ((unfriendly_partition_iff_all_clocks G).mpr h)

end TenChallenges.Continuation

/- Inlined from Continuation/Challenge10Next.lean. -/
set_option linter.all false


namespace Continuation.TC10
open Classical SimpleGraph
open scoped Cardinal
variable {V : Type u} (G : SimpleGraph V)

/-- Every colored vertex is currently unfriendly. -/
def Stable (f : V → Option Bool) : Prop :=
  ∀ x b, f x = some b → UnfriendlyAt G f x

/-- Two simple shapes of a partial coloring which can safely accommodate one more query. -/
def Ready (f : V → Option Bool) : Prop :=
  ((∀ x b, f x = some b → b = false) ∧
    ∀ x y, f x = some false → f y = some false → ¬ G.Adj x y) ∨
  ((∀ b, (f ⁻¹' {some b}).Subsingleton) ∧
    ∀ x b, f x = some b → ∃ y, G.Adj x y ∧ f y = some (!b))

lemma neigh_update {f : V → Option Bool} (x : V) (b c : Bool) :
    #(NeighColored G (Function.update f x (some b)) x (some c)) =
      #(NeighColored G f x (some c)) := by
  apply Cardinal.mk_congr
  exact Equiv.subtypeEquivRight fun y => and_congr_right fun hy => by
    simp only [Set.mem_preimage, Function.update_of_ne (G.ne_of_adj hy).symm]

lemma no_same {f : V → Option Bool} {x : V} (b : Bool)
    (hfx : f x = some b) (hno : ∀ y, G.Adj x y → f y ≠ some b) :
    UnfriendlyAt G f x := by
  refine ⟨b, hfx, ?_⟩
  have hempty : IsEmpty (NeighColored G f x (some b)) :=
    ⟨fun ⟨y, hy⟩ => hno y hy.1 hy.2⟩
  exact (@Cardinal.mk_eq_zero (NeighColored G f x (some b)) hempty).symm ▸ zero_le

lemma unique_same {f : V → Option Bool} {x : V} (b : Bool)
    (hfx : f x = some b)
    (hsame : (G.neighborSet x ∩ f ⁻¹' {some b}).Subsingleton)
    (hopp : ∃ y, G.Adj x y ∧ f y = some (!b)) :
    UnfriendlyAt G f x := by
  refine ⟨b, hfx, hsame.cardinalMk_le_one.trans ?_⟩
  exact Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr
    (let ⟨y, hya, hyc⟩ := hopp; ⟨⟨y, hya, hyc⟩⟩))

lemma minority_update (f : V → Option Bool) (x : V) :
    ∃ b, UnfriendlyAt G (Function.update f x (some b)) x := by
  rcases le_total #(NeighColored G f x (some false)) #(NeighColored G f x (some true)) with h | h
  · exact ⟨false, false, by simp, by simpa only [neigh_update, Bool.not_false] using h⟩
  · exact ⟨true, true, by simp, by simpa only [neigh_update, Bool.not_true] using h⟩

lemma update_extends {f : V → Option Bool} {x : V} (hx : f x = none) (b : Bool) :
    Extends f (Function.update f x (some b)) := by
  intro y c hfy
  have hyx : y ≠ x := fun heq => by simpa [heq, hx] using hfy
  simpa only [Function.update_of_ne hyx] using hfy

lemma finite_update {f : V → Option Bool} (hf : HasFiniteDomain f) (x : V) (b : Bool) :
    HasFiniteDomain (Function.update f x (some b)) := by
  exact (hf.insert x).subset (fun y hy => (eq_or_ne y x).elim
    (fun h => Or.inl h)
    (fun h => Or.inr (by simpa only [Set.mem_setOf_eq, Function.update_of_ne h] using hy)))

lemma wins_zero (f : V → Option Bool) : PartitionerWins G f (0 : Ordinal.{v}) := by
  rw [PartitionerWins]
  exact fun _ _ h => (not_lt_zero h).elim


lemma stable_wins_one {f : V → Option Bool} (hf : HasFiniteDomain f) (hs : Stable G f) :
    PartitionerWins G f (1 : Ordinal.{v}) := by
  classical
  rw [PartitionerWins]
  intro x β hβ
  obtain rfl := Order.lt_one_iff.mp hβ
  exact (Classical.em (f x = none)).elim
    (fun hx => let ⟨b, hb⟩ := minority_update G f x
      ⟨Function.update f x (some b),
        ⟨update_extends hx b, finite_update hf x b, hb⟩, wins_zero G _⟩)
    (fun hx => let ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
      ⟨f, ⟨fun _ _ h => h, hf, hs x b hb⟩, wins_zero G _⟩)

lemma ready_stable {f : V → Option Bool} (hr : Ready G f) : Stable G f := by
  intro x b hfx
  rcases hr with ⟨hc, hi⟩ | ⟨hs, ho⟩
  · exact no_same G b hfx (fun y hxy hfy =>
      hi x y (hc x b hfx ▸ hfx) (hc y b hfy ▸ hfy) hxy)
  · exact no_same G b hfx (fun y hxy hfy => G.ne_of_adj hxy (hs b hfx hfy))

lemma ready_update {f : V → Option Bool} (hr : Ready G f) {x : V}
    (hx : f x = none) : ∃ b, Stable G (Function.update f x (some b)) := by
  rcases hr with hind | hsparse
  · refine ⟨true, fun y c hy => no_same G c hy ?_⟩
    intro z hyz hz
    cases c
    · simp [Function.update_apply, ite_eq_iff] at hy hz
      exact hind.2 y z hy.2 hz.2 hyz
    · have htrue : ∀ w, f w ≠ some true := fun w hw => Bool.noConfusion (hind.1 w true hw)
      simp [Function.update_apply, ite_eq_iff, htrue] at hy hz
      exact G.ne_of_adj hyz (hy.trans hz.symm)
  · obtain ⟨b, hb⟩ := minority_update G f x
    refine ⟨b, fun y c hy => ?_⟩
    by_cases hyx : y = x
    · exact hyx.symm ▸ hb
    · refine unique_same G c hy ?_ ?_
      · refine (Set.subsingleton_singleton (a := x)).anti ?_
        intro z hz
        by_contra hzx
        exact G.ne_of_adj hz.1 (hsparse.1 c
          (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hyx] using hy)
          (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hzx] using hz.2))
      · obtain ⟨z, hzy, hz⟩ := hsparse.2 y c (by simpa only [Function.update_of_ne hyx] using hy)
        exact ⟨z, hzy, update_extends hx b z (!c) hz⟩

lemma ready_response {f : V → Option Bool} (hf : HasFiniteDomain f) (hr : Ready G f) (x : V) :
    ∃ g, IsLegalResponse G f g x ∧ Stable G g := by
  by_cases hx : f x = none
  · obtain ⟨b, hb⟩ := ready_update G hr hx
    exact ⟨_, ⟨update_extends hx b, finite_update hf x b, hb x b (by simp)⟩, hb⟩
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨f, ⟨fun _ _ h => h, hf, ready_stable G hr x b hb⟩, ready_stable G hr⟩

noncomputable def first (a : V) : V → Option Bool :=
  Function.update (emptyPartition V) a (some false)

noncomputable def second (a b : V) : V → Option Bool :=
  Function.update (first a) b (some (if G.Adj a b then true else false))

lemma first_legal (a : V) : IsLegalResponse G (emptyPartition V) (first a) a := by
  refine ⟨update_extends rfl false,
    finite_update (by simp [HasFiniteDomain, emptyPartition]) a false,
    no_same G false (by simp [first]) ?_⟩
  intro y hay
  simp [first, Function.update_of_ne (G.ne_of_adj hay).symm, emptyPartition]

lemma second_legal_ready (a b : V) :
    IsLegalResponse G (first a) (second G a b) b ∧ Ready G (second G a b) := by
  have hr : Ready G (second G a b) := by
    by_cases hab : G.Adj a b
    · have hne := G.ne_of_adj hab
      have hfalse (x : V) : second G a b x = some false ↔ x = a := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition]
        exact fun e => e.symm ▸ hne
      have htrue (x : V) : second G a b x = some true ↔ x = b := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition]
      refine Or.inr ⟨?_, ?_⟩
      · intro c
        cases c
        · exact fun x hx y hy => (hfalse x).mp hx |>.trans ((hfalse y).mp hy).symm
        · exact fun x hx y hy => (htrue x).mp hx |>.trans ((htrue y).mp hy).symm
      · rintro x (_ | _) hx
        · exact ⟨b, ((hfalse x).mp hx).symm ▸ hab, (htrue b).mpr rfl⟩
        · exact ⟨a, ((htrue x).mp hx).symm ▸ hab.symm, (hfalse a).mpr rfl⟩
    · have hfalse (x : V) : second G a b x = some false ↔ x = b ∨ x = a := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition, imp_iff_not_or]
      refine Or.inl ⟨?_, ?_⟩
      · rintro x (_ | _) hx
        · rfl
        · simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition] at hx
      · intro x y hx hy
        rcases (hfalse x).mp hx with rfl | rfl
        all_goals rcases (hfalse y).mp hy with rfl | rfl
        all_goals simp_all [SimpleGraph.adj_comm]
  refine ⟨⟨?_, finite_update (first_legal G a).2.1 b (if G.Adj a b then true else false),
    ready_stable G hr b (if G.Adj a b then true else false) (by simp [second])⟩, hr⟩
  intro x c hx
  simp [first, Function.update_apply, emptyPartition, ite_eq_iff] at hx
  rcases hx with ⟨rfl, rfl⟩
  by_cases hxb : x = b <;> simp [second, first, hxb]


lemma wins_mono {f : V → Option Bool} {α β : Ordinal.{v}}
    (hβα : β ≤ α) (h : PartitionerWins G f α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)


/-- Partitioner wins the four-round game on every simple graph, without a countability assumption. -/
theorem win_four : PartitionerWins G (emptyPartition V) (4 : Ordinal.{v}) := by
  rw [PartitionerWins]
  intro a α hα
  refine ⟨first a, first_legal G a,
    wins_mono G (Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => α < o) (Ordinal.natCast_succ 3)).mp hα)) ?_⟩
  rw [PartitionerWins]
  intro b β hβ
  refine ⟨second G a b, (second_legal_ready G a b).1,
    wins_mono G (Order.lt_succ_iff.mp
      ((congrArg (fun o : Ordinal.{v} => β < o) (Ordinal.natCast_succ 2)).mp hβ)) ?_⟩
  rw [PartitionerWins]
  intro c γ hγ
  obtain ⟨g, hg, hs⟩ := ready_response G (second_legal_ready G a b).1.2.1
    (second_legal_ready G a b).2 c
  exact ⟨g, hg, wins_mono G
    ((show ((1 : ℕ) : Ordinal.{v}) = 1 from Nat.cast_one) ▸ Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => γ < o)
      (Ordinal.natCast_succ 1)).mp hγ)) (stable_wins_one G hg.2.1 hs)⟩

end Continuation.TC10

/- Inlined from Continuation/UnfriendlyInfiniteDegree.lean. -/
/-!
# Unfriendly partition games on graphs of infinite degree

Every finite partial coloring admits a legal response at a vertex with infinitely
many neighbors. Consequently, when every neighborhood is infinite, Partitioner
wins for every ordinal clock from every finite partial coloring.
-/

open SimpleGraph
open scoped Cardinal


namespace Continuation.InfiniteDegree

variable {V : Type u} (G : SimpleGraph V)

/-- A colored vertex with infinitely many neighbors can be made unfriendly by a finite extension. -/
lemma legal_response_colored {f : V → Option Bool} (hf : HasFiniteDomain f)
    (x : V) (b : Bool) (hfx : f x = some b) (hx : (G.neighborSet x).Infinite) :
    ∃ g, IsLegalResponse G f g x := by
  classical
  let D : Set V := {y | f y ≠ none}
  letI : Fintype D := hf.fintype
  have hT : (G.neighborSet x \ D).Infinite := hx.sdiff hf
  let e : D ↪ ↥(G.neighborSet x \ D) :=
    ((Fintype.equivFin D).toEmbedding.trans Fin.valEmbedding).trans (hT.natEmbedding _)
  let S : Set V := Set.range fun d : D => (e d).val
  have hSf : S.Finite := Set.finite_range _
  have hS : S ⊆ G.neighborSet x \ D := fun y ⟨d, hd⟩ => hd ▸ (e d).property
  let g : V → Option Bool := fun y => if y ∈ S then some (!b) else f y
  have hExt : Extends f g := fun y c hy =>
    (if_neg (fun hs : y ∈ S => (hS hs).2
      (show y ∈ D from fun hn => Option.some_ne_none c (hy.symm.trans hn)))).trans hy
  have hgf : HasFiniteDomain g := (hf.union hSf).subset fun y hy =>
    if h : y ∈ S then Or.inr h else Or.inl
      (show f y ≠ none from fun hn => hy ((if_neg h).trans hn))
  have hxS : x ∉ S := fun h => G.irrefl (hS h).1
  have hsame : (G.neighborSet x ∩ g ⁻¹' {some b}) ⊆ D := fun y hy =>
    if h : y ∈ S then False.elim ((Bool.not_eq_self b).mp
      (Option.some.inj ((if_pos h).symm.trans hy.2)))
    else fun hn => Option.some_ne_none b (hy.2.symm.trans ((if_neg h).trans hn))
  let E : D ↪ NeighColored G g x (some (!b)) :=
    ⟨fun d => ⟨(e d).val, (e d).property.1, if_pos ⟨d, rfl⟩⟩,
      fun d d' h => e.injective (Subtype.ext
        (congrArg (fun z : NeighColored G g x (some (!b)) => z.val) h))⟩
  exact ⟨g, hExt, hgf, b, (if_neg hxS).trans hfx,
    (Cardinal.mk_le_mk_of_subset hsame).trans ((Cardinal.le_def ..).mpr ⟨E⟩)⟩

/-- Every query at a vertex of infinite degree admits a finite legal response. -/
theorem legal_response {f : V → Option Bool} (hf : HasFiniteDomain f)
    (x : V) (hx : (G.neighborSet x).Infinite) :
    ∃ g, IsLegalResponse G f g x := by
  classical
  exact match hfx : f x with
    | some b => legal_response_colored G hf x b hfx hx
    | none =>
      let ⟨g, hg⟩ := legal_response_colored G (TC10.finite_update hf x false)
        x false (Function.update_self ..) hx
      ⟨g, ⟨fun y c hy => hg.1 y c (TC10.update_extends hfx false y c hy), hg.2⟩⟩

/-- No countability assumption is needed when all neighborhoods are infinite. -/
theorem partitionerWins_of_infinite_neighbors
    (hG : ∀ x, (G.neighborSet x).Infinite) (α : Ordinal.{v})
    {f : V → Option Bool} (hf : HasFiniteDomain f) : PartitionerWins G f α := by
  induction α using WellFoundedLT.induction generalizing f
  rename_i α ih
  rw [PartitionerWins]
  exact fun x β hβ => let ⟨g, hg⟩ := legal_response G hf x (hG x)
    ⟨g, hg, ih β hβ hg.2.1⟩

/-- Partitioner wins at every clock on a graph of infinite degree at every vertex. -/
theorem partitionerWins_empty_of_infinite_neighbors
    (hG : ∀ x, (G.neighborSet x).Infinite) (α : Ordinal.{v}) :
    PartitionerWins G (emptyPartition V) α :=
  partitionerWins_of_infinite_neighbors G hG α
    (by simp [HasFiniteDomain, emptyPartition])

end Continuation.InfiniteDegree

/- Inlined from Continuation/UnfriendlyRobustSteps.lean. -/
/-!
# Further extension steps for robust colourings of infinite-degree vertices

A maximal robust frozen colouring (see `UnfriendlyRecurrentBlocks`) cannot be extended by
any of three steps: a recurrent block, a vertex with infinitely many frozen neighbours, or
a set of vertices each having infinitely many neighbours inside the set. A finite set of
remaining infinite-degree vertices is then absorbed by finite repairs, which keep the
colouring strongly maximal and therefore keep every robust witness.

This is a special case of the countable unfriendly partition problem. It does not prove
the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

variable {V : Type u}

open Classical in
/-- Recurrent blocks are monotone in the frozen set: enlarging it only removes vertices
from the block. -/
theorem RecurrentBlock.relativize (G : SimpleGraph V) (S₀ S : Set V) (hS : S₀ ⊆ S)
    (B : Finset V) (h : RecurrentBlock G S₀ B) :
    RecurrentBlock G S (B.filter (· ∉ S)) := by
  obtain ⟨C, hdisj, hfin, hbdry, htouch⟩ := h
  refine ⟨C, hdisj, hfin, ?_, fun i u hu => htouch i u (Finset.mem_filter.mp hu).1⟩
  intro i x hx y hxy
  rcases hbdry i x hx y hxy with hC | hB | hE
  · exact Or.inl hC
  · by_cases hyS : y ∈ S
    · exact Or.inr (Or.inr hyS)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hB, hyS⟩))
  · exact Or.inr (Or.inr (hS hE))

/-- A vertex with infinitely many frozen neighbours can be frozen with the colour opposite
to infinitely many of them. -/
theorem Robust.extend_frozen_neighbors (G : SimpleGraph V) (M S : Set V) (q : V → Bool)
    (hq : Robust G M S q) (v : V) (hvS : v ∉ S)
    (hinf : (G.neighborSet v ∩ S).Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ {v}) q' := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Bool, {w | G.Adj v w ∧ w ∈ S ∧ q w = b}.Infinite := by
    by_contra hno
    have hf : ∀ b : Bool, {w | G.Adj v w ∧ w ∈ S ∧ q w = b}.Finite := fun b =>
      Set.not_infinite.mp fun hi => hno ⟨b, hi⟩
    refine hinf (((hf true).union (hf false)).subset fun w hw => ?_)
    cases hqw : q w
    · exact Or.inr ⟨hw.1, hw.2, hqw⟩
    · exact Or.inl ⟨hw.1, hw.2, hqw⟩
  have hq'S : Set.EqOn (Function.update q v (!b)) q S := fun y hy =>
    Function.update_of_ne (show y ≠ v from fun h => hvS (h ▸ hy)) _ _
  refine ⟨Function.update q v (!b), hq'S, ?_⟩
  intro c hc hcq u hu
  have hcS : Set.EqOn c q S := fun y hy => (hcq (Or.inl hy)).trans (hq'S hy)
  rcases hu with huS | huv
  · exact hq c hc hcS u huS
  · obtain rfl : u = v := huv
    have hcu : c u = !b := (hcq (Or.inr rfl)).trans (Function.update_self ..)
    refine hb.mono fun w hw => ⟨hw.1, ?_⟩
    rw [hcS hw.2.1, hw.2.2, hcu]
    cases b <;> simp

private theorem induce_neighbors_infinite (G : SimpleGraph V) (R : Set V)
    (hR : ∀ v ∈ R, (G.neighborSet v ∩ R).Infinite) :
    ∀ x : R, ((G.induce R).neighborSet x).Infinite := by
  intro x
  apply Set.Infinite.of_image (Subtype.val : R → V)
  simpa [SimpleGraph.neighborSet_induce, Set.image_preimage_eq_inter_range] using
    hR x.val x.property

private theorem exists_boolean_unfriendly_of_infinite_degrees [Countable V]
    (G : SimpleGraph V) (hG : ∀ x, (G.neighborSet x).Infinite) :
    ∃ c : V → Bool, ∀ x, UnfriendlyAt G (fun w => some (c w)) x := by
  obtain ⟨p, hp⟩ := (unfriendly_partition_iff_all_clocks G).mpr
    (fun α => _root_.Continuation.InfiniteDegree.partitionerWins_empty_of_infinite_neighbors
      G hG α)
  let c : V → Bool := fun x => (p x).getD false
  have hpc : p = fun x => some (c x) := by
    funext x
    obtain ⟨b, hb, _⟩ := hp x
    simp [c, hb]
  exact ⟨c, hpc ▸ hp⟩

/-- A set of unfrozen vertices, each with infinitely many neighbours inside the set, can be
frozen all at once: the induced graph has infinite minimum degree. -/
theorem Robust.extend_core [Countable V] (G : SimpleGraph V) (M S : Set V) (q : V → Bool)
    (hq : Robust G M S q) (J : Set V) (hJS : ∀ v ∈ J, v ∉ S)
    (hJ : ∀ v ∈ J, (G.neighborSet v ∩ J).Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ J) q' := by
  classical
  obtain ⟨cJ, hcJ⟩ := exists_boolean_unfriendly_of_infinite_degrees (G.induce J)
    (induce_neighbors_infinite G J hJ)
  let q' : V → Bool := fun w => if hw : w ∈ J then cJ ⟨w, hw⟩ else q w
  have hq'S : Set.EqOn q' q S := fun y hy => dif_neg (fun hyJ => hJS y hyJ hy)
  refine ⟨q', hq'S, ?_⟩
  intro c hc hcq v hv
  rcases hv with hvS | hvJ
  · exact hq c hc (fun y hy => (hcq (Or.inl hy)).trans (hq'S hy)) v hvS
  · have hcJ' : ∀ x : J, c x.val = cJ x := fun x =>
      (hcq (Or.inr x.property)).trans (dif_pos x.property)
    have hi := infinite_opposite_of_unfriendly (G.induce J) cJ ⟨v, hvJ⟩
      (induce_neighbors_infinite G J hJ ⟨v, hvJ⟩) (hcJ ⟨v, hvJ⟩)
    refine (hi.image (fun _ _ _ _ h => Subtype.ext h)).mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hy.1, fun heq => hy.2 ((hcJ' y).symm.trans (heq.trans (hcJ' ⟨v, hvJ⟩)))⟩

/-- Repair finitely many unfrozen infinite-degree vertices while preserving strong maximality
on `A` and the colours on `D`. Every vertex outside `A` with infinitely many opponents
before the repair still has infinitely many afterwards. -/
theorem finite_hub_stage_preserving [Countable V] (G : SimpleGraph V)
    (A D : Set V) (hDA : D ⊆ Aᶜ) (c0 : V → Bool)
    (hc0 : StrongMaximal G A c0) (F : Finset V)
    (hF : ∀ v ∈ F, (G.neighborSet v).Infinite ∧ v ∉ A ∧ v ∉ D) :
    ∃ c, Set.EqOn c c0 D ∧ StrongMaximal G A c ∧
      ∀ v ∉ A, v ∈ F ∨ (oppositeSet G c0 v).Infinite → (oppositeSet G c v).Infinite := by
  classical
  revert hF
  induction F using Finset.induction_on
  case empty =>
    exact fun _ => ⟨c0, fun _ _ => rfl, hc0,
      fun w _ hw => hw.resolve_left (Finset.notMem_empty w)⟩
  case insert v F hvF ih =>
    intro hF
    obtain ⟨c, hcD, hc, hgood⟩ := ih (fun w hw => hF w (Finset.mem_insert_of_mem hw))
    obtain ⟨hNv, hvA, hvD⟩ := hF v (Finset.mem_insert_self v F)
    have hold (w : V) (hwA : w ∉ A) (hwv : w ≠ v)
        (hw : w ∈ insert v F ∨ (oppositeSet G c0 w).Infinite) :
        (oppositeSet G c w).Infinite :=
      hgood w hwA (hw.imp_left fun h => (Finset.mem_insert.mp h).resolve_left hwv)
    by_cases hOpp : (oppositeSet G c v).Infinite
    · exact ⟨c, hcD, hc, fun w hwA hw => (eq_or_ne w v).elim
        (fun hwv => hwv.symm ▸ hOpp) (fun hwv => hold w hwA hwv hw)⟩
    · have hO : (oppositeSet G c v).Finite := Set.not_infinite.mp hOpp
      have hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v :=
        fun hUF => hOpp (infinite_opposite_of_unfriendly G c v hNv hUF)
      obtain ⟨S, hSA, _, hstable⟩ := exists_strongMaximal_repair G A c hc v hvA
        hO.toFinset (fun w ha hne => hO.mem_toFinset.mpr ⟨ha, hne⟩)
      have hfix : Set.EqOn (flip (flip c {v}) S) c D := fun w hw =>
        (if_neg (show w ∉ S from fun hwS => hDA hw (hSA hwS))).trans
          (if_neg (show w ∉ ({v} : Finset V) from
            fun hwv => hvD ((Finset.mem_singleton.mp hwv) ▸ hw)))
      have hnew : (oppositeSet G (flip (flip c {v}) S) v).Infinite :=
        infinite_opposite_flip G (flip c {v}) v S (fun hvS => hvA (hSA hvS))
          (infinite_opposite_flip_bad G c v hNv hbad)
      refine ⟨flip (flip c {v}) S, fun w hw => (hfix hw).trans (hcD hw), hstable, ?_⟩
      intro w hwA hw
      by_cases hwv : w = v
      · exact hwv.symm ▸ hnew
      · exact infinite_opposite_flip G (flip c {v}) w S (fun hwS => hwA (hSA hwS))
          (infinite_opposite_flip G c w {v} (fun h => hwv (Finset.mem_singleton.mp h))
            (hold w hwA hwv hw))

/-- Finitely many infinite-degree vertices outside `A` and outside a fixed set `D` can
acquire infinite opposite neighbourhoods, keeping strong maximality on `A` and all colours
on `D`. -/
theorem finite_hub_stage_fixing [Countable V] (G : SimpleGraph V)
    (A D : Set V) (hDA : D ⊆ Aᶜ) (c0 : V → Bool)
    (hc0 : StrongMaximal G A c0) (F : Finset V)
    (hF : ∀ v ∈ F, (G.neighborSet v).Infinite ∧ v ∉ A ∧ v ∉ D) :
    ∃ c, Set.EqOn c c0 D ∧ StrongMaximal G A c ∧
      ∀ v ∈ F, (oppositeSet G c v).Infinite :=
  let ⟨c, hfixed, hmax, hgood⟩ := finite_hub_stage_preserving G A D hDA c0 hc0 F hF
  ⟨c, hfixed, hmax, fun v hv => hgood v (hF v hv).2.1 (Or.inl hv)⟩

/-- A robust frozen colouring of all but finitely many infinite-degree vertices yields an
unfriendly partition: the finite remainder is repaired without leaving the strongly
maximal colourings that agree with the frozen colours. -/
theorem exists_unfriendly_of_robust_cofinite [Countable V] (G : SimpleGraph V)
    (S : Set V) (q : V → Bool)
    (hS : S ⊆ {v | (G.neighborSet v).Infinite})
    (hq : Robust G {v | (G.neighborSet v).Infinite}ᶜ S q)
    (hfin : ({v | (G.neighborSet v).Infinite} \ S).Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  obtain ⟨c0, hc0q, hc0⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {v | (G.neighborSet v).Infinite} q
  obtain ⟨c, hcS, hc, hgood⟩ := finite_hub_stage_fixing G
    {v | (G.neighborSet v).Infinite}ᶜ S (fun v hv hvc => hvc (hS hv)) c0 hc0 hfin.toFinset
    (fun v hv => ⟨(hfin.mem_toFinset.mp hv).1, fun hvc => hvc (hfin.mem_toFinset.mp hv).1,
      (hfin.mem_toFinset.mp hv).2⟩)
  refine ⟨fun v => some (c v), fun v => ?_⟩
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G _ c hc v (fun hInf => hInf hN) hN
  · apply unfriendly_of_infinite_opposite G c v
    by_cases hvS : v ∈ S
    · exact hq c hc (fun y hy => (hcS hy).trans (hc0q (hS hy))) v hvS
    · exact hgood v (hfin.mem_toFinset.mpr ⟨hN, hvS⟩)

/-- **Robust exhaustion.** Suppose that whenever a set `S` of infinite-degree vertices
leaves infinitely many of them outside, one of three steps is available: a nonempty
recurrent block over `S`, a further vertex with infinitely many neighbours in `S`, or a
nonempty set of further vertices each having infinitely many neighbours in that set.
Then the countable graph has an unfriendly partition. -/
theorem exists_unfriendly_of_robust_steps [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ v, (G.neighborSet v).Infinite ∧ v ∉ S ∧ (G.neighborSet v ∩ S).Infinite) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, (G.neighborSet v ∩ J).Infinite)) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {v | (G.neighborSet v).Infinite}ᶜ {v | (G.neighborSet v).Infinite}
  by_cases hfin : ({v | (G.neighborSet v).Infinite} \ S).Finite
  · exact exists_unfriendly_of_robust_cofinite G S q hSH hrob hfin
  · exfalso
    rcases h S hSH hfin with ⟨A, ⟨a, ha⟩, hA, hblock⟩ | ⟨v, hvI, hvS, hinf⟩ |
      ⟨J, ⟨j, hj⟩, hJ, hJinf⟩
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob A (fun v hv => (hA v hv).2)
        (fun v hv => (hA v hv).1) (fun x hx hinf => hinf hx) hblock
      exact (hA a ha).2 (hmax (S ∪ (A : Set V)) q'
        (Set.union_subset hSH (fun v hv => (hA v hv).1)) hq' Set.subset_union_left hq'q
        (Or.inr ha))
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_frozen_neighbors G _ S q hrob v hvS hinf
      exact hvS (hmax (S ∪ {v}) q'
        (Set.union_subset hSH (Set.singleton_subset_iff.mpr hvI)) hq' Set.subset_union_left
        hq'q (Or.inr rfl))
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_core G _ S q hrob J (fun v hv => (hJ v hv).2)
        hJinf
      exact (hJ j hj).2 (hmax (S ∪ J) q'
        (Set.union_subset hSH (fun v hv => (hJ v hv).1)) hq' Set.subset_union_left hq'q
        (Or.inr hj))

/-- **Recurrent or hub-rich.** A countable graph has an unfriendly partition if all but
finitely many of its infinite-degree vertices either lie in a recurrent finite boundary of
infinite-degree vertices or have infinitely many infinite-degree neighbours. -/
theorem exists_unfriendly_of_recurrent_or_hub_rich [Countable V] (G : SimpleGraph V)
    (h : {v | (G.neighborSet v).Infinite ∧
        (¬ ∃ B : Finset V, v ∈ B ∧ (∀ u ∈ B, (G.neighborSet u).Infinite) ∧
          RecurrentBlock G ∅ B) ∧
        (G.neighborSet v ∩ {w | (G.neighborSet w).Infinite}).Finite}.Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  refine exists_unfriendly_of_robust_steps G fun S hSH hinfS => ?_
  by_cases hrec : ∃ v, (G.neighborSet v).Infinite ∧ v ∉ S ∧
      ∃ B : Finset V, v ∈ B ∧ (∀ u ∈ B, (G.neighborSet u).Infinite) ∧ RecurrentBlock G ∅ B
  · obtain ⟨v, _, hvS, B, hvB, hBI, hB⟩ := hrec
    exact Or.inl ⟨B.filter (· ∉ S), ⟨v, Finset.mem_filter.mpr ⟨hvB, hvS⟩⟩,
      fun u hu => ⟨hBI u (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩,
      RecurrentBlock.relativize G ∅ S (Set.empty_subset S) B hB⟩
  · by_cases hfro : ∃ v, (G.neighborSet v).Infinite ∧ v ∉ S ∧ (G.neighborSet v ∩ S).Infinite
    · exact Or.inr (Or.inl hfro)
    · refine Or.inr (Or.inr ⟨_, (hinfS.sdiff h).nonempty,
        fun v hv => ⟨hv.1.1, hv.1.2⟩, fun v hv => ?_⟩)
      have hhub : (G.neighborSet v ∩ {w | (G.neighborSet w).Infinite}).Infinite := fun hf =>
        hv.2 ⟨hv.1.1, fun hB => hrec ⟨v, hv.1.1, hv.1.2, hB⟩, hf⟩
      have hSfin : (G.neighborSet v ∩ S).Finite :=
        Set.not_infinite.mp fun hi => hfro ⟨v, hv.1.1, hv.1.2, hi⟩
      refine (hhub.sdiff (hSfin.union h)).mono fun w hw => ?_
      exact ⟨hw.1.1, ⟨hw.1.2, fun hwS => hw.2 (Or.inl ⟨hw.1.1, hwS⟩)⟩,
        fun hwX => hw.2 (Or.inr hwX)⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyPairWitness.lean. -/
/-!
# Pair-profile witnesses without covering every finite-degree vertex

The auxiliary edge type retains each piece and each pair identity. Vertices
with infinitely many positive-slack pieces can receive arbitrary hub colours.
The two finiteness arguments use finite pieces and finite boundary-pair fibres,
without any uniform size bound or any countability assumption on the index type.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

open Energy
open scoped BigOperators

variable {V : Type u} {ι : Type v}

abbrev Hubs (G : SimpleGraph V) := {x : V // (G.neighborSet x).Infinite}

/-- Disjoint closed finite pieces with pair profiles. They need not cover the
finite-degree vertices. -/
structure PairWitnessSystem (G : SimpleGraph V) (ι : Type v) where
  piece : ι → Energy.FinitePiece G
  disjoint : Pairwise (Function.onFun Disjoint (fun i => (piece i).verts))
  boundary_hub : ∀ i, ∀ x : (piece i).boundary, (G.neighborSet x.val).Infinite
  constant : ι → ℤ
  coefficient : (i : ι) → (piece i).boundary → (piece i).boundary → ℤ
  representation : ∀ i, PairProfile.Represents (piece i).profile (constant i) (coefficient i)

namespace PairWitnessSystem

variable {G : SimpleGraph V} (D : PairWitnessSystem G ι)

abbrev DirectEdge (_D : PairWitnessSystem G ι) :=
  {p : Hubs G × Hubs G // G.Adj p.1.val p.2.val}

abbrev PiecePair (i : ι) := {p : (D.piece i).boundary × (D.piece i).boundary //
  p.1 ≠ p.2 ∧ D.coefficient i p.1 p.2 ≠ 0}

abbrev ComponentEdge := Σ i : ι, D.PiecePair i

abbrev Edge := D.DirectEdge ⊕ D.ComponentEdge

def hubOfBoundary (i : ι) (x : (D.piece i).boundary) : Hubs G :=
  ⟨x.val, D.boundary_hub i x⟩

noncomputable def auxiliary : SignedSelection.SignedMultiGraph (Hubs G) D.Edge where
  left := Sum.elim (fun e => e.val.1) (fun e => D.hubOfBoundary e.1 e.2.val.1)
  right := Sum.elim (fun e => e.val.2) (fun e => D.hubOfBoundary e.1 e.2.val.2)
  parity := Sum.elim (fun _ => true) (fun e => decide (0 < D.coefficient e.1 e.2.val.1 e.2.val.2))
  loopless := by
    intro e
    cases e with
    | inl e => exact fun h => G.ne_of_adj e.property (congrArg Subtype.val h)
    | inr e =>
      exact fun h => e.2.property.1
        (Subtype.ext (congrArg (Subtype.val : Hubs G → V) h))

def source : D.Edge → Option ι := Sum.elim (fun _ => none) (fun e => some e.1)

def automatic (x : Hubs G) : Set ι := {i | ∃ hx : x.val ∈ (D.piece i).boundary,
  PairProfile.weight (D.coefficient i) ⟨x.val, hx⟩ <
    2 * pieceDegree (D.piece i).edges x.val}

def protectedHubs : Set (Hubs G) := {x | (D.automatic x).Infinite}

private theorem piece_in_finite (i : ι) :
    ((D.piece i).verts : Set V) ⊆ {x | (G.neighborSet x).Infinite}ᶜ :=
  fun x hx hInf => hInf ((D.piece i).finite_degree x hx)

private theorem finite_pieces_meeting {S : Set V} (hS : S.Finite) :
    {i | ∃ w ∈ S, w ∈ (D.piece i).verts}.Finite := by
  have hf : ∀ w : V, {i | w ∈ (D.piece i).verts}.Subsingleton := by
    intro w i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp (D.disjoint hij) hi hj
  exact (hS.biUnion (fun w _ => (hf w).finite)).subset
    (fun i ⟨w, hw, hwi⟩ => Set.mem_iUnion₂.mpr ⟨w, hw, hwi⟩)

private theorem automatic_forces (x : Hubs G) (i : ι) (hi : i ∈ D.automatic x)
    (c : V → Bool) (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c) :
    ∃ w ∈ (D.piece i).verts, G.Adj x.val w ∧ c w ≠ c x.val := by
  obtain ⟨hx, hslack⟩ := hi
  exact (D.piece i).opponent_of_slack _ c (D.piece_in_finite i) hc
    (fun v => c v.val) (fun _ => rfl) (D.constant i) (D.coefficient i)
    (D.representation i) ⟨x.val, hx⟩ hslack

/-- A hub has infinitely many direct hub neighbours or infinitely many selected
finite pieces incident with it. -/
def SupportedAt (x : Hubs G) : Prop :=
  (G.neighborSet x.val ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    {i | x.val ∈ (D.piece i).boundary}.Infinite

private theorem auxiliary_degree (x : Hubs G) (hx : x ∉ D.protectedHubs)
    (hsupport : D.SupportedAt x) : {e | D.auxiliary.Incident x e}.Infinite := by
  classical
  intro hfin
  have hAuto : (D.automatic x).Finite := Set.not_infinite.mp hx
  let incident : Set D.Edge := {e | D.auxiliary.Incident x e}
  let sources : Set ι := {i | some i ∈ D.source '' incident}
  have hSource : sources.Finite :=
    (hfin.image D.source).preimage (fun _ _ _ _ h => Option.some.inj h)
  let J : Set ι := D.automatic x ∪ sources
  have hJ : J.Finite := hAuto.union hSource
  let H : Set V :=
    (fun e : D.Edge => (D.auxiliary.left e).val) '' incident ∪
      (fun e : D.Edge => (D.auxiliary.right e).val) '' incident
  have hH : H.Finite :=
    (hfin.image (fun e => (D.auxiliary.left e).val)).union
      (hfin.image (fun e => (D.auxiliary.right e).val))
  rcases hsupport with hHub | hPiece
  · apply hHub (hH.subset ?_)
    intro w hw
    let e : D.Edge := Sum.inl ⟨(x, ⟨w, hw.2⟩), hw.1⟩
    exact Or.inr ⟨e, Or.inl rfl, rfl⟩
  · apply hPiece (hJ.subset ?_)
    intro i hxB
    let v : (D.piece i).boundary := ⟨x.val, hxB⟩
    by_cases hslack : PairProfile.weight (D.coefficient i) v <
        2 * pieceDegree (D.piece i).edges x.val
    · exact Or.inl ⟨hxB, hslack⟩
    · obtain ⟨u, hvu, hne⟩ := (D.piece i).exists_interaction_of_not_slack
        (D.constant i) (D.coefficient i) (D.representation i) v hslack
      let e : D.Edge := Sum.inr ⟨i, ⟨(v, u), hvu, hne⟩⟩
      have he : D.auxiliary.Incident x e := Or.inl rfl
      exact Or.inr ⟨e, he, rfl⟩

private theorem favoured_of_signed (a : ℤ) (ha : a ≠ 0) (x y : Bool)
    (h : x = SignedSelection.twist y (decide (0 < a))) :
    PairProfile.Favoured a x y := by
  by_cases hp : 0 < a
  · refine Or.inl ⟨hp, ?_⟩
    cases x <;> cases y <;> simp_all [SignedSelection.twist]
  · have hn : a < 0 := by omega
    refine Or.inr ⟨hn, ?_⟩
    simpa only [hp, decide_false, SignedSelection.twist, Bool.false_eq_true, if_false] using h

private theorem component_forces (x : Hubs G) (h : Hubs G → Bool) (c : V → Bool)
    (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c)
    (hmatch : ∀ y : Hubs G, c y.val = h y) (e : D.ComponentEdge)
    (hi : D.auxiliary.Incident x (Sum.inr e))
    (hs : D.auxiliary.Satisfied h (Sum.inr e)) :
    ∃ w ∈ (D.piece e.1).verts, G.Adj x.val w ∧ c w ≠ c x.val := by
  let i := e.1
  let u := e.2.val.1
  let v := e.2.val.2
  change h (D.hubOfBoundary i u) =
    SignedSelection.twist (h (D.hubOfBoundary i v)) (decide (0 < D.coefficient i u v)) at hs
  rw [← hmatch (D.hubOfBoundary i u), ← hmatch (D.hubOfBoundary i v)] at hs
  have hf := favoured_of_signed (D.coefficient i u v) e.2.property.2
    (c u.val) (c v.val) hs
  have hrev : PairProfile.Favoured (D.coefficient i v u) (c v.val) (c u.val) := by
    rw [(D.representation i).1 v u]
    exact hf.elim (fun h => Or.inl ⟨h.1, h.2.symm⟩) (fun h => Or.inr ⟨h.1, h.2.symm⟩)
  have hforce : ∀ z t : (D.piece i).boundary,
      PairProfile.Favoured (D.coefficient i z t) (c z.val) (c t.val) →
      ∃ w ∈ (D.piece i).verts, G.Adj z.val w ∧ c w ≠ c z.val :=
    fun z t hf => (D.piece i).opponent_of_favoured _ c (D.piece_in_finite i) hc
      (fun y => c y.val) (fun _ => rfl) (D.constant i) (D.coefficient i)
      (D.representation i) z t hf
  change D.hubOfBoundary i u = x ∨ D.hubOfBoundary i v = x at hi
  rcases hi with hu | hv
  · obtain ⟨w, hw, hadj, hne⟩ := hforce u v hf
    exact ⟨w, hw, (congrArg (Subtype.val : Hubs G → V) hu) ▸ hadj,
      (congrArg (Subtype.val : Hubs G → V) hu) ▸ hne⟩
  · obtain ⟨w, hw, hadj, hne⟩ := hforce v u hrev
    exact ⟨w, hw, (congrArg (Subtype.val : Hubs G → V) hv) ▸ hadj,
      (congrArg (Subtype.val : Hubs G → V) hv) ▸ hne⟩

private theorem direct_forces (x : Hubs G) (h : Hubs G → Bool) (c : V → Bool)
    (hmatch : ∀ y : Hubs G, c y.val = h y) (e : D.DirectEdge)
    (hi : D.auxiliary.Incident x (Sum.inl e))
    (hs : D.auxiliary.Satisfied h (Sum.inl e)) :
    (e.val.1 = x ∧ e.val.2.val ∈ oppositeSet G c x.val) ∨
      (e.val.2 = x ∧ e.val.1.val ∈ oppositeSet G c x.val) := by
  change h e.val.1 = SignedSelection.twist (h e.val.2) true at hs
  have hne : c e.val.1.val ≠ c e.val.2.val := by
    rw [hmatch e.val.1, hmatch e.val.2]
    cases h₁ : h e.val.1 <;> cases h₂ : h e.val.2 <;>
      simp_all [SignedSelection.twist]
  change e.val.1 = x ∨ e.val.2 = x at hi
  rcases hi with rfl | rfl
  · exact Or.inl ⟨rfl, e.property, hne.symm⟩
  · exact Or.inr ⟨rfl, e.property.symm, hne⟩

private theorem satisfied_finite (x : Hubs G) (h : Hubs G → Bool) (c : V → Bool)
    (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c)
    (hmatch : ∀ y : Hubs G, c y.val = h y)
    (hO : (oppositeSet G c x.val).Finite) :
    {e | D.auxiliary.Incident x e ∧ D.auxiliary.Satisfied h e}.Finite := by
  classical
  let O : Set V := oppositeSet G c x.val
  have hOI : {y : Hubs G | y.val ∈ O}.Finite :=
    hO.preimage (fun _ _ _ _ h => Subtype.ext h)
  let A : Set (Hubs G × Hubs G) :=
    (fun y => (x, y)) '' {y : Hubs G | y.val ∈ O} ∪
      (fun y => (y, x)) '' {y : Hubs G | y.val ∈ O}
  have hA : A.Finite :=
    (hOI.image (fun y => (x, y))).union (hOI.image (fun y => (y, x)))
  have hD : {e : D.DirectEdge | e.val ∈ A}.Finite :=
    hA.preimage (fun _ _ _ _ h => Subtype.ext h)
  let J : Set ι := {i | ∃ w ∈ O, w ∈ (D.piece i).verts}
  have hJ : J.Finite := D.finite_pieces_meeting hO
  have hT : ((Sum.inl : D.DirectEdge → D.Edge) '' {e : D.DirectEdge | e.val ∈ A} ∪
      ⋃ i ∈ J, Set.range (fun p : D.PiecePair i =>
        (Sum.inr ⟨i, p⟩ : D.Edge))).Finite :=
    (hD.image Sum.inl).union (hJ.biUnion fun i _ =>
      Set.finite_range (fun p : D.PiecePair i => (Sum.inr ⟨i, p⟩ : D.Edge)))
  refine hT.subset ?_
  rintro (e | e) ⟨hi, hs⟩
  · apply Or.inl
    refine ⟨e, ?_, rfl⟩
    rcases D.direct_forces x h c hmatch e hi hs with ⟨hL, hy⟩ | ⟨hR, hy⟩
    · exact Or.inl ⟨e.val.2, hy, Prod.ext hL.symm rfl⟩
    · exact Or.inr ⟨e.val.1, hy, Prod.ext rfl hR.symm⟩
  · obtain ⟨w, hw, hadj, hne⟩ := D.component_forces x h c hc hmatch e hi hs
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e.1, ⟨w, ⟨hadj, hne⟩, hw⟩, e.2, rfl⟩)

/-- A robust hub reservoir may keep its colours while the remaining hubs are
supported by selected pair-profile witnesses. -/
theorem extend_robust [Countable V] (S : Set V) (q : V → Bool)
    (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (hsupport : ∀ x : Hubs G, x.val ∉ S → D.SupportedAt x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' := by
  classical
  let P : Set (Hubs G) := {x | x.val ∈ S} ∪ D.protectedHubs
  obtain ⟨h, hfix, hh⟩ := D.auxiliary.exists_infinitely_satisfied_extension
    P (fun x => q x.val) (fun x hx => D.auxiliary_degree x
      (fun ha => hx (Or.inr ha)) (hsupport x (fun hs => hx (Or.inl hs))))
  let q' : V → Bool := fun x =>
    if hx : (G.neighborSet x).Infinite then h ⟨x, hx⟩ else q x
  have hq'S : Set.EqOn q' q S := fun x hx =>
    (dif_pos (hS hx)).trans (hfix (Or.inl hx))
  refine ⟨q', hq'S, ?_⟩
  intro c hc hcq v hv
  by_cases hvS : v ∈ S
  · exact hq c hc (fun y hy => (hcq (hS hy)).trans (hq'S hy)) v hvS
  · intro hO
    let x : Hubs G := ⟨v, hv⟩
    have hmatch : ∀ y : Hubs G, c y.val = h y := fun y =>
      (hcq y.property).trans (dif_pos y.property)
    by_cases hx : x ∈ D.protectedHubs
    · apply hx
      apply (D.finite_pieces_meeting hO).subset
      intro i hi
      obtain ⟨w, hw, hadj, hne⟩ := D.automatic_forces x i hi c hc
      exact ⟨w, ⟨hadj, hne⟩, hw⟩
    · exact hh x (fun hp => hp.elim hvS hx) (D.satisfied_finite x h c hc hmatch hO)

/-- Every strongly maximal completion of the selected hub colours is unfriendly
at every hub. Witnesses are certified uniformly over all such completions. -/
theorem exists_robust (D : PairWitnessSystem G ι) [Countable V]
    (hsupport : ∀ x : Hubs G, D.SupportedAt x) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  obtain ⟨q, _, hq⟩ := D.extend_robust ∅ (fun _ => false) (Set.empty_subset _)
    (fun _ _ _ _ hv => hv.elim) (fun x _ => hsupport x)
  exact ⟨q, hq⟩

/-- Recurrent finite boundaries of arbitrary size may supply the hubs not
supported by selected pair-profile pieces. -/
theorem exists_robust_of_recurrent_or_supported [Countable V]
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ D.SupportedAt x) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  classical
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite}
  have hs : ∀ x : Hubs G, x.val ∉ S → D.SupportedAt x := by
    intro x hxS
    rcases h x with ⟨B, hxB, hBI, hB⟩ | hs
    · have hb := RecurrentBlock.relativize G ∅ S (Set.empty_subset S) B hB
      obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob (B.filter (· ∉ S))
        (fun y hy => (Finset.mem_filter.mp hy).2)
        (fun y hy => hBI y (Finset.mem_filter.mp hy).1)
        (fun y hy hInf => hInf hy) hb
      exact (hxS (hmax _ q'
        (Set.union_subset hSH (fun y hy => hBI y (Finset.mem_filter.mp hy).1))
        hq' Set.subset_union_left hq'q (Or.inr (Finset.mem_filter.mpr ⟨hxB, hxS⟩)))).elim
    · exact hs
  obtain ⟨q', _, hq'⟩ := D.extend_robust S q hSH hrob hs
  exact ⟨q', hq'⟩

/-- The robust hub assignment gives a global unfriendly partition. -/
theorem exists_unfriendly (D : PairWitnessSystem G ι) [Countable V]
    (hsupport : ∀ x : Hubs G, D.SupportedAt x) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨q, hq⟩ := D.exists_robust hsupport
  exact exists_unfriendly_of_robust_cofinite G {x | (G.neighborSet x).Infinite} q
    Set.Subset.rfl hq (by simp)

end PairWitnessSystem
end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyPairAssembly.lean. -/
/-!
# Covering pair-profile decompositions

A decomposition covering every finite-degree vertex supplies the support
hypothesis of `PairWitnessSystem`. Its previous public selection interfaces
remain available through that witness system.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

open Energy

variable {V : Type u} {ι : Type v}

/-- A covering collection of disjoint closed finite pieces with pair profiles. -/
structure PairDecomposition (G : SimpleGraph V) (ι : Type v) where
  piece : ι → Energy.FinitePiece G
  disjoint : Pairwise (Function.onFun Disjoint (fun i => (piece i).verts))
  cover : ∀ x, (G.neighborSet x).Finite → ∃ i, x ∈ (piece i).verts
  boundary_hub : ∀ i, ∀ x : (piece i).boundary, (G.neighborSet x.val).Infinite
  constant : ι → ℤ
  coefficient : (i : ι) → (piece i).boundary → (piece i).boundary → ℤ
  representation : ∀ i, PairProfile.Represents (piece i).profile (constant i) (coefficient i)


namespace PairDecomposition

variable {G : SimpleGraph V} (D : PairDecomposition G ι)

/-- Forget coverage while retaining the selected pieces and their certificates. -/
def toPairWitnessSystem : PairWitnessSystem G ι where
  piece := D.piece
  disjoint := D.disjoint
  boundary_hub := D.boundary_hub
  constant := D.constant
  coefficient := D.coefficient
  representation := D.representation

abbrev DirectEdge (D : PairDecomposition G ι) := D.toPairWitnessSystem.DirectEdge
abbrev PiecePair (i : ι) := D.toPairWitnessSystem.PiecePair i
abbrev ComponentEdge := D.toPairWitnessSystem.ComponentEdge
abbrev Edge := D.toPairWitnessSystem.Edge
abbrev hubOfBoundary (i : ι) (x : (D.piece i).boundary) :=
  D.toPairWitnessSystem.hubOfBoundary i x
noncomputable abbrev auxiliary := D.toPairWitnessSystem.auxiliary
abbrev source := D.toPairWitnessSystem.source
abbrev automatic := D.toPairWitnessSystem.automatic
abbrev protectedHubs := D.toPairWitnessSystem.protectedHubs

/-- Coverage and infinite original degree force infinitely many direct hub
neighbours or infinitely many incident selected pieces. -/
theorem supportedAt (x : Hubs G) : D.toPairWitnessSystem.SupportedAt x := by
  classical
  by_cases hHub : (G.neighborSet x.val ∩ {y | (G.neighborSet y).Infinite}).Infinite
  · exact Or.inl hHub
  · refine Or.inr ?_
    intro hPiece
    have hHF := Set.not_infinite.mp hHub
    have hP : (⋃ i ∈ {i | x.val ∈ (D.piece i).boundary}, ((D.piece i).verts : Set V)).Finite :=
      hPiece.biUnion (fun i _ => (D.piece i).verts.finite_toSet)
    apply x.property ((hHF.union hP).subset ?_)
    intro w hw
    by_cases hwI : (G.neighborSet w).Infinite
    · exact Or.inl ⟨hw, hwI⟩
    · obtain ⟨i, hwi⟩ := D.cover w (Set.not_infinite.mp hwI)
      have hxC : x.val ∉ (D.piece i).verts :=
        fun h => x.property ((D.piece i).finite_degree x.val h)
      have hxB := (D.piece i).mem_boundary_of_adj hxC hwi hw
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hxB, hwi⟩)

/-- Every strongly maximal completion of the selected hub colours is unfriendly
at every hub. -/
theorem exists_robust (D : PairDecomposition G ι) [Countable V] :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q :=
  D.toPairWitnessSystem.exists_robust D.supportedAt

/-- The robust hub assignment gives a global unfriendly partition. -/
theorem exists_unfriendly (D : PairDecomposition G ι) [Countable V] :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x :=
  D.toPairWitnessSystem.exists_unfriendly D.supportedAt

end PairDecomposition
end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyThreeBoundaryGraph.lean. -/
/-!
# Finite components with at most three boundary hubs

Every finite-degree component is finite, but there is no uniform bound on its
size. Full hub boundaries vary freely. The resulting hub assignment makes
every strongly maximal completion unfriendly, and such completions exist.
This is a special case, not a proof of the unrestricted countable conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.ThreeBoundaryGraph

open Energy

variable {V : Type u}

abbrev finiteGraph (G : SimpleGraph V) := G.induce {x | (G.neighborSet x).Finite}

abbrev Component (G : SimpleGraph V) := (finiteGraph G).ConnectedComponent

def hubBoundary (G : SimpleGraph V) (C : Component G) : Set V :=
  {x | (G.neighborSet x).Infinite ∧ ∃ y ∈ C.supp, G.Adj x y.val}

noncomputable def piece (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite) :
    FinitePiece G where
  verts := (hC.image Subtype.val).toFinset
  finite_degree := by
    intro x hx
    obtain ⟨y, _, hxy⟩ := (hC.image Subtype.val).mem_toFinset.mp hx
    exact hxy ▸ y.property

theorem piece_mem (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite) (x : V) :
    x ∈ (piece G C hC).verts ↔ ∃ y ∈ C.supp, y.val = x :=
  (hC.image Subtype.val).mem_toFinset

private theorem boundary_hub (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite)
    (x : (piece G C hC).boundary) : (G.neighborSet x.val).Infinite := by
  intro hxF
  obtain ⟨w, hw, hadj⟩ := (piece G C hC).boundary_touch x
  obtain ⟨y, hy, hyw⟩ := (piece_mem G C hC w).mp hw
  have hxy : (finiteGraph G).Adj y ⟨x.val, hxF⟩ :=
    show G.Adj y.val x.val from hyw.symm ▸ hadj.symm
  have hxC := C.mem_supp_of_adj_mem_supp hy hxy
  exact (piece G C hC).boundary_not_mem x.property
    ((piece_mem G C hC x.val).mpr ⟨⟨x.val, hxF⟩, hxC, rfl⟩)

theorem boundary_eq (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite) :
    ((piece G C hC).boundary : Set V) = hubBoundary G C := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · intro hx
    obtain ⟨w, hw, hadj⟩ := (piece G C hC).boundary_touch ⟨x, hx⟩
    obtain ⟨y, hy, hyw⟩ := (piece_mem G C hC w).mp hw
    exact ⟨boundary_hub G C hC ⟨x, hx⟩, y, hy, hyw.symm ▸ hadj⟩
  · rintro ⟨hxI, y, hy, hxy⟩
    have hyC : y.val ∈ (piece G C hC).verts :=
      (piece_mem G C hC y.val).mpr ⟨y, hy, rfl⟩
    have hxC : x ∉ (piece G C hC).verts :=
      fun h => hxI ((piece G C hC).finite_degree x h)
    exact (piece G C hC).mem_boundary_of_adj hxC hyC hxy

private theorem component_disjoint (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) :
    Pairwise (Function.onFun Disjoint (fun C => (piece G C (hfinite C)).verts)) := by
  intro C D hCD
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨y, hy, hyx⟩ := (piece_mem G C (hfinite C) x).mp hxC
  obtain ⟨z, hz, hzx⟩ := (piece_mem G D (hfinite D) x).mp hxD
  have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
  exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex hy (hyz.symm ▸ hz))

private theorem component_cover (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (x : V) (hx : (G.neighborSet x).Finite) :
    ∃ C : Component G, x ∈ (piece G C (hfinite C)).verts := by
  let y : {x : V // (G.neighborSet x).Finite} := ⟨x, hx⟩
  refine ⟨(finiteGraph G).connectedComponentMk y, ?_⟩
  exact (piece_mem G _ _ x).mpr
    ⟨y, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩

private theorem exists_decomposition (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hpair : ∀ C : Component G, ∃ K a,
      PairProfile.Represents (piece G C (hfinite C)).profile K a) :
    Nonempty (PairDecomposition G (Component G)) := by
  classical
  choose K a ha using hpair
  exact ⟨{
    piece := fun C => piece G C (hfinite C)
    disjoint := component_disjoint G hfinite
    cover := component_cover G hfinite
    boundary_hub := fun C => boundary_hub G C (hfinite C)
    constant := K
    coefficient := a
    representation := ha
  }⟩

/-- Generalization to components with an integer-scaled pair representation. -/
theorem exists_robust_of_pair_components [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hpair : ∀ C : Component G, ∃ K a,
      PairProfile.Represents (piece G C (hfinite C)).profile K a) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  obtain ⟨D⟩ := exists_decomposition G hfinite hpair
  exact D.exists_robust

/-- Finite components with at most three distinct boundary hubs allow robust
hub colours, uniformly over every strongly maximal completion. -/
theorem exists_robust_of_three_boundary [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  apply exists_robust_of_pair_components G hfinite
  intro C
  apply (piece G C (hfinite C)).exists_pair_representation
  have h := hboundary C
  rw [← boundary_eq G C (hfinite C)] at h
  simpa only [Set.ncard_coe_finset] using h

private theorem completion_unfriendly [Countable V] (G : SimpleGraph V)
    (q : V → Bool)
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q)
    (c : V → Bool) (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c)
    (heq : Set.EqOn c q {x | (G.neighborSet x).Infinite}) :
    ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  intro v
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G _ c hc v (fun hInf => hInf hN) hN
  · exact unfriendly_of_infinite_opposite G c v (hq c hc heq v hN)

/-- The precise robust three-boundary theorem: a hub assignment has strongly
maximal completions on the finite-degree vertices, and every such completion
is globally unfriendly. -/
theorem exists_hub_assignment [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust_of_three_boundary G hfinite hboundary
  obtain ⟨c, hfix, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {x | (G.neighborSet x).Infinite} q
  have hF : {x | (G.neighborSet x).Infinite}ᶜ = {x | (G.neighborSet x).Finite} :=
    Set.ext fun _ => Set.not_infinite
  refine ⟨fun x => q x.val, ⟨c, hF ▸ hc, fun x => hfix x.property⟩, ?_⟩
  intro d hd hmatch
  exact completion_unfriendly G q hq d (hF.symm ▸ hd)
    (fun x hx => hmatch ⟨x, hx⟩)

theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨h, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment G hfinite hboundary
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly G hfinite hboundary)

end TenChallenges.Continuation.ThreeBoundaryGraph

/- Inlined from Continuation/UnfriendlyComponentMaximality.lean. -/
/-!
# Strong maximality on finite-degree components

A finite flip of finite-degree vertices splits among the components that it
meets. Its gain is the sum of the gains in those components.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped symmDiff

variable {V : Type u}

/-- Strong maximality on every component of the finite-degree subgraph implies
strong maximality on all finite-degree vertices. -/
theorem strongMaximal_of_components (G : SimpleGraph V) (c : V → Bool)
    (h : ∀ C : ThreeBoundaryGraph.Component G,
      StrongMaximal G (Subtype.val '' C.supp) c) :
    StrongMaximal G {x | (G.neighborSet x).Finite} c := by
  classical
  intro U _
  refine Finset.strongInductionOn U ?_
  intro U ih hU
  by_cases hne : U.Nonempty
  case neg => simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  obtain ⟨a, ha⟩ := hne
  let aF : {x : V // (G.neighborSet x).Finite} := ⟨a, hU a ha⟩
  let C : ThreeBoundaryGraph.Component G := (ThreeBoundaryGraph.finiteGraph G).connectedComponentMk aF
  let B : Set V := Subtype.val '' C.supp
  let S := U.filter (· ∈ B)
  let T := U \ S
  have hSU : S ⊆ U := Finset.filter_subset ..
  have hTU : T ⊆ U := Finset.sdiff_subset
  have hSB : (S : Set V) ⊆ B := fun _ hx => (Finset.mem_filter.mp hx).2
  have haS : a ∈ S := Finset.mem_filter.mpr
    ⟨ha, aF, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩
  have hTF : ∀ x ∈ T, (G.neighborSet x).Finite := fun x hx => hU x (hTU hx)
  have hSF : ∀ x ∈ S, (G.neighborSet x).Finite := fun x hx => hU x (hSU hx)
  have hSm := h C S hSB hSF
  have hTm := ih T (Finset.sdiff_ssubset hSU ⟨a, haS⟩) hTF
  have hTnot (y : V) (hy : y ∈ T) : y ∉ B :=
    fun hyB => (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨hTU hy, hyB⟩)
  have hnonadj {x y : V} (hx : x ∈ S) (hy : y ∈ T) (hadj : G.Adj x y) : False := by
    obtain ⟨xF, hxF, rfl⟩ := hSB hx
    let yF : {v : V // (G.neighborSet v).Finite} := ⟨y, hTF y hy⟩
    exact hTnot y hy ⟨yF, C.mem_supp_of_adj_mem_supp hxF
      (show (ThreeBoundaryGraph.finiteGraph G).Adj xF yF from hadj), rfl⟩
  have hdisj : Disjoint S T :=
    Finset.disjoint_left.mpr fun x hx hy => hTnot x hy (hSB hx)
  have hcong : gain G (flip c S) T = gain G c T :=
    gain_congr_of_incident_eq G (flip c S) c T fun e he =>
      he.2.elim
        (fun hx => ⟨if_neg (fun h => hTnot e.1 hx (hSB h)),
          if_neg (fun h => hnonadj h hx he.1.symm)⟩)
        (fun hy => ⟨if_neg (fun h => hnonadj h hy he.1),
          if_neg (fun h => hTnot e.2 hy (hSB h))⟩)
  have hsplit : S ∆ T = U := (Finset.symmDiff_eq_union hdisj).trans (Finset.union_sdiff_of_subset hSU)
  rw [← hsplit, gain_symmDiff G c S T hSF hTF, hcong]
  exact add_nonpos hSm hTm

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyComponentGluing.lean. -/
/-!
# Gluing strongly maximal component colourings

Colour each finite-degree component by its own interior pattern and keep the
prescribed hub colours. If the component colourings agree with those colours
on their boundaries, all incident cut gains stay the same after gluing.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.ComponentGluing

open Energy ThreeBoundaryGraph

variable {V : Type u} {G : SimpleGraph V}

/-- The vertices of a component, regarded as vertices of the whole graph. -/
def interior (C : Component G) : Set V := Subtype.val '' C.supp

theorem not_mem_interior_of_hub (C : Component G) {x : V}
    (hx : (G.neighborSet x).Infinite) : x ∉ interior C :=
  fun ⟨y, _, h⟩ => hx (h ▸ y.property)

/-- A neighbour outside a finite-degree component is a hub. -/
theorem hub_of_adj_not_mem_interior (C : Component G) {x y : V}
    (hx : x ∈ interior C) (ha : G.Adj x y) (hy : y ∉ interior C) :
    (G.neighborSet y).Infinite := by
  intro hyf
  obtain ⟨z, hz, rfl⟩ := hx
  let w : {v : V // (G.neighborSet v).Finite} := ⟨y, hyf⟩
  exact hy ⟨w, C.mem_supp_of_adj_mem_supp hz (show (finiteGraph G).Adj z w from ha), rfl⟩

/-- Strongly maximal colourings of individual components glue when their
boundary colours agree with the prescribed colours of the hubs. -/
theorem exists_strongMaximal_glued (G : SimpleGraph V) (q : V → Bool)
    (d : Component G → V → Bool)
    (hadj : ∀ (C : Component G) (x : V), x ∉ interior C →
      (∃ y ∈ interior C, G.Adj y x) → d C x = q x)
    (hmax : ∀ C : Component G, StrongMaximal G (interior C) (d C)) :
    ∃ c : V → Bool, Set.EqOn c q {v | (G.neighborSet v).Infinite} ∧
      (∀ C : Component G, Set.EqOn c (d C) (interior C)) ∧
      StrongMaximal G {v | (G.neighborSet v).Finite} c := by
  classical
  let c (x : V) : Bool := if hx : (G.neighborSet x).Finite then
    d ((finiteGraph G).connectedComponentMk ⟨x, hx⟩) x else q x
  have hhub : Set.EqOn c q {v | (G.neighborSet v).Infinite} := fun _ hx => dif_neg hx
  have hcomp (C : Component G) : Set.EqOn c (d C) (interior C) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (dif_pos x.property).trans (congrArg (fun B => d B x.val) ((C.mem_supp_iff x).mp hx))
  have hnear (C : Component G) {x y : V} (hx : x ∈ interior C) (hxy : G.Adj x y) :
      c y = d C y := by
    by_cases hy : y ∈ interior C
    · exact hcomp C hy
    · exact (hhub (hub_of_adj_not_mem_interior C hx hxy hy)).trans (hadj C y hy ⟨x, hx, hxy⟩).symm
  refine ⟨c, hhub, hcomp, strongMaximal_of_components G c ?_⟩
  intro C S hS hSf
  have heq : gain G c S = gain G (d C) S :=
    gain_congr_of_incident_eq G c (d C) S fun e he =>
      he.2.elim (fun hx => ⟨hcomp C (hS hx), hnear C (hS hx) he.1⟩)
        (fun hy => ⟨hnear C (hS hy) he.1.symm, hcomp C (hS hy)⟩)
  exact heq.le.trans (hmax C S hS hSf)

end TenChallenges.Continuation.ComponentGluing

/- Inlined from Continuation/UnfriendlyLightInterfaceRepair.lean. -/
/-!
# Repair after changing the finite part of an interface

Only changed exterior vertices adjacent to the region affect its cuts. If
those edges are finite, colours inside the region need only change finitely.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

variable {V : Type u}

/-- An infinite opposite neighbourhood inside a region survives finitely many
colour changes there if the centre keeps its colour. -/
theorem infinite_opposite_inside_of_finite_difference (G : SimpleGraph V) (A : Set V)
    {c d : V → Bool} (x : V) (hcolour : c x = d x)
    (hfinite : {y | y ∈ A ∧ c y ≠ d y}.Finite) (h : (oppositeSet G c x ∩ A).Infinite) :
    (oppositeSet G d x ∩ A).Infinite := by
  exact (h.sdiff hfinite).mono fun y hy =>
    let he : c y = d y := Classical.byContradiction (fun hn => hy.2 ⟨hy.1.2, hn⟩)
    ⟨⟨hy.1.1.1, fun e => hy.1.1.2 (he.trans (e.trans hcolour.symm))⟩, hy.1.2⟩

/-- Restore strong maximality after changing the light part of a boundary.
The prescribed colouring `q` may differ from `q₀` on `T`. The local colouring
`d` already matches `q` on `Q ⊆ T` and the reference away from the region and
`Q`. Finitely many edges join the region to `T \ Q`. -/
theorem reconcile_finite_interface (G : SimpleGraph V) (A T Q : Set V) (q₀ q d : V → Bool)
    (hQt : Q ⊆ T) (hTA : Disjoint T A) (hA : ∀ x ∈ A, (G.neighborSet x).Finite)
    (hdMax : StrongMaximal G A d) (hdq : Set.EqOn d q Q)
    (hdRef : Set.EqOn d q₀ (A ∪ Q)ᶜ) (hq : Set.EqOn q q₀ Tᶜ)
    (hfinite : {e : V × V | e.1 ∈ T \ Q ∧ e.2 ∈ A ∧ G.Adj e.1 e.2}.Finite) :
    ∃ c, StrongMaximal G A c ∧
      (∀ x, x ∉ A → (∃ y ∈ A, G.Adj y x) → c x = q x) ∧
      Set.EqOn c d Q ∧ {x | c x ≠ d x}.Finite := by
  classical
  let E := {e : V × V | e.1 ∈ T \ Q ∧ e.2 ∈ A ∧ G.Adj e.1 e.2}
  have hE : E.Finite := hfinite
  let B := (hE.image Prod.fst).toFinset
  have hsub : (B : Set V) ⊆ T \ Q := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (hE.image Prod.fst).mem_toFinset.mp hx
    exact he.1
  have hB (x : V) (hx : x ∈ B) : x ∉ A ∧ (G.neighborSet x ∩ A).Finite := by
    have hxt := hsub hx
    refine ⟨Set.disjoint_left.mp hTA hxt.1, (hE.image Prod.snd).subset ?_⟩
    intro y hy
    exact ⟨(x, y), ⟨hxt, hy.2, hy.1⟩, rfl⟩
  obtain ⟨c, hcB, hfix, hmax, hdiff⟩ :=
    exists_strongMaximal_of_finite_boundary G A d q hA hdMax B hB
  refine ⟨c, hmax, ?_, ?_, hdiff⟩
  · rintro x hxA ⟨y, hy, hyx⟩
    by_cases hxB : x ∈ B
    · exact hcB hxB
    have same : c x = d x := hfix (fun h => h.elim hxA hxB)
    by_cases hxQ : x ∈ Q
    · exact same.trans (hdq hxQ)
    have hxT : x ∉ T := fun h => hxB ((hE.image Prod.fst).mem_toFinset.mpr
      ⟨(x, y), ⟨⟨h, hxQ⟩, hy, hyx.symm⟩, rfl⟩)
    exact same.trans ((hdRef (fun h => h.elim hxA hxQ)).trans (hq hxT).symm)
  intro x hx
  exact hfix (fun h => h.elim (Set.disjoint_left.mp hTA (hQt hx)) (fun hxB => (hsub hxB).2 hx))

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyFiniteBands.lean. -/
/-!
# Finite distance bands in locally finite graphs

Distance balls within a component are finite. A clique lies in the level of
its closest vertex to a fixed root and the next level.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FiniteBands

variable {V : Type u} (R : SimpleGraph V)

/-- A closed distance ball inside the root component of a locally finite graph
has finitely many vertices. -/
theorem finite_dist_ball (hfinite : ∀ x, (R.neighborSet x).Finite) (root : V) (n : ℕ) :
    {x | R.Reachable root x ∧ R.dist root x ≤ n}.Finite := by
  induction n
  case zero =>
    refine (Set.finite_singleton root).subset ?_
    rintro x ⟨hx, hd⟩
    exact (hx.dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hd)).symm
  case succ n ih =>
    let B := {x | R.Reachable root x ∧ R.dist root x ≤ n}
    have hB : B.Finite := ih
    refine (hB.union (hB.biUnion fun y _ => hfinite y)).subset ?_
    rintro x ⟨hx, hd⟩
    obtain ⟨p, hp⟩ := hx.symm.exists_walk_length_eq_dist
    cases p with
    | nil => simp [B]
    | cons hadj p =>
      have hlen : p.length + 1 ≤ n + 1 :=
        (SimpleGraph.Walk.length_cons hadj p).symm.le.trans
          (hp.le.trans ((R.dist_comm (u := x) (v := root)).le.trans hd))
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨_, ⟨⟨p.reverse⟩, ?_⟩, hadj.symm⟩)
      exact (R.dist_le p.reverse).trans
        (p.length_reverse.le.trans (Nat.le_of_succ_le_succ hlen))

/-- Two consecutive distance levels within a component form a finite set. -/
theorem finite_two_levels (hfinite : ∀ x, (R.neighborSet x).Finite) (root : V) (n : ℕ) :
    {x | R.Reachable root x ∧ (R.dist root x = n ∨ R.dist root x = n + 1)}.Finite :=
  (finite_dist_ball R hfinite root (n + 1)).subset fun _ hx =>
    ⟨hx.1, hx.2.elim (fun h => h.le.trans (Nat.le_succ _)) Eq.le⟩

/-- Along an edge, the two distances from any root differ by at most one. -/
theorem dist_le_succ_of_adj (root : V) {x y : V} (hxy : R.Adj x y) :
    R.dist root y ≤ R.dist root x + 1 ∧ R.dist root x ≤ R.dist root y + 1 := by
  refine ⟨?_, ?_⟩
  · simpa only [R.dist_eq_one_iff_adj.mpr hxy] using hxy.reachable.dist_triangle_right root
  · simpa only [R.dist_eq_one_iff_adj.mpr hxy.symm] using hxy.symm.reachable.dist_triangle_right root

/-- A nonempty clique lies in two consecutive levels.
The lower level is attained. -/
theorem clique_in_two_levels (root : V) (A : Set V) (hne : A.Nonempty)
    (hclique : A.Pairwise R.Adj) :
    ∃ n : ℕ, (∃ x ∈ A, R.dist root x = n) ∧
      ∀ x ∈ A, R.dist root x = n ∨ R.dist root x = n + 1 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hlevels : ∃ n, ∃ x ∈ A, R.dist root x = n := ⟨R.dist root x₀, x₀, hx₀, rfl⟩
  obtain ⟨a, ha, hlevel⟩ := Nat.find_spec hlevels
  refine ⟨Nat.find hlevels, ⟨a, ha, hlevel⟩, fun x hx => ?_⟩
  have hlo : Nat.find hlevels ≤ R.dist root x := Nat.find_min' hlevels ⟨x, hx, rfl⟩
  have hhi : R.dist root x ≤ Nat.find hlevels + 1 := by
    by_cases hax : a = x
    · exact (hax ▸ hlevel).le.trans (Nat.le_succ _)
    · exact hlevel ▸ (dist_le_succ_of_adj R root (hclique ha hx hax)).1
  exact (eq_or_lt_of_le hlo).elim (fun h => Or.inl h.symm)
    (fun h => Or.inr (Nat.le_antisymm hhi h))

end TenChallenges.Continuation.FiniteBands

/- Inlined from Continuation/UnfriendlyBandSchedule.lean. -/
/-!
# Scheduling finite bands of a locally finite graph

Order cliques by the parity of their minimum distance from the component root,
then by a countable index. Each vertex takes its colour from its earliest clique.
Within a round an influence stays at the same level. Between rounds it can only
pass from an even level to an adjacent odd level.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.BandSchedule

private theorem exists_bands {X : Type u} {ι : Type v}
    (R : SimpleGraph X) (hloc : ∀ x, (R.neighborSet x).Finite)
    (A : ι → Set X) (hinj : Function.Injective A)
    (hne : ∀ i, (A i).Nonempty) (hclique : ∀ i, (A i).Pairwise R.Adj) :
    ∃ (component : ι → R.ConnectedComponent) (level : ι → ℕ),
      (∀ i, (A i).Finite) ∧
      (∀ c n, {i | component i = c ∧ level i = n}.Finite) ∧
      (∀ i j x, x ∈ A i → x ∈ A j →
        component i = component j ∧ level i ≤ level j + 1 ∧ level j ≤ level i + 1) := by
  choose point hpoint using hne
  choose root hroot using fun c : R.ConnectedComponent => c.nonempty_supp
  let component (i : ι) := R.connectedComponentMk (point i)
  have hcomp (i : ι) (x : X) (hx : x ∈ A i) : R.connectedComponentMk x = component i := by
    by_cases hxp : x = point i
    · exact congrArg R.connectedComponentMk hxp
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (hclique i hx (hpoint i) hxp)
  have hreach (i : ι) (x : X) (hx : x ∈ A i) : R.Reachable (root (component i)) x :=
    SimpleGraph.ConnectedComponent.exact
      ((((component i).mem_supp_iff _).mp (hroot (component i))).trans (hcomp i x hx).symm)
  choose level _ hlevels using fun i => FiniteBands.clique_in_two_levels R
    (root (component i)) (A i) ⟨point i, hpoint i⟩ (hclique i)
  refine ⟨component, level, ?_, ?_, ?_⟩
  · exact fun i => (FiniteBands.finite_two_levels R hloc (root (component i)) (level i)).subset
      fun x hx => ⟨hreach i x hx, hlevels i x hx⟩
  · intro c n
    refine ((FiniteBands.finite_two_levels R hloc (root c) n).powerset.preimage hinj.injOn).subset ?_
    rintro i ⟨hc, hn⟩ x hx
    exact ⟨hc ▸ hreach i x hx, hc ▸ hn ▸ hlevels i x hx⟩
  · intro i j x hi hj
    have hsame : component i = component j := (hcomp i x hi).symm.trans (hcomp j x hj)
    have hleft := hlevels i x hi
    have hright : R.dist (root (component i)) x = level j ∨
        R.dist (root (component i)) x = level j + 1 := hsame.symm ▸ hlevels j x hj
    exact ⟨hsame, by omega, by omega⟩

private theorem exists_order {ι : Type v} [Countable ι] (level : ι → ℕ) :
    ∃ before : ι → ι → Prop, WellFounded before ∧
      (∀ i j, i ≠ j → before i j ∨ before j i) ∧
      (∀ i j, before i j → level i ≤ level j + 1 → level j ≤ level i + 1 →
        BlockOwnership.BandInfluence (level i) (level j)) := by
  obtain ⟨code, hcode⟩ := exists_injective_nat ι
  let rank (i : ι) := (level i % 2, code i)
  let before (i j : ι) := Prod.Lex (· < ·) (· < ·) (rank i) (rank j)
  have hwf : WellFounded before := InvImage.wf rank (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  refine ⟨before, hwf, ?_, ?_⟩
  · intro i j hij
    rcases lt_trichotomy (level i % 2) (level j % 2) with hp | hp | hp
    · exact Or.inl (Prod.lex_def.mpr (Or.inl hp))
    · exact (lt_or_gt_of_ne (fun e => hij (hcode e))).imp
        (fun h => Prod.lex_def.mpr (Or.inr ⟨hp, h⟩))
        (fun h => Prod.lex_def.mpr (Or.inr ⟨hp.symm, h⟩))
    · exact Or.inr (Prod.lex_def.mpr (Or.inl hp))
  · intro i j hbefore hlo hhi
    have hpass : level i % 2 < level j % 2 ∨ level i % 2 = level j % 2 ∧ code i < code j :=
      Prod.lex_def.mp hbefore
    rcases hpass with hp | ⟨hp, _⟩
    · exact Or.inr ⟨by omega, by omega, hlo, hhi⟩
    · exact Or.inl (by omega)

/-- A countable cover by nonempty cliques of a locally finite graph gives a
well-founded network with finite blocks and finite forward influence. -/
theorem exists_network {X : Type u} {ι : Type v} [Countable ι]
    (R : SimpleGraph X) (hloc : ∀ x, (R.neighborSet x).Finite)
    (A : ι → Set X) (hinj : Function.Injective A)
    (hne : ∀ i, (A i).Nonempty) (hclique : ∀ i, (A i).Pairwise R.Adj)
    (hcover : ∀ x, ∃ i, x ∈ A i) :
    ∃ N : BlockAssembly.Network X ι, (∀ x, x ∈ A (N.owner x)) ∧
      (∀ i, {x | N.owner x = i}.Finite) ∧
      (∀ i, (↑(N.parents i) : Set X) = A i \ {x | N.owner x = i}) ∧
      (∀ i, ∃ C : Set ι, C.Finite ∧ i ∈ C ∧ N.ForwardClosed C) := by
  classical
  obtain ⟨component, level, ha, hband, hoverlap⟩ := exists_bands R hloc A hinj hne hclique
  obtain ⟨before, hwf, hcompare, hinfluence⟩ := exists_order level
  obtain ⟨owner, howner, hblock, hearlier⟩ := BlockOwnership.exists_owner A ha hcover before hwf
    (fun i j hij _ _ _ => hcompare i j hij)
  let parentSet (i : ι) : Set X := A i \ {x | owner x = i}
  have hfinite (i : ι) : (parentSet i).Finite := (ha i).subset Set.sdiff_subset
  let N : BlockAssembly.Network X ι :=
    { owner := owner
      parents := fun i => (hfinite i).toFinset
      lt := before
      wf := hwf
      parent_lt := fun i p =>
        let hp : p.val ∈ parentSet i := (hfinite i).mem_toFinset.mp p.property
        hearlier i p.val hp.1 hp.2 }
  refine ⟨N, howner, hblock, fun i => (hfinite i).coe_toFinset, ?_⟩
  intro i
  obtain ⟨C, hC, hi, hclosure⟩ := BlockOwnership.finite_influence_closure component level hband i
  refine ⟨C, hC, hi, fun j p hp => ?_⟩
  have hparent : p.val ∈ parentSet j := (hfinite j).mem_toFinset.mp p.property
  obtain ⟨hc, hlo, hhi⟩ := hoverlap (owner p.val) j p.val (howner p.val) hparent.1
  exact hclosure (owner p.val) hp j hc (hinfluence (owner p.val) j (N.parent_lt j p) hlo hhi)

end TenChallenges.Continuation.BandSchedule

/- Inlined from Continuation/UnfriendlyForcedWitness.lean. -/
/-!
# Forced opponents at boundary vertices of finite pieces

A boundary vertex `v` of a finite piece is *forced* by a boundary colouring `b`
when recolouring `v` does not raise the optimized score by the whole incidence
count of `v`. The profile Lipschitz bound makes this the exact criterion: `v`
is forced precisely when every maximizing interior colouring gives `v` an
opponent inside the piece. Only the direction used later is proved here.

Three consequences need no assumption on the size of the boundary and no pair
representation:

* a vertex that is not forced becomes forced after its own colour is reversed;
* that reversal keeps every other forced boundary vertex forced;
* for each colour of `v`, either some colouring of the other free boundary
  vertices forces `v`, or the opposite colour forces `v` under every colouring
  of them.

Pair representations are a sufficient condition: positive slack or one favoured
interaction forces the vertex.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy.FinitePiece

open scoped BigOperators

variable {V : Type u} {G : SimpleGraph V} (P : FinitePiece G)

/-- Recolouring the boundary vertex does not gain its entire incidence count. -/
def Forced (b : P.boundary → Bool) (v : P.boundary) : Prop :=
  P.profile (PairProfile.toggle b v) < P.profile b + pieceDegree P.edges v.val

/-- `x` lies on the boundary and is forced by the boundary colours of `c`. -/
def ForcedAt (c : V → Bool) (x : V) : Prop :=
  ∃ hx : x ∈ P.boundary, P.Forced (fun u => c u.val) ⟨x, hx⟩

/-- `x` is forced under every colouring that agrees with `q` on `T`. -/
def UniversalAt (T : Set V) (q : V → Bool) (x : V) : Prop :=
  ∀ c : V → Bool, Set.EqOn c q T → P.ForcedAt c x

/-- Being forced depends only on the colours of the boundary. -/
theorem forcedAt_congr (c c' : V → Bool) (h : Set.EqOn c c' (P.boundary : Set V)) (x : V)
    (hf : P.ForcedAt c x) : P.ForcedAt c' x := by
  obtain ⟨hx, hf⟩ := hf
  have heq : (fun u : P.boundary => c u.val) = fun u => c' u.val :=
    funext fun u => h u.property
  exact ⟨hx, heq ▸ hf⟩

theorem universalAt_mono {T T' : Set V} {q q' : V → Bool} (hT : T ⊆ T')
    (hq : Set.EqOn q' q T) (x : V) (h : P.UniversalAt T q x) : P.UniversalAt T' q' x :=
  fun c hc => h c fun _ hy => (hc (hT hy)).trans (hq hy)

/-- A forced boundary vertex has an opponent inside the piece in every colouring that
is strongly maximal on the piece. -/
theorem opponent_of_forcedAt (M : Set V) (c : V → Bool) (hPM : (P.verts : Set V) ⊆ M)
    (hc : StrongMaximal G M c) (x : V) (hf : P.ForcedAt c x) :
    ∃ w ∈ P.verts, G.Adj x w ∧ c w ≠ c x := by
  obtain ⟨hx, hf⟩ := hf
  have hresp : pieceDegree P.edges x + P.profile (fun u => c u.val) -
      P.profile (PairProfile.toggle (fun u => c u.val) ⟨x, hx⟩) ≤
        2 * pieceOpponents P.edges c x :=
    P.profile_response (fun u => c u.val) c (fun _ => rfl)
      (P.eq_profile_of_strongMaximal M c hPM hc (fun u => c u.val) (fun _ => rfl)) ⟨x, hx⟩
  have hf' : P.profile (PairProfile.toggle (fun u => c u.val) ⟨x, hx⟩) <
      P.profile (fun u => c u.val) + pieceDegree P.edges x := hf
  have hpos : 0 < pieceOpponents P.edges c x := by omega
  exact P.exists_opponent_of_pos c ⟨x, hx⟩ hpos

private theorem toggle_toggle (b : P.boundary → Bool) (v : P.boundary) :
    PairProfile.toggle (PairProfile.toggle b v) v = b := by
  classical
  funext u
  simp [PairProfile.toggle]

open Classical in
private theorem restrict_update (c : V → Bool) (x : V) (hx : x ∈ P.boundary) :
    (fun u : P.boundary => Function.update c x (!c x) u.val) =
      PairProfile.toggle (fun u : P.boundary => c u.val) ⟨x, hx⟩ := by
  funext u
  by_cases hu : u = ⟨x, hx⟩
  · subst hu
    simp [PairProfile.toggle]
  · have hval : u.val ≠ x := fun h => hu (Subtype.ext h)
    simp only [PairProfile.toggle, Function.update, dif_neg hval, dif_neg hu]

open Classical in
/-- A boundary vertex that is not forced becomes forced when its own colour is reversed. -/
theorem forcedAt_update_of_not (c : V → Bool) (x : V) (hx : x ∈ P.boundary)
    (h : ¬ P.ForcedAt c x) : P.ForcedAt (Function.update c x (!c x)) x := by
  refine ⟨hx, ?_⟩
  have hn : ¬ P.Forced (fun u => c u.val) ⟨x, hx⟩ := fun hf => h ⟨hx, hf⟩
  have hd := P.degree_pos ⟨x, hx⟩
  rw [P.restrict_update c x hx]
  unfold Forced at hn ⊢
  rw [P.toggle_toggle]
  omega

private theorem toggle_comm (b : P.boundary → Bool) (v u : P.boundary) (huv : u ≠ v) :
    PairProfile.toggle (PairProfile.toggle b v) u =
      PairProfile.toggle (PairProfile.toggle b u) v := by
  classical
  funext y
  by_cases hyu : y = u
  · subst hyu
    simp only [PairProfile.toggle, Function.update, dif_neg huv, dif_pos]
  · by_cases hyv : y = v
    · subst hyv
      simp only [PairProfile.toggle, Function.update, dif_neg hyu, dif_pos]
    · simp only [PairProfile.toggle, Function.update, dif_neg hyu, dif_neg hyv]

open Classical in
/-- Reversing the colour of a boundary vertex that is not forced keeps every other
forced boundary vertex forced. -/
theorem forcedAt_update_of_forcedAt (c : V → Bool) (x w : V) (hwx : w ≠ x)
    (hx : x ∈ P.boundary) (hnx : ¬ P.ForcedAt c x) (hw : P.ForcedAt c w) :
    P.ForcedAt (Function.update c x (!c x)) w := by
  obtain ⟨hwB, hwf⟩ := hw
  refine ⟨hwB, ?_⟩
  have hnf : ¬ P.Forced (fun u => c u.val) ⟨x, hx⟩ := fun h => hnx ⟨hx, h⟩
  have huv : (⟨w, hwB⟩ : P.boundary) ≠ ⟨x, hx⟩ := fun h => hwx (congrArg Subtype.val h)
  have hlip := P.profile_flip_bound
    (PairProfile.toggle (PairProfile.toggle (fun u => c u.val) ⟨w, hwB⟩) ⟨x, hx⟩) ⟨x, hx⟩
  rw [P.toggle_toggle] at hlip
  rw [P.restrict_update c x hx]
  unfold Forced at hwf hnf ⊢
  rw [P.toggle_comm _ ⟨x, hx⟩ ⟨w, hwB⟩ huv]
  omega

open Classical in
/-- **Servable or universal.** Fix the colours on `S` and the colour of the boundary
vertex `x ∉ S`. Either some colouring of the remaining vertices forces `x`, or the
opposite colour of `x` forces it under every colouring of the remaining vertices. -/
theorem servable_or_universal (S : Set V) (c : V → Bool) (x : V) (hxS : x ∉ S)
    (hx : x ∈ P.boundary) :
    (∃ c₁ : V → Bool, Set.EqOn c₁ c (S ∪ {x}) ∧ P.ForcedAt c₁ x) ∨
      P.UniversalAt (S ∪ {x}) (Function.update c x (!c x)) x := by
  by_cases h : ∃ c₁ : V → Bool, Set.EqOn c₁ c (S ∪ {x}) ∧ P.ForcedAt c₁ x
  · exact Or.inl h
  · refine Or.inr fun c₁ hc₁ => ?_
    have hc₁x : c₁ x = !c x := (hc₁ (Or.inr rfl)).trans (Function.update_self ..)
    have hc₀ : Set.EqOn (Function.update c₁ x (!c₁ x)) c (S ∪ {x}) := by
      intro y hy
      rcases hy with hyS | hyx
      · have hne : y ≠ x := fun e => hxS (e ▸ hyS)
        exact (Function.update_of_ne hne _ _).trans
          ((hc₁ (Or.inl hyS)).trans (Function.update_of_ne hne _ _))
      · have hyx' : y = x := hyx
        rw [hyx', Function.update_self, hc₁x, Bool.not_not]
    have hflip := P.forcedAt_update_of_not _ x hx (fun hf => h ⟨_, hc₀, hf⟩)
    have hback : Function.update (Function.update c₁ x (!c₁ x)) x
        (!Function.update c₁ x (!c₁ x) x) = c₁ := by
      funext y
      by_cases hy : y = x
      · rw [hy]
        simp
      · simp [Function.update_of_ne hy]
    rw [hback] at hflip
    exact hflip

open Classical in
private theorem favouredWeight_nonneg (a : P.boundary → P.boundary → ℤ)
    (b : P.boundary → Bool) (v : P.boundary) : 0 ≤ PairProfile.favouredWeight a b v := by
  unfold PairProfile.favouredWeight
  refine Finset.sum_nonneg fun u _ => ?_
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

open Classical in
private theorem favouredWeight_pos (a : P.boundary → P.boundary → ℤ)
    (b : P.boundary → Bool) (v u : P.boundary)
    (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    0 < PairProfile.favouredWeight a b v := by
  have hpos : 0 < |a v u| := abs_pos.mpr
    (hfav.elim (fun h => ne_of_gt h.1) (fun h => ne_of_lt h.1))
  have hnon : ∀ w ∈ (Finset.univ : Finset P.boundary), 0 ≤
      (if PairProfile.Favoured (a v w) (b v) (b w) then |a v w| else 0) := by
    intro w _
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  unfold PairProfile.favouredWeight
  apply (Finset.sum_pos_iff_of_nonneg hnon).mpr
  exact ⟨u, Finset.mem_univ u, by simpa only [if_pos hfav] using hpos⟩

private theorem forced_of_certificate (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (b : P.boundary → Bool) (v : P.boundary)
    (h : 0 < 2 * pieceDegree P.edges v.val - PairProfile.weight a v +
      2 * PairProfile.favouredWeight a b v) : P.Forced b v := by
  have hflip := P.profile_flip_bound (PairProfile.toggle b v) v
  rw [P.toggle_toggle] at hflip
  have hcert : PairProfile.weight a v ≤ 2 * pieceDegree P.edges v.val ∧
      2 * pieceDegree P.edges v.val - PairProfile.weight a v +
        2 * PairProfile.favouredWeight a b v ≤
          4 * (pieceDegree P.edges v.val + P.profile b -
            P.profile (PairProfile.toggle b v)) :=
    PairProfile.universal_opponent_certificate P.profile K a hrep
      (fun v => pieceDegree P.edges v.val) P.profile_flip_bound b v
      (pieceDegree P.edges v.val + P.profile b - P.profile (PairProfile.toggle b v))
      (by omega)
  unfold Forced
  omega

/-- Positive slack in a pair representation forces the vertex under every boundary
colouring. -/
theorem forced_of_slack (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (b : P.boundary → Bool) (v : P.boundary)
    (hslack : PairProfile.weight a v < 2 * pieceDegree P.edges v.val) : P.Forced b v :=
  P.forced_of_certificate K a hrep b v (by linarith [P.favouredWeight_nonneg a b v])

/-- One favoured interaction of a pair representation forces the vertex, whatever the
other boundary colours are. -/
theorem forced_of_favoured (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (b : P.boundary → Bool)
    (v u : P.boundary) (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    P.Forced b v := by
  have hw : PairProfile.weight a v ≤ 2 * pieceDegree P.edges v.val :=
    PairProfile.weight_budget P.profile K a hrep (fun v => pieceDegree P.edges v.val)
      P.profile_flip_bound v
  exact P.forced_of_certificate K a hrep b v
    (by linarith [P.favouredWeight_pos a b v u hfav])

end TenChallenges.Continuation.Energy.FinitePiece

/- Inlined from Continuation/UnfriendlyFreshSelection.lean. -/
/-!
# Fresh selection of permanent witnesses

A countable set of vertices is coloured in finitely many commitments per stage.
Each stage serves one vertex with a witness whose finite support is committed
at once, so the witness is permanent. A vertex is served again for every finite
set of forbidden keys, which makes its witness set infinite.

The service hypothesis is the only place where a combinatorial structure enters.
No limit of recolourings is taken: committed colours never change.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FreshSelection

variable {V : Type u} {Λ : Type v}

/-- Colours prescribed on `S` extend so that every vertex of `J` has infinitely
many witnesses, provided that each vertex of `J` can always be served: for every
finite set `D` of committed vertices, every finite set `F` of forbidden keys and
every current colouring, some witness with key outside `F` holds after changing
colours only outside `D ∪ S`. -/
theorem exists_fresh_selection [Countable V] (S J : Set V) (q : V → Bool)
    (key : Λ → V) (supp : Λ → V → Finset V)
    (Wit : Λ → V → (V → Bool) → Prop)
    (hlocal : ∀ (j : Λ) (v : V) (c c' : V → Bool),
      Set.EqOn c c' (supp j v) → Wit j v c → Wit j v c')
    (hserve : ∀ v ∈ J, ∀ (D F : Finset V) (c : V → Bool),
      ∃ (j : Λ) (c' : V → Bool), key j ∉ F ∧ Set.EqOn c' q S ∧
        Set.EqOn c' c (↑D \ S) ∧ Wit j v c') :
    ∃ c : V → Bool, Set.EqOn c q S ∧ ∀ v ∈ J, {j | Wit j v c}.Infinite := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · exact ⟨q, fun _ _ => rfl, fun v hv => hv.elim⟩
  · haveI : Nonempty J := hJ.to_subtype
    -- Schedule every vertex of `J` together with every finite forbidden key set.
    obtain ⟨e, he⟩ := exists_surjective_nat (J × Finset V)
    choose pick col hkey hS hD hW using fun v : J => hserve v.val v.property
    let s : ℕ → Finset V × (V → Bool) :=
      Nat.rec (∅, q) (fun n st =>
        (st.1 ∪ supp (pick (e n).1 st.1 (e n).2 st.2) (e n).1.val,
          col (e n).1 st.1 (e n).2 st.2))
    have hDstep : ∀ n, (s n).1 ⊆ (s (n + 1)).1 := fun n => Finset.subset_union_left
    have hDmono : Monotone (fun n => (s n).1) := monotone_nat_of_le_succ hDstep
    have hSall : ∀ n, Set.EqOn (s n).2 q S := by
      intro n
      cases n with
      | zero => exact fun _ _ => rfl
      | succ n => exact hS (e n).1 (s n).1 (e n).2 (s n).2
    -- Committed colours outside `S` never change.
    have hcolstep : ∀ n y, y ∈ (s n).1 → y ∉ S → (s (n + 1)).2 y = (s n).2 y :=
      fun n y hy hyS => hD (e n).1 (s n).1 (e n).2 (s n).2 ⟨hy, hyS⟩
    have hcoh : ∀ {m n : ℕ}, m ≤ n → ∀ y ∈ (s m).1, (s n).2 y = (s m).2 y := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact fun _ _ => rfl
      | succ k hmk ih =>
        intro y hy
        by_cases hyS : y ∈ S
        · exact (hSall (k + 1) hyS).trans (hSall m hyS).symm
        · exact (hcolstep k y (hDmono hmk hy) hyS).trans (ih y hy)
    let c : V → Bool := fun y =>
      if h : ∃ n, y ∈ (s n).1 then (s (Classical.choose h)).2 y else q y
    have hc : ∀ n, ∀ y ∈ (s n).1, c y = (s n).2 y := by
      intro n y hy
      have h : ∃ n, y ∈ (s n).1 := ⟨n, hy⟩
      have hval : c y = (s (Classical.choose h)).2 y := dif_pos h
      rw [hval]
      exact (hcoh (Nat.le_max_right n (Classical.choose h)) y
        (Classical.choose_spec h)).symm.trans
          (hcoh (Nat.le_max_left n (Classical.choose h)) y hy)
    have hcS : Set.EqOn c q S := by
      intro y hy
      by_cases h : ∃ n, y ∈ (s n).1
      · exact (dif_pos h).trans (hSall _ hy)
      · exact dif_neg h
    -- The witness chosen at a stage survives, since its support was committed.
    have hrequest : ∀ n, ∃ j, key j ∉ (e n).2 ∧ Wit j (e n).1.val c := fun n =>
      ⟨pick (e n).1 (s n).1 (e n).2 (s n).2, hkey (e n).1 (s n).1 (e n).2 (s n).2,
        hlocal _ _ (s (n + 1)).2 c
          (fun y hy => (hc (n + 1) y (Finset.mem_union_right _ hy)).symm)
          (hW (e n).1 (s n).1 (e n).2 (s n).2)⟩
    refine ⟨c, hcS, fun v hv hfin => ?_⟩
    obtain ⟨n, hn⟩ := he (⟨v, hv⟩, (hfin.image key).toFinset)
    obtain ⟨j, hjF, hjW⟩ := hrequest n
    rw [hn] at hjF hjW
    exact hjF ((hfin.image key).mem_toFinset.mpr ⟨j, hjW, rfl⟩)

end TenChallenges.Continuation.FreshSelection

/- Inlined from Continuation/UnfriendlyFreshWitness.lean. -/
/-!
# Fresh finite pieces as permanent witnesses

A robust frozen colouring is first enlarged to a maximal one. Maximality rules out
three kinds of further robust steps, and what remains can be served greedily:

* a vertex with infinitely many frozen neighbours;
* a vertex that infinitely many pieces force with one colour, whatever the other
  free boundary colours are;
* a finite set that is the exact free boundary of infinitely many pieces;
* two vertices joined by nonzero pair interactions in infinitely many pieces.

After these exclusions every remaining vertex can be given a new permanent witness
at each finite stage, using a neighbour or a piece whose other free boundary
vertices have not been coloured yet. No bound on the boundary size of a piece and
no pair representation is needed for that last step.

This is a special case of the countable unfriendly partition problem. It does not
prove the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

namespace Energy

variable {V : Type u}

/-- No robust frozen colouring inside `H` properly extends `(S, q)`. -/
def MaximalRobust (G : SimpleGraph V) (M S H : Set V) (q : V → Bool) : Prop :=
  ∀ (S' : Set V) (q' : V → Bool), S' ⊆ H → Robust G M S' q' → S ⊆ S' →
    Set.EqOn q' q S → S' ⊆ S

/-- Maximal robust frozen colourings exist above any robust frozen colouring. -/
theorem exists_maximal_robust_extending (G : SimpleGraph V) (M H S₀ : Set V)
    (q₀ : V → Bool) (hS₀ : S₀ ⊆ H) (hq₀ : Robust G M S₀ q₀) :
    ∃ (S : Set V) (q : V → Bool), S₀ ⊆ S ∧ S ⊆ H ∧ Set.EqOn q q₀ S₀ ∧
      Robust G M S q ∧ MaximalRobust G M S H q := by
  classical
  let T : Type u := {P : Set V × (V → Bool) //
    S₀ ⊆ P.1 ∧ P.1 ⊆ H ∧ Set.EqOn P.2 q₀ S₀ ∧ Robust G M P.1 P.2}
  let r : T → T → Prop := fun P Q => P.1.1 ⊆ Q.1.1 ∧ Set.EqOn Q.1.2 P.1.2 P.1.1
  have htrans : ∀ {a b c : T}, r a b → r b c → r a c := fun {a b c} hab hbc =>
    ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 (hab.1 hy)).trans (hab.2 hy)⟩
  have hchain : ∀ c : Set T, IsChain r c → ∃ ub, ∀ a ∈ c, r a ub := by
    intro c hc
    let dom : Set V := S₀ ∪ ⋃ P ∈ c, P.1.1
    let col : V → Bool := fun y =>
      if h : ∃ P ∈ c, y ∈ P.1.1 then (Classical.choose h).1.2 y else q₀ y
    have hcol : ∀ P ∈ c, Set.EqOn col P.1.2 P.1.1 := by
      intro P hP y hy
      have h : ∃ P ∈ c, y ∈ P.1.1 := ⟨P, hP, hy⟩
      have hspec := Classical.choose_spec h
      have hval : col y = (Classical.choose h).1.2 y := dif_pos h
      rw [hval]
      by_cases hPQ : Classical.choose h = P
      · rw [hPQ]
      · rcases hc hspec.1 hP hPQ with hle | hle
        · exact (hle.2 hspec.2).symm
        · exact hle.2 hy
    have hcol₀ : Set.EqOn col q₀ S₀ := by
      intro y hy
      by_cases h : ∃ P ∈ c, y ∈ P.1.1
      · exact (dif_pos h).trans ((Classical.choose h).2.2.2.1 hy)
      · exact dif_neg h
    have hdomH : dom ⊆ H :=
      Set.union_subset hS₀ (Set.iUnion₂_subset fun P _ => P.2.2.1)
    have hrob : Robust G M dom col := by
      intro cc hcc heq v hv
      rcases hv with hv₀ | hv
      · exact hq₀ cc hcc (fun y hy => (heq (Or.inl hy)).trans (hcol₀ hy)) v hv₀
      · obtain ⟨P, hP, hvP⟩ := Set.mem_iUnion₂.mp hv
        exact P.2.2.2.2 cc hcc
          (fun y hy => (heq (Or.inr (Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩))).trans
            (hcol P hP hy)) v hvP
    exact ⟨⟨(dom, col), Set.subset_union_left, hdomH, hcol₀, hrob⟩, fun P hP =>
      ⟨fun y hy => Or.inr (Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩), hcol P hP⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  refine ⟨m.1.1, m.1.2, m.2.1, m.2.2.1, m.2.2.2.1, m.2.2.2.2,
    fun S' q' hS'H hrob hSS' heq => ?_⟩
  exact (hm ⟨(S', q'), m.2.1.trans hSS', hS'H,
    fun y hy => (heq (m.2.1 hy)).trans (m.2.2.2.1 hy), hrob⟩ ⟨hSS', heq⟩).1

end Energy

open Energy

variable {V : Type u} {ι : Type v}

/-- Pairwise disjoint finite pieces of finite-degree vertices. -/
structure PieceFamily (G : SimpleGraph V) (ι : Type v) where
  piece : ι → Energy.FinitePiece G
  disjoint : Pairwise (Function.onFun Disjoint (fun i => (piece i).verts))

namespace PieceFamily

variable {G : SimpleGraph V} (D : PieceFamily G ι)

theorem finite_pieces_meeting {O : Set V} (hO : O.Finite) :
    {i | ∃ w ∈ O, w ∈ (D.piece i).verts}.Finite := by
  have hf : ∀ w : V, {i | w ∈ (D.piece i).verts}.Subsingleton := by
    intro w i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp (D.disjoint hij) hi hj
  exact (hO.biUnion (fun w _ => (hf w).finite)).subset
    (fun i ⟨w, hw, hwi⟩ => Set.mem_iUnion₂.mpr ⟨w, hw, hwi⟩)

theorem piece_subset (M : Set V) (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (i : ι) :
    ((D.piece i).verts : Set V) ⊆ M :=
  fun x hx => hM x ((D.piece i).finite_degree x hx)

/-- Opponents inside infinitely many pieces are infinitely many opponents. -/
theorem infinite_opposite_of_pieces (c : V → Bool) (x : V)
    (h : {i | ∃ w ∈ (D.piece i).verts, G.Adj x w ∧ c w ≠ c x}.Infinite) :
    (oppositeSet G c x).Infinite := fun hO =>
  h ((D.finite_pieces_meeting hO).subset
    fun _ ⟨w, hw, hadj, hne⟩ => ⟨w, ⟨hadj, hne⟩, hw⟩)

open Classical in
/-- **Universal step.** A vertex that infinitely many pieces force with the colour `β`,
under every colouring of the vertices outside `S ∪ {x}`, can be frozen with `β`. -/
theorem robust_update_of_universal (M S : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hq : Robust G M S q)
    (x : V) (hx : x ∉ S) (β : Bool)
    (hinf : {i | (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x}.Infinite) :
    Robust G M (S ∪ {x}) (Function.update q x β) := by
  intro c hc hcq v hv
  rcases hv with hvS | hvx
  · exact hq c hc (fun y hy => (hcq (Or.inl hy)).trans
      (Function.update_of_ne (fun h : y = x => hx (h ▸ hy)) _ _)) v hvS
  · have hvx' : v = x := hvx
    rw [hvx']
    apply D.infinite_opposite_of_pieces c x
    exact hinf.mono fun i
        (hi : (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x) =>
      (D.piece i).opponent_of_forcedAt M c (D.piece_subset M hM i) hc x (hi c hcq)

open Classical in
private theorem robust_update_of_favoured_pair (M S : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hq : Robust G M S q)
    (x p : V) (hx : x ∉ S) (hp : p ∉ S) (hxp : x ≠ p) (γ : Bool)
    (hinf : {i | ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K a ∧
          PairProfile.Favoured (a ⟨x, hx⟩ ⟨p, hp⟩) false γ}.Infinite) :
    Robust G M (S ∪ {x, p}) (Function.update (Function.update q x false) p γ) := by
  intro c hc hcq v hv
  have hcx : c x = false := (hcq (Or.inr (Or.inl rfl))).trans
    ((Function.update_of_ne hxp _ _).trans (Function.update_self ..))
  have hcp : c p = γ := (hcq (Or.inr (Or.inr rfl))).trans (Function.update_self ..)
  rcases hv with hvS | hvx | hvp
  · refine hq c hc (fun y hy => (hcq (Or.inl hy)).trans ?_) v hvS
    exact (Function.update_of_ne (fun h : y = p => hp (h ▸ hy)) _ _).trans
      (Function.update_of_ne (fun h : y = x => hx (h ▸ hy)) _ _)
  · have hvx' : v = x := hvx
    rw [hvx']
    apply D.infinite_opposite_of_pieces c x
    refine hinf.mono fun i hi => ?_
    obtain ⟨K, a, hxB, hpB, hrep, hfav⟩ := hi
    refine (D.piece i).opponent_of_forcedAt M c (D.piece_subset M hM i) hc x ⟨hxB, ?_⟩
    apply (D.piece i).forced_of_favoured K a hrep (fun u => c u.val) ⟨x, hxB⟩ ⟨p, hpB⟩
    show PairProfile.Favoured (a ⟨x, hxB⟩ ⟨p, hpB⟩) (c x) (c p)
    rw [hcx, hcp]
    exact hfav
  · have hvp' : v = p := hvp
    rw [hvp']
    apply D.infinite_opposite_of_pieces c p
    refine hinf.mono fun i hi => ?_
    obtain ⟨K, a, hxB, hpB, hrep, hfav⟩ := hi
    refine (D.piece i).opponent_of_forcedAt M c (D.piece_subset M hM i) hc p ⟨hpB, ?_⟩
    apply (D.piece i).forced_of_favoured K a hrep (fun u => c u.val) ⟨p, hpB⟩ ⟨x, hxB⟩
    show PairProfile.Favoured (a ⟨p, hpB⟩ ⟨x, hxB⟩) (c p) (c x)
    rw [hrep.1 ⟨p, hpB⟩ ⟨x, hxB⟩, hcx, hcp]
    exact hfav.elim (fun h => Or.inl ⟨h.1, h.2.symm⟩) (fun h => Or.inr ⟨h.1, h.2.symm⟩)

/-- **Pair step.** Two unfrozen vertices joined by a nonzero pair interaction in
infinitely many pieces can be frozen together. -/
theorem exists_robust_of_pair (M S : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hq : Robust G M S q)
    (x p : V) (hx : x ∉ S) (hp : p ∉ S) (hxp : x ≠ p)
    (hinf : {i | ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K a ∧ a ⟨x, hx⟩ ⟨p, hp⟩ ≠ 0}.Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ {x, p}) q' := by
  classical
  have hsplit : ∃ γ : Bool, {i | ∃ (K : ℤ)
      (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
      (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
      PairProfile.Represents (D.piece i).profile K a ∧
        PairProfile.Favoured (a ⟨x, hx⟩ ⟨p, hp⟩) false γ}.Infinite := by
    by_contra hno
    have hf : ∀ γ : Bool, {i | ∃ (K : ℤ)
        (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K a ∧
          PairProfile.Favoured (a ⟨x, hx⟩ ⟨p, hp⟩) false γ}.Finite :=
      fun γ => Set.not_infinite.mp fun hi => hno ⟨γ, hi⟩
    refine hinf (((hf true).union (hf false)).subset ?_)
    rintro i ⟨K, a, hxB, hpB, hrep, hne⟩
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact Or.inr ⟨K, a, hxB, hpB, hrep, Or.inr ⟨hneg, rfl⟩⟩
    · exact Or.inl ⟨K, a, hxB, hpB, hrep, Or.inl ⟨hpos, by decide⟩⟩
  obtain ⟨γ, hγ⟩ := hsplit
  refine ⟨Function.update (Function.update q x false) p γ, fun y hy => ?_,
    D.robust_update_of_favoured_pair M S q hM hq x p hx hp hxp γ hγ⟩
  exact (Function.update_of_ne (fun h : y = p => hp (h ▸ hy)) _ _).trans
    (Function.update_of_ne (fun h : y = x => hx (h ▸ hy)) _ _)

open Classical in
/-- Infinitely many pieces with the same free boundary form a recurrent block. -/
theorem recurrentBlock_of_infinite (S : Set V) (A : Finset V)
    (hinf : {i | (D.piece i).boundary.filter (· ∉ S) = A}.Infinite) :
    RecurrentBlock G S A := by
  let f := hinf.natEmbedding
  have hf : ∀ n, (D.piece (f n).val).boundary.filter (· ∉ S) = A := fun n => (f n).property
  refine ⟨fun n => (D.piece (f n).val).verts, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact D.disjoint fun h => hmn (f.injective (Subtype.ext h))
  · intro n x hx
    exact (D.piece (f n).val).finite_degree x hx
  · intro n x hx y hxy
    by_cases hy : y ∈ (D.piece (f n).val).verts
    · exact Or.inl hy
    · have hyB := (D.piece (f n).val).mem_boundary_of_adj hy hx hxy.symm
      by_cases hyS : y ∈ S
      · exact Or.inr (Or.inr hyS)
      · refine Or.inr (Or.inl ?_)
        rw [← hf n]
        exact Finset.mem_filter.mpr ⟨hyB, hyS⟩
  · intro n v hv
    rw [← hf n] at hv
    obtain ⟨w, hw, hadj⟩ :=
      (D.piece (f n).val).boundary_touch ⟨v, (Finset.mem_filter.mp hv).1⟩
    exact ⟨w, hw, hadj⟩

/-- Witness identities: a neighbour, or a piece together with one of its vertices and the
set of boundary vertices whose colours certify the witness. -/
abbrev WitnessIndex (D : PieceFamily G ι) :=
  V ⊕ (Σ i : ι, {w : V // w ∈ (D.piece i).verts} ×
    {Q : Finset V // Q ∈ (D.piece i).boundary.powerset})

def witnessKey : D.WitnessIndex → V :=
  Sum.elim id (fun p => p.2.1.val)

open Classical in
noncomputable def witnessSupport : D.WitnessIndex → V → Finset V :=
  Sum.elim (fun u x => {u, x}) (fun p _ => p.2.2.val)

/-- A neighbour in `H` of the opposite colour, or a piece that forces `x` under every
colouring agreeing with `c` on a certifying set inside `H`. -/
def Witness (H : Set V) : D.WitnessIndex → V → (V → Bool) → Prop :=
  Sum.elim (fun u x c => G.Adj x u ∧ u ∈ H ∧ c u ≠ c x)
    (fun p x c => (p.2.2.val : Set V) ⊆ H ∧
      (D.piece p.1).UniversalAt (p.2.2.val : Set V) c x)

theorem witness_local (H : Set V) (j : D.WitnessIndex) (x : V) (c c' : V → Bool)
    (h : Set.EqOn c c' (D.witnessSupport j x)) (hW : D.Witness H j x c) :
    D.Witness H j x c' := by
  classical
  rcases j with u | p
  · obtain ⟨hadj, huH, hne⟩ := hW
    have hu : c u = c' u := h (by simp [witnessSupport])
    have hx : c x = c' x := h (by simp [witnessSupport])
    exact ⟨hadj, huH, fun heq => hne (hu.trans (heq.trans hx.symm))⟩
  · obtain ⟨hQ, hU⟩ := hW
    exact ⟨hQ, fun c₁ hc₁ => hU c₁ fun y hy => (hc₁ hy).trans (h hy).symm⟩

theorem witness_of_eqOn (H : Set V) (c d : V → Bool) (h : Set.EqOn c d H) (x : V)
    (hx : x ∈ H) (j : D.WitnessIndex) (hW : D.Witness H j x c) : D.Witness H j x d := by
  rcases j with u | p
  · obtain ⟨hadj, huH, hne⟩ := hW
    exact ⟨hadj, huH, fun heq => hne ((h huH).trans (heq.trans (h hx).symm))⟩
  · obtain ⟨hQ, hU⟩ := hW
    exact ⟨hQ, fun c₁ hc₁ => hU c₁ fun y hy => (hc₁ hy).trans (h (hQ hy)).symm⟩

/-- A vertex with finitely many opponents has finitely many witnesses. -/
theorem witness_finite (M H : Set V) (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M)
    (c : V → Bool) (hc : StrongMaximal G M c) (x : V)
    (hO : (oppositeSet G c x).Finite) : {j | D.Witness H j x c}.Finite := by
  classical
  have hI := D.finite_pieces_meeting hO
  have hT : ((Sum.inl : V → D.WitnessIndex) '' oppositeSet G c x ∪
      ⋃ i ∈ {i | ∃ w ∈ oppositeSet G c x, w ∈ (D.piece i).verts},
        Set.range (fun t : {w : V // w ∈ (D.piece i).verts} ×
            {Q : Finset V // Q ∈ (D.piece i).boundary.powerset} =>
          (Sum.inr ⟨i, t⟩ : D.WitnessIndex))).Finite :=
    (hO.image Sum.inl).union (hI.biUnion fun i _ => Set.finite_range _)
  refine hT.subset ?_
  rintro (u | ⟨i, t⟩) hW
  · obtain ⟨hadj, _, hne⟩ := hW
    exact Or.inl ⟨u, ⟨hadj, hne⟩, rfl⟩
  · obtain ⟨_, hU⟩ := hW
    obtain ⟨z, hz, hadj, hne⟩ := (D.piece i).opponent_of_forcedAt M c
      (D.piece_subset M hM i) hc x (hU c fun _ _ => rfl)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, ⟨z, ⟨hadj, hne⟩, hz⟩, t, rfl⟩)

/-- The vertex `x` can be given a new witness at every finite stage: the colours on
`S` and on the committed set `K` are kept, and the key avoids `F`. -/
def Servable (S H : Set V) (q : V → Bool) (x : V) : Prop :=
  ∀ (K F : Finset V) (c : V → Bool), ∃ (j : D.WitnessIndex) (c' : V → Bool),
    D.witnessKey j ∉ F ∧ Set.EqOn c' q S ∧ Set.EqOn c' c (↑K \ S) ∧ D.Witness H j x c'

/-- A robust frozen colouring extends to all of `H` when every other vertex of `H` can
always be served. -/
theorem robust_of_servable [Countable V] (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H) (hq : Robust G M S q)
    (hserve : ∀ x ∈ H, x ∉ S → D.Servable S H q x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M H q' := by
  obtain ⟨c, hcS, hc⟩ := FreshSelection.exists_fresh_selection S (H \ S) q D.witnessKey
    D.witnessSupport (D.Witness H) (D.witness_local H)
    (fun x hx K F c => hserve x hx.1 hx.2 K F c)
  refine ⟨c, hcS, fun d hd hdc x hxH => ?_⟩
  by_cases hxS : x ∈ S
  · exact hq d hd (fun y hy => (hdc (hSH hy)).trans (hcS hy)) x hxS
  · intro hO
    exact hc x ⟨hxH, hxS⟩ ((D.witness_finite M H hM d hd x hO).subset
      fun j hj => D.witness_of_eqOn H c d (fun y hy => (hdc hy).symm) x hxH j hj)

end PieceFamily
end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyFiniteDefect.lean. -/
/-!
# Finite-defect repair of certified hub colourings

Under a total colouring, a vertex is *certified* when it has infinitely many
opposite neighbours in the target set or is forced by infinitely many pieces whose
boundary lies in the target set. Certified vertices have infinitely many opponents
in every strongly maximal colouring with the same colours on the target set.

Reversing the colour of one uncertified vertex certifies it, when it has enough
neighbours or pieces, and never destroys the certificate of another vertex: the
reversal can only cost witnesses in the finitely many pieces that forced the
reversed vertex. Consequently a colouring with finitely many uncertified vertices
can be repaired at finitely many of them.

No statement is made about infinitely many reversals; their accumulated loss of
witnesses is exactly what the unrestricted problem has to control.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PieceFamily

open Energy

variable {V : Type u} {ι : Type v} {G : SimpleGraph V} (D : PieceFamily G ι)

/-- Under the total colouring `c`, the vertex `x` has infinitely many opposite
neighbours in `H` or is forced by infinitely many pieces with boundary in `H`. -/
def CertifiedAt (H : Set V) (c : V → Bool) (x : V) : Prop :=
  (G.neighborSet x ∩ {u | u ∈ H ∧ c u ≠ c x}).Infinite ∨
    {i | ((D.piece i).boundary : Set V) ⊆ H ∧ (D.piece i).ForcedAt c x}.Infinite

/-- Infinitely many neighbours in `H`, or infinitely many pieces at `x` with boundary
in `H`. This does not depend on any colouring. -/
def Supplied (H : Set V) (x : V) : Prop :=
  (G.neighborSet x ∩ H).Infinite ∨
    {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H}.Infinite

/-- A certified vertex has infinitely many opponents in every strongly maximal
colouring that agrees with `c` on `H`. -/
theorem infinite_opposite_of_certified (M H : Set V)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (c d : V → Bool)
    (hd : StrongMaximal G M d) (hdc : Set.EqOn d c H) (x : V) (hx : x ∈ H)
    (h : D.CertifiedAt H c x) : (oppositeSet G d x).Infinite := by
  rcases h with hhub | hpiece
  · refine hhub.mono fun u hu => ⟨hu.1, ?_⟩
    rw [hdc hu.2.1, hdc hx]
    exact hu.2.2
  · apply D.infinite_opposite_of_pieces d x
    refine hpiece.mono fun i hi => ?_
    exact (D.piece i).opponent_of_forcedAt M d (D.piece_subset M hM i) hd x
      ((D.piece i).forcedAt_congr c d (fun y hy => (hdc (hi.1 hy)).symm) x hi.2)

open Classical in
/-- Reversing the colour of an uncertified but supplied vertex certifies it. -/
theorem certifiedAt_update_self (H : Set V) (c : V → Bool) (x : V)
    (hsup : D.Supplied H x) (hn : ¬ D.CertifiedAt H c x) :
    D.CertifiedAt H (Function.update c x (!c x)) x := by
  have hn1 : (G.neighborSet x ∩ {u | u ∈ H ∧ c u ≠ c x}).Finite :=
    Set.not_infinite.mp fun h => hn (Or.inl h)
  have hn2 : {i | ((D.piece i).boundary : Set V) ⊆ H ∧ (D.piece i).ForcedAt c x}.Finite :=
    Set.not_infinite.mp fun h => hn (Or.inr h)
  rcases hsup with hhub | hpiece
  · refine Or.inl ((hhub.sdiff hn1).mono fun u hu => ?_)
    obtain ⟨⟨hadj, huH⟩, hnot⟩ := hu
    have hadj' : G.Adj x u := hadj
    have hux : u ≠ x := fun h => G.ne_of_adj hadj' h.symm
    have hcu : c u = c x := Classical.byContradiction fun hne => hnot ⟨hadj, huH, hne⟩
    refine ⟨hadj, huH, ?_⟩
    rw [Function.update_of_ne hux, Function.update_self, hcu]
    cases c x <;> decide
  · refine Or.inr ((hpiece.sdiff hn2).mono fun i hi => ?_)
    obtain ⟨⟨hxB, hBH⟩, hnot⟩ := hi
    exact ⟨hBH, (D.piece i).forcedAt_update_of_not c x hxB fun hf => hnot ⟨hBH, hf⟩⟩

open Classical in
/-- Reversing the colour of an uncertified vertex keeps every other certified vertex
certified. -/
theorem certifiedAt_update_other (H : Set V) (c : V → Bool) (x y : V) (hyx : y ≠ x)
    (hn : ¬ D.CertifiedAt H c x) (hy : D.CertifiedAt H c y) :
    D.CertifiedAt H (Function.update c x (!c x)) y := by
  have hn2 : {i | ((D.piece i).boundary : Set V) ⊆ H ∧ (D.piece i).ForcedAt c x}.Finite :=
    Set.not_infinite.mp fun h => hn (Or.inr h)
  have hcy : Function.update c x (!c x) y = c y := Function.update_of_ne hyx _ _
  rcases hy with hhub | hpiece
  · refine Or.inl ((hhub.sdiff (Set.finite_singleton x)).mono fun u hu => ?_)
    obtain ⟨⟨hadj, huH, hne⟩, hux⟩ := hu
    refine ⟨hadj, huH, ?_⟩
    rw [Function.update_of_ne (fun h : u = x => hux h), hcy]
    exact hne
  · refine Or.inr ((hpiece.sdiff hn2).mono fun i hi => ?_)
    obtain ⟨⟨hBH, hf⟩, hnot⟩ := hi
    refine ⟨hBH, ?_⟩
    by_cases hxB : x ∈ (D.piece i).boundary
    · exact (D.piece i).forcedAt_update_of_forcedAt c x y hyx hxB
        (fun hfx => hnot ⟨hBH, hfx⟩) hf
    · exact (D.piece i).forcedAt_congr c _
        (fun z hz => (Function.update_of_ne
          (fun h : z = x => hxB (h ▸ Finset.mem_coe.mp hz)) _ _).symm) y hf

/-- **Finite-defect repair.** If only finitely many vertices of `T` are uncertified
and every vertex of `T` is supplied, then recolouring vertices of `T` certifies all
of `T`. Colours outside `T` are kept. -/
theorem exists_certified_of_finite_defect (H T : Set V) (c : V → Bool)
    (hsup : ∀ x ∈ T, D.Supplied H x)
    (hfin : {x | x ∈ T ∧ ¬ D.CertifiedAt H c x}.Finite) :
    ∃ c' : V → Bool, (∀ y, y ∉ T → c' y = c y) ∧ ∀ x ∈ T, D.CertifiedAt H c' x := by
  classical
  suffices h : ∀ (n : ℕ) (c : V → Bool)
      (hfin : {x | x ∈ T ∧ ¬ D.CertifiedAt H c x}.Finite), hfin.toFinset.card ≤ n →
        ∃ c' : V → Bool, (∀ y, y ∉ T → c' y = c y) ∧ ∀ x ∈ T, D.CertifiedAt H c' x from
    h _ c hfin le_rfl
  intro n
  induction n with
  | zero =>
    intro c hfin hcard
    refine ⟨c, fun _ _ => rfl, fun x hx => ?_⟩
    by_contra hbad
    have hmem : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hx, hbad⟩
    have hempty : hfin.toFinset = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    rw [hempty] at hmem
    exact Finset.notMem_empty x hmem
  | succ n ih =>
    intro c hfin hcard
    by_cases hall : ∀ x ∈ T, D.CertifiedAt H c x
    · exact ⟨c, fun _ _ => rfl, hall⟩
    · obtain ⟨x, hxT, hxbad⟩ : ∃ x, x ∈ T ∧ ¬ D.CertifiedAt H c x := by
        by_contra hno
        exact hall fun x hx => Classical.byContradiction fun hb => hno ⟨x, hx, hb⟩
      have hself := D.certifiedAt_update_self H c x (hsup x hxT) hxbad
      have hsub : {y | y ∈ T ∧ ¬ D.CertifiedAt H (Function.update c x (!c x)) y} ⊆
          ((hfin.toFinset.erase x : Finset V) : Set V) := by
        intro y hy
        obtain ⟨hyT, hybad⟩ := hy
        have hyx : y ≠ x := fun h => hybad (h ▸ hself)
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr
          ⟨hyx, hfin.mem_toFinset.mpr ⟨hyT, fun hcy => ?_⟩⟩)
        exact hybad (D.certifiedAt_update_other H c x y hyx hxbad hcy)
      have hfin' : {y | y ∈ T ∧
          ¬ D.CertifiedAt H (Function.update c x (!c x)) y}.Finite :=
        (Finset.finite_toSet _).subset hsub
      have hcard' : hfin'.toFinset.card ≤ n := by
        have h1 : hfin'.toFinset ⊆ hfin.toFinset.erase x := fun y hy =>
          Finset.mem_coe.mp (hsub (hfin'.mem_toFinset.mp hy))
        have h2 := Finset.card_le_card h1
        have h3 := Finset.card_erase_of_mem (hfin.mem_toFinset.mpr ⟨hxT, hxbad⟩)
        omega
      obtain ⟨c', hc'T, hc'⟩ := ih (Function.update c x (!c x)) hfin' hcard'
      refine ⟨c', fun y hy => ?_, hc'⟩
      exact (hc'T y hy).trans
        (Function.update_of_ne (fun h : y = x => hy (h ▸ hxT)) _ _)

/-- **Robustness after finite-defect repair.** Over a robust frozen colouring on `S`,
a colouring of `H` with finitely many uncertified vertices outside `S`, all of them
supplied, can be recoloured outside `S` to a robust colouring of `H`. -/
theorem robust_of_finite_defect (M S H : Set V) (q c : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hcq : Set.EqOn c q S)
    (hsup : ∀ x ∈ H, x ∉ S → D.Supplied H x)
    (hfin : {x | x ∈ H \ S ∧ ¬ D.CertifiedAt H c x}.Finite) :
    ∃ c' : V → Bool, Set.EqOn c' q S ∧ Robust G M H c' := by
  obtain ⟨c', hc'T, hc'⟩ := D.exists_certified_of_finite_defect H (H \ S) c
    (fun x hx => hsup x hx.1 hx.2) hfin
  have hc'S : Set.EqOn c' q S := fun y hy => (hc'T y fun h => h.2 hy).trans (hcq hy)
  refine ⟨c', hc'S, fun d hd hdc x hxH => ?_⟩
  by_cases hxS : x ∈ S
  · exact hq d hd (fun y hy => (hdc (hSH hy)).trans (hc'S hy)) x hxS
  · exact D.infinite_opposite_of_certified M H hM c' d hd hdc x hxH (hc' x ⟨hxH, hxS⟩)

end TenChallenges.Continuation.PieceFamily

/- Inlined from Continuation/UnfriendlyFinitePalettes.lean. -/
/-!
# Minimal admissible families of finite patterns

A family of allowed coordinate patterns is admissible when every coordinate can
be repaired within its allowed patterns for each allowed assignment. A minimal
admissible family supports every retained pattern.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FinitePalettes

private def Admissible {ι : Type u} [DecidableEq ι] {A : ι → Type v}
    (P : ι → ((i : ι) → A i) → Prop) (B : (i : ι) → Set (A i)) : Prop :=
  (∀ i, (B i).Nonempty) ∧
    ∀ i x, (∀ j, x j ∈ B j) → ∃ a ∈ B i, P i (Function.update x i a)

private theorem exists_mem_of_nested {α σ : Type*} [Finite α] [Nonempty σ]
    (R : σ → Set α) (hR : ∀ j, (R j).Nonempty)
    (nested : ∀ j k, R j ⊆ R k ∨ R k ⊆ R j) :
    ∃ a, ∀ j, a ∈ R j := by
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ :=
    (Set.toFinite (Set.range R)).exists_minimal (Set.range_nonempty R)
  obtain ⟨a, ha⟩ := hR j
  exact ⟨a, fun k => (nested j k).elim (fun h => h ha)
    (fun h => hj (Set.mem_range_self k) h ha)⟩

private theorem admissible_lower_bound {ι : Type u} [DecidableEq ι]
    {A : ι → Type v} [∀ i, Finite (A i)] [∀ i, Nonempty (A i)]
    {P : ι → ((i : ι) → A i) → Prop} (hTop : Admissible P ⊤)
    (C : Set ((i : ι) → Set (A i))) (hC : ∀ B ∈ C, Admissible P B)
    (hc : IsChain (· ≥ ·) C) : ∃ B, Admissible P B ∧ ∀ D ∈ C, B ≤ D := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⊤, hTop, by simp⟩
  · haveI : Nonempty C := hne.to_subtype
    let B (i : ι) : Set (A i) := {a | ∀ D : C, a ∈ D.val i}
    have below : ∀ D ∈ C, B ≤ D := fun D hD i a ha => ha ⟨D, hD⟩
    have comparable (D E : C) : D.val ≤ E.val ∨ E.val ≤ D.val :=
      (hc.total D.property E.property).symm
    refine ⟨B, ⟨?_, ?_⟩, below⟩
    · exact fun i => exists_mem_of_nested (fun D : C => D.val i)
        (fun D => (hC D.val D.property).1 i)
        (fun D E => (comparable D E).imp (fun h => h i) (fun h => h i))
    intro i x hx
    let responses (D : C) : Set (A i) :=
      {a ∈ D.val i | P i (Function.update x i a)}
    have available (D : C) : (responses D).Nonempty :=
      (hC D.val D.property).2 i x fun j => hx j D
    have nested (D E : C) : responses D ⊆ responses E ∨ responses E ⊆ responses D :=
      (comparable D E).imp (fun h a ha => ⟨h i ha.1, ha.2⟩)
        (fun h a ha => ⟨h i ha.1, ha.2⟩)
    obtain ⟨a, ha⟩ := exists_mem_of_nested responses available nested
    exact ⟨a, fun D => (ha D).1, (ha (Classical.choice inferInstance)).2⟩

private theorem pattern_of_minimal {ι : Type u} [DecidableEq ι]
    {A : ι → Type v} {P : ι → ((i : ι) → A i) → Prop}
    {B : (i : ι) → Set (A i)} (hB : Minimal (Admissible P) B)
    (i : ι) (a : A i) (ha : a ∈ B i) :
    ∃ x : (j : ι) → A j, (∀ j, x j ∈ B j) ∧ x i = a ∧ P i x := by
  by_contra unsupported
  have respondsWithout (x : (j : ι) → A j) (hx : ∀ j, x j ∈ B j) :
      ∃ b ∈ B i \ {a}, P i (Function.update x i b) := by
    obtain ⟨b, hb, hp⟩ := hB.1.2 i x hx
    refine ⟨b, ⟨hb, ?_⟩, hp⟩
    intro hba
    exact unsupported ⟨Function.update x i b,
      (Function.forall_update_iff x (fun j xj => xj ∈ B j)).mpr ⟨hb, fun j _ => hx j⟩,
      (Function.update_self i b x).trans (Set.mem_singleton_iff.mp hba), hp⟩
  let smaller := Function.update B i (B i \ {a})
  have le : smaller ≤ B :=
    (Function.forall_update_iff B (fun j patterns => patterns ⊆ B j)).mpr
      ⟨Set.sdiff_subset, fun _ _ => Set.Subset.rfl⟩
  have admissible : Admissible P smaller := by
    refine ⟨?_, ?_⟩
    · let x : (j : ι) → A j := fun j => (hB.1.1 j).choose
      obtain ⟨b, hb, _⟩ := respondsWithout x fun j => (hB.1.1 j).choose_spec
      exact (Function.forall_update_iff B (fun _ patterns => patterns.Nonempty)).mpr
        ⟨⟨b, hb⟩, fun j _ => hB.1.1 j⟩
    intro j x hx
    have hxB (k : ι) : x k ∈ B k := le k (hx k)
    rcases Decidable.eq_or_ne j i with rfl | hji
    · simpa only [smaller, Function.update_self] using respondsWithout x hxB
    · simpa only [smaller, Function.update_of_ne hji] using hB.1.2 j x hxB
  have ha' : a ∈ smaller i := hB.2 admissible le i ha
  simp [smaller] at ha'

/-- Local solvability on a product of finite pattern spaces allows restriction to
nonempty sets of patterns in which every retained pattern certifies its coordinate
in some retained assignment. -/
theorem exists_supported_patterns {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [∀ i, Finite (A i)] [∀ i, Nonempty (A i)]
    (P : ι → ((i : ι) → A i) → Prop)
    (hlocal : ∀ i x, ∃ a : A i, P i (Function.update x i a)) :
    ∃ B : (i : ι) → Set (A i), (∀ i, (B i).Nonempty) ∧
      ∀ i a, a ∈ B i → ∃ x : (j : ι) → A j, (∀ j, x j ∈ B j) ∧ x i = a ∧ P i x := by
  have hTop : Admissible P ⊤ :=
    ⟨fun _ => Set.univ_nonempty, fun i x _ =>
      let ⟨a, ha⟩ := hlocal i x
      ⟨a, Set.mem_univ a, ha⟩⟩
  obtain ⟨B, hB⟩ : ∃ B, Minimal (Admissible P) B :=
    @zorn_le₀ (((i : ι) → Set (A i))ᵒᵈ) _ {B | Admissible P B}
      (fun C hC hc => admissible_lower_bound hTop C hC hc)
  exact ⟨B, hB.1.1, pattern_of_minimal hB⟩

end TenChallenges.Continuation.FinitePalettes

/- Inlined from Continuation/UnfriendlyBlockBaire.lean. -/
/-!
# Simultaneous requirements on finite patterns

Use Baire category to meet countably many requirements on a product of finite
sets. Each retained coordinate value has a successful extension, and a
requirement survives changes to finitely many other coordinates.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.BlockBaire

open Set Topology Filter

/-- An infinite set of witnesses defines a Gδ condition when each witness defines an open set. -/
theorem isGδ_infinite_witnesses {W : Type*} {X : Type*} [TopologicalSpace X]
    (Q : W → X → Prop) (hQ : ∀ w, IsOpen {x | Q w x}) :
    IsGδ {x | {w | Q w x}.Infinite} := by
  let U (n : ℕ) : Set X :=
    ⋃ t : {s : Finset W // s.card = n}, ⋂ w : (t.val : Set W), {x | Q w x}
  have ho : ∀ n, IsOpen (U n) := fun n =>
    isOpen_iUnion (fun t => isOpen_iInter_of_finite (fun w : (t.val : Set W) => hQ w))
  suffices heq : {x | {w | Q w x}.Infinite} = ⋂ n, U n from
    heq ▸ IsGδ.iInter_of_isOpen ho
  ext x
  simp only [U, mem_ofPred_eq, mem_iInter, mem_iUnion, Subtype.exists]
  constructor
  · intro hi n
    obtain ⟨t, ht, hcard⟩ := hi.exists_subset_card_eq n
    exact ⟨t, hcard, fun w => ht w.property⟩
  · intro h hf
    obtain ⟨t, hcard, ht⟩ := h (hf.toFinset.card + 1)
    have hsub : t ⊆ hf.toFinset := fun _ hw => hf.mem_toFinset.mpr (ht ⟨_, hw⟩)
    exact Nat.not_succ_le_self _ (hcard ▸ Finset.card_le_card hsub)

/-- A countable family of Gδ requirements can be met simultaneously if each can be met by
replacing its own coordinate and survives changes to finitely many other coordinates. -/
theorem exists_simultaneously {ι : Type u} [Countable ι] [DecidableEq ι]
    (A : ι → Type v) [∀ i, Finite (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
    (P : ι → ((i : ι) → A i) → Prop)
    (hlocal : ∀ i x, ∃ a : A i, P i (Function.update x i a))
    (hfinite : ∀ i x y, x i = y i → Set.Finite {j : ι | x j ≠ y j} → (P i x ↔ P i y))
    (hgdelta : ∀ i, IsGδ {x | P i x}) : ∃ x, ∀ i, P i x := by
  classical
  obtain ⟨B, hB, hpattern⟩ := FinitePalettes.exists_supported_patterns A P hlocal
  let X := (i : ι) → B i
  have (i : ι) : Nonempty (B i) := (hB i).to_subtype
  let lift : X → ((i : ι) → A i) := fun x i => (x i).val
  have hlift : Continuous lift :=
    continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))
  let U (i : ι) : Set X := {x | P i (lift x)}
  have hg : ∀ i, IsGδ (U i) := fun i => (hgdelta i).preimage hlift
  have hd : ∀ i, Dense (U i) := by
    refine fun i => dense_iff_inter_open.mpr ?_
    rintro W hW ⟨x, hx⟩
    have hw : W ∈ 𝓝 x := hW.mem_nhds hx
    rw [nhds_pi] at hw
    simp only [nhds_discrete] at hw
    obtain ⟨F, hF, hsub⟩ := (Filter.hasBasis_pi_pure x).mem_iff.mp hw
    -- Start with the target pattern of `x`, then match its finite neighbourhood.
    obtain ⟨z, hz, hzi, hpz⟩ := hpattern i (x i).val (x i).property
    let y (j : ι) : B j := if j ∈ F then x j else ⟨z j, hz j⟩
    have hyW : y ∈ W := hsub (fun j hj => if_pos hj)
    have hi : z i = lift y i := by
      by_cases hi : i ∈ F <;> simp [lift, y, hi, hzi]
    have hdiff : {j : ι | z j ≠ lift y j}.Finite :=
      hF.subset (fun j hj => by_contra fun hjF => hj (by simp [lift, y, hjF]))
    exact ⟨y, hyW, (hfinite i z (lift y) hi hdiff).mp hpz⟩
  obtain ⟨x, hx⟩ := (dense_iInter_of_Gδ hg hd).nonempty
  exact ⟨lift x, fun i => show x ∈ U i from Set.mem_iInter.mp hx i⟩

end TenChallenges.Continuation.BlockBaire

/- Inlined from Continuation/UnfriendlyCertificateTopology.lean. -/
/-!
# Local dependence of hub certificates

Certification survives finitely many colour changes outside a hub when each changed
hub shares only finitely many pieces with it. The set of certifying colourings is
also a Gδ set in the product of discrete colour spaces.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PieceFamily

variable {V : Type u} {ι : Type v} {G : SimpleGraph V} (D : PieceFamily G ι) (H : Set V)

/-- Changing the colours of finitely many vertices can remove only finitely many
direct opponents and pieces whose boundaries meet both the hub and a changed vertex. -/
theorem certifiedAt_of_finite_changes (c d : V → Bool) (x : V) (hx : c x = d x)
    (hfin : Set.Finite {y | c y ≠ d y})
    (hco : ∀ y ∈ H, c y ≠ d y →
      {i | x ∈ (D.piece i).boundary ∧ y ∈ (D.piece i).boundary}.Finite)
    (hc : D.CertifiedAt H c x) : D.CertifiedAt H d x := by
  rcases hc with hhub | hpiece
  case inr =>
    have hbad : (⋃ y ∈ H ∩ {y | c y ≠ d y},
        {i | x ∈ (D.piece i).boundary ∧ y ∈ (D.piece i).boundary}).Finite :=
      (hfin.subset Set.inter_subset_right).biUnion fun y hy => hco y hy.1 hy.2
    exact Or.inr ((hpiece.sdiff hbad).mono fun i hi =>
      ⟨hi.1.1, (D.piece i).forcedAt_congr c d
        (fun y hy => Classical.byContradiction fun hne =>
          hi.2 (Set.mem_iUnion₂.mpr ⟨y, ⟨hi.1.1 hy, hne⟩, hi.1.2.choose, hy⟩)) x hi.1.2⟩)
  case inl =>
    exact Or.inl ((hhub.sdiff hfin).mono fun y hy =>
      ⟨hy.1.1, hy.1.2.1,
        fun heq => hy.1.2.2 ((Classical.byContradiction hy.2).trans (heq.trans hx.symm))⟩)

private theorem isOpen_of_finite_colours (F : Finset V) (P : (V → Bool) → Prop)
    (h : ∀ c d, Set.EqOn c d (F : Set V) → P c → P d) : IsOpen {c | P c} := by
  exact isOpen_pi_iff.mpr fun c hc =>
    ⟨F, fun y => {c y}, fun y _ => ⟨isOpen_discrete _, rfl⟩,
      fun d hd => h c d (fun y hy => (show d y = c y from hd y hy).symm) hc⟩

open Classical in
/-- The colourings that certify a hub form a Gδ set. -/
theorem isGδ_certifiedAt (x : V) : IsGδ {c : V → Bool | D.CertifiedAt H c x} := by
  apply IsGδ.union
  case ht =>
    exact BlockBaire.isGδ_infinite_witnesses
      (fun i c => ((D.piece i).boundary : Set V) ⊆ H ∧ (D.piece i).ForcedAt c x)
      (fun i => isOpen_of_finite_colours (D.piece i).boundary _
        fun c d h hc => ⟨hc.1, (D.piece i).forcedAt_congr c d h x hc.2⟩)
  case hs =>
    exact BlockBaire.isGδ_infinite_witnesses
      (fun y c => y ∈ G.neighborSet x ∧ y ∈ H ∧ c y ≠ c x)
      (fun y => isOpen_of_finite_colours {y, x} _ fun c d h hc =>
        ⟨hc.1, hc.2.1, fun heq => hc.2.2
          ((h (by simp)).trans (heq.trans (h (by simp)).symm))⟩)

end TenChallenges.Continuation.PieceFamily

/- Inlined from Continuation/UnfriendlyBlockActionCertificates.lean. -/
/-!
# Certification by block actions

An action assigns the colours of a finite block for each possible colouring of
its parent vertices. If each block affects only finitely many later blocks, and
the selected witnesses share finitely with vertices outside the block and its
parents, the finite-action Baire theorem produces simultaneous certificates.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.BlockActionCertificates


variable {V : Type u} {ι : Type v} {G : SimpleGraph V} {T : Set V} {keys : ι → Type w}

open Classical in
private noncomputable def fill (q₀ : V → Bool) (q : T → Bool) (v : V) : Bool :=
  if hv : v ∈ T then q ⟨v, hv⟩ else q₀ v

private theorem fill_apply (q₀ : V → Bool) (q : T → Bool) (x : T) :
    fill q₀ q x.val = q x := dif_pos x.property

private theorem fill_outside (q₀ : V → Bool) (q : T → Bool) {v : V} (hv : v ∉ T) :
    fill q₀ q v = q₀ v := dif_neg hv

open Classical in
private noncomputable def parentOverride (N : BlockAssembly.Network T ι) (i : ι)
    (p : N.parents i → Bool) (x : T) : Option Bool :=
  if hx : x ∈ N.parents i then some (p ⟨x, hx⟩) else none

private noncomputable def assembled (N : BlockAssembly.Network T ι) (q₀ : V → Bool)
    (i : ι) (p : N.parents i → Bool) (actions : N.Assignment) : V → Bool :=
  fill q₀ (N.assemble actions (parentOverride N i p))

private def Good (N : BlockAssembly.Network T ι) (D : ∀ i, PieceFamily G (keys i))
    (H : Set V) (q₀ : V → Bool) (i : ι) (actions : N.Assignment) : Prop :=
  ∀ (p : N.parents i → Bool) (x : N.Vertices i), (D i).CertifiedAt H
    (assembled N q₀ i p actions) x.val.val

private theorem assembled_parent (N : BlockAssembly.Network T ι) (q₀ : V → Bool)
    (i : ι) (p : N.parents i → Bool) (actions : N.Assignment) (x : N.parents i) :
    assembled N q₀ i p actions x.val.val = p x := by
  rw [assembled, fill_apply, N.assemble_eq]
  simp only [parentOverride, dif_pos x.property, Option.getD_some]

private theorem parent_owner_ne (N : BlockAssembly.Network T ι) (i : ι) (x : N.parents i) :
    N.owner x.val ≠ i := fun h =>
  N.wf.irrefl.irrefl i ((congrArg (fun j => N.lt j i) h).mp (N.parent_lt i x))

private theorem assembled_block (N : BlockAssembly.Network T ι) (q₀ : V → Bool)
    (i : ι) (p : N.parents i → Bool) (actions : N.Assignment) (x : N.Vertices i) :
    assembled N q₀ i p actions x.val.val = actions i p x := by
  obtain ⟨x, howner⟩ := x
  subst i
  have hx : x ∉ N.parents (N.owner x) := fun hx => parent_owner_ne N _ ⟨x, hx⟩ rfl
  have hp : (fun y : N.parents (N.owner x) =>
      N.assemble actions (parentOverride N (N.owner x) p) y.val) = p :=
    funext fun y => (fill_apply q₀ _ y.val).symm.trans
      (assembled_parent N q₀ (N.owner x) p actions y)
  rw [assembled, fill_apply, N.assemble_eq]
  simp only [parentOverride, dif_neg hx, Option.getD_none]
  rw [hp]

private theorem certified_transfer (N : BlockAssembly.Network T ι) (D : ∀ i, PieceFamily G (keys i))
    (H : Set V) (i : ι) (c d : V → Bool) (x : N.Vertices i)
    (hshare : ∀ y : T, N.owner y ≠ i → y ∉ N.parents i →
      {j | x.val.val ∈ ((D i).piece j).boundary ∧ y.val ∈ ((D i).piece j).boundary}.Finite)
    (hout : Set.EqOn c d Tᶜ)
    (hblock : ∀ u : N.Vertices i, c u.val.val = d u.val.val)
    (hparent : ∀ u : N.parents i, c u.val.val = d u.val.val)
    (hdiff : Set.Finite {v | c v ≠ d v}) (hc : (D i).CertifiedAt H c x.val.val) :
    (D i).CertifiedAt H d x.val.val := by
  refine (D i).certifiedAt_of_finite_changes H c d _ (hblock x) hdiff ?_ hc
  intro v _ hv
  have hvT : v ∈ T := Classical.byContradiction fun h => hv (hout h)
  let y : T := ⟨v, hvT⟩
  exact hshare y (fun h => hv (hblock ⟨y, h⟩)) (fun h => hv (hparent ⟨y, h⟩))

private theorem finite_assembly_changes (N : BlockAssembly.Network T ι) (q₀ : V → Bool)
    (hfinite : ∀ i, {x : T | N.owner x = i}.Finite)
    (hclosure : ∀ i, ∃ C : Set ι, C.Finite ∧ i ∈ C ∧ N.ForwardClosed C)
    (a b : N.Assignment) (override : T → Option Bool)
    (hf : Set.Finite {i | a i ≠ b i}) :
    Set.Finite {v | fill q₀ (N.assemble a override) v ≠ fill q₀ (N.assemble b override) v} := by
  choose closures hfC hiC hclosed using hclosure
  let C := ⋃ i ∈ {j | a j ≠ b j}, closures i
  have hC : C.Finite := hf.biUnion fun j _ => hfC j
  have hforward : N.ForwardClosed C := fun i p h =>
    let ⟨j, hj, hp⟩ := Set.mem_iUnion₂.mp h
    Set.mem_iUnion₂.mpr ⟨j, hj, hclosed j i p hp⟩
  have hact : ∀ i ∉ C, a i = b i := fun i hi =>
    Classical.byContradiction fun h => hi (Set.mem_iUnion₂.mpr ⟨i, h, hiC i⟩)
  have hagree := N.assemble_eqOn_outside a b override hforward hact
  have hverts : {x : T | N.owner x ∈ C}.Finite :=
    (hC.biUnion fun j _ => hfinite j).subset fun x hx =>
      Set.mem_iUnion₂.mpr ⟨N.owner x, hx, rfl⟩
  refine (hverts.image Subtype.val).subset ?_
  intro v hv
  have hvT : v ∈ T := Classical.byContradiction fun h =>
    hv ((fill_outside q₀ _ h).trans (fill_outside q₀ _ h).symm)
  let x : T := ⟨v, hvT⟩
  refine ⟨x, ?_, rfl⟩
  exact Classical.byContradiction fun h => hv
    ((fill_apply q₀ _ x).trans ((hagree h).trans (fill_apply q₀ _ x).symm))

private theorem good_of_finite_changes (N : BlockAssembly.Network T ι) (D : ∀ i, PieceFamily G (keys i))
    (H : Set V) (q₀ : V → Bool) (i : ι)
    (hfinite : ∀ i, {x : T | N.owner x = i}.Finite)
    (hclosure : ∀ i, ∃ C : Set ι, C.Finite ∧ i ∈ C ∧ N.ForwardClosed C)
    (hshare : ∀ x y : T, N.owner x = i → N.owner y ≠ i → y ∉ N.parents i →
      {j | x.val ∈ ((D i).piece j).boundary ∧ y.val ∈ ((D i).piece j).boundary}.Finite)
    (a b : N.Assignment) (hi : a i = b i) (hf : Set.Finite {j | a j ≠ b j})
    (ha : Good N D H q₀ i a) : Good N D H q₀ i b := by
  intro p x
  refine certified_transfer N D H i (assembled N q₀ i p a) (assembled N q₀ i p b)
    x (hshare x.val · x.property) ?_ ?_ ?_
    (finite_assembly_changes N q₀ hfinite hclosure a b (parentOverride N i p) hf) (ha p x)
  · exact fun _ hv => (fill_outside q₀ _ hv).trans (fill_outside q₀ _ hv).symm
  · exact fun y => (assembled_block N q₀ i p a y).trans
      ((congrFun (congrFun hi p) y).trans (assembled_block N q₀ i p b y).symm)
  · exact fun y => (assembled_parent N q₀ i p a y).trans (assembled_parent N q₀ i p b y).symm

private theorem local_repair [DecidableEq ι] (N : BlockAssembly.Network T ι)
    (D : ∀ i, PieceFamily G (keys i)) (H : Set V) (q₀ : V → Bool) (i : ι)
    (hfinite : ∀ i, {x : T | N.owner x = i}.Finite)
    (hclosure : ∀ i, ∃ C : Set ι, C.Finite ∧ i ∈ C ∧ N.ForwardClosed C)
    (hsup : ∀ x : N.Vertices i, (D i).Supplied H x.val.val)
    (hshare : ∀ x y : T, N.owner x = i → N.owner y ≠ i → y ∉ N.parents i →
      {j | x.val ∈ ((D i).piece j).boundary ∧ y.val ∈ ((D i).piece j).boundary}.Finite)
    (actions : N.Assignment) :
    ∃ a : N.Action i, Good N D H q₀ i (Function.update actions i a) := by
  classical
  let B : Set V := Subtype.val '' {x : T | N.owner x = i}
  have hB : B.Finite := (hfinite i).image Subtype.val
  have hBT : B ⊆ T := fun _ ⟨x, _, eq⟩ => eq ▸ x.property
  have supplies : ∀ v ∈ B, (D i).Supplied H v :=
    fun _ ⟨x, hx, eq⟩ => eq ▸ hsup ⟨x, hx⟩
  let initial (p : N.parents i → Bool) := assembled N q₀ i p actions
  have repair (p : N.parents i → Bool) :
      ∃ c, (∀ v, v ∉ B → c v = initial p v) ∧ ∀ v ∈ B, (D i).CertifiedAt H c v :=
    (D i).exists_certified_of_finite_defect H B (initial p) supplies (hB.subset fun _ hv => hv.1)
  choose repaired hfixed hcert using repair
  let output : N.Action i := fun p x => repaired p x.val.val
  let modified := Function.update actions i output
  refine ⟨output, fun p x => ?_⟩
  let post := assembled N q₀ i p modified
  have hA : {j | actions j ≠ modified j}.Finite :=
    (Set.finite_singleton i).subset fun j hj =>
      Classical.byContradiction fun hn => hj (Function.update_of_ne hn _ _).symm
  have hpost : {v | initial p v ≠ post v}.Finite :=
    finite_assembly_changes N q₀ hfinite hclosure actions modified (parentOverride N i p) hA
  have hdiff : {v | repaired p v ≠ post v}.Finite :=
    (hB.union hpost).subset fun v hv => (Classical.em (v ∈ B)).elim Or.inl
      (fun hvB => Or.inr (fun he => hv ((hfixed p v hvB).trans he)))
  have hout : Set.EqOn (repaired p) post Tᶜ := fun v hv =>
    (hfixed p v (fun hb => hv (hBT hb))).trans
      ((fill_outside q₀ (N.assemble actions (parentOverride N i p)) hv).trans
        (fill_outside q₀ (N.assemble modified (parentOverride N i p)) hv).symm)
  have hblock : ∀ y : N.Vertices i, repaired p y.val.val = post y.val.val := fun y =>
    ((assembled_block N q₀ i p modified y).trans
      (congrFun (congrFun (Function.update_self i output actions) p) y)).symm
  have hparent : ∀ y : N.parents i, repaired p y.val.val = post y.val.val := fun y =>
    let hyB : y.val.val ∉ B := fun ⟨z, hz, he⟩ =>
      parent_owner_ne N i y ((congrArg N.owner (Subtype.ext he)).symm.trans hz)
    (hfixed p y.val.val hyB).trans
      ((assembled_parent N q₀ i p actions y).trans (assembled_parent N q₀ i p modified y).symm)
  exact certified_transfer N D H i (repaired p) post x (hshare x.val · x.property)
    hout hblock hparent hdiff (hcert p x.val.val ⟨x.val, x.property, rfl⟩)

private theorem continuous_fill (q₀ : V → Bool) : Continuous (fill (T := T) q₀) := by
  refine continuous_pi fun v => ?_
  by_cases hv : v ∈ T
  · simpa only [fill, dif_pos hv] using (continuous_apply (⟨v, hv⟩ : T) :
      Continuous (fun q : T → Bool => q ⟨v, hv⟩))
  · simpa only [fill, dif_neg hv] using (continuous_const (y := q₀ v) :
      Continuous (fun _ : T → Bool => q₀ v))

private theorem good_isGδ (N : BlockAssembly.Network T ι) (D : ∀ i, PieceFamily G (keys i))
    (H : Set V) (q₀ : V → Bool) (i : ι) [∀ j, Finite (N.Vertices j)] :
    IsGδ {actions : N.Assignment | Good N D H q₀ i actions} := by
  let S (p : N.parents i → Bool) (x : N.Vertices i) : Set N.Assignment :=
    {a | (D i).CertifiedAt H (assembled N q₀ i p a) x.val.val}
  rw [show {a | Good N D H q₀ i a} = ⋂ p, ⋂ x, S p x from Set.ext fun a => by simp [Good, S]]
  refine IsGδ.iInter fun p => IsGδ.iInter fun x => ?_
  exact ((D i).isGδ_certifiedAt H x.val.val).preimage
    ((continuous_fill q₀).comp (N.continuous_assemble (parentOverride N i p)))

private theorem ordinary_eq_overridden (N : BlockAssembly.Network T ι) (q₀ : V → Bool)
    (i : ι) (actions : N.Assignment) :
    assembled N q₀ i (fun p => N.assemble actions (fun _ => none) p.val) actions =
      fill q₀ (N.assemble actions (fun _ => none)) := by
  refine congrArg (fill q₀) (N.assemble_override_eq _ _ ?_)
  intro v b hv
  unfold parentOverride at hv
  split at hv
  · exact Option.some.inj hv
  · cases hv


/-- Choose block actions that certify all target vertices while preserving the prescribed
colours outside the target set. -/
theorem exists_certified {V : Type u} {ι : Type v} {G : SimpleGraph V} {T : Set V}
    [Countable ι] {keys : ι → Type w} (N : BlockAssembly.Network T ι)
    (D : ∀ i, PieceFamily G (keys i)) (H : Set V) (q₀ : V → Bool)
    (hfinite : ∀ i, {x : T | N.owner x = i}.Finite)
    (hclosure : ∀ i, ∃ C : Set ι, C.Finite ∧ i ∈ C ∧ N.ForwardClosed C)
    (hsup : ∀ x : T, (D (N.owner x)).Supplied H x.val)
    (hshare : ∀ i (x y : T), N.owner x = i → N.owner y ≠ i → y ∉ N.parents i →
      {j | x.val ∈ ((D i).piece j).boundary ∧ y.val ∈ ((D i).piece j).boundary}.Finite) :
    ∃ q : V → Bool, Set.EqOn q q₀ Tᶜ ∧ ∀ x : T, (D (N.owner x)).CertifiedAt H q x.val := by
  classical
  have (i : ι) : Finite (N.Vertices i) := Set.finite_coe_iff.mpr (hfinite i)
  have (i : ι) : Nonempty (N.Action i) := ⟨fun _ _ => false⟩
  obtain ⟨a, ha⟩ := BlockBaire.exists_simultaneously N.Action (Good N D H q₀)
    (fun i => local_repair N D H q₀ i hfinite hclosure
      (fun x => (congrArg (fun j => (D j).Supplied H x.val.val) x.property).mp (hsup x.val))
      (hshare i))
    (fun i a b hi hdiff =>
      ⟨good_of_finite_changes N D H q₀ i hfinite hclosure (hshare i) a b hi hdiff,
        good_of_finite_changes N D H q₀ i hfinite hclosure (hshare i) b a hi.symm
          (hdiff.subset fun j hj he => hj he.symm)⟩)
    (fun i => good_isGδ N D H q₀ i)
  refine ⟨fill q₀ (N.assemble a (fun _ => none)), fun _ hv => fill_outside _ _ hv, ?_⟩
  intro x
  have hx := ha (N.owner x) (fun p => N.assemble a (fun _ => none) p.val) ⟨x, rfl⟩
  rw [ordinary_eq_overridden] at hx
  exact hx

end TenChallenges.Continuation.BlockActionCertificates

/- Inlined from Continuation/UnfriendlyFreshSupport.lean. -/
/-!
# Support conditions served by fresh witnesses

Over a maximal robust frozen colouring, three kinds of support let a vertex be
served at every finite stage:

* infinitely many neighbours in the target set;
* *piece support*: every finite set of committed vertices is either avoided by the
  boundaries of infinitely many pieces at the vertex, or contains the remaining free
  boundary of infinitely many of them. No bound on the boundary size is assumed.
  Boundaries with at most two free vertices are a special case;
* *pair support*: infinitely many pieces at the vertex whose optimized profile has a
  pair representation, for instance all pieces with at most three boundary vertices.

The resulting extension theorem keeps every colour of the given robust frozen
colouring. It is a special case of the countable unfriendly partition problem and
does not prove the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PieceFamily

open Energy

variable {V : Type u} {ι : Type v} {G : SimpleGraph V} (D : PieceFamily G ι)

/-- Piece support of `x` over the frozen set `S` inside `H`: for every finite set `K`,
infinitely many pieces at `x` have a boundary in `H` that either avoids `K` outside
`S ∪ {x}` or lies in `S ∪ K ∪ {x}`. -/
def PieceSupported (S H : Set V) (x : V) : Prop :=
  ∀ K : Finset V, {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
    ((∀ y ∈ (D.piece i).boundary, y ∈ K → y ∈ S ∨ y = x) ∨
      (∀ y ∈ (D.piece i).boundary, y ∈ S ∨ y ∈ K ∨ y = x))}.Infinite

/-- Infinitely many pieces at `x` with boundary in `H` have a pair representation. -/
def PairSupported (H : Set V) (x : V) : Prop :=
  {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
    ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ),
      PairProfile.Represents (D.piece i).profile K a}.Infinite

/-- Support by neighbours in `H`, by pieces, or by pair-profile pieces. -/
def SupportedAt (S H : Set V) (x : V) : Prop :=
  (G.neighborSet x ∩ H).Infinite ∨ D.PieceSupported S H x ∨ D.PairSupported H x

theorem PieceSupported.mono {S S' H : Set V} (hS : S ⊆ S') {x : V}
    (h : D.PieceSupported S H x) : D.PieceSupported S' H x :=
  fun K => (h K).mono fun _ hi => ⟨hi.1, hi.2.1, hi.2.2.imp
    (fun h y hyB hyK => (h y hyB hyK).imp_left fun hy => hS hy)
    (fun h y hyB => (h y hyB).imp_left fun hy => hS hy)⟩

/-- Fresh pieces: every finite set is avoided outside `S ∪ {x}`. -/
theorem pieceSupported_of_fresh (S H : Set V) (x : V)
    (h : ∀ K : Finset V, {i | x ∈ (D.piece i).boundary ∧
      ((D.piece i).boundary : Set V) ⊆ H ∧
        ∀ y ∈ (D.piece i).boundary, y ∈ K → y ∈ S ∨ y = x}.Infinite) :
    D.PieceSupported S H x :=
  fun K => (h K).mono fun _ hi => ⟨hi.1, hi.2.1, Or.inl hi.2.2⟩

open Classical in
/-- Pieces with at most two boundary vertices outside the frozen set. -/
theorem pieceSupported_of_residual_le_two (S H : Set V) (x : V) (hxS : x ∉ S)
    (h : {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
      ((D.piece i).boundary.filter (· ∉ S)).card ≤ 2}.Infinite) :
    D.PieceSupported S H x := by
  intro K
  refine h.mono fun i hi => ?_
  obtain ⟨hxB, hBH, hcard⟩ := hi
  refine ⟨hxB, hBH, ?_⟩
  have hxR : x ∈ (D.piece i).boundary.filter (· ∉ S) := Finset.mem_filter.mpr ⟨hxB, hxS⟩
  have hone : (((D.piece i).boundary.filter (· ∉ S)).erase x).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hxR]
    omega
  by_cases hK : ∃ u ∈ ((D.piece i).boundary.filter (· ∉ S)).erase x, u ∈ K
  · obtain ⟨u, hu, huK⟩ := hK
    refine Or.inr fun y hyB => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · by_cases hyx : y = x
      · exact Or.inr (Or.inr hyx)
      · have hy : y ∈ ((D.piece i).boundary.filter (· ∉ S)).erase x :=
          Finset.mem_erase.mpr ⟨hyx, Finset.mem_filter.mpr ⟨hyB, hyS⟩⟩
        have hyu : y = u := Finset.card_le_one.mp hone y hy u hu
        exact Or.inr (Or.inl (hyu ▸ huK))
  · refine Or.inl fun y hyB hyK => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · refine Or.inr (Classical.byContradiction fun hyx => hK ⟨y, ?_, hyK⟩)
      exact Finset.mem_erase.mpr ⟨hyx, Finset.mem_filter.mpr ⟨hyB, hyS⟩⟩

/-- Pieces with at most three boundary vertices have pair representations. -/
theorem pairSupported_of_card_le_three (H : Set V) (x : V)
    (h : {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).boundary.card ≤ 3}.Infinite) : D.PairSupported H x :=
  h.mono fun i hi => ⟨hi.1, hi.2.1, (D.piece i).exists_pair_representation hi.2.2⟩

/-! ### Consequences of maximality -/

private theorem frozen_neighbors_finite (M S H : Set V) (q : V → Bool) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) : (G.neighborSet x ∩ S).Finite := by
  by_contra hinf
  obtain ⟨q', hq'q, hq'⟩ := Robust.extend_frozen_neighbors G M S q hq x hxS hinf
  exact hxS (hmax (S ∪ {x}) q' (Set.union_subset hSH (Set.singleton_subset_iff.mpr hxH))
    hq' Set.subset_union_left hq'q (Or.inr rfl))

open Classical in
private theorem universal_finite (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (β : Bool) :
    {i | (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x}.Finite := by
  by_contra hinf
  have hr := D.robust_update_of_universal M S q hM hq x hxS β hinf
  exact hxS (hmax (S ∪ {x}) (Function.update q x β)
    (Set.union_subset hSH (Set.singleton_subset_iff.mpr hxH)) hr Set.subset_union_left
    (fun y hy => Function.update_of_ne (fun h : y = x => hxS (h ▸ hy)) _ _) (Or.inr rfl))

open Classical in
private theorem block_finite (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q)
    (A : Finset V) (hA : A.Nonempty) :
    {i | ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).boundary.filter (· ∉ S) = A}.Finite := by
  by_contra hinf
  have hinf' : {i | ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).boundary.filter (· ∉ S) = A}.Infinite := hinf
  obtain ⟨i, hiH, hiA⟩ := hinf'.nonempty
  have hAB : ∀ v ∈ A, v ∈ (D.piece i).boundary ∧ v ∉ S := by
    intro v hv
    rw [← hiA] at hv
    exact Finset.mem_filter.mp hv
  obtain ⟨a, ha⟩ := hA
  obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G M S q hq A (fun v hv => (hAB v hv).2)
    (fun v hv => hH (hiH (Finset.mem_coe.mpr (hAB v hv).1))) hM
    (D.recurrentBlock_of_infinite S A (hinf'.mono fun _ hi => hi.2))
  exact (hAB a ha).2 (hmax (S ∪ (A : Set V)) q'
    (Set.union_subset hSH fun v hv =>
      hiH (Finset.mem_coe.mpr (hAB v (Finset.mem_coe.mp hv)).1))
    hq' Set.subset_union_left hq'q (Or.inr (Finset.mem_coe.mpr ha)))

private theorem pair_finite (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x p : V)
    (hxH : x ∈ H) (hpH : p ∈ H) (hxS : x ∉ S) (hpS : p ∉ S) (hxp : x ≠ p) :
    {i | ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
      (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
      PairProfile.Represents (D.piece i).profile K a ∧ a ⟨x, hx⟩ ⟨p, hp⟩ ≠ 0}.Finite := by
  by_contra hinf
  obtain ⟨q', hq'q, hq'⟩ := D.exists_robust_of_pair M S q hM hq x p hxS hpS hxp hinf
  have hsub : S ∪ {x, p} ⊆ H := by
    rintro y (hy | hy | hy)
    · exact hSH hy
    · exact (show y = x from hy) ▸ hxH
    · exact (show y = p from hy) ▸ hpH
  exact hxS (hmax (S ∪ {x, p}) q' hsub hq' Set.subset_union_left hq'q (Or.inr (Or.inl rfl)))

private theorem favoured_choice (a : ℤ) (ha : a ≠ 0) (b : Bool) :
    PairProfile.Favoured a b (if 0 < a then !b else b) := by
  by_cases hpos : 0 < a
  · rw [if_pos hpos]
    exact Or.inl ⟨hpos, by cases b <;> decide⟩
  · rw [if_neg hpos]
    exact Or.inr ⟨lt_of_le_of_ne (not_lt.mp hpos) ha, rfl⟩

private theorem favoured_choice' (a : ℤ) (ha : a ≠ 0) (b : Bool) :
    PairProfile.Favoured a (if 0 < a then !b else b) b := by
  by_cases hpos : 0 < a
  · rw [if_pos hpos]
    exact Or.inl ⟨hpos, by cases b <;> decide⟩
  · rw [if_neg hpos]
    exact Or.inr ⟨lt_of_le_of_ne (not_lt.mp hpos) ha, rfl⟩

/-! ### Serving the remaining vertices -/

private theorem servable_of_hub (M S H : Set V) (q : V → Bool) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (hhub : (G.neighborSet x ∩ H).Infinite) : D.Servable S H q x := by
  classical
  intro K F c
  let cf : V → Bool := fun y => if y ∈ S then q y else c y
  have hcfS : Set.EqOn cf q S := fun y hy => if_pos hy
  have hcfc : ∀ y, y ∉ S → cf y = c y := fun y hy => if_neg hy
  have hfin := frozen_neighbors_finite M S H q hSH hq hmax x hxH hxS
  obtain ⟨u, ⟨hadj, huH⟩, hunot⟩ :=
    (hhub.sdiff (hfin.union (K ∪ F).finite_toSet)).nonempty
  have huS : u ∉ S := fun h => hunot (Or.inl ⟨hadj, h⟩)
  have huK : u ∉ K :=
    fun h => hunot (Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left _ h)))
  have huF : u ∉ F :=
    fun h => hunot (Or.inr (Finset.mem_coe.mpr (Finset.mem_union_right _ h)))
  have hadj' : G.Adj x u := hadj
  have hxu : x ≠ u := G.ne_of_adj hadj'
  refine ⟨Sum.inl u, Function.update cf u (!cf x), huF, ?_, ?_, ?_⟩
  · intro y hy
    exact (Function.update_of_ne (fun h : y = u => huS (h ▸ hy)) _ _).trans (hcfS hy)
  · intro y hy
    exact (Function.update_of_ne
      (fun h : y = u => huK (h ▸ Finset.mem_coe.mp hy.1)) _ _).trans (hcfc y hy.2)
  · show G.Adj x u ∧ u ∈ H ∧
      Function.update cf u (!cf x) u ≠ Function.update cf u (!cf x) x
    refine ⟨hadj', huH, ?_⟩
    rw [Function.update_self, Function.update_of_ne hxu]
    cases cf x <;> decide

private theorem servable_of_pieceSupported (M S₀ S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hS₀ : S₀ ⊆ S) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (hpiece : D.PieceSupported S₀ H x) : D.Servable S H q x := by
  classical
  intro K F c
  let cf : V → Bool := fun y => if y ∈ S then q y else c y
  have hcfS : Set.EqOn cf q S := fun y hy => if_pos hy
  have hcfc : ∀ y, y ∉ S → cf y = c y := fun y hy => if_neg hy
  -- Only finitely many pieces at `x` have their free boundary inside `K ∪ {x}`.
  have h1 : {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
      ∀ y ∈ (D.piece i).boundary, y ∈ S₀ ∨ y ∈ K ∨ y = x}.Finite := by
    have hU : (⋃ A ∈ ((insert x K).powerset : Set (Finset V)),
        {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
          (D.piece i).boundary.filter (· ∉ S) = A}).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun A _ => ?_
      by_cases hxA : x ∈ A
      · exact (D.block_finite M S H q hM hSH hH hq hmax A ⟨x, hxA⟩).subset
          fun i hi => ⟨hi.2.1, hi.2.2⟩
      · refine Set.Finite.subset Set.finite_empty fun i hi => hxA ?_
        rw [← hi.2.2]
        exact Finset.mem_filter.mpr ⟨hi.1, hxS⟩
    refine hU.subset fun i hi => ?_
    obtain ⟨hxB, hBH, hres⟩ := hi
    refine Set.mem_iUnion₂.mpr ⟨(D.piece i).boundary.filter (· ∉ S), ?_, hxB, hBH, rfl⟩
    refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun y hy => ?_)
    obtain ⟨hyB, hyS⟩ := Finset.mem_filter.mp hy
    rcases hres y hyB with hyS₀ | hyK | hyx
    · exact (hyS (hS₀ hyS₀)).elim
    · exact Finset.mem_insert_of_mem hyK
    · exact hyx ▸ Finset.mem_insert_self x K
  have h2 := D.finite_pieces_meeting F.finite_toSet
  have h3 := D.universal_finite M S H q hM hSH hq hmax x hxH hxS (!cf x)
  obtain ⟨i, ⟨hxB, hBH, hkind⟩, hnot⟩ :=
    ((hpiece K).sdiff ((h1.union h2).union h3)).nonempty
  have hfirst : ∀ y ∈ (D.piece i).boundary, y ∈ K → y ∈ S₀ ∨ y = x :=
    hkind.resolve_right fun h => hnot (Or.inl (Or.inl ⟨hxB, hBH, h⟩))
  have hF : ∀ w ∈ (D.piece i).verts, w ∉ F :=
    fun w hw hwF => hnot (Or.inl (Or.inr ⟨w, Finset.mem_coe.mpr hwF, hw⟩))
  have hnu : ¬ (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x (!cf x)) x :=
    fun h => hnot (Or.inr h)
  -- Since the opposite colour is not universal, the present colour can be served.
  obtain ⟨c₁, hc₁, hforced⟩ : ∃ c₁ : V → Bool, Set.EqOn c₁ cf (S ∪ {x}) ∧
      (D.piece i).ForcedAt c₁ x := by
    rcases (D.piece i).servable_or_universal S cf x hxS hxB with h | h
    · exact h
    · refine (hnu ((D.piece i).universalAt_mono Set.Subset.rfl ?_ x h)).elim
      intro y hy
      rcases hy with hyS | hyx
      · have hne : y ≠ x := fun e => hxS (e ▸ hyS)
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact (hcfS hyS).symm
      · have hyx' : y = x := hyx
        rw [hyx', Function.update_self, Function.update_self]
  obtain ⟨w, hw, -⟩ := (D.piece i).boundary_touch ⟨x, hxB⟩
  let c' : V → Bool := fun y => if y ∈ (D.piece i).boundary then c₁ y else cf y
  refine ⟨Sum.inr ⟨i, ⟨w, hw⟩, ⟨(D.piece i).boundary,
    Finset.mem_powerset.mpr (Finset.Subset.refl _)⟩⟩, c', hF w hw, ?_, ?_, ?_⟩
  · intro y hy
    by_cases hyB : y ∈ (D.piece i).boundary
    · exact (if_pos hyB).trans ((hc₁ (Or.inl hy)).trans (hcfS hy))
    · exact (if_neg hyB).trans (hcfS hy)
  · intro y hy
    by_cases hyB : y ∈ (D.piece i).boundary
    · rcases hfirst y hyB (Finset.mem_coe.mp hy.1) with hyS₀ | hyx
      · exact (hy.2 (hS₀ hyS₀)).elim
      · exact (if_pos hyB).trans ((hc₁ (Or.inr hyx)).trans (hcfc y hy.2))
    · exact (if_neg hyB).trans (hcfc y hy.2)
  · show ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).UniversalAt ((D.piece i).boundary : Set V) c' x
    refine ⟨hBH, fun c₂ hc₂ => ?_⟩
    exact (D.piece i).forcedAt_congr c₁ c₂
      (fun y hy => ((hc₂ hy).trans (if_pos (Finset.mem_coe.mp hy))).symm) x hforced

private theorem servable_of_pairSupported (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (hpair : D.PairSupported H x) : D.Servable S H q x := by
  classical
  intro K F c
  let cf : V → Bool := fun y => if y ∈ S then q y else c y
  have hcfS : Set.EqOn cf q S := fun y hy => if_pos hy
  have hcfc : ∀ y, y ∉ S → cf y = c y := fun y hy => if_neg hy
  have h1 := (D.universal_finite M S H q hM hSH hq hmax x hxH hxS true).union
    (D.universal_finite M S H q hM hSH hq hmax x hxH hxS false)
  have h2 := D.finite_pieces_meeting F.finite_toSet
  -- Only finitely many pieces join `x` to a committed free vertex by a nonzero term.
  have h3 : (⋃ p ∈ (K : Set V), {i | p ∈ H ∧ p ∉ S ∧ x ≠ p ∧
      ∃ (K' : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K' a ∧ a ⟨x, hx⟩ ⟨p, hp⟩ ≠ 0}).Finite := by
    refine Set.Finite.biUnion K.finite_toSet fun p _ => ?_
    by_cases hp : p ∈ H ∧ p ∉ S ∧ x ≠ p
    · exact (D.pair_finite M S H q hM hSH hq hmax x p hxH hp.1 hxS hp.2.1 hp.2.2).subset
        fun i hi => hi.2.2.2
    · exact Set.Finite.subset Set.finite_empty fun i hi => hp ⟨hi.1, hi.2.1, hi.2.2.1⟩
  obtain ⟨i, ⟨hxB, hBH, K', a, hrep⟩, hnot⟩ :=
    (hpair.sdiff ((h1.union h2).union h3)).nonempty
  have hF : ∀ w ∈ (D.piece i).verts, w ∉ F :=
    fun w hw hwF => hnot (Or.inl (Or.inr ⟨w, Finset.mem_coe.mpr hwF, hw⟩))
  have hnu : ∀ β : Bool,
      ¬ (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x := by
    intro β h
    cases β
    · exact hnot (Or.inl (Or.inl (Or.inr h)))
    · exact hnot (Or.inl (Or.inl (Or.inl h)))
  -- No slack: some interaction at `x` is nonzero.
  have hns : ¬ PairProfile.weight a ⟨x, hxB⟩ < 2 * pieceDegree (D.piece i).edges x :=
    fun hslack => hnu true fun c₁ _ =>
      ⟨hxB, (D.piece i).forced_of_slack K' a hrep (fun y => c₁ y.val) ⟨x, hxB⟩ hslack⟩
  obtain ⟨u, hvu, hne⟩ :=
    (D.piece i).exists_interaction_of_not_slack K' a hrep ⟨x, hxB⟩ hns
  have hxu : x ≠ u.val := fun h => hvu (Subtype.ext h)
  have huH : u.val ∈ H := hBH (Finset.mem_coe.mpr u.property)
  -- A frozen partner would force `x` universally with one colour.
  have huS : u.val ∉ S := by
    intro huS
    refine hnu (if 0 < a ⟨x, hxB⟩ u then !q u.val else q u.val) fun c₁ hc₁ => ⟨hxB, ?_⟩
    apply (D.piece i).forced_of_favoured K' a hrep (fun y => c₁ y.val) ⟨x, hxB⟩ u
    have e1 : c₁ x = (if 0 < a ⟨x, hxB⟩ u then !q u.val else q u.val) :=
      (hc₁ (Or.inr rfl)).trans (Function.update_self ..)
    have e2 : c₁ u.val = q u.val :=
      (hc₁ (Or.inl huS)).trans (Function.update_of_ne hxu.symm _ _)
    show PairProfile.Favoured (a ⟨x, hxB⟩ u) (c₁ x) (c₁ u.val)
    rw [e1, e2]
    exact favoured_choice' _ hne _
  have huK : u.val ∉ K := fun huK => hnot (Or.inr (Set.mem_iUnion₂.mpr
    ⟨u.val, Finset.mem_coe.mpr huK, huH, huS, hxu, K', a, hxB, u.property, hrep, hne⟩))
  obtain ⟨w, hw, -⟩ := (D.piece i).boundary_touch ⟨x, hxB⟩
  have hQ : ({x, u.val} : Finset V) ∈ (D.piece i).boundary.powerset := by
    refine Finset.mem_powerset.mpr fun y hy => ?_
    rcases Finset.mem_insert.mp hy with hyx | hy
    · exact hyx ▸ hxB
    · exact (Finset.mem_singleton.mp hy) ▸ u.property
  refine ⟨Sum.inr ⟨i, ⟨w, hw⟩, ⟨{x, u.val}, hQ⟩⟩,
    Function.update cf u.val (if 0 < a ⟨x, hxB⟩ u then !cf x else cf x), hF w hw, ?_, ?_, ?_⟩
  · intro y hy
    exact (Function.update_of_ne (fun h : y = u.val => huS (h ▸ hy)) _ _).trans (hcfS hy)
  · intro y hy
    exact (Function.update_of_ne
      (fun h : y = u.val => huK (h ▸ Finset.mem_coe.mp hy.1)) _ _).trans (hcfc y hy.2)
  · show ((({x, u.val} : Finset V)) : Set V) ⊆ H ∧
      (D.piece i).UniversalAt ((({x, u.val} : Finset V)) : Set V)
        (Function.update cf u.val (if 0 < a ⟨x, hxB⟩ u then !cf x else cf x)) x
    refine ⟨fun y hy => ?_, fun c₂ hc₂ => ⟨hxB, ?_⟩⟩
    · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with hyx | hy
      · exact hyx ▸ hxH
      · exact (Finset.mem_singleton.mp hy) ▸ huH
    · apply (D.piece i).forced_of_favoured K' a hrep (fun y => c₂ y.val) ⟨x, hxB⟩ u
      have e1 : c₂ x = cf x :=
        (hc₂ (by simp)).trans (Function.update_of_ne hxu _ _)
      have e2 : c₂ u.val = (if 0 < a ⟨x, hxB⟩ u then !cf x else cf x) :=
        (hc₂ (by simp)).trans (Function.update_self ..)
      show PairProfile.Favoured (a ⟨x, hxB⟩ u) (c₂ x) (c₂ u.val)
      rw [e1, e2]
      exact favoured_choice _ hne _

/-! ### The extension theorems -/

open Classical in
/-- **Fresh-witness extension with recurrent boundaries.** A robust frozen colouring on
`S` extends to a robust colouring of `H`, keeping every colour on `S`, when each further
vertex of `H` lies in a recurrent finite boundary over `S` or is supported over `S`
together with all such recurrent vertices. -/
theorem extend_robust_of_recurrent [Countable V] (M S H R : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite}) (hq : Robust G M S q)
    (hR : ∀ x ∈ R, ∃ B : Finset V, x ∈ B ∧ (B : Set V) ⊆ H ∧ RecurrentBlock G S B)
    (hsupport : ∀ x ∈ H, x ∉ S → x ∉ R → D.SupportedAt (S ∪ R) H x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M H q' := by
  obtain ⟨S', q', hSS', hS'H, hq'q, hrob, hmax⟩ :=
    exists_maximal_robust_extending G M H S q hSH hq
  -- Recurrent boundaries are absorbed by the maximal frozen colouring.
  have hRS' : R ⊆ S' := by
    intro x hxR
    by_contra hxS'
    obtain ⟨B, hxB, hBH, hB⟩ := hR x hxR
    have hb := RecurrentBlock.relativize G S S' hSS' B hB
    obtain ⟨q'', hq''q', hq''⟩ := Robust.extend_block G M S' q' hrob (B.filter (· ∉ S'))
      (fun y hy => (Finset.mem_filter.mp hy).2)
      (fun y hy => hH (hBH (Finset.mem_coe.mpr (Finset.mem_filter.mp hy).1))) hM hb
    exact hxS' (hmax _ q''
      (Set.union_subset hS'H fun y hy =>
        hBH (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1))
      hq'' Set.subset_union_left hq''q'
      (Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hxB, hxS'⟩))))
  obtain ⟨q'', hq''q', hq''⟩ := D.robust_of_servable M S' H q' hM hS'H hrob
    (fun x hxH hxS' => by
      rcases hsupport x hxH (fun h => hxS' (hSS' h)) (fun h => hxS' (hRS' h)) with
        hhub | hpiece | hpair
      · exact D.servable_of_hub M S' H q' hS'H hrob hmax x hxH hxS' hhub
      · exact D.servable_of_pieceSupported M (S ∪ R) S' H q' hM
          (Set.union_subset hSS' hRS') hS'H hH hrob hmax x hxH hxS' hpiece
      · exact D.servable_of_pairSupported M S' H q' hM hS'H hrob hmax x hxH hxS' hpair)
  exact ⟨q'', fun y hy => (hq''q' (hSS' hy)).trans (hq'q hy), hq''⟩

/-- **Fresh-witness extension.** A robust frozen colouring on `S` extends to a robust
colouring of `H`, keeping every colour on `S`, when each further vertex of `H` is
supported by neighbours in `H`, by pieces, or by pair-profile pieces. -/
theorem extend_robust [Countable V] (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite}) (hq : Robust G M S q)
    (hsupport : ∀ x ∈ H, x ∉ S → D.SupportedAt S H x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M H q' :=
  D.extend_robust_of_recurrent M S H ∅ q hM hSH hH hq (fun _ hx => hx.elim)
    (fun x hxH hxS _ => by simpa only [Set.union_empty] using hsupport x hxH hxS)

/-- **Supported exhaustion.** Suppose that whenever a set `S` of infinite-degree
vertices leaves infinitely many of them outside, there is a nonempty recurrent block
over `S`, or a nonempty set `J` of further infinite-degree vertices each supported
inside `S ∪ J` over `S`. Then the countable graph has an unfriendly partition. A
vertex with infinitely many neighbours in `S`, and a set of vertices each having
infinitely many neighbours in the set, are instances of the second alternative. -/
theorem exists_unfriendly_of_supported_steps [Countable V]
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, D.SupportedAt S (S ∪ J) v)) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {v | (G.neighborSet v).Infinite}ᶜ {v | (G.neighborSet v).Infinite}
  by_cases hfin : ({v | (G.neighborSet v).Infinite} \ S).Finite
  · exact exists_unfriendly_of_robust_cofinite G S q hSH hrob hfin
  · exfalso
    rcases h S hSH hfin with ⟨A, ⟨a, ha⟩, hA, hblock⟩ | ⟨J, ⟨j, hj⟩, hJ, hJsup⟩
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob A
        (fun v hv => (hA v hv).2) (fun v hv => (hA v hv).1)
        (fun x hx hinf => hinf hx) hblock
      exact (hA a ha).2 (hmax (S ∪ (A : Set V)) q'
        (Set.union_subset hSH (fun v hv => (hA v hv).1)) hq' Set.subset_union_left hq'q
        (Or.inr ha))
    · have hH : S ∪ J ⊆ {v | (G.neighborSet v).Infinite} :=
        Set.union_subset hSH (fun v hv => (hJ v hv).1)
      obtain ⟨q', hq'q, hq'⟩ := D.extend_robust {v | (G.neighborSet v).Infinite}ᶜ S
        (S ∪ J) q (fun x hx hinf => hinf hx) Set.subset_union_left hH hrob
        (fun x hx hxS => hJsup x (hx.resolve_left hxS))
      exact (hJ j hj).2 (hmax (S ∪ J) q' hH hq' Set.subset_union_left hq'q (Or.inr hj))

end TenChallenges.Continuation.PieceFamily

/- Inlined from Continuation/UnfriendlyPairWitnessGraph.lean. -/
/-!
# Selected finite components as permanent hub witnesses

Only the selected components need to be finite with at most three boundary
hubs. Other components may be infinite or have arbitrary finite boundaries.
A hub is supported when it has infinitely many hub neighbours or meets
infinitely many selected components. Recurrent full boundaries of arbitrary
size may supply the other hubs. Every conclusion retains the universal
quantifier over strongly maximal completions.

These are special cases of Challenge 10; the unrestricted conjecture remains.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PairWitnessGraph

open Energy ThreeBoundaryGraph

variable {V : Type u}

/-- Finite components whose full boundary has at most three distinct hubs. -/
abbrev SelectedComponent (G : SimpleGraph V) :=
  {C : Component G // C.supp.Finite ∧ (hubBoundary G C).ncard ≤ 3}

noncomputable def selectedPiece (G : SimpleGraph V) (C : SelectedComponent G) :
    FinitePiece G :=
  piece G C.val C.property.1

/-- Infinite support by direct hub neighbours or by selected finite components. -/
def SupportedAt (G : SimpleGraph V) (x : V) : Prop :=
  (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    {C : SelectedComponent G | x ∈ hubBoundary G C.val}.Infinite

private theorem selected_disjoint (G : SimpleGraph V) :
    Pairwise (Function.onFun Disjoint (fun C : SelectedComponent G =>
      (selectedPiece G C).verts)) := by
  classical
  intro C D hCD
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨y, hy, hyx⟩ := (piece_mem G C.val C.property.1 x).mp hxC
  obtain ⟨z, hz, hzx⟩ := (piece_mem G D.val D.property.1 x).mp hxD
  have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
  exact hCD (Subtype.ext
    (SimpleGraph.ConnectedComponent.eq_of_common_vertex hy (hyz.symm ▸ hz)))

private theorem selected_pair (G : SimpleGraph V) (C : SelectedComponent G) :
    ∃ K a, PairProfile.Represents (selectedPiece G C).profile K a := by
  apply (selectedPiece G C).exists_pair_representation
  have h := C.property.2
  rw [← boundary_eq G C.val C.property.1] at h
  simpa only [selectedPiece, Set.ncard_coe_finset] using h

/-- The selected components form a witness system without a coverage assumption. -/
noncomputable def witnessSystem (G : SimpleGraph V) :
    PairWitnessSystem G (SelectedComponent G) := by
  classical
  choose K a ha using selected_pair G
  refine {
    piece := selectedPiece G
    disjoint := selected_disjoint G
    boundary_hub := ?_
    constant := K
    coefficient := a
    representation := ha
  }
  intro C x
  have hx : x.val ∈ hubBoundary G C.val := by
    rw [← boundary_eq G C.val C.property.1]
    exact x.property
  exact hx.1

private theorem support_transfer (G : SimpleGraph V) (x : Hubs G)
    (hx : SupportedAt G x.val) : (witnessSystem G).SupportedAt x := by
  change (G.neighborSet x.val ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    {C : SelectedComponent G | x.val ∈ (selectedPiece G C).boundary}.Infinite
  have hmem : ∀ C : SelectedComponent G,
      x.val ∈ (piece G C.val C.property.1).boundary ↔ x.val ∈ hubBoundary G C.val :=
    fun C => Set.ext_iff.mp (boundary_eq G C.val C.property.1) x.val
  simpa only [SupportedAt, selectedPiece, hmem] using hx

/-- Every hub may use direct neighbours or selected finite components. Other
finite-degree components have no imposed size or boundary condition. -/
theorem exists_robust [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q :=
  (witnessSystem G).exists_robust (fun x => support_transfer G x (h x))

/-- Selected components and recurrent full boundaries of arbitrary size may
supply different hubs of the same graph. -/
theorem exists_robust_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  apply (witnessSystem G).exists_robust_of_recurrent_or_supported
  intro x
  exact (h x).imp_right (support_transfer G x)

private theorem assignment_of_robust [Countable V] (G : SimpleGraph V)
    (q : V → Bool)
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨c, hfix, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {x | (G.neighborSet x).Infinite} q
  have hF : {x | (G.neighborSet x).Infinite}ᶜ = {x | (G.neighborSet x).Finite} :=
    Set.ext fun _ => Set.not_infinite
  refine ⟨fun x => q x.val, ⟨c, hF ▸ hc, fun x => hfix x.property⟩, ?_⟩
  intro d hd hmatch v
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G {x | (G.neighborSet x).Finite} d hd v hN hN
  · exact unfriendly_of_infinite_opposite G d v
      (hq d (hF.symm ▸ hd) (fun x hx => hmatch ⟨x, hx⟩) v hN)

/-- A hub assignment has strongly maximal completions on all finite-degree
vertices, and every such completion is globally unfriendly. -/
theorem exists_hub_assignment [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust G h
  exact assignment_of_robust G q hq

/-- The same universal completion conclusion for the mixed recurrent and
selected-component criterion. -/
theorem exists_hub_assignment_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust_of_recurrent_or_supported G h
  exact assignment_of_robust G q hq

theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment G h
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem exists_unfriendly_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment_of_recurrent_or_supported G h
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly G h)

theorem all_clocks_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly_of_recurrent_or_supported G h)

end TenChallenges.Continuation.PairWitnessGraph

/- Inlined from Continuation/UnfriendlyFreshWitnessGraph.lean. -/
/-!
# Finite components as fresh permanent witnesses

The witness pieces are all finite components of the graph induced on the
finite-degree vertices. Other components may be infinite. A robust frozen hub
colouring is preserved, and every other hub needs one of three supports:

* infinitely many hub neighbours;
* *component support* over the frozen set `S`: every finite set `K` of hubs is, for
  infinitely many finite components at the hub, either avoided outside `S` or large
  enough to contain the rest of the boundary. There is no bound on the number of
  boundary hubs. Components with at most two boundary hubs outside `S`, and hubs that
  share only finitely many components with each other hub, are special cases;
* infinitely many finite components with at most three boundary hubs.

Every conclusion keeps the universal quantifier over strongly maximal completions.
These are special cases of Challenge 10; the unrestricted conjecture remains.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FreshWitnessGraph

open Energy ThreeBoundaryGraph

variable {V : Type u}

/-- Finite components of the graph induced on the finite-degree vertices. -/
abbrev FiniteComponent (G : SimpleGraph V) := {C : Component G // C.supp.Finite}

/-- All finite components, as a family of pairwise disjoint finite pieces. -/
noncomputable def componentFamily (G : SimpleGraph V) :
    PieceFamily G (FiniteComponent G) where
  piece C := piece G C.val C.property
  disjoint := by
    classical
    intro C D hCD
    apply Finset.disjoint_left.mpr
    intro x hxC hxD
    obtain ⟨y, hy, hyx⟩ := (piece_mem G C.val C.property x).mp hxC
    obtain ⟨z, hz, hzx⟩ := (piece_mem G D.val D.property x).mp hxD
    have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
    exact hCD (Subtype.ext
      (SimpleGraph.ConnectedComponent.eq_of_common_vertex hy (hyz.symm ▸ hz)))

private theorem mem_boundary_iff (G : SimpleGraph V) (C : FiniteComponent G) (y : V) :
    y ∈ ((componentFamily G).piece C).boundary ↔ y ∈ hubBoundary G C.val :=
  Set.ext_iff.mp (boundary_eq G C.val C.property) y

private theorem boundary_subset_hubs (G : SimpleGraph V) (C : FiniteComponent G) :
    (((componentFamily G).piece C).boundary : Set V) ⊆ {y | (G.neighborSet y).Infinite} :=
  fun y hy => ((mem_boundary_iff G C y).mp hy).1

private theorem hubBoundary_finite (G : SimpleGraph V) (C : FiniteComponent G) :
    (hubBoundary G C.val).Finite := by
  rw [← boundary_eq G C.val C.property]
  exact Finset.finite_toSet _

/-- Component support of the hub `x` over the frozen set `S`: for every finite set `K`,
infinitely many finite components at `x` have a hub boundary that either avoids `K`
outside `S ∪ {x}` or lies in `S ∪ K ∪ {x}`. -/
def ComponentSupported (G : SimpleGraph V) (S : Set V) (x : V) : Prop :=
  ∀ K : Finset V, {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
    ((∀ y ∈ hubBoundary G C.val, y ∈ K → y ∈ S ∨ y = x) ∨
      (∀ y ∈ hubBoundary G C.val, y ∈ S ∨ y ∈ K ∨ y = x))}.Infinite

/-- Infinitely many finite components at `x` have at most three boundary hubs. -/
def SmallBoundarySupported (G : SimpleGraph V) (x : V) : Prop :=
  {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
    (hubBoundary G C.val).ncard ≤ 3}.Infinite

/-- The three supports of a hub outside the frozen set `S`. -/
def SupportedAt (G : SimpleGraph V) (S : Set V) (x : V) : Prop :=
  (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    ComponentSupported G S x ∨ SmallBoundarySupported G x

/-- Fresh components: every finite set of hubs is avoided outside `S ∪ {x}`. -/
theorem componentSupported_of_fresh (G : SimpleGraph V) (S : Set V) (x : V)
    (h : ∀ K : Finset V, {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
      ∀ y ∈ hubBoundary G C.val, y ∈ K → y ∈ S ∨ y = x}.Infinite) :
    ComponentSupported G S x :=
  fun K => (h K).mono fun _ hC => ⟨hC.1, Or.inl hC.2⟩

/-- Components with at most two boundary hubs outside the frozen set. The whole
boundary may be arbitrarily large. -/
theorem componentSupported_of_residual_le_two (G : SimpleGraph V) (S : Set V) (x : V)
    (hxS : x ∉ S)
    (h : {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
      (hubBoundary G C.val \ S).ncard ≤ 2}.Infinite) : ComponentSupported G S x := by
  intro K
  refine h.mono fun C hC => ?_
  obtain ⟨hxB, hcard⟩ := hC
  refine ⟨hxB, ?_⟩
  have hfin : (hubBoundary G C.val \ S).Finite :=
    (hubBoundary_finite G C).subset Set.sdiff_subset
  have hthree : ∀ y u, y ∈ hubBoundary G C.val \ S → u ∈ hubBoundary G C.val \ S →
      y ≠ x → u ≠ x → y = u := by
    intro y u hy hu hyx hux
    by_contra hyu
    have hlt : 2 < (hubBoundary G C.val \ S).ncard :=
      (Set.two_lt_ncard_iff hfin).mpr
        ⟨x, y, u, ⟨hxB, hxS⟩, hy, hu, fun h => hyx h.symm, fun h => hux h.symm, hyu⟩
    omega
  by_cases hK : ∃ u ∈ hubBoundary G C.val \ S, u ≠ x ∧ u ∈ K
  · obtain ⟨u, hu, hux, huK⟩ := hK
    refine Or.inr fun y hyB => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · by_cases hyx : y = x
      · exact Or.inr (Or.inr hyx)
      · have hyu : y = u := hthree y u ⟨hyB, hyS⟩ hu hyx hux
        exact Or.inr (Or.inl (hyu ▸ huK))
  · refine Or.inl fun y hyB hyK => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · exact Or.inr (Classical.byContradiction fun hyx => hK ⟨y, ⟨hyB, hyS⟩, hyx, hyK⟩)

/-- A hub on the boundary of infinitely many finite components, sharing only finitely
many of them with each other hub outside the frozen set. -/
theorem componentSupported_of_cooccurrence (G : SimpleGraph V) (S : Set V) (x : V)
    (hinf : {C : FiniteComponent G | x ∈ hubBoundary G C.val}.Infinite)
    (hco : ∀ y, y ∉ S → y ≠ x →
      {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧ y ∈ hubBoundary G C.val}.Finite) :
    ComponentSupported G S x := by
  apply componentSupported_of_fresh
  intro K
  have hbad : (⋃ y ∈ (K : Set V), {C : FiniteComponent G | (y ∉ S ∧ y ≠ x) ∧
      x ∈ hubBoundary G C.val ∧ y ∈ hubBoundary G C.val}).Finite := by
    refine Set.Finite.biUnion K.finite_toSet fun y _ => ?_
    by_cases hy : y ∉ S ∧ y ≠ x
    · exact (hco y hy.1 hy.2).subset fun C hC => hC.2
    · exact Set.Finite.subset Set.finite_empty fun C hC => hy hC.1
  refine (hinf.sdiff hbad).mono fun C hC => ⟨hC.1, fun y hyB hyK => ?_⟩
  by_contra hno
  have hyS : y ∉ S := fun h => hno (Or.inl h)
  have hyx : y ≠ x := fun h => hno (Or.inr h)
  exact hC.2 (Set.mem_iUnion₂.mpr ⟨y, Finset.mem_coe.mpr hyK, ⟨hyS, hyx⟩, hC.1, hyB⟩)

private theorem support_transfer (G : SimpleGraph V) (S : Set V) (x : V)
    (h : SupportedAt G S x) :
    (componentFamily G).SupportedAt S {y | (G.neighborSet y).Infinite} x := by
  rcases h with hhub | hcomp | hsmall
  · exact Or.inl hhub
  · refine Or.inr (Or.inl fun K => (hcomp K).mono fun C hC => ?_)
    refine ⟨(mem_boundary_iff G C x).mpr hC.1, boundary_subset_hubs G C, ?_⟩
    exact hC.2.imp
      (fun h y hyB hyK => h y ((mem_boundary_iff G C y).mp hyB) hyK)
      (fun h y hyB => h y ((mem_boundary_iff G C y).mp hyB))
  · refine Or.inr (Or.inr ((componentFamily G).pairSupported_of_card_le_three _ x
      (hsmall.mono fun C hC => ?_)))
    refine ⟨(mem_boundary_iff G C x).mpr hC.1, boundary_subset_hubs G C, ?_⟩
    have h := hC.2
    rw [← boundary_eq G C.val C.property] at h
    have h' : (piece G C.val C.property).boundary.card ≤ 3 := by
      simpa only [Set.ncard_coe_finset] using h
    exact h'

/-- **Extension with recurrent boundaries.** A robust frozen hub colouring on `S`
extends to all hubs, keeping every colour on `S`, when each further hub lies in a
recurrent finite boundary over `S` or is supported over `S` together with all such
recurrent hubs. -/
theorem extend_robust_of_recurrent [Countable V] (G : SimpleGraph V) (S R : Set V)
    (q : V → Bool) (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (hR : ∀ x ∈ R, ∃ B : Finset V, x ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
      RecurrentBlock G S B)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S → x ∉ R → SupportedAt G (S ∪ R) x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' :=
  (componentFamily G).extend_robust_of_recurrent _ S _ R q (fun _ hx hInf => hInf hx) hS
    Set.Subset.rfl hq
    (fun x hx => let ⟨B, hxB, hBI, hB⟩ := hR x hx
      ⟨B, hxB, fun y hy => hBI y (Finset.mem_coe.mp hy), hB⟩)
    (fun x hxI hxS hxR => support_transfer G (S ∪ R) x (h x hxI hxS hxR))

/-- **Extension of a robust reservoir.** A robust frozen hub colouring on `S` extends
to all hubs, keeping every colour on `S`, when each further hub is supported. -/
theorem extend_robust [Countable V] (G : SimpleGraph V) (S : Set V) (q : V → Bool)
    (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S → SupportedAt G S x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' :=
  extend_robust_of_recurrent G S ∅ q hS hq (fun _ hx => hx.elim)
    (fun x hxI hxS _ => by simpa only [Set.union_empty] using h x hxI hxS)

/-- **Robust reservoir with two residual boundary hubs.** Each hub outside the robust
reservoir `S` has infinitely many hub neighbours or meets infinitely many finite
components with at most two boundary hubs outside `S`. The full boundaries may be
arbitrarily large and the frozen colours on them may be mixed. -/
theorem extend_robust_of_residual_le_two [Countable V] (G : SimpleGraph V) (S : Set V)
    (q : V → Bool) (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S →
      (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
        {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
          (hubBoundary G C.val \ S).ncard ≤ 2}.Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' :=
  extend_robust G S q hS hq fun x hxI hxS => (h x hxI hxS).imp_right
    fun hres => Or.inl (componentSupported_of_residual_le_two G S x hxS hres)

/-- The hubs lying in a finite set of hubs that is the exact outside neighbourhood of
infinitely many pairwise disjoint finite pieces. -/
def recurrentHubs (G : SimpleGraph V) : Set V :=
  {x | ∃ B : Finset V, x ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
    RecurrentBlock G ∅ B}

/-- **Recurrent or supported.** Every hub lies in a recurrent finite boundary or is
supported over the set of all recurrent hubs. -/
theorem exists_robust [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  obtain ⟨q, -, hq⟩ := extend_robust_of_recurrent G ∅ (recurrentHubs G) (fun _ => false)
    (Set.empty_subset _) (fun _ _ _ _ hv => hv.elim) (fun _ hx => hx)
    (fun x hxI _ hxR => by simpa only [Set.empty_union] using h x hxI hxR)
  exact ⟨q, hq⟩

/-- A robust colouring of all hubs is a hub assignment with strongly maximal
completions, each of which is globally unfriendly. -/
theorem hub_assignment_of_robust [Countable V] (G : SimpleGraph V) (q : V → Bool)
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q) :
    (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
      ∀ x : Hubs G, c x.val = q x.val) ∧
    ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
      (∀ x : Hubs G, c x.val = q x.val) →
      ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨c, hfix, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {x | (G.neighborSet x).Infinite} q
  have hF : {x | (G.neighborSet x).Infinite}ᶜ = {x | (G.neighborSet x).Finite} :=
    Set.ext fun _ => Set.not_infinite
  refine ⟨⟨c, hF ▸ hc, fun x => hfix x.property⟩, ?_⟩
  intro d hd hmatch v
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G {x | (G.neighborSet x).Finite} d hd v hN hN
  · exact unfriendly_of_infinite_opposite G d v
      (hq d (hF.symm ▸ hd) (fun x hx => hmatch ⟨x, hx⟩) v hN)

/-- **Universal completions over a robust reservoir.** The reservoir colours are kept,
strongly maximal completions of the resulting hub assignment exist, and every such
completion is globally unfriendly. -/
theorem exists_hub_assignment_extending [Countable V] (G : SimpleGraph V) (S R : Set V)
    (q : V → Bool) (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (hR : ∀ x ∈ R, ∃ B : Finset V, x ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
      RecurrentBlock G S B)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S → x ∉ R → SupportedAt G (S ∪ R) x) :
    ∃ a : Hubs G → Bool, (∀ x : Hubs G, x.val ∈ S → a x = q x.val) ∧
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = a x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = a x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q', hq'q, hq'⟩ := extend_robust_of_recurrent G S R q hS hq hR h
  obtain ⟨hex, hall⟩ := hub_assignment_of_robust G q' hq'
  exact ⟨fun x => q' x.val, fun x hx => hq'q hx, hex, hall⟩

/-- **Universal completions.** Under the recurrent-or-supported criterion, a hub
assignment has strongly maximal completions on all finite-degree vertices, and every
such completion is globally unfriendly. -/
theorem exists_hub_assignment [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∃ a : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = a x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = a x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust G h
  obtain ⟨hex, hall⟩ := hub_assignment_of_robust G q hq
  exact ⟨fun x => q x.val, hex, hall⟩

theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment G h
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly G h)

/-- **Supported exhaustion for finite components.** Whenever a set `S` of hubs leaves
infinitely many hubs outside, there is a nonempty recurrent block over `S`, or a
nonempty set `J` of further hubs each supported inside `S ∪ J` over `S` by neighbours
or finite components. Then the graph has an unfriendly partition. -/
theorem exists_unfriendly_of_supported_steps [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, (componentFamily G).SupportedAt S (S ∪ J) v)) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v :=
  (componentFamily G).exists_unfriendly_of_supported_steps h

theorem all_clocks_of_supported_steps [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, (componentFamily G).SupportedAt S (S ∪ J) v)) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly_of_supported_steps G h)

/-- With every finite-degree component finite, a hub with finitely many hub neighbours
lies on the boundary of infinitely many components. -/
private theorem infinite_components_at (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (x : V)
    (hx : (G.neighborSet x).Infinite)
    (hhub : ¬ (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite) :
    {C : FiniteComponent G | x ∈ hubBoundary G C.val}.Infinite := by
  intro hfin
  have hHF := Set.not_infinite.mp hhub
  have hP : (⋃ C ∈ {C : FiniteComponent G | x ∈ hubBoundary G C.val},
      (((componentFamily G).piece C).verts : Set V)).Finite :=
    hfin.biUnion fun C _ => Finset.finite_toSet _
  apply hx ((hHF.union hP).subset ?_)
  intro w hw
  by_cases hwI : (G.neighborSet w).Infinite
  · exact Or.inl ⟨hw, hwI⟩
  · have hwF : (G.neighborSet w).Finite := Set.not_infinite.mp hwI
    let y : {z : V // (G.neighborSet z).Finite} := ⟨w, hwF⟩
    let C : FiniteComponent G :=
      ⟨(finiteGraph G).connectedComponentMk y, hfinite _⟩
    have hyC : y ∈ C.val.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    have hxC : x ∈ hubBoundary G C.val := ⟨hx, y, hyC, hw⟩
    have hwC : w ∈ ((componentFamily G).piece C).verts :=
      (piece_mem G C.val C.property w).mpr ⟨y, hyC, rfl⟩
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨C, hxC, Finset.mem_coe.mpr hwC⟩)

/-- **Finite co-occurrence.** Every finite-degree component is finite, with no bound on
its size or on the number of its boundary hubs, and any two hubs lie together on the
boundary of only finitely many components. Then some hub assignment has strongly
maximal completions, and every such completion is globally unfriendly. -/
theorem exists_hub_assignment_of_finite_cooccurrence [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hco : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → x ≠ y →
      {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∃ a : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = a x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = a x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  apply exists_hub_assignment G
  intro x hxI _
  by_cases hhub : (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite
  · exact Or.inl hhub
  · refine Or.inr (Or.inl (componentSupported_of_cooccurrence G _ x
      (infinite_components_at G hfinite x hxI hhub) fun y _ hyx => ?_))
    by_cases hyI : (G.neighborSet y).Infinite
    · exact ((hco x y hxI hyI (Ne.symm hyx)).preimage
        Subtype.val_injective.injOn).subset fun C hC => hC
    · exact Set.Finite.subset Set.finite_empty fun C hC => hyI hC.2.1

theorem exists_unfriendly_of_finite_cooccurrence [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hco : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → x ≠ y →
      {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ :=
    exists_hub_assignment_of_finite_cooccurrence G hfinite hco
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks_of_finite_cooccurrence [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hco : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → x ≠ y →
      {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly_of_finite_cooccurrence G hfinite hco)

end TenChallenges.Continuation.FreshWitnessGraph

/- Inlined from Continuation/UnfriendlyFiniteKernel.lean. -/
/-!
# Finite exceptional sets of hubs

Two hubs can share infinitely many finite-degree components. Suppose a finite
set meets every such pair. First choose compatible colours for all hubs outside
this set, using a countable sequence of permanent witnesses. Then repair the
finite set. No initial hub colouring is assumed.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FiniteKernel

open Energy ThreeBoundaryGraph FreshWitnessGraph

variable {V : Type u} {ι : Type v} {G : SimpleGraph V}

private abbrev Agrees (A : Set (V × Bool)) (c : V → Bool) :=
  ∀ {x b}, (x, b) ∈ A → c x = b

/-- A consistent partial assignment whose assigned vertices satisfy `P` in every completion. -/
private def Sound (P : (V → Bool) → V → Prop) (A : Set (V × Bool)) : Prop :=
  (∀ {x a b}, (x, a) ∈ A → (x, b) ∈ A → a = b) ∧
  ∀ c, Agrees A c → ∀ {x b}, (x, b) ∈ A → P c x

private def entries (S : Set V) (q : V → Bool) : Set (V × Bool) :=
  {z | z.1 ∈ S ∧ z.2 = q z.1}

private theorem sound_entries (P : (V → Bool) → V → Prop) (S : Set V) (q : V → Bool)
    (h : ∀ c, Set.EqOn c q S → ∀ x ∈ S, P c x) : Sound P (entries S q) :=
  ⟨fun ha hb => ha.2.trans hb.2.symm, fun c hc x _ hx =>
    h c (fun y hy => hc (show (y, q y) ∈ entries S q from ⟨hy, rfl⟩)) x hx.1⟩

private theorem maximal_sound (P : (V → Bool) → V → Prop) (A₀ : Set (V × Bool)) (h₀ : Sound P A₀) :
    ∃ A, A₀ ⊆ A ∧ Maximal (Sound P) A := by
  apply zorn_subset_nonempty {A | Sound P A} _ A₀ h₀
  intro L hL hchain _
  refine ⟨⋃₀ L, ⟨?_, ?_⟩, fun _ h => Set.subset_sUnion_of_mem h⟩
  · rintro x a b ⟨A, hA, ha⟩ ⟨B, hB, hb⟩
    obtain ⟨C, hC, hAC, hBC⟩ := hchain.directedOn A hA B hB
    exact (hL hC).1 (hAC ha) (hBC hb)
  · rintro c hc x b ⟨A, hA, ha⟩
    exact (hL hA).2 c (fun {y d} hd => hc (Set.mem_sUnion_of_mem hd hA)) ha

open Classical in
private theorem other_colour (P : (V → Bool) → V → Prop)
    (repair : ∀ c x, ¬ P c x → P (Function.update c x (!c x)) x)
    (S : Set V) (q : V → Bool) (x : V) (hx : x ∉ S) (b : Bool)
    (hn : ¬ ∃ f, Set.EqOn f q S ∧ f x = b ∧ P f x) (c : V → Bool)
    (hc : Set.EqOn c q S) (hcx : c x = !b) : P c x := by
  let f := Function.update c x b
  have hf : Set.EqOn f q S := fun z hz =>
    (Function.update_of_ne (fun e : z = x => hx (e ▸ hz)) _ _).trans (hc hz)
  have hb : ¬ P f x := fun h => hn ⟨f, hf, Function.update_self .., h⟩
  simpa only [f, Function.update_self, Function.update_idem, ← hcx, Function.update_eq_self]
    using repair f x hb

open Classical in
/-- Freeze universally valid colours. Outside a maximal such assignment, each of the
two colours occurs in some completion satisfying the vertex requirement. -/
private theorem freeze (P : (V → Bool) → V → Prop)
    (repair : ∀ c x, ¬ P c x → P (Function.update c x (!c x)) x)
    (K : Set V) (q₀ : V → Bool) (init : ∀ c, Set.EqOn c q₀ K → ∀ x ∈ K, P c x) :
    ∃ (S : Set V) (q : V → Bool), K ⊆ S ∧ Set.EqOn q q₀ K ∧
      (∀ c, Set.EqOn c q S → ∀ x ∈ S, P c x) ∧
      ∀ x ∉ S, ∀ b, ∃ c, Set.EqOn c q S ∧ c x = b ∧ P c x := by
  obtain ⟨A, hKA, hmax⟩ := maximal_sound P (entries K q₀) (sound_entries P K q₀ init)
  let S := {x : V | ∃ b, (x, b) ∈ A}
  let q := fun x => if h : x ∈ S then Classical.choose h else q₀ x
  have hq : Agrees A q := fun {x b} hb =>
    let h : x ∈ S := ⟨b, hb⟩
    (dif_pos h).trans (hmax.1.1 (Classical.choose_spec h) hb)
  have safe (c : V → Bool) (hc : Set.EqOn c q S) (x : V) (hx : x ∈ S) : P c x :=
    let ⟨_, hb⟩ := hx
    hmax.1.2 c (fun {z a} ha => (hc (show z ∈ S from ⟨a, ha⟩)).trans (hq ha)) hb
  have maximal (T : Set V) (d : V → Bool) (hST : S ⊆ T) (hd : Set.EqOn d q S)
      (hgood : ∀ c, Set.EqOn c d T → ∀ x ∈ T, P c x) : T ⊆ S := by
    have sub : A ⊆ entries T d := fun ⟨x, b⟩ hb =>
      let hx : x ∈ S := ⟨b, hb⟩
      ⟨hST hx, ((hd hx).trans (hq hb)).symm⟩
    exact fun y hy => ⟨d y, hmax.2 (sound_entries P T d hgood) sub
      (show (y, d y) ∈ entries T d from ⟨hy, rfl⟩)⟩
  have fixed (x : V) (hx : x ∈ K) : (x, q₀ x) ∈ A := hKA ⟨hx, rfl⟩
  refine ⟨S, q, fun x hx => ⟨q₀ x, fixed x hx⟩, fun x hx => hq (fixed x hx), safe, ?_⟩
  intro x hx b
  by_contra hn
  let d := Function.update q x (!b)
  have hd : Set.EqOn d q S := fun y hy => Function.update_of_ne (fun e : y = x => hx (e ▸ hy)) _ _
  apply hx
  apply maximal (insert x S) d (Set.subset_insert _ _) hd _ (Set.mem_insert x S)
  intro c hc y hy
  have hcs : Set.EqOn c q S := fun z hz => (hc (Set.mem_insert_of_mem _ hz)).trans (hd hz)
  exact hy.elim (fun e : y = x => e ▸ other_colour P repair S q x hx b hn c hcs
    ((hc (Set.mem_insert x S)).trans (Function.update_self ..))) (safe c hcs y)

variable (D : PieceFamily G ι)

private theorem certified_of_witnesses (H : Set V) (hB : ∀ i, ((D.piece i).boundary : Set V) ⊆ H)
    (c : V → Bool) (x : V) (hw : {j | D.Witness H j x c}.Infinite) : D.CertifiedAt H c x := by
  classical
  refine or_iff_not_imp_left.mpr fun hdir hp => ?_
  let U := G.neighborSet x ∩ {y | y ∈ H ∧ c y ≠ c x}
  let I := {i | ((D.piece i).boundary : Set V) ⊆ H ∧ (D.piece i).ForcedAt c x}
  have hall : ((Sum.inl : V → D.WitnessIndex) '' U ∪ ⋃ i ∈ I,
      Set.range (fun t : {w : V // w ∈ (D.piece i).verts} ×
        {Q : Finset V // Q ∈ (D.piece i).boundary.powerset} =>
        (Sum.inr ⟨i, t⟩ : D.WitnessIndex))).Finite :=
    ((Set.not_infinite.mp hdir).image Sum.inl).union (hp.biUnion fun _ _ => Set.finite_range _)
  apply hw (hall.subset ?_)
  rintro (y | ⟨i, t⟩) hj
  · exact Or.inl ⟨y, hj, rfl⟩
  · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, ⟨hB i, hj.2 c (fun _ _ => rfl)⟩, t, rfl⟩)

/-- A witness for the current colour of `x` can avoid all previously committed
vertices outside `S`, including when its component meets several vertices of `K`. -/
private theorem servable_outside (H K S : Set V) (hKS : K ⊆ S) (q : V → Bool) (x : V)
    (hco : ∀ y ∈ H \ K, x ≠ y → {i | x ∈ (D.piece i).boundary ∧ y ∈ (D.piece i).boundary}.Finite)
    (attain : ∀ b, ∃ c, Set.EqOn c q S ∧ c x = b ∧ D.CertifiedAt H c x) :
    D.Servable S H q x := by
  classical
  intro A F t
  obtain ⟨r, hrS, hrx, hc⟩ := attain (t x)
  let p := fun y => if y ∈ (A : Set V) \ S then t y else r y
  have hpS : Set.EqOn p q S := fun y hy =>
    (if_neg (fun h : y ∈ (A : Set V) \ S => h.2 hy)).trans (hrS hy)
  have hpA : Set.EqOn p t ((A : Set V) \ S) := fun _ hy => if_pos hy
  have hpx : p x = r x := (Classical.em (x ∈ (A : Set V) \ S)).elim
    (fun h => (hpA h).trans hrx.symm) (fun h => if_neg h)
  rcases hc with hdir | hpiece
  · obtain ⟨y, ⟨ha, hy, hop⟩, hout⟩ := (hdir.sdiff (A ∪ F).finite_toSet).nonempty
    have hyA : y ∉ A := fun h => hout (Finset.mem_union_left _ h)
    have hpy : p y = r y := if_neg (fun h : y ∈ (A : Set V) \ S => hyA h.1)
    exact ⟨Sum.inl y, p, fun h => hout (Finset.mem_union_right _ h), hpS, hpA,
      ha, hy, fun e => hop (hpy.symm.trans (e.trans hpx))⟩
  · -- Each committed hub outside the frozen set eliminates only finitely many pieces.
    let T : Set V := (A : Set V) ∩ ((H \ S) \ {x})
    have hT : T.Finite := A.finite_toSet.subset Set.inter_subset_left
    have hbad : (⋃ y ∈ T, {i | x ∈ (D.piece i).boundary ∧ y ∈ (D.piece i).boundary}).Finite :=
      hT.biUnion fun y hy => hco y ⟨hy.2.1.1, fun h => hy.2.1.2 (hKS h)⟩ (fun e => hy.2.2 e.symm)
    obtain ⟨i, ⟨hiH, hi⟩, hskip⟩ :=
      (hpiece.sdiff (hbad.union (D.finite_pieces_meeting F.finite_toSet))).nonempty
    have agree : Set.EqOn r p ((D.piece i).boundary : Set V) := by
      intro y hy
      by_cases e : y = x
      · exact e ▸ hpx.symm
      · refine (if_neg (show y ∉ (A : Set V) \ S from ?_)).symm
        exact fun h => hskip (Or.inl (Set.mem_iUnion₂.mpr
          ⟨y, ⟨h.1, ⟨hiH hy, h.2⟩, e⟩, hi.1, hy⟩))
    obtain ⟨w, hw, _⟩ := (D.piece i).boundary_touch ⟨x, hi.1⟩
    exact ⟨Sum.inr ⟨i, ⟨w, hw⟩, ⟨(D.piece i).boundary, Finset.mem_powerset.mpr (Finset.Subset.refl _)⟩⟩,
      p, fun h => hskip (Or.inr ⟨w, h, hw⟩), hpS, hpA, hiH, fun d he =>
        (D.piece i).forcedAt_congr r d (fun y hy => (agree hy).trans (he hy).symm) x hi⟩

/-- Prescribe the colours on `K` and certify all other vertices in `H`. Finiteness
of `K` is only needed later, when repairing the vertices in `K` itself. -/
private theorem certified_off_kernel [Countable V] (H K : Set V) (q₀ : V → Bool)
    (hsup : ∀ x ∈ H, D.Supplied H x)
    (hB : ∀ i, ((D.piece i).boundary : Set V) ⊆ H)
    (hco : ∀ x ∈ H \ K, ∀ y ∈ H \ K, x ≠ y →
      {i | x ∈ (D.piece i).boundary ∧ y ∈ (D.piece i).boundary}.Finite) :
    ∃ q, Set.EqOn q q₀ K ∧ ∀ x ∈ H \ K, D.CertifiedAt H q x := by
  classical
  let P := fun (c : V → Bool) (x : V) => x ∈ H \ K → D.CertifiedAt H c x
  have repair (c : V → Bool) (x : V) (h : ¬ P c x) : P (Function.update c x (!c x)) x :=
    fun hx => D.certifiedAt_update_self H c x (hsup x hx.1) (fun hc => h (fun _ => hc))
  obtain ⟨S, q, hKS, hqK, hsafe, ha⟩ := freeze P repair K q₀
    (fun _ _ _ hx hy => (hy.2 hx).elim)
  have serve (x : V) (hx : x ∈ (H \ K) \ S) : D.Servable S H q x :=
    servable_outside D H K S hKS q x (hco x hx.1) fun b =>
      let ⟨d, hd, he, hP⟩ := ha x hx.2 b
      ⟨d, hd, he, hP hx.1⟩
  obtain ⟨c, hcS, hc⟩ := FreshSelection.exists_fresh_selection S ((H \ K) \ S) q D.witnessKey
    D.witnessSupport (D.Witness H) (D.witness_local H) serve
  exact ⟨c, fun y hy => (hcS (hKS hy)).trans (hqK hy), fun x hx =>
    (Classical.em (x ∈ S)).elim (fun h => hsafe c hcS x h hx)
      (fun h => certified_of_witnesses D H hB c x (hc x ⟨hx, h⟩))⟩

/-- If all finite-degree components are finite, every hub has infinitely many hub
neighbours or lies on the boundary of infinitely many finite-degree components. -/
theorem components_supply (G : SimpleGraph V) (hfinite : ∀ C : Component G, C.supp.Finite)
    (x : V) (hx : (G.neighborSet x).Infinite) :
    (componentFamily G).Supplied {v | (G.neighborSet v).Infinite} x := by
  let H := {v | (G.neighborSet v).Infinite}
  let D := componentFamily G
  refine or_iff_not_imp_left.mpr fun hdir hp => ?_
  let I := {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H}
  have hf : (⋃ i ∈ I, ((D.piece i).verts : Set V)).Finite :=
    hp.biUnion fun i _ => (D.piece i).verts.finite_toSet
  apply hx (((Set.not_infinite.mp hdir).union hf).subset ?_)
  intro y hy
  by_cases h : (G.neighborSet y).Finite
  · let w : {v | (G.neighborSet v).Finite} := ⟨y, h⟩
    let C := (finiteGraph G).connectedComponentMk w
    let i : FiniteComponent G := ⟨C, hfinite C⟩
    have hw : w ∈ C.supp := rfl
    have hb : ((D.piece i).boundary : Set V) = hubBoundary G C := boundary_eq G C (hfinite C)
    have hi : i ∈ I := ⟨(Set.ext_iff.mp hb x).mpr ⟨hx, w, hw, hy⟩,
      fun z hz => ((hb ▸ hz) : z ∈ hubBoundary G C).1⟩
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, (piece_mem G C (hfinite C) y).mpr ⟨w, hw, rfl⟩⟩)
  · exact Or.inl ⟨hy, h⟩

/-- Extend a robust colouring on `R` when, outside `R`, a finite set meets every
pair of hubs that share infinitely many finite-degree components. -/
theorem extend_robust [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (R K : Set V) (hK : K.Finite)
    (q₀ : V → Bool) (hR : R ⊆ {v | (G.neighborSet v).Infinite})
    (h₀ : Robust G {v | (G.neighborSet v).Infinite}ᶜ R q₀)
    (hco : ∀ x ∈ {v | (G.neighborSet v).Infinite} \ (R ∪ K),
      ∀ y ∈ {v | (G.neighborSet v).Infinite} \ (R ∪ K), x ≠ y →
        {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∃ p : V → Bool, Set.EqOn p q₀ R ∧ Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} p := by
  let H := {v | (G.neighborSet v).Infinite}
  let D := componentFamily G
  have hb (C : FiniteComponent G) : ((D.piece C).boundary : Set V) = hubBoundary G C.val :=
    boundary_eq G C.val C.property
  have hbound (C : FiniteComponent G) : ((D.piece C).boundary : Set V) ⊆ H :=
    fun y hy => ((Set.ext_iff.mp (hb C) y).mp hy).1
  have hshare : ∀ x ∈ H \ (R ∪ K), ∀ y ∈ H \ (R ∪ K), x ≠ y →
      {i | x ∈ (D.piece i).boundary ∧ y ∈ (D.piece i).boundary}.Finite :=
    fun x hx y hy hxy => ((hco x hx y hy hxy).preimage Subtype.val_injective.injOn).subset
      fun i hi => ⟨(Set.ext_iff.mp (hb i) x).mp hi.1, (Set.ext_iff.mp (hb i) y).mp hi.2⟩
  obtain ⟨q, hq, hc⟩ := certified_off_kernel D H (R ∪ K) q₀
    (components_supply G hfinite) hbound hshare
  refine D.robust_of_finite_defect Hᶜ R H q₀ q (fun _ hf h => h hf) hR h₀
    (fun _ hy => hq (Or.inl hy)) (fun x hx _ => components_supply G hfinite x hx) (hK.subset ?_)
  intro x hx
  by_contra h
  exact hx.2 (hc x ⟨hx.1.1, fun hrk => hrk.elim hx.1.2 h⟩)

/-- A finite set meets every pair of hubs sharing infinitely many components of
the finite-degree subgraph. If those components are all finite, the graph admits
a hub colouring for which every strongly maximal completion is unfriendly at the hubs. -/
theorem exists_robust [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (K : Set V) (hK : K.Finite)
    (hco : ∀ x ∈ {v | (G.neighborSet v).Infinite} \ K,
      ∀ y ∈ {v | (G.neighborSet v).Infinite} \ K, x ≠ y →
        {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∃ q : V → Bool, Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} q := by
  obtain ⟨q, _, hq⟩ := extend_robust G hfinite ∅ K hK (fun _ => false) (Set.empty_subset _)
    (fun _ _ _ _ h => h.elim) (by simpa only [Set.empty_union] using hco)
  exact ⟨q, hq⟩

/-- A countable graph satisfying the finite exceptional set condition admits an
unfriendly partition. -/
theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (K : Set V) (hK : K.Finite)
    (hco : ∀ x ∈ {v | (G.neighborSet v).Infinite} \ K,
      ∀ y ∈ {v | (G.neighborSet v).Infinite} \ K, x ≠ y →
        {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨q, hq⟩ := exists_robust G hfinite K hK hco
  exact exists_unfriendly_of_robust_cofinite G _ q Set.Subset.rfl hq (by simp)

/-- The finite exceptional set condition gives a winning strategy at every ordinal clock. -/
theorem all_clocks [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (K : Set V) (hK : K.Finite)
    (hco : ∀ x ∈ {v | (G.neighborSet v).Infinite} \ K,
      ∀ y ∈ {v | (G.neighborSet v).Infinite} \ K, x ≠ y →
        {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r :=
  all_clocks_of_global G (exists_unfriendly G hfinite K hK hco)

end TenChallenges.Continuation.FiniteKernel

/- Inlined from Continuation/UnfriendlyFiniteBlocks.lean. -/
/-!
# Finite blocks of hubs

The hubs are partitioned into finite blocks. Hubs in different blocks may
interact, but each such pair shares only finitely many finite-degree components.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FiniteBlocks

open Energy ThreeBoundaryGraph FreshWitnessGraph

variable {V : Type u} {ι : Type v} {κ : Type*} {G : SimpleGraph V} {T : Set V}

private abbrev Pattern (block : T → ι) (i : ι) :=
  {x : T // block x = i} → Bool

private def blockVertices (block : T → ι) (i : ι) : Set V :=
  Subtype.val '' {x : T | block x = i}

private theorem mem_blockVertices (block : T → ι) (i : ι) (x : T) :
    x.val ∈ blockVertices block i ↔ block x = i :=
  ⟨fun ⟨y, hy, he⟩ => (Subtype.ext he : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩

open Classical in
private noncomputable def assemble (q₀ : V → Bool) (block : T → ι)
    (p : (i : ι) → Pattern block i) (x : V) : Bool :=
  if hx : x ∈ T then p (block ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ else q₀ x

private theorem assemble_mem (q₀ : V → Bool) (block : T → ι) (p : (i : ι) → Pattern block i)
    (x : T) :
    assemble q₀ block p x.val = p (block x) ⟨x, rfl⟩ :=
  dif_pos x.property

private theorem assemble_agree (q₀ : V → Bool) (block : T → ι) {p q : (i : ι) → Pattern block i}
    (x : T) (h : p (block x) = q (block x)) :
    assemble q₀ block p x.val = assemble q₀ block q x.val := by
  simpa only [assemble_mem] using congrFun h ⟨x, rfl⟩

private def Good (D : PieceFamily G κ) (H : Set V) (q₀ : V → Bool)
    (block : T → ι) (i : ι) (p : (j : ι) → Pattern block j) : Prop :=
  ∀ x : {x : T // block x = i}, D.CertifiedAt H (assemble q₀ block p) x.val.val

private theorem local_repair [DecidableEq ι] (D : PieceFamily G κ) (H : Set V)
    (q₀ : V → Bool) (block : T → ι) (i : ι)
    (hblock : {x : T | block x = i}.Finite)
    (hsup : ∀ x ∈ blockVertices block i, D.Supplied H x)
    (p : (j : ι) → Pattern block j) :
    ∃ a : Pattern block i, Good D H q₀ block i (Function.update p i a) := by
  let B := blockVertices block i
  have hB : B.Finite := hblock.image Subtype.val
  obtain ⟨c, hkeep, hc⟩ := D.exists_certified_of_finite_defect H B (assemble q₀ block p)
    hsup (hB.subset fun _ hx => hx.1)
  let a : Pattern block i := fun x => c x.val.val
  have eq : assemble q₀ block (Function.update p i a) = c := by
    funext x
    by_cases hx : x ∈ T
    · let u : T := ⟨x, hx⟩
      change assemble q₀ block (Function.update p i a) u.val = c u.val
      rw [assemble_mem]
      by_cases hi : block u = i
      · subst i
        simp [a]
      · rw [Function.update_of_ne hi]
        exact (assemble_mem q₀ block p u).symm.trans
          (hkeep u.val (fun h => hi ((mem_blockVertices block i u).mp h))).symm
    · have hout : x ∉ B := fun ⟨u, _, he⟩ => hx (he ▸ u.property)
      simpa only [assemble, dif_neg hx] using (hkeep x hout).symm
  exact ⟨a, fun x => eq.symm ▸ hc x.val.val ((mem_blockVertices block i x.val).mpr x.property)⟩

private theorem good_of_finite_changes (D : PieceFamily G κ) (H : Set V) (q₀ : V → Bool)
    (block : T → ι) (hblocks : ∀ i, {x : T | block x = i}.Finite)
    (i : ι) (hshare : ∀ x y, block x = i → block y ≠ i →
      {j | x.val ∈ (D.piece j).boundary ∧ y.val ∈ (D.piece j).boundary}.Finite)
    (p q : (j : ι) → Pattern block j) (hi : p i = q i)
    (hfin : {j | p j ≠ q j}.Finite) (hp : Good D H q₀ block i p) :
    Good D H q₀ block i q := by
  intro u
  have same (x : T) (hx : block x = i) :
      assemble q₀ block p x.val = assemble q₀ block q x.val :=
    assemble_agree q₀ block x (hx.symm ▸ hi)
  have changed : {x | assemble q₀ block p x ≠ assemble q₀ block q x}.Finite := by
    refine (hfin.biUnion (fun j _ => (hblocks j).image Subtype.val)).subset ?_
    intro x hx
    by_cases hv : x ∈ T
    · let v : T := ⟨x, hv⟩
      exact Set.mem_iUnion₂.mpr ⟨block v, fun h => hx (assemble_agree q₀ block v h),
        (mem_blockVertices block (block v) v).mpr rfl⟩
    · exact (hx (by simp [assemble, hv])).elim
  apply D.certifiedAt_of_finite_changes H _ _ u.val.val
    (same u.val u.property) changed _ (hp u)
  intro y _ hdiff
  have hy : y ∈ T := Classical.byContradiction fun h => hdiff (by simp [assemble, h])
  exact hshare u.val ⟨y, hy⟩ u.property (fun he => hdiff (same ⟨y, hy⟩ he))

private theorem isGδ_good (D : PieceFamily G κ) (H : Set V) (q₀ : V → Bool)
    (block : T → ι) (i : ι) (hblock : {x : T | block x = i}.Finite) :
    IsGδ {p | Good D H q₀ block i p} := by
  letI : Finite {x : T // block x = i} := Set.finite_coe_iff.mpr hblock
  have hcont : Continuous (assemble q₀ block) := by
    apply continuous_pi
    intro x
    by_cases hx : x ∈ T
    · let u : T := ⟨x, hx⟩
      simpa only [assemble, dif_pos hx, Function.comp_def] using
        (continuous_apply (⟨u, rfl⟩ : {v : T // block v = block u})).comp
          (continuous_apply (block u))
    · simpa only [assemble, dif_neg hx] using
        (continuous_const : Continuous (fun _ : (j : ι) → Pattern block j => q₀ x))
  let S (x : {x : T // block x = i}) := (assemble q₀ block) ⁻¹'
    {c | D.CertifiedAt H c x.val.val}
  rw [show {p | Good D H q₀ block i p} = ⋂ x, S x from Set.ext fun p => by simp [Good, S]]
  exact IsGδ.iInter fun x => (D.isGδ_certifiedAt H x.val.val).preimage hcont

/-- Choose colours on finite blocks of `T` with all outside colours prescribed.
Each block may use its own family of pieces. Every vertex must be supplied by
its block's family, and within that family any other block shares only finitely
many witness pieces with a given vertex of the block. -/
theorem exists_certified_by_blocks [Countable ι] {keys : ι → Type w}
    (D : (i : ι) → PieceFamily G (keys i)) (H : Set V) (q₀ : V → Bool)
    (block : T → ι) (hblocks : ∀ i, {x : T | block x = i}.Finite)
    (hsup : ∀ x : T, (D (block x)).Supplied H x.val)
    (hshare : ∀ i (x y : T), block x = i → block y ≠ i →
      {j | x.val ∈ ((D i).piece j).boundary ∧ y.val ∈ ((D i).piece j).boundary}.Finite) :
    ∃ q : V → Bool, Set.EqOn q q₀ Tᶜ ∧ ∀ x : T, (D (block x)).CertifiedAt H q x.val := by
  classical
  letI (i : ι) : Finite {x : T // block x = i} := Set.finite_coe_iff.mpr (hblocks i)
  letI (i : ι) : Nonempty (Pattern block i) := ⟨fun _ => false⟩
  have supply (i : ι) (x : V) (hx : x ∈ blockVertices block i) : (D i).Supplied H x := by
    obtain ⟨u, hu, rfl⟩ := hx
    exact (show block u = i from hu) ▸ hsup u
  obtain ⟨p, hp⟩ := BlockBaire.exists_simultaneously (Pattern block)
    (fun i => Good (D i) H q₀ block i)
    (fun i => local_repair (D i) H q₀ block i (hblocks i) (supply i))
    (fun i p q hi hf =>
      ⟨good_of_finite_changes (D i) H q₀ block hblocks i (hshare i) p q hi hf,
        good_of_finite_changes (D i) H q₀ block hblocks i (hshare i) q p hi.symm
          (hf.subset fun j hj h => hj h.symm)⟩)
    (fun i => isGδ_good (D i) H q₀ block i (hblocks i))
  exact ⟨assemble q₀ block p, fun _ hx => dif_neg hx, fun x => hp (block x) ⟨x, rfl⟩⟩

/-- Specialize block certification to the family of finite-degree components
which are finite. -/
theorem exists_certified_on [Countable ι] (G : SimpleGraph V) (q₀ : V → Bool)
    (block : T → ι) (hblocks : ∀ i, {x : T | block x = i}.Finite)
    (hsup : ∀ x : T, (componentFamily G).Supplied {v | (G.neighborSet v).Infinite} x.val)
    (hshare : ∀ x y, block x ≠ block y →
      {C : FiniteComponent G | x.val ∈ hubBoundary G C.val ∧ y.val ∈ hubBoundary G C.val}.Finite) :
    ∃ q : V → Bool, Set.EqOn q q₀ Tᶜ ∧
      ∀ x : T, (componentFamily G).CertifiedAt {v | (G.neighborSet v).Infinite} q x.val :=
  exists_certified_by_blocks (fun _ => componentFamily G) _ q₀ block hblocks hsup
    (fun _ x y hx hy => (hshare x y (fun e => hy (e.symm.trans hx))).subset fun C hC =>
      let hb := boundary_eq G C.val C.property
      ⟨(Set.ext_iff.mp hb x.val).mp hC.1, (Set.ext_iff.mp hb y.val).mp hC.2⟩)

/-- Preserve the colours of a robust set `R` and extend its robustness to all
hubs. The remaining hubs, outside a finite exceptional set `K`, use finite
blocks with finite pairwise sharing across blocks. Infinite components of the
finite-degree subgraph are allowed provided every hub outside `R` has enough
hub neighbours or touches infinitely many finite components. -/
theorem extend_robust [Countable ι] (G : SimpleGraph V) (R K : Set V) (q₀ : V → Bool)
    (hR : R ⊆ {v | (G.neighborSet v).Infinite}) (hK : K.Finite)
    (hrob : Robust G {v | (G.neighborSet v).Infinite}ᶜ R q₀)
    (hsup : ∀ x ∈ {v | (G.neighborSet v).Infinite}, x ∉ R →
      (componentFamily G).Supplied {v | (G.neighborSet v).Infinite} x)
    (block : ↑({v | (G.neighborSet v).Infinite} \ (R ∪ K)) → ι)
    (hblocks : ∀ i, {x | block x = i}.Finite)
    (hshare : ∀ x y, block x ≠ block y →
      {C : FiniteComponent G | x.val ∈ hubBoundary G C.val ∧ y.val ∈ hubBoundary G C.val}.Finite) :
    ∃ q : V → Bool, Set.EqOn q q₀ R ∧ Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} q := by
  let H := {v | (G.neighborSet v).Infinite}
  let D := componentFamily G
  obtain ⟨q, hq, hc⟩ := exists_certified_on G q₀ block hblocks
    (fun x => hsup x.val x.property.1 (fun h => x.property.2 (Or.inl h))) hshare
  refine D.robust_of_finite_defect Hᶜ R H q₀ q (fun _ hf h => h hf) hR hrob
    (fun _ hx => hq (fun h => h.2 (Or.inl hx))) hsup (hK.subset ?_)
  intro x hx
  by_contra h
  exact hx.2 (hc ⟨x, hx.1.1, fun hRK => hRK.elim hx.1.2 h⟩)

/-- If two hubs in different finite blocks share only finitely many components
and all finite-degree components are finite, there is a robust hub colouring. -/
theorem exists_robust [Countable V] [Countable ι] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (block : Hubs G → ι)
    (hblocks : ∀ i, {x : Hubs G | block x = i}.Finite)
    (hshare : ∀ x y, block x ≠ block y →
      {C : Component G | x.val ∈ hubBoundary G C ∧ y.val ∈ hubBoundary G C}.Finite) :
    ∃ q : V → Bool, Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} q := by
  let H := {v | (G.neighborSet v).Infinite}
  let D := componentFamily G
  obtain ⟨q, _, hq⟩ := exists_certified_on G (fun _ => false) block hblocks
    (fun x => FiniteKernel.components_supply G hfinite x.val x.property)
    (fun x y h => (hshare x y h).preimage Subtype.val_injective.injOn)
  exact ⟨q, fun d hd heq x hx => D.infinite_opposite_of_certified Hᶜ H (fun _ hf h => h hf)
    q d hd heq x hx (hq ⟨x, hx⟩)⟩

/-- The finite-block co-occurrence condition implies an unfriendly partition. -/
theorem exists_unfriendly [Countable V] [Countable ι] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (block : Hubs G → ι)
    (hblocks : ∀ i, {x : Hubs G | block x = i}.Finite)
    (hshare : ∀ x y, block x ≠ block y →
      {C : Component G | x.val ∈ hubBoundary G C ∧ y.val ∈ hubBoundary G C}.Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨q, hq⟩ := exists_robust G hfinite block hblocks hshare
  exact exists_unfriendly_of_robust_cofinite G _ q Set.Subset.rfl hq (by simp)

/-- The finite-block co-occurrence condition gives a winning strategy at every ordinal clock. -/
theorem all_clocks [Countable V] [Countable ι] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (block : Hubs G → ι)
    (hblocks : ∀ i, {x : Hubs G | block x = i}.Finite)
    (hshare : ∀ x y, block x ≠ block y →
      {C : Component G | x.val ∈ hubBoundary G C ∧ y.val ∈ hubBoundary G C}.Finite) :
    ∀ r : Ordinal.{w}, PartitionerWins G (emptyPartition V) r :=
  all_clocks_of_global G (exists_unfriendly G hfinite block hblocks hshare)

/-- Join two hubs when they share infinitely many finite-degree components. -/
def recurrentSharing (G : SimpleGraph V) : SimpleGraph (Hubs G) where
  Adj x y := x ≠ y ∧ {C : Component G | x.val ∈ hubBoundary G C ∧ y.val ∈ hubBoundary G C}.Infinite
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.mono fun _ hC => ⟨hC.2, hC.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The connected components of the graph of repeatedly sharing hubs can serve as the blocks. -/
theorem exists_unfriendly_of_finite_recurrent_components [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hrec : ∀ C : (recurrentSharing G).ConnectedComponent, C.supp.Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  let R := recurrentSharing G
  have : Countable R.ConnectedComponent :=
    (show Function.Surjective R.connectedComponentMk from fun c => c.ind fun x => ⟨x, rfl⟩).countable
  refine exists_unfriendly G hfinite R.connectedComponentMk (fun i => hrec i) ?_
  intro x y hxy
  refine Set.not_infinite.mp fun hi => hxy (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ?_)
  exact (show R.Adj x y from ⟨fun e => hxy (congrArg R.connectedComponentMk e), hi⟩)

end TenChallenges.Continuation.FiniteBlocks

/- Inlined from Continuation/UnfriendlyFiniteBlockExtensions.lean. -/
/-!
# Finite exceptions to the finite-block criterion

First certify the hubs in the finite blocks with the exceptional hub colours
fixed. Then build a strongly maximal completion and repair the exceptional
hubs by finitely many colour changes.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FiniteBlocks

open Energy ThreeBoundaryGraph FreshWitnessGraph

variable {V : Type u} {ι : Type v}

/-- Complete a certified hub colouring while repairing a finite set of
exceptions and keeping the colours on a prescribed robust set. -/
theorem exists_unfriendly_of_certified [Countable V] {κ : Type*} (G : SimpleGraph V)
    (D : PieceFamily G κ) (R K : Set V) (q₀ q : V → Bool)
    (hR : R ⊆ {v | (G.neighborSet v).Infinite}) (hK : K.Finite)
    (hrob : Robust G {v | (G.neighborSet v).Infinite}ᶜ R q₀) (hq : Set.EqOn q q₀ R)
    (hcert : ∀ x : ↑({v | (G.neighborSet v).Infinite} \ (R ∪ K)),
      D.CertifiedAt {v | (G.neighborSet v).Infinite} q x.val) :
    ∃ c : V → Bool, Set.EqOn c q₀ R ∧ ∀ x, UnfriendlyAt G (fun v => some (c v)) x := by
  let H := {v | (G.neighborSet v).Infinite}
  let E := (H ∩ K) \ R
  have hE : E.Finite := hK.subset fun _ hx => hx.1.2
  obtain ⟨c₀, hmatch, hc₀⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G H q
  have hbase : Set.EqOn c₀ q₀ R := fun _ hx =>
    (hmatch (hR hx)).trans (hq hx)
  obtain ⟨c, hfix, hm, hnew⟩ := finite_hub_stage_preserving G Hᶜ R (fun _ hx h => h (hR hx)) c₀ hc₀ hE.toFinset
    (fun _ hv => let he := hE.mem_toFinset.mp hv; ⟨he.1.1, fun h => h he.1.1, he.2⟩)
  refine ⟨c, hfix.trans hbase, fun x => ?_⟩
  by_cases hx : (G.neighborSet x).Finite
  · exact unfriendlyAt_of_strongMaximal G _ c hm x (fun h => h hx) hx
  · apply unfriendly_of_infinite_opposite G c x
    apply hnew x (fun h => h hx)
    by_cases hr : x ∈ R
    · exact Or.inr (hrob c₀ hc₀ hbase x hr)
    by_cases hk : x ∈ K
    · exact Or.inl (hE.mem_toFinset.mpr ⟨⟨hx, hk⟩, hr⟩)
    exact Or.inr (D.infinite_opposite_of_certified Hᶜ H
      (fun _ hf h => h hf) q c₀ hc₀ hmatch x hx (hcert ⟨x, hx, fun h => h.elim hr hk⟩))

/-- Extend prescribed colours on a robust set of hubs. Every other hub outside
a finite exceptional set must be supplied and belong to a finite block, with
finite pairwise sharing of finite components across blocks. -/
theorem exists_unfriendly_extending [Countable V] [Countable ι] (G : SimpleGraph V)
    (R K : Set V) (q₀ : V → Bool)
    (hR : R ⊆ {v | (G.neighborSet v).Infinite}) (hK : K.Finite)
    (hrob : Robust G {v | (G.neighborSet v).Infinite}ᶜ R q₀)
    (block : ↑({v | (G.neighborSet v).Infinite} \ (R ∪ K)) → ι)
    (hblocks : ∀ i, {x | block x = i}.Finite)
    (hsup : ∀ x : ↑({v | (G.neighborSet v).Infinite} \ (R ∪ K)),
      (componentFamily G).Supplied {v | (G.neighborSet v).Infinite} x.val)
    (hshare : ∀ x y, block x ≠ block y →
      {C : FiniteComponent G | x.val ∈ hubBoundary G C.val ∧ y.val ∈ hubBoundary G C.val}.Finite) :
    ∃ c : V → Bool, Set.EqOn c q₀ R ∧ ∀ x, UnfriendlyAt G (fun v => some (c v)) x := by
  obtain ⟨q, hq, hcert⟩ := exists_certified_on G q₀ block hblocks hsup hshare
  exact exists_unfriendly_of_certified G (componentFamily G) R K q₀ q hR hK hrob
    (fun _ hx => hq (fun h => h.2 (Or.inl hx))) hcert

/-- The finite-block criterion with finite exceptions gives a winning strategy at
every ordinal clock. Supplying components need only be finite at the hubs that
use them. -/
theorem all_clocks_off_finite [Countable V] [Countable ι] (G : SimpleGraph V)
    (K : Set V) (hK : K.Finite)
    (block : ↑({v | (G.neighborSet v).Infinite} \ K) → ι)
    (hblocks : ∀ i, {x | block x = i}.Finite)
    (hsup : ∀ x : ↑({v | (G.neighborSet v).Infinite} \ K),
      (componentFamily G).Supplied {v | (G.neighborSet v).Infinite} x.val)
    (hshare : ∀ x y, block x ≠ block y →
      {C : FiniteComponent G | x.val ∈ hubBoundary G C.val ∧ y.val ∈ hubBoundary G C.val}.Finite) :
    ∀ r : Ordinal.{w}, PartitionerWins G (emptyPartition V) r := by
  have h := exists_unfriendly_extending (ι := ι) G ∅ K (fun _ => false)
    (Set.empty_subset _) hK (fun _ _ _ _ hx => hx.elim)
  let H := {v | (G.neighborSet v).Infinite}
  let restrict (x : ↑(H \ ((∅ : Set V) ∪ K))) : ↑(H \ K) :=
    ⟨x.val, x.property.1, fun h => x.property.2 (Or.inr h)⟩
  have inj : Function.Injective restrict := fun _ _ e => Subtype.ext (congrArg (fun x : ↑(H \ K) => x.val) e)
  obtain ⟨c, _, hc⟩ := h (block ∘ restrict) (fun i => (hblocks i).preimage inj.injOn)
    (fun x => hsup (restrict x)) (fun x y hn => hshare (restrict x) (restrict y) hn)
  exact all_clocks_of_global G ⟨fun v => some (c v), hc⟩

end TenChallenges.Continuation.FiniteBlocks

/- Inlined from Continuation/UnfriendlyRecurrentFamilies.lean. -/
/-!
# Maximal recurrent sets

A recurrent set lies in the boundary of infinitely many pieces. When a vertex
shares infinitely many pieces with only finitely many other vertices, every
recurrent set containing it extends to a finite maximal recurrent set.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.RecurrentFamilies

variable {V : Type u} {I : Type v}

/-- Infinitely many pieces have all vertices of `A` on their boundaries. -/
def Recurrent (boundary : I → Set V) (A : Set V) : Prop :=
  {i | A ⊆ boundary i}.Infinite

/-- Obtain a finite maximal recurrent set by restricting to the closed
neighbourhood of one of its vertices in the graph of repeatedly sharing pairs. -/
theorem exists_finite_maximal (boundary : I → Set V) {A : Set V} (x : V)
    (hx : x ∈ A) (hA : Recurrent boundary A)
    (hfinite : {y | y ≠ x ∧ {i | x ∈ boundary i ∧ y ∈ boundary i}.Infinite}.Finite) :
    ∃ B, A ⊆ B ∧ B.Finite ∧ Maximal (Recurrent boundary) B := by
  let N := insert x {y | y ≠ x ∧ {i | x ∈ boundary i ∧ y ∈ boundary i}.Infinite}
  have hN : N.Finite := hfinite.insert x
  have bound {B : Set V} (hxB : x ∈ B) (hB : Recurrent boundary B) : B ⊆ N := by
    intro y hy
    by_cases e : y = x
    · exact Or.inl e
    · exact Or.inr ⟨e, (show {i | B ⊆ boundary i}.Infinite from hB).mono fun i hi =>
        let h : B ⊆ boundary i := hi
        ⟨h hxB, h hy⟩⟩
  let E := {B : Set V | A ⊆ B ∧ B ⊆ N ∧ Recurrent boundary B}
  have hE : E.Finite := hN.powerset.subset fun _ h => h.2.1
  obtain ⟨B, hB⟩ := hE.exists_maximal ⟨A, Set.Subset.rfl, bound hx hA, hA⟩
  exact ⟨B, hB.1.1, hN.subset hB.1.2.1, hB.1.2.2, fun C hC hBC =>
    hB.2 (show C ∈ E from ⟨hB.1.1.trans hBC, bound (hBC (hB.1.1 hx)) hC, hC⟩) hBC⟩

/-- Each additional vertex meets only finitely many witnesses for a maximal
recurrent set. -/
theorem finite_extra (boundary : I → Set V) {A : Set V}
    (hA : Maximal (Recurrent boundary) A) {y : V} (hy : y ∉ A) :
    {i | A ⊆ boundary i ∧ y ∈ boundary i}.Finite := by
  apply Set.not_infinite.mp
  intro hi
  have hrec : Recurrent boundary (insert y A) :=
    hi.mono fun i h => Set.insert_subset_iff.mpr ⟨h.2, h.1⟩
  exact hy (hA.2 hrec (Set.subset_insert y A) (Set.mem_insert y A))

end TenChallenges.Continuation.RecurrentFamilies

/- Inlined from Continuation/UnfriendlyPieceSharingCover.lean. -/
/-!
# Covers by maximal recurrent sets and singletons

Use the maximal recurrent sets of movable vertices as labels, together with
singleton labels for vertices that do not lie on infinitely many piece
boundaries. The maximal labels are finite when the sharing graph is locally
finite.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PieceSharingCover

open Energy

variable {V : Type u} {κ : Type w} {G : SimpleGraph V} (D : PieceFamily G κ) (T : Set V)

/-- Restrict the boundary of a piece to the movable vertex set. -/
def boundary (j : κ) : Set T := {x | x.val ∈ (D.piece j).boundary}

/-- Two movable vertices share infinitely many pieces if they are adjacent. -/
def sharing : SimpleGraph T where
  Adj x y := x ≠ y ∧ {j | x ∈ boundary D T j ∧ y ∈ boundary D T j}.Infinite
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.mono fun _ hj => ⟨hj.2, hj.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A recurrent set is contained in the boundaries of infinitely many pieces. -/
abbrev Recurrent (A : Set T) : Prop := RecurrentFamilies.Recurrent (boundary D T) A

abbrev MaximalLabel :=
  {A : Finset T // A.Nonempty ∧ Maximal (Recurrent D T) (A : Set T)}

abbrev SingletonLabel := {x : T // ¬ Recurrent D T ({x} : Set T)}

/-- Labels represent either a finite maximal recurrent set or a nonrecurrent singleton. -/
abbrev Labels := MaximalLabel D T ⊕ SingletonLabel D T

/-- The movable vertices represented by a label. -/
def vertices : Labels D T → Set T
  | .inl A => A.val
  | .inr x => {x.val}

private def selected (i : Labels D T) (j : κ) : Prop :=
  match i with
  | .inl A => (A.val : Set T) ⊆ boundary D T j
  | .inr _ => False

/-- The component witnesses associated to a label. -/
abbrev keys (i : Labels D T) := {j : κ // selected D T i j}

/-- The piece family restricted to the witnesses of a label. -/
noncomputable def family (i : Labels D T) : PieceFamily G (keys D T i) where
  piece j := D.piece j.val
  disjoint := fun _ _ h => D.disjoint (fun e => h (Subtype.ext e))

theorem vertices_injective : Function.Injective (vertices D T) := by
  rintro (A | x) (B | y) h
  · exact congrArg Sum.inl (Subtype.ext (Finset.coe_injective h))
  · exact (y.property ((show (A.val : Set T) = {y.val} from h) ▸ A.property.2.1)).elim
  · exact (x.property ((show (B.val : Set T) = {x.val} from h.symm) ▸ B.property.2.1)).elim
  · exact congrArg Sum.inr (Subtype.ext (Set.singleton_injective h))

theorem vertices_nonempty (i : Labels D T) : (vertices D T i).Nonempty :=
  match i with
  | .inl A => Finset.coe_nonempty.mpr A.property.1
  | .inr x => Set.singleton_nonempty x.val

theorem vertices_finite (i : Labels D T) : (vertices D T i).Finite :=
  match i with
  | .inl A => A.val.finite_toSet
  | .inr x => Set.finite_singleton x.val

theorem vertices_pairwise (i : Labels D T) : (vertices D T i).Pairwise (sharing D T).Adj := by
  rcases i with A | x
  · intro a ha b hb hab
    exact ⟨hab, (show {j | (A.val : Set T) ⊆ boundary D T j}.Infinite from A.property.2.1).mono
      fun j hj => let hs : (A.val : Set T) ⊆ boundary D T j := hj; ⟨hs ha, hs hb⟩⟩
  · intro a ha b hb hab
    exact (hab ((show a = x.val from ha).trans (show b = x.val from hb).symm)).elim

/-- Under local finiteness of sharing, the labels cover all movable vertices. -/
theorem exists_mem_vertices (hloc : ∀ x, ((sharing D T).neighborSet x).Finite) (x : T) :
    ∃ i : Labels D T, x ∈ vertices D T i := by
  by_cases hx : Recurrent D T ({x} : Set T)
  · have hnear : {y : T | y ≠ x ∧ {j | x ∈ boundary D T j ∧ y ∈ boundary D T j}.Infinite}.Finite :=
      (hloc x).subset fun _ hy => ⟨hy.1.symm, hy.2⟩
    obtain ⟨A, hsub, hAf, hA⟩ := RecurrentFamilies.exists_finite_maximal
      (boundary D T) x (Set.mem_singleton x) hx hnear
    have hxA : x ∈ A := hsub (Set.mem_singleton x)
    let label : MaximalLabel D T :=
      ⟨hAf.toFinset, hAf.toFinset_nonempty.mpr ⟨x, hxA⟩, hAf.coe_toFinset.symm ▸ hA⟩
    exact ⟨.inl label, hAf.mem_toFinset.mpr hxA⟩
  · exact ⟨.inr ⟨x, hx⟩, Set.mem_singleton x⟩

/-- Every member of a label can use that label's family as its supply. -/
theorem family_supplied (H : Set V) (hbound : ∀ j, ((D.piece j).boundary : Set V) ⊆ H)
    (hsup : ∀ x : T, D.Supplied H x.val) (i : Labels D T) {x : T}
    (hx : x ∈ vertices D T i) : (family D T i).Supplied H x.val := by
  rcases i with A | singleton
  · have : Infinite (keys D T (.inl A)) := Set.infinite_coe_iff.mpr A.property.2.1
    exact Or.inr (Set.infinite_univ.mono fun j _ =>
      ⟨(show (A.val : Set T) ⊆ boundary D T j.val from j.property) hx, hbound j.val⟩)
  · have heq : x = singleton.val := hx
    subst x
    rcases hsup singleton.val with hd | hp
    · exact Or.inl hd
    exact (singleton.property (hp.mono fun _ hj => Set.singleton_subset_iff.mpr hj.1)).elim

/-- Outside vertices touch only finitely many pieces of a label's family. -/
theorem family_finite_extra (i : Labels D T) {y : T} (hy : y ∉ vertices D T i) :
    {j | y.val ∈ ((family D T i).piece j).boundary}.Finite := by
  rcases i with A | singleton
  · have hyA : y ∉ (A.val : Set T) := hy
    have hfinite := RecurrentFamilies.finite_extra (boundary D T) A.property.2 hyA
    exact (hfinite.preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
      fun j hj => ⟨j.property, hj⟩
  · exact Set.finite_empty.subset fun j _ => (j.property : False).elim

/-- A certificate using a restricted family also works for the original family. -/
theorem family_certified (i : Labels D T) (H : Set V) (q : V → Bool) (x : V) :
    (family D T i).CertifiedAt H q x → D.CertifiedAt H q x := by
  rintro (hd | hp)
  · exact Or.inl hd
  refine Or.inr ((hp.image (f := Subtype.val) Subtype.val_injective.injOn).mono ?_)
  rintro _ ⟨j, hj, rfl⟩
  exact hj

end TenChallenges.Continuation.PieceSharingCover

/- Inlined from Continuation/UnfriendlyLocallyFiniteSharing.lean. -/
/-!
# Locally finite sharing of components between hubs

Maximal recurrent sets supply pieces for the hubs they cover. A two-round
distance schedule assigns each remaining hub to one such set. Block actions
depend on their parent colours and have finite influence on the assembly.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.LocallyFiniteSharing

open Energy ThreeBoundaryGraph FreshWitnessGraph PieceSharingCover

variable {V : Type u} {I : Type v}

/-- Prescribed colours extend to a colouring certifying the supplied vertices
of `T` when the graph of repeatedly sharing pieces on `T` is locally finite. -/
theorem exists_certified [Countable V] {G : SimpleGraph V} (D : PieceFamily G I)
    (H T : Set V) (q₀ : V → Bool)
    (hbound : ∀ j, ((D.piece j).boundary : Set V) ⊆ H)
    (hsup : ∀ x : T, D.Supplied H x.val)
    (hloc : ∀ x, ((sharing D T).neighborSet x).Finite) :
    ∃ q : V → Bool, Set.EqOn q q₀ Tᶜ ∧ ∀ x : T, D.CertifiedAt H q x.val := by
  obtain ⟨N, howner, hfinite, hparents, hclosure⟩ := BandSchedule.exists_network
    (sharing D T) hloc (vertices D T) (vertices_injective D T) (vertices_nonempty D T)
    (vertices_pairwise D T) (exists_mem_vertices D T hloc)
  have hsup' (x : T) : (family D T (N.owner x)).Supplied H x.val :=
    family_supplied D T H hbound hsup _ (howner x)
  have hshare (i : Labels D T) (x y : T) (_hx : N.owner x = i)
      (hy : N.owner y ≠ i) (hpar : y ∉ N.parents i) :
      {j | x.val ∈ ((family D T i).piece j).boundary ∧
        y.val ∈ ((family D T i).piece j).boundary}.Finite := by
    have hout : y ∉ vertices D T i := fun hyA =>
      hpar (Finset.mem_coe.mp ((Set.ext_iff.mp (hparents i) y).mpr ⟨hyA, hy⟩))
    exact (family_finite_extra D T i hout).subset fun _ hj => hj.2
  obtain ⟨q, hq, hcert⟩ := BlockActionCertificates.exists_certified N (family D T) H q₀
    hfinite hclosure hsup' hshare
  exact ⟨q, hq, fun x => family_certified D T (N.owner x) H q x.val (hcert x)⟩

/-- Preserve prescribed robust hub colours and repair a finite exceptional set.
Every other hub needs to be supplied and have only finitely many recurrent
sharing partners among the other hubs being certified. -/
theorem exists_unfriendly_extending [Countable V] (G : SimpleGraph V) (D : PieceFamily G I)
    (S K : Set V) (q₀ : V → Bool)
    (hS : S ⊆ {v | (G.neighborSet v).Infinite}) (hK : K.Finite)
    (hrob : Robust G {v | (G.neighborSet v).Infinite}ᶜ S q₀)
    (hbound : ∀ j, ((D.piece j).boundary : Set V) ⊆ {v | (G.neighborSet v).Infinite})
    (hsup : ∀ x : ↑({v | (G.neighborSet v).Infinite} \ (S ∪ K)),
      D.Supplied {v | (G.neighborSet v).Infinite} x.val)
    (hloc : ∀ x, ((sharing D ({v | (G.neighborSet v).Infinite} \ (S ∪ K))).neighborSet x).Finite) :
    ∃ c : V → Bool, Set.EqOn c q₀ S ∧ ∀ x, UnfriendlyAt G (fun v => some (c v)) x := by
  let H := {v | (G.neighborSet v).Infinite}
  obtain ⟨q, hq, hcert⟩ := exists_certified D H (H \ (S ∪ K)) q₀ hbound hsup hloc
  exact FiniteBlocks.exists_unfriendly_of_certified G D S K q₀ q hS hK hrob
    (fun _ hx => hq (fun h => h.2 (Or.inl hx))) hcert

/-- Local finiteness of repeated sharing among all hubs supplies a robust
colouring when the chosen piece family supplies every hub. -/
theorem exists_robust_of_pieces [Countable V] (G : SimpleGraph V) (D : PieceFamily G I)
    (hbound : ∀ i, ((D.piece i).boundary : Set V) ⊆ {v | (G.neighborSet v).Infinite})
    (hsup : ∀ x : Hubs G, D.Supplied {v | (G.neighborSet v).Infinite} x.val)
    (hloc : ∀ x, ((sharing D {v | (G.neighborSet v).Infinite}).neighborSet x).Finite) :
    ∃ q : V → Bool, Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} q := by
  let H := {v | (G.neighborSet v).Infinite}
  obtain ⟨q, _, hq⟩ := exists_certified D H H (fun _ => false) hbound hsup hloc
  exact ⟨q, fun c hc heq x hx => D.infinite_opposite_of_certified Hᶜ H (fun _ hf h => h hf)
    q c hc heq x hx (hq ⟨x, hx⟩)⟩

/-- When every component of the finite-degree graph is finite, local finiteness
of recurrent sharing implies the existence of a robust colouring. -/
theorem exists_robust [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hloc : ∀ x, ((FiniteBlocks.recurrentSharing G).neighborSet x).Finite) :
    ∃ q : V → Bool, Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} q := by
  let H := {v | (G.neighborSet v).Infinite}
  let D := componentFamily G
  have hbound (i : FiniteComponent G) : ((D.piece i).boundary : Set V) ⊆ H :=
    fun x hx => ((Set.ext_iff.mp (boundary_eq G i.val i.property) x).mp hx).1
  refine exists_robust_of_pieces G D hbound
    (fun x => FiniteKernel.components_supply G hfinite x.val x.property) (fun x => (hloc x).subset ?_)
  intro y h
  have hj : {i : FiniteComponent G |
      x.val ∈ (D.piece i).boundary ∧ y.val ∈ (D.piece i).boundary}.Infinite := h.2
  refine ⟨h.1, (hj.image (f := Subtype.val) Subtype.val_injective.injOn).mono ?_⟩
  rintro _ ⟨i, hi, rfl⟩
  have he := boundary_eq G i.val i.property
  exact ⟨(Set.ext_iff.mp he x.val).mp hi.1, (Set.ext_iff.mp he y.val).mp hi.2⟩

/-- The locally finite recurrent-sharing condition gives an unfriendly partition. -/
theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hloc : ∀ x, ((FiniteBlocks.recurrentSharing G).neighborSet x).Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨q, hq⟩ := exists_robust G hfinite hloc
  exact exists_unfriendly_of_robust_cofinite G _ q Set.Subset.rfl hq (by simp)

/-- The same conditions give a winning strategy for every ordinal clock. -/
theorem all_clocks [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hloc : ∀ x, ((FiniteBlocks.recurrentSharing G).neighborSet x).Finite) :
    ∀ r : Ordinal.{w}, PartitionerWins G (emptyPartition V) r :=
  all_clocks_of_global G (exists_unfriendly G hfinite hloc)

end TenChallenges.Continuation.LocallyFiniteSharing

/- Inlined from Continuation/UnfriendlyFiniteWindowTransfer.lean. -/
/-!
# Strong maximality from a finite window

When two colourings can differ on only a finite subset of the domain and agree
on its outside boundary, strong maximality on that finite subset transfers
from one colouring to the other.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped symmDiff

variable {V : Type u}

/-- If a colouring agrees with a strongly maximal colouring away from a finite
window on the original domain and its boundary, strong maximality on the
window implies strong maximality on the original domain. -/
theorem strongMaximal_of_finite_window (G : SimpleGraph V) (A : Set V) (P : Finset V)
    (c d : V → Bool) (hA : ∀ x ∈ A, (G.neighborSet x).Finite)
    (hP : (P : Set V) ⊆ A) (hc : StrongMaximal G A c)
    (hd : StrongMaximal G (P : Set V) d)
    (hEq : ∀ x, x ∉ P → (x ∈ A ∨ ∃ y ∈ A, G.Adj y x) → c x = d x) :
    StrongMaximal G A d := by
  classical
  let S := P.filter fun x => c x ≠ d x
  have hSP : (S : Set V) ⊆ P := fun _ hx => (Finset.mem_filter.mp hx).1
  have hSA : (S : Set V) ⊆ A := hSP.trans hP
  have hSF (x : V) (hx : x ∈ S) : (G.neighborSet x).Finite := hA x (hSA hx)
  have hcolor (x : V) (hx : x ∈ A ∨ ∃ y ∈ A, G.Adj y x) : flip c S x = d x := by
    by_cases hxp : x ∈ P
    · cases hcx : c x <;> cases hdx : d x <;> simp [flip, S, hxp, hcx, hdx]
    · exact (if_neg (fun hxS => hxp (hSP hxS))).trans (hEq x hxp hx)
  have hgain (U : Finset V) (hUA : (U : Set V) ⊆ A) : gain G (flip c S) U = gain G d U :=
    gain_congr_of_incident_eq G (flip c S) d U fun e he =>
      ⟨hcolor e.1 (he.2.elim (fun h => Or.inl (hUA h))
        (fun h => Or.inr ⟨e.2, hUA h, he.1.symm⟩)),
       hcolor e.2 (he.2.elim (fun h => Or.inr ⟨e.1, hUA h, he.1⟩)
        (fun h => Or.inl (hUA h)))⟩
  have hsum : gain G c S + gain G d S = 0 := by
    rw [← hgain S hSA, ← gain_symmDiff G c S S hSF hSF, symmDiff_self]
    exact gain_empty G c
  have hzero : gain G c S = 0 := by
    have hSc := hc S hSA hSF
    have hSd := hd S hSP hSF
    omega
  intro U hUA hUF
  have hSU : (↑(S ∆ U) : Set V) ⊆ A := fun _ hx =>
    (Finset.mem_symmDiff.mp hx).elim (fun h => hSA h.1) (fun h => hUA h.1)
  have hcomp := gain_symmDiff G c S U hSF hUF
  rw [hzero, zero_add, hgain U hUA] at hcomp
  exact hcomp ▸ hc (S ∆ U) hSU (fun x hx => hA x (hSU hx))

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyFiniteWindows.lean. -/
/-!
# Finite windows for finite boundary changes

A region of finite-degree vertices can be infinite. If only finitely many
exterior vertices can change and each has finitely many neighbours in the
region, a finite window suffices for every pattern of those boundary colours.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

variable {V : Type u}

/-- There is one finite window for all patterns on a finite boundary interface.
Every strongly maximal colouring of the window that agrees with the reference
on the rest of the region and its fixed boundary is strongly maximal throughout
the region. The window includes every inner endpoint of the movable interface. -/
theorem exists_strongMaximal_window (G : SimpleGraph V) (A : Set V) (c₀ : V → Bool)
    (hA : ∀ x ∈ A, (G.neighborSet x).Finite) (hc₀ : StrongMaximal G A c₀)
    (B : Finset V) (hB : ∀ x ∈ B, x ∉ A ∧ (G.neighborSet x ∩ A).Finite) :
    ∃ P : Finset V, (P : Set V) ⊆ A ∧
      (∀ x ∈ A, (∃ b ∈ B, G.Adj b x) → x ∈ P) ∧
      ∀ d : V → Bool,
        (∀ x, x ∉ P → x ∉ B → (x ∈ A ∨ ∃ y ∈ A, G.Adj y x) → d x = c₀ x) →
        StrongMaximal G (P : Set V) d → StrongMaximal G A d := by
  classical
  let recolour (b : B → Bool) (x : V) : Bool := if hx : x ∈ B then b ⟨x, hx⟩ else c₀ x
  choose c hcB hcOut hcMax hcDiff using
    fun b : B → Bool => exists_strongMaximal_of_finite_boundary G A c₀ (recolour b) hA hc₀ B hB
  let W := ⋃ b ∈ (B : Set V), G.neighborSet b ∩ A
  have hW : W.Finite := B.finite_toSet.biUnion fun b hb => (hB b hb).2
  let changes (b : B → Bool) : Set V := {x | x ∈ A ∧ c b x ≠ c₀ x}
  have hchanges : (⋃ b, changes b).Finite :=
    Set.finite_iUnion fun b => (hcDiff b).subset fun _ hx => hx.2
  let U := W ∪ ⋃ b, changes b
  have hU : U.Finite := hW.union hchanges
  let P := hU.toFinset
  have hPA : (P : Set V) ⊆ A := by
    intro x hx
    rcases hU.mem_toFinset.mp hx with hx | hx
    · exact (Set.mem_iUnion₂.mp hx).choose_spec.2.2
    exact (Set.mem_iUnion.mp hx).choose_spec.1
  refine ⟨P, hPA, ?_, ?_⟩
  · rintro x hx ⟨b, hb, hbx⟩
    exact hU.mem_toFinset.mpr (Or.inl (Set.mem_iUnion₂.mpr ⟨b, hb, hbx, hx⟩))
  intro d hfix hd
  let b : B → Bool := fun x => d x.val
  apply strongMaximal_of_finite_window G A P (c b) d hA hPA (hcMax b) hd
  intro x hxP hx
  by_cases hxB : x ∈ B
  · exact (hcB b hxB).trans (dif_pos hxB)
  have hdc₀ : d x = c₀ x := hfix x hxP hxB hx
  by_cases hxA : x ∈ A
  · have hcc₀ : c b x = c₀ x := Classical.byContradiction fun hn =>
      hxP (hU.mem_toFinset.mpr (Or.inr (Set.mem_iUnion.mpr ⟨b, hxA, hn⟩)))
    exact hcc₀.trans hdc₀.symm
  · exact (hcOut b (fun h => h.elim hxA hxB)).trans hdc₀.symm

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyComponentWindows.lean. -/
/-!
# Finite windows in the components of the finite-degree subgraph

Finite movable interfaces allow simultaneous finite windows, including in
infinite components. The windows are pairwise disjoint and their boundaries
lie outside their union.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.ComponentWindows

open Energy ThreeBoundaryGraph

variable {V : Type u} {G : SimpleGraph V}

/-- The union of the vertices of all windows. -/
def active (D : PieceFamily G (Component G)) : Set V :=
  ⋃ C, ((D.piece C).verts : Set V)

/-- All movable hubs lie outside every window. -/
theorem movable_subset_complement (D : PieceFamily G (Component G)) {T : Set V}
    (hT : T ⊆ {v | (G.neighborSet v).Infinite}) : T ⊆ (active D)ᶜ := by
  rintro x hx hh
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hh
  exact hT hx ((D.piece C).finite_degree x hC)

private abbrev region (C : Component G) : Set V := Subtype.val '' C.supp

private theorem region_degree {C : Component G} {x : V} (hx : x ∈ region C) :
    (G.neighborSet x).Finite :=
  let ⟨v, _, hv⟩ := hx
  hv ▸ v.property

private theorem same_component {C C' : Component G} {x : V}
    (hx : x ∈ region C) (hx' : x ∈ region C') : C = C' :=
  let ⟨u, hu, hux⟩ := hx
  let ⟨v, hv, hvx⟩ := hx'
  let huv : u = v := Subtype.ext (hux.trans hvx.symm)
  SimpleGraph.ConnectedComponent.eq_of_common_vertex hu (huv.symm ▸ hv)

private theorem region_of_adj (C : Component G) {x y : V}
    (hx : x ∈ region C) (hxy : G.Adj x y) (hfin : (G.neighborSet y).Finite) :
    y ∈ region C := by
  obtain ⟨u, hu, rfl⟩ := hx
  let v : {w : V // (G.neighborSet w).Finite} := ⟨y, hfin⟩
  exact ⟨v, C.mem_supp_of_adj_mem_supp hu (show (finiteGraph G).Adj u v from hxy), rfl⟩

private theorem active_near_in_piece (D : PieceFamily G (Component G))
    (hsub : ∀ C, ((D.piece C).verts : Set V) ⊆ region C) (C : Component G) {x : V}
    (hx : x ∈ active D) (hnear : x ∈ region C ∨ ∃ y ∈ region C, G.Adj y x) :
    x ∈ (D.piece C).verts :=
  let ⟨C', hx'⟩ := Set.mem_iUnion.mp hx
  let hxC : x ∈ region C := hnear.elim id fun ⟨_, hy, ha⟩ =>
    region_of_adj C hy ha ((D.piece C').finite_degree x hx')
  (same_component (hsub C' hx') hxC) ▸ hx'

/-- An active vertex of a component lies in that component's window. -/
theorem mem_piece_of_mem_active_of_mem_component (D : PieceFamily G (Component G))
    (hsub : ∀ C, ((D.piece C).verts : Set V) ⊆ Subtype.val '' C.supp)
    (C : Component G) {x : V} (hx : x ∈ active D) (hxC : x ∈ Subtype.val '' C.supp) :
    x ∈ (D.piece C).verts :=
  active_near_in_piece D hsub C hx (Or.inl hxC)

private theorem exists_window (G : SimpleGraph V) (T : Set V)
    (hT : T ⊆ {v | (G.neighborSet v).Infinite}) (c₀ : V → Bool)
    (hc₀ : StrongMaximal G {v | (G.neighborSet v).Finite} c₀)
    (C : Component G)
    (hinterface : {e : V × V | e.1 ∈ T ∧ e.2 ∈ region C ∧ G.Adj e.1 e.2}.Finite) :
    ∃ P : Energy.FinitePiece G, (P.verts : Set V) ⊆ region C ∧
      (∀ x ∈ region C, (∃ y ∈ T, G.Adj y x) → x ∈ P.verts) ∧
      ∀ c, (∀ x, x ∉ P.verts → x ∉ T →
        (x ∈ region C ∨ ∃ y ∈ region C, G.Adj y x) → c x = c₀ x) →
        StrongMaximal G (P.verts : Set V) c → StrongMaximal G (region C) c := by
  classical
  let B := (hinterface.image Prod.fst).toFinset
  have hb (x : V) : x ∈ B ↔ x ∈ T ∧ ∃ y ∈ region C, G.Adj x y :=
    (hinterface.image Prod.fst).mem_toFinset.trans
      ⟨fun ⟨⟨_, y⟩, ⟨hx, hy, ha⟩, rfl⟩ => ⟨hx, y, hy, ha⟩,
        fun ⟨hx, y, hy, ha⟩ => ⟨(x, y), ⟨hx, hy, ha⟩, rfl⟩⟩
  have hB : ∀ x ∈ B, x ∉ region C ∧ (G.neighborSet x ∩ region C).Finite :=
    fun x hx => ⟨fun h => hT ((hb x).mp hx).1 (region_degree h),
      (hinterface.image Prod.snd).subset fun y hy =>
        ⟨(x, y), ⟨((hb x).mp hx).1, hy.2, hy.1⟩, rfl⟩⟩
  have hreg : StrongMaximal G (region C) c₀ := fun s hs hfin =>
    hc₀ s (fun _ hx => region_degree (hs hx)) hfin
  obtain ⟨P, hP, hcover, htransfer⟩ := exists_strongMaximal_window G (region C) c₀
    (fun _ hx => region_degree hx) hreg B hB
  refine ⟨⟨P, fun _ hx => region_degree (hP hx)⟩, hP, ?_, ?_⟩
  · exact fun x hx ⟨y, hy, ha⟩ => hcover x hx ⟨y, (hb y).mpr ⟨hy, x, hx, ha⟩, ha⟩
  intro c hfix hc
  refine htransfer c ?_ hc
  intro x hxP hxB hxnear
  exact hfix x hxP
    (fun hxT => hxnear.elim (fun h => hT hxT (region_degree h))
      (fun ⟨y, hy, ha⟩ => hxB ((hb x).mpr ⟨hxT, y, hy, ha.symm⟩))) hxnear

/-- Choose finite windows inside their components, retaining movable boundary
incidences and transferring strong maximality to the entire components. -/
theorem exists_family_with_vertices (G : SimpleGraph V) (T : Set V)
    (hT : T ⊆ {v | (G.neighborSet v).Infinite}) (c₀ : V → Bool)
    (hc₀ : StrongMaximal G {v | (G.neighborSet v).Finite} c₀)
    (hinterface : ∀ C : Component G,
      {e : V × V | e.1 ∈ T ∧ e.2 ∈ Subtype.val '' C.supp ∧ G.Adj e.1 e.2}.Finite) :
    ∃ D : PieceFamily G (Component G),
      (∀ C, ((D.piece C).verts : Set V) ⊆ Subtype.val '' C.supp) ∧
      (∀ C, ((D.piece C).boundary : Set V) ⊆ (active D)ᶜ) ∧
      (∀ C x, x ∈ T → (x ∈ (D.piece C).boundary ↔ x ∈ hubBoundary G C)) ∧
      ∀ c, Set.EqOn c c₀ ((active D)ᶜ \ T) → StrongMaximal G (active D) c →
        ∀ C : Component G, StrongMaximal G (Subtype.val '' C.supp) c := by
  classical
  choose pieces hsub hcover hwindow using fun C => exists_window G T hT c₀ hc₀ C (hinterface C)
  let D : PieceFamily G (Component G) :=
    { piece := pieces
      disjoint := fun C C' hne =>
        Finset.disjoint_left.mpr fun _ h₁ h₂ => hne (same_component (hsub C h₁) (hsub C' h₂)) }
  have htransfer (c : V → Bool) (hfix : Set.EqOn c c₀ ((active D)ᶜ \ T))
      (hmax : StrongMaximal G (active D) c) (C : Component G) : StrongMaximal G (region C) c :=
    hwindow C c (fun x hxP hxT hx => hfix
      ⟨fun ha => hxP (active_near_in_piece D hsub C ha hx), hxT⟩)
      (fun s hs hfin => hmax s (fun _ hx => Set.mem_iUnion.mpr ⟨C, hs hx⟩) hfin)
  refine ⟨D, hsub, ?_, ?_, htransfer⟩
  · intro C x hx hxactive
    obtain ⟨y, hy, hxy⟩ := (D.piece C).boundary_touch ⟨x, hx⟩
    exact (D.piece C).boundary_not_mem hx
      (active_near_in_piece D hsub C hxactive (Or.inr ⟨y, hsub C hy, hxy.symm⟩))
  intro C x hxT
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (D.piece C).boundary_touch ⟨x, hx⟩
    obtain ⟨u, hu, rfl⟩ := hsub C hy
    exact ⟨hT hxT, u, hu, hxy⟩
  · rintro ⟨_, y, hy, hxy⟩
    exact (D.piece C).mem_boundary_of_adj
      (fun hx => hT hxT ((D.piece C).finite_degree x hx))
      (hcover C y.val ⟨y, hy, rfl⟩ ⟨x, hxT, hxy⟩) hxy

/-- Choose finite windows retaining movable boundary incidences and transferring
strong maximality to the entire components. -/
theorem exists_family (G : SimpleGraph V) (T : Set V)
    (hT : T ⊆ {v | (G.neighborSet v).Infinite}) (c₀ : V → Bool)
    (hc₀ : StrongMaximal G {v | (G.neighborSet v).Finite} c₀)
    (hinterface : ∀ C : Component G,
      {e : V × V | e.1 ∈ T ∧ e.2 ∈ Subtype.val '' C.supp ∧ G.Adj e.1 e.2}.Finite) :
    ∃ D : PieceFamily G (Component G),
      (∀ C, ((D.piece C).boundary : Set V) ⊆ (active D)ᶜ) ∧
      (∀ C x, x ∈ T → (x ∈ (D.piece C).boundary ↔ x ∈ hubBoundary G C)) ∧
      ∀ c, Set.EqOn c c₀ ((active D)ᶜ \ T) → StrongMaximal G (active D) c →
        ∀ C : Component G, StrongMaximal G (Subtype.val '' C.supp) c :=
  let ⟨D, _, hboundary, hshare, hmax⟩ := exists_family_with_vertices G T hT c₀ hc₀ hinterface
  ⟨D, hboundary, hshare, hmax⟩

end TenChallenges.Continuation.ComponentWindows

/- Inlined from Continuation/UnfriendlyWindowSharing.lean. -/
/-!
# Finite component interfaces and locally finite sharing

Replace each finite-degree component by a finite window. Outside the windows,
hold the finite-degree colours fixed. Certify the movable hubs by the windows
and the fixed vertices, and recover strong maximality over the whole graph.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.WindowSharing

open Energy ThreeBoundaryGraph ComponentWindows

variable {V : Type u}

/-- Repeated sharing on a chosen set of hubs, using all finite-degree
components, including the infinite ones. -/
def sharingOn (G : SimpleGraph V) (T : Set V) : SimpleGraph T where
  Adj x y := x ≠ y ∧ {C : Component G | x.val ∈ hubBoundary G C ∧ y.val ∈ hubBoundary G C}.Infinite
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.mono fun _ hC => ⟨hC.2, hC.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem supplied_by_windows {G : SimpleGraph V} (D : PieceFamily G (Component G))
    (hb : ∀ C, ((D.piece C).boundary : Set V) ⊆ (active D)ᶜ)
    (x : V) (hx : (G.neighborSet x).Infinite) : D.Supplied (active D)ᶜ x := by
  refine or_iff_not_imp_left.mpr fun hdir hpiece => ?_
  let I := {C | x ∈ (D.piece C).boundary ∧
    ((D.piece C).boundary : Set V) ⊆ (active D)ᶜ}
  have hsmall : (⋃ C ∈ I, ((D.piece C).verts : Set V)).Finite :=
    hpiece.biUnion fun C _ => (D.piece C).verts.finite_toSet
  apply hx (((Set.not_infinite.mp hdir).union hsmall).subset ?_)
  intro y hy
  by_cases hyW : y ∈ active D
  · obtain ⟨C, hyC⟩ := Set.mem_iUnion.mp hyW
    have hxC : x ∉ (D.piece C).verts := fun h => hx ((D.piece C).finite_degree x h)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨C, ⟨(D.piece C).mem_boundary_of_adj hxC hyC hy, hb C⟩, hyC⟩)
  · exact Or.inl ⟨hy, hyW⟩

/-- Complete a strongly maximal reference colouring by certifying the movable
hubs and changing only finitely many vertices in each finite-degree component. -/
theorem exists_window_completion [Countable V] (G : SimpleGraph V) (T : Set V)
    (hT : T ⊆ {v | (G.neighborSet v).Infinite}) (c₀ : V → Bool)
    (hc₀ : StrongMaximal G {v | (G.neighborSet v).Finite} c₀)
    (hinterface : ∀ C : Component G,
      {e : V × V | e.1 ∈ T ∧ e.2 ∈ Subtype.val '' C.supp ∧ G.Adj e.1 e.2}.Finite)
    (hloc : ∀ x, ((sharingOn G T).neighborSet x).Finite) :
    ∃ d : V → Bool, Set.EqOn d c₀ ({v | (G.neighborSet v).Infinite} \ T) ∧
      StrongMaximal G {v | (G.neighborSet v).Infinite}ᶜ d ∧
      (∀ x ∈ T, (oppositeSet G d x).Infinite) ∧
      ∀ C : Component G, {x | x ∈ Subtype.val '' C.supp ∧ d x ≠ c₀ x}.Finite := by
  let H := {v | (G.neighborSet v).Infinite}
  obtain ⟨D, hverts, hb, hbnd, htransfer⟩ :=
    ComponentWindows.exists_family_with_vertices G T hT c₀ hc₀ hinterface
  let B := (active D)ᶜ
  have hHB : H ⊆ B := movable_subset_complement D Set.Subset.rfl
  have hlocD (x : T) : ((PieceSharingCover.sharing D T).neighborSet x).Finite :=
    (hloc x).subset fun y hy => ⟨hy.1, hy.2.mono fun C hC =>
      ⟨(hbnd C x.val x.property).mp hC.1, (hbnd C y.val y.property).mp hC.2⟩⟩
  obtain ⟨q, hq, hcert⟩ := LocallyFiniteSharing.exists_certified D B T c₀ hb
    (fun x => supplied_by_windows D hb x.val (hT x.property)) hlocD
  obtain ⟨d, hdq, hd⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G B q
  have hdW : StrongMaximal G (active D) d := by simpa only [B, compl_compl] using hd
  have hfix : Set.EqOn d c₀ (B \ T) := fun _ hx => (hdq hx.1).trans (hq hx.2)
  have hdF := strongMaximal_of_components G d (htransfer d hfix hdW)
  have hdH : StrongMaximal G Hᶜ d := fun U _ hU => hdF U (fun v hv => hU v hv) hU
  refine ⟨d, (fun _ hx => hfix ⟨hHB hx.1, hx.2⟩), hdH, ?_, ?_⟩
  · exact fun x hx => D.infinite_opposite_of_certified Hᶜ B (fun _ hf h => h hf)
      q d hdH hdq x (hHB (hT hx)) (hcert ⟨x, hx⟩)
  · exact fun C => (D.piece C).verts.finite_toSet.subset fun x ⟨hxC, hne⟩ =>
      mem_piece_of_mem_active_of_mem_component D hverts C
        (Classical.byContradiction fun hx => hne (hfix
          ⟨hx, fun hxT => let ⟨y, _, hy⟩ := hxC; hT hxT (hy ▸ y.property)⟩)) hxC

/-- Locally finite sharing among movable hubs implies an unfriendly partition
if each finite-degree component has a finite edge interface to those hubs.
The partition preserves the prescribed robust hub colours on `S` and
allows a finite exceptional set `K`. -/
theorem exists_unfriendly_extending [Countable V] (G : SimpleGraph V) (S K T : Set V)
    (q₀ : V → Bool)
    (hS : S ⊆ {v | (G.neighborSet v).Infinite}) (hK : K.Finite)
    (hT : T = {v | (G.neighborSet v).Infinite} \ (S ∪ K))
    (hrob : Robust G {v | (G.neighborSet v).Infinite}ᶜ S q₀)
    (hinterface : ∀ C : Component G,
      {e : V × V | e.1 ∈ T ∧ e.2 ∈ Subtype.val '' C.supp ∧ G.Adj e.1 e.2}.Finite)
    (hloc : ∀ x, ((sharingOn G T).neighborSet x).Finite) :
    ∃ c : V → Bool, Set.EqOn c q₀ S ∧ ∀ x, UnfriendlyAt G (fun v => some (c v)) x := by
  let H := {v | (G.neighborSet v).Infinite}
  have hTH : T ⊆ H := fun _ hx => (hT ▸ hx).1
  obtain ⟨c₀, hc₀q, hc₀⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G H q₀
  have hc₀F : StrongMaximal G {v | (G.neighborSet v).Finite} c₀ :=
    fun U hUF hU => hc₀ U (fun _ hx hi => hi (hUF hx)) hU
  obtain ⟨d, hdc₀, hdH, hdopp, _⟩ := exists_window_completion G T hTH c₀ hc₀F hinterface hloc
  have hdS : Set.EqOn d q₀ S := fun _ hx =>
    (hdc₀ ⟨hS hx, fun ht => (hT ▸ ht).2 (Or.inl hx)⟩).trans (hc₀q (hS hx))
  let E := (H ∩ K) \ S
  have hE : E.Finite := hK.subset fun _ hx => hx.1.2
  obtain ⟨c, hcS, hc, hopp⟩ := finite_hub_stage_preserving G Hᶜ S
    (fun _ hx h => h (hS hx)) d hdH hE.toFinset
    (fun _ hv => let he := hE.mem_toFinset.mp hv; ⟨he.1.1, fun h => h he.1.1, he.2⟩)
  refine ⟨c, hcS.trans hdS, fun x => ?_⟩
  by_cases hx : (G.neighborSet x).Finite
  · exact unfriendlyAt_of_strongMaximal G _ c hc x (fun h => h hx) hx
  · apply unfriendly_of_infinite_opposite G c x
    apply hopp x (fun h => h hx)
    by_cases hxs : x ∈ S
    · exact Or.inr (hrob d hdH hdS x hxs)
    by_cases hxk : x ∈ K
    · exact Or.inl (hE.mem_toFinset.mpr ⟨⟨hx, hxk⟩, hxs⟩)
    have hxt : x ∈ T := hT.symm ▸
      (show x ∈ H \ (S ∪ K) from ⟨hx, fun h => h.elim hxs hxk⟩)
    exact Or.inr (hdopp x hxt)

/-- Local finiteness of recurrent sharing and a finite edge interface at every
finite-degree component imply an unfriendly partition. -/
theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (hinterface : ∀ C : Component G,
      {e : V × V | (G.neighborSet e.1).Infinite ∧ e.2 ∈ Subtype.val '' C.supp ∧ G.Adj e.1 e.2}.Finite)
    (hloc : ∀ x, ((sharingOn G {v | (G.neighborSet v).Infinite}).neighborSet x).Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  let H := {v | (G.neighborSet v).Infinite}
  obtain ⟨c, _, hc⟩ := exists_unfriendly_extending G ∅ ∅ H (fun _ => false)
    (Set.empty_subset _) Set.finite_empty (by simp [H]) (fun _ _ _ _ hx => hx.elim) hinterface hloc
  exact ⟨fun v => some (c v), hc⟩

/-- The finite-interface condition reaches every ordinal clock. -/
theorem all_clocks [Countable V] (G : SimpleGraph V)
    (hinterface : ∀ C : Component G,
      {e : V × V | (G.neighborSet e.1).Infinite ∧ e.2 ∈ Subtype.val '' C.supp ∧ G.Adj e.1 e.2}.Finite)
    (hloc : ∀ x, ((sharingOn G {v | (G.neighborSet v).Infinite}).neighborSet x).Finite) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r :=
  all_clocks_of_global G (exists_unfriendly G hinterface hloc)

end TenChallenges.Continuation.WindowSharing

/- Inlined from Continuation/UnfriendlyOverlappingInterfaces.lean. -/
/-!
# Overlapping infinite component interfaces

Assign a hub to the earliest component in which it has an infinite
neighbourhood. Earlier hub colours are inputs to a later component.
Once these hubs are served, finite windows serve the remaining hubs.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.OverlappingInterfaces

open Energy ThreeBoundaryGraph ComponentGluing InfiniteInterfaceAssignment

variable {V : Type u}

/-- The movable hubs having infinitely many neighbours in this component. -/
abbrev demandingHubs (G : SimpleGraph V) (T : Set V) (C : Component G) : Set V :=
  demanding G T (fun C : Component G => interior C) C

/-- The movable hubs that can be served inside at least one component. -/
abbrev coveredHubs (G : SimpleGraph V) (T : Set V) : Set V :=
  requested G T (fun C : Component G => interior C)

/-- The edges from movable hubs with only finitely many neighbours in this component. -/
def finiteNeighbourEdges (G : SimpleGraph V) (T : Set V) (C : Component G) : Set (V × V) :=
  {e | e.1 ∈ T \ demandingHubs G T C ∧ e.2 ∈ interior C ∧ G.Adj e.1 e.2}

private theorem covered_subset {G : SimpleGraph V} {T : Set V} : coveredHubs G T ⊆ T :=
  fun _ hx => (Set.mem_iUnion.mp hx).choose_spec.1

private theorem reference_with_component_opponents [Countable V] (G : SimpleGraph V) (T : Set V)
    (hT : T ⊆ {v | (G.neighborSet v).Infinite}) (c₀ : V → Bool)
    (hDemand : ∀ C : Component G, (demandingHubs G T C).Finite)
    (hEdges : ∀ C : Component G, (finiteNeighbourEdges G T C).Finite) :
    ∃ c, Set.EqOn c c₀ ({v | (G.neighborSet v).Infinite} \ coveredHubs G T) ∧
      StrongMaximal G {v | (G.neighborSet v).Finite} c ∧
      ∀ x ∈ coveredHubs G T, ∃ C : Component G, (oppositeSet G c x ∩ interior C).Infinite := by
  have : Countable (Component G) :=
    (show Function.Surjective (finiteGraph G).connectedComponentMk from
      fun C => C.ind fun x => ⟨x, rfl⟩).countable
  have hA (C : Component G) (x : V) (hx : x ∈ interior C) : (G.neighborSet x).Finite :=
    let ⟨y, _, he⟩ := hx
    he ▸ y.property
  have hdisj (C : Component G) : Disjoint T (interior C) :=
    Set.disjoint_left.mpr fun x hx hxi => hT hx (hA C x hxi)
  obtain ⟨q, d, hq, hdMax, hdq, hdRef, hdOpp⟩ :=
    exists_assignments G T (fun C : Component G => interior C) c₀ hdisj hA hDemand
  have hqT : Set.EqOn q c₀ Tᶜ := fun _ hx => hq (fun h => hx (covered_subset h))
  have patch (C : Component G) :=
    reconcile_finite_interface G (interior C) T (demandingHubs G T C) c₀ q (d C)
      (fun _ hx => hx.1) (hdisj C) (hA C) (hdMax C) (hdq C) (hdRef C) hqT (hEdges C)
  choose e heMax heBoundary _ heDiff using patch
  obtain ⟨c, hcq, hcE, hmax⟩ := exists_strongMaximal_glued G q e heBoundary heMax
  refine ⟨c, fun _ hx => (hcq hx.1).trans (hq hx.2), hmax, ?_⟩
  intro x hx
  obtain ⟨C, hxC, hxOpp⟩ := hdOpp x hx
  refine ⟨C, infinite_opposite_inside_of_finite_difference G (interior C) x
    ((hdq C hxC).trans (hcq (hT hxC.1)).symm) ?_ hxOpp⟩
  exact (heDiff C).subset fun y hy hn => hy.2 (hn.symm.trans (hcE C hy.1).symm)

/-- The sets of movable hubs with infinite neighbourhoods inside a component
may overlap arbitrarily. Each such set must be finite, and each component must
have finitely many edges to its other movable hubs. Local finiteness of
repeated sharing is required only among hubs served by no single component. -/
theorem exists_unfriendly_extending [Countable V] (G : SimpleGraph V) (S K T : Set V)
    (q₀ : V → Bool)
    (hS : S ⊆ {v | (G.neighborSet v).Infinite}) (hK : K.Finite)
    (hT : T = {v | (G.neighborSet v).Infinite} \ (S ∪ K))
    (hrob : Robust G {v | (G.neighborSet v).Infinite}ᶜ S q₀)
    (hDemand : ∀ C : Component G, (demandingHubs G T C).Finite)
    (hEdges : ∀ C : Component G, (finiteNeighbourEdges G T C).Finite)
    (hloc : ∀ x, ((WindowSharing.sharingOn G (T \ coveredHubs G T)).neighborSet x).Finite) :
    ∃ c : V → Bool, Set.EqOn c q₀ S ∧ ∀ x, UnfriendlyAt G (fun v => some (c v)) x := by
  let H := {v | (G.neighborSet v).Infinite}
  let U := coveredHubs G T
  let L := T \ U
  have hTH : T ⊆ H := fun _ hx => (hT ▸ hx).1
  obtain ⟨c₀, hc₀, hMax, hInf⟩ := reference_with_component_opponents G T hTH q₀ hDemand hEdges
  have hfinite (C : Component G) :
      {e : V × V | e.1 ∈ L ∧ e.2 ∈ interior C ∧ G.Adj e.1 e.2}.Finite :=
    (hEdges C).subset fun e h =>
      ⟨⟨h.1.1, fun hd => h.1.2 (Set.mem_iUnion.mpr ⟨C, hd⟩)⟩, h.2⟩
  obtain ⟨d, hd, hdMax, hdL, hdDiff⟩ := WindowSharing.exists_window_completion G L
    (fun _ hx => hTH hx.1) c₀ hMax hfinite hloc
  have hdS : Set.EqOn d q₀ S := fun x hx =>
    let hout : x ∉ T := fun ht => (hT ▸ ht).2 (Or.inl hx)
    (hd ⟨hS hx, fun hl => hout hl.1⟩).trans
      (hc₀ ⟨hS hx, fun hu => hout (covered_subset hu)⟩)
  let E := (H ∩ K) \ S
  have hE : E.Finite := hK.subset fun _ hx => hx.1.2
  obtain ⟨c, hcS, hc, hopp⟩ := finite_hub_stage_preserving G Hᶜ S
    (fun _ hx h => h (hS hx)) d hdMax hE.toFinset
    (fun _ hv => let he := hE.mem_toFinset.mp hv; ⟨he.1.1, fun h => h he.1.1, he.2⟩)
  refine ⟨c, hcS.trans hdS, fun x => ?_⟩
  by_cases hx : (G.neighborSet x).Finite
  · exact unfriendlyAt_of_strongMaximal G _ c hc x (fun h => h hx) hx
  · apply unfriendly_of_infinite_opposite G c x
    apply hopp x (fun h => h hx)
    by_cases hxS : x ∈ S
    · exact Or.inr (hrob d hdMax hdS x hxS)
    by_cases hxK : x ∈ K
    · exact Or.inl (hE.mem_toFinset.mpr ⟨⟨hx, hxK⟩, hxS⟩)
    by_cases hxU : x ∈ U
    · obtain ⟨C, hgood⟩ := hInf x hxU
      have hh : c₀ x = d x := (hd ⟨hx, fun hl => hl.2 hxU⟩).symm
      have hf : {y | y ∈ interior C ∧ c₀ y ≠ d y}.Finite :=
        (hdDiff C).subset fun _ hy => ⟨hy.1, hy.2.symm⟩
      exact Or.inr ((infinite_opposite_inside_of_finite_difference G (interior C) x hh hf hgood).mono
        Set.inter_subset_left)
    exact Or.inr (hdL x ⟨hT.symm ▸ (show x ∈ H \ (S ∪ K) from
      ⟨hx, fun h => h.elim hxS hxK⟩), hxU⟩)

/-- Infinite component interfaces may overlap, subject to the per-component
finiteness assumptions and local finiteness of sharing among the other hubs. -/
theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (hDemand : ∀ C : Component G,
      (demandingHubs G {v | (G.neighborSet v).Infinite} C).Finite)
    (hEdges : ∀ C : Component G,
      (finiteNeighbourEdges G {v | (G.neighborSet v).Infinite} C).Finite)
    (hloc : ∀ x, ((WindowSharing.sharingOn G
      ({v | (G.neighborSet v).Infinite} \ coveredHubs G {v | (G.neighborSet v).Infinite})).neighborSet x).Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  let H := {v | (G.neighborSet v).Infinite}
  obtain ⟨c, _, hc⟩ := exists_unfriendly_extending G ∅ ∅ H (fun _ => false)
    (Set.empty_subset _) Set.finite_empty (by simp [H]) (fun _ _ _ _ hx => hx.elim) hDemand hEdges hloc
  exact ⟨fun v => some (c v), hc⟩

/-- The overlapping-interface hypotheses give a winning strategy at every
ordinal clock. -/
theorem all_clocks [Countable V] (G : SimpleGraph V)
    (hDemand : ∀ C : Component G,
      (demandingHubs G {v | (G.neighborSet v).Infinite} C).Finite)
    (hEdges : ∀ C : Component G,
      (finiteNeighbourEdges G {v | (G.neighborSet v).Infinite} C).Finite)
    (hloc : ∀ x, ((WindowSharing.sharingOn G
      ({v | (G.neighborSet v).Infinite} \ coveredHubs G {v | (G.neighborSet v).Infinite})).neighborSet x).Finite) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r :=
  all_clocks_of_global G (exists_unfriendly G hDemand hEdges hloc)

end TenChallenges.Continuation.OverlappingInterfaces

theorem solution {V : Type u} [Countable V] (G : SimpleGraph V) :
    let H : Set V := {v | (G.neighborSet v).Infinite}
    let Comp := (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent
    let A (C : Comp) : Set V := Subtype.val '' C.supp
    let demand (C : Comp) : Set V := {x | x ∈ H ∧ (G.neighborSet x ∩ A C).Infinite}
    let U : Set V := ⋃ C, demand C
    ∀ (hDemand : ∀ C : Comp, (demand C).Finite)
      (hEdges : ∀ C : Comp, {e : V × V |
        e.1 ∈ H \ demand C ∧ e.2 ∈ A C ∧ G.Adj e.1 e.2}.Finite)
      (R : SimpleGraph ↑(H \ U))
      (hAdj : ∀ x y, R.Adj x y ↔ x ≠ y ∧
        {C : Comp |
          (∃ a ∈ C.supp, G.Adj x.val a.val) ∧ (∃ b ∈ C.supp, G.Adj y.val b.val)}.Infinite)
      (hloc : ∀ x, (R.neighborSet x).Finite),
      (∃ f : V → Option Bool, ∀ x : V, UnfriendlyAt G f x) ∧
        ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by
  intro H Comp A demand U hDemand hEdges R hAdj hloc
  have hR : R = TenChallenges.Continuation.WindowSharing.sharingOn G (H \ U) := by
    ext x y
    exact (hAdj x y).trans (and_congr_right fun _ =>
      ⟨fun hi => hi.mono fun _ h => ⟨⟨x.property.1, h.1⟩, ⟨y.property.1, h.2⟩⟩,
        fun hi => hi.mono fun _ h => ⟨h.1.2, h.2.2⟩⟩)
  subst R
  have hg := TenChallenges.Continuation.OverlappingInterfaces.exists_unfriendly G hDemand hEdges hloc
  exact ⟨hg, TenChallenges.Continuation.all_clocks_of_global G hg⟩

#print axioms solution
