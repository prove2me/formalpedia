-- Prove2me | solution 1 for TenChallenges.unfriendly_partition_iff_all_clocks
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:22:40.710312+00:00
-- url     : https://prove2.me/submissions/722de28d-1702-49d8-80f3-13a85331d91a

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false

universe u v

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

/-!
# Global unfriendly partitions and all ordinal game clocks

For a countable graph, existence of a global unfriendly partition is equivalent
to winning the game at every ordinal clock in the vertex universe. A global
partition also gives winning strategies for clocks in any independent universe.

This equivalence does not prove either existence statement for all countable
graphs. In particular, it does not prove that the empty state is persistent.
-/



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

/-- The global partition assertion is equivalent to winning at every vertex-universe clock. -/
theorem solution {V : Type u} [Countable V] (G : SimpleGraph V) :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ↔
      ∀ α : Ordinal.{u}, PartitionerWins G (emptyPartition V) α :=
  TenChallenges.Continuation.unfriendly_partition_iff_all_clocks G

#print axioms solution
