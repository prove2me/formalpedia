-- Prove2me | solution 1 for OpenSearchSafety.bootstrap_compatible
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:55:32.196948+00:00
-- url     : https://prove2.me/submissions/807aa8b8-b809-4d6a-b03a-0ffb0c35783b

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_init
import Theorems.Thm_OpenSearchSafety_inv_bootstrap
import Theorems.Thm_OpenSearchSafety_inv_startJoin
import Theorems.Thm_OpenSearchSafety_inv_join
import Theorems.Thm_OpenSearchSafety_inv_clientValue
import Theorems.Thm_OpenSearchSafety_inv_publish
import Theorems.Thm_OpenSearchSafety_inv_respond
import Theorems.Thm_OpenSearchSafety_inv_commit
import Theorems.Thm_OpenSearchSafety_inv_restart
import Theorems.Thm_OpenSearchSafety_inv_restartAny
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_won_of_electionWon
import Theorems.Thm_OpenSearchSafety_inv_pub_lcc
import Theorems.Thm_OpenSearchSafety_inv_leader_completeness
import Theorems.Thm_OpenSearchSafety_inv_committed_comparable

open OpenSearchCoordination OpenSearchSafety

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- **Bootstrapping with different partial views gives compatible configurations.** Two configurations of the form
`ClusterBootstrapService` builds (`BootstrapConfig`, with the same requirements, `resolve` and `placeholder`) meet the
condition of `Params.InitCompatible`, whatever subset of the required nodes each bootstrapping node has discovered,
provided each requirement names its own node, the same everywhere (`resolve` injective on the requirements),
placeholders are distinct from each other and from the named nodes, and placeholders are not cluster-manager-eligible
node ids. `Params` is not mentioned: that the model's bootstrap configurations have this form is not formalized. -/
theorem solution (eligible : NodeId → Bool) (k : Nat) (resolve placeholder : Nat → NodeId)
    (hres : ∀ i j, i < k → j < k → resolve i = resolve j → i = j)
    (hph : ∀ i j, i < k → j < k → placeholder i = placeholder j → i = j)
    (hdis : ∀ i j, i < k → j < k → placeholder i ≠ resolve j)
    (hphe : ∀ i, i < k → eligible (placeholder i) = false)
    (X Y : VotingConfiguration) (mX mY : Nat → Bool)
    (hX : BootstrapConfig k resolve placeholder mX X) (hY : BootstrapConfig k resolve placeholder mY Y)
    (q₁ q₂ : List NodeId) (hq₁ : ∀ x ∈ q₁, eligible x = true) (hq₂ : ∀ x ∈ q₂, eligible x = true)
    (h₁ : X.hasQuorum q₁ = true) (h₂ : Y.hasQuorum q₂ = true) : ∃ x, x ∈ q₁ ∧ x ∈ q₂ := by
  -- an eligible quorum of a bootstrap configuration names more than half of the requirements, all matched
  have key : ∀ (m : Nat → Bool) (Z : VotingConfiguration) (q : List NodeId),
      BootstrapConfig k resolve placeholder m Z → (∀ x ∈ q, eligible x = true) → Z.hasQuorum q = true →
      ((List.range k).filter (fun i => m i && q.contains (resolve i))).length * 2 > k := by
    intro m Z q hZ hq hQ
    have hinj : ∀ i j, i < k → j < k → (if m i then resolve i else placeholder i) =
        (if m j then resolve j else placeholder j) → i = j := by
      intro i j hi hj he
      cases hmi : m i <;> cases hmj : m j <;> simp only [hmi, hmj, if_true, if_false,
        Bool.false_eq_true] at he
      · exact hph i j hi hj he
      · exact absurd he (hdis i j hi hj)
      · exact absurd he.symm (hdis j i hj hi)
      · exact hres i j hi hj he
    have hnodupZ : Z.nodeIds.Nodup := Z.sorted.imp (fun h => Nat.ne_of_lt h)
    -- the configuration has at least `k` members
    have hL : ((List.range k).map (fun i => if m i then resolve i else placeholder i)).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      exact List.nodup_range.imp_of_mem
        (fun ha hb hab he => hab (hinj _ _ (List.mem_range.mp ha) (List.mem_range.mp hb) he))
    have hsub1 : (List.range k).map (fun i => if m i then resolve i else placeholder i) ⊆ Z.nodeIds := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact (hZ.1 _).mpr ⟨i, List.mem_range.mp hi, rfl⟩
    have hk : k ≤ Z.nodeIds.length := by
      have := List.Nodup.length_le_of_subset hL hsub1
      simpa using this
    -- its members in the quorum are the matched requirements named in the quorum
    have hsub2 : Z.nodeIds.filter (fun x => q.contains x) ⊆
        ((List.range k).filter (fun i => m i && q.contains (resolve i))).map resolve := by
      intro x hx
      rw [List.mem_filter, List.contains_iff_mem] at hx
      obtain ⟨i, hi, rfl⟩ := (hZ.1 _).mp hx.1
      have hxq := hx.2
      cases hmi : m i
      · simp only [hmi, if_false, Bool.false_eq_true] at hxq
        have := hq _ hxq
        rw [hphe i hi] at this
        cases this
      · simp only [hmi, if_true] at hxq ⊢
        exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [hmi, hxq]⟩, rfl⟩
    have hle := List.Nodup.length_le_of_subset (hnodupZ.sublist List.filter_sublist) hsub2
    rw [List.length_map] at hle
    simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at hQ
    omega
  have hA := key mX X q₁ hX hq₁ h₁
  have hB := key mY Y q₂ hY hq₂ h₂
  have hc := filter_length_add_le (List.range k) (fun i => mX i && q₁.contains (resolve i))
    (fun i => mY i && q₂.contains (resolve i))
  rw [List.length_range] at hc
  have hpos : 0 < ((List.range k).filter
      (fun i => (mX i && q₁.contains (resolve i)) && (mY i && q₂.contains (resolve i)))).length := by
    omega
  obtain ⟨i, hi⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem] at hi
  exact ⟨resolve i, hi.2.1.2, hi.2.2.2⟩
