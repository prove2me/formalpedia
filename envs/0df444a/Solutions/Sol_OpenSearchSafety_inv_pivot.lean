-- Prove2me | solution 1 for OpenSearchSafety.inv_pivot
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:29.018037+00:00
-- url     : https://prove2.me/submissions/bcce6b96-6498-4907-9b13-b60286bb6c6a

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_deepest_committed
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_lineage
import Theorems.Thm_OpenSearchSafety_inv_root_lcc

open OpenSearchCoordination OpenSearchSafety

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Two quorums of the same voting configuration share a member of the configuration. -/
private theorem quorum_intersect (c : VotingConfiguration) (a b : List NodeId)
    (ha : c.hasQuorum a = true) (hb : c.hasQuorum b = true) :
    ∃ x, x ∈ c.nodeIds ∧ x ∈ a ∧ x ∈ b := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha hb
  have key := filter_length_add_le c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
  have hpos : 0 < (c.nodeIds.filter (fun x => a.contains x && b.contains x)).length := by omega
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

/-- No configuration has a quorum of the empty list. -/
private theorem hasQuorum_nil (c : VotingConfiguration) : c.hasQuorum [] = false := by
  unfold VotingConfiguration.hasQuorum
  rw [decide_eq_false_iff_not]
  have : (c.nodeIds.filter (fun x => ([] : List NodeId).contains x)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; simp
  omega

/-- (Pivot and path summary) If `(x, y)` realizes the key `b`, then either `b` has a deepest committed ancestor-or-self,
a publication whose last accepted configuration is `x` or `y`; or `b` has no committed ancestor-or-self, and `x` is a
bootstrap configuration. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (bt : Nat) (bv : Int) (x y : VotingConfiguration) (hr : Realizes P W bt bv x y) :
    (∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ Committed W s.term s.version ∧
      Descends W s.term s.version bt bv ∧
      (∀ et ev, Committed W et ev → Descends W et ev bt bv → Descends W et ev s.term s.version) ∧
      (x = s.lastAcceptedConfiguration ∨ y = s.lastAcceptedConfiguration)) ∨
    ((∀ et ev, Committed W et ev → ¬ Descends W et ev bt bv) ∧ P.initConfs x) := by
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d h₁ h₂
    rcases inv_descends_key P W hinv _ _ _ _ h₁ with h | ⟨-, h₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ h₂ with ⟨h, h'⟩ | ⟨-, h₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  rcases inv_deepest_committed P W hinv bt bv with ⟨dt, dv, hdc, hdd, hmax⟩ | hnone
  · left
    obtain ⟨hdpos, srcD, sD, ptD, pvD, hD, hDt, hDv⟩ := inv_committed_published P W hinv dt dv hdc
    subst hDt hDv
    refine ⟨srcD, sD, ptD, pvD, hD, hdc, hdd, hmax, ?_⟩
    by_cases heq : sD.term = bt ∧ sD.version = bv
    · -- the base is the deepest committed key itself
      rcases hr with ⟨h0, -⟩ | ⟨src, s, pt, pv, hs, h1, h2, h3, -⟩
      · omega
      · obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hD hs (heq.1.trans h1.symm)
          (heq.2.trans h2.symm)
        exact Or.inr h3
    · -- the base is strictly below it: uncommitted, so realized by its own configurations
      rcases hr with ⟨h0, -⟩ | ⟨src, s, pt, pv, hs, h1, h2, h3, h4⟩
      · rcases inv_descends_key P W hinv _ _ _ _ hdd with ⟨h5, -⟩ | ⟨h5, -⟩ <;> omega
      · have hbnc : ¬ Committed W bt bv := fun hc => heq (hanti _ _ _ _ hdd (hmax bt bv hc (.refl _ _)))
        have hx : x = s.lastCommittedConfiguration := h4.resolve_right (fun h => hbnc h.2)
        have hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv →
            Descends W ft fv s.term s.version →
            (ft = sD.term ∧ fv = sD.version) ∨ (ft = s.term ∧ fv = s.version) := by
          intro ft fv hfc hf1 hf2
          rw [h1, h2] at hf2
          have := hanti _ _ _ _ hf1 (hmax ft fv hfc hf2)
          exact Or.inl ⟨this.1.symm, this.2.symm⟩
        rcases inv_lineage P W hinv srcD src sD s ptD pt pvD pv hD hs (by rw [h1, h2]; exact hdd)
          (by rw [h1, h2]; exact heq) hint with hl | hl
        · exact Or.inl (hx.trans hl)
        · exact Or.inr (h3.trans hl)
  · right
    refine ⟨hnone, ?_⟩
    rcases hr with ⟨-, -, hX⟩ | ⟨src, s, pt, pv, hs, h1, h2, -, h4⟩
    · exact hX
    · have hbnc : ¬ Committed W bt bv := fun hc => hnone bt bv hc (.refl _ _)
      rw [h4.resolve_right (fun h => hbnc h.2)]
      apply inv_root_lcc P W hinv src s pt pv hs
      intro ft fv hfc hfd
      rw [h1, h2] at hfd
      exact absurd hfd (hnone ft fv hfc)
