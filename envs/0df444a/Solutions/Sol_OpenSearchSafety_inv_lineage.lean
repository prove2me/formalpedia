-- Prove2me | solution 1 for OpenSearchSafety.inv_lineage
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:09.83092+00:00
-- url     : https://prove2.me/submissions/3fbae822-a5f5-4af8-883c-bc2f9a2153a5

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_descends_key

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

/-- (Path summary; design 2's lineage lemma) Along a non-trivial descent from a publication `D` to a publication `E` with
no committed key strictly in between, `D`'s last accepted configuration is one of `E`'s two configurations: the last
committed configuration changes only below a committed key, and the last accepted one only when the last committed one
is the parent's last accepted one. -/
theorem solution {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD srcE : NodeId) (sD sE : ClusterState V) (ptD ptE : Nat) (pvD pvE : Int)
    (hD : W.sent (.publishRequest srcD sD ptD pvD)) (hE : W.sent (.publishRequest srcE sE ptE pvE))
    (h : Descends W sD.term sD.version sE.term sE.version)
    (hne : ¬ (sD.term = sE.term ∧ sD.version = sE.version))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv sE.term sE.version →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = sE.term ∧ fv = sE.version)) :
    sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨
    sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration := by
  suffices key : ∀ t' v', Descends W sD.term sD.version t' v' → ¬ (sD.term = t' ∧ sD.version = v') →
      (∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv t' v' →
        (ft = sD.term ∧ fv = sD.version) ∨ (ft = t' ∧ fv = v')) →
      ∀ srcE sE ptE pvE, W.sent (.publishRequest srcE sE ptE pvE) → sE.term = t' → sE.version = v' →
      sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨
      sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration from
    key _ _ h hne hint srcE sE ptE pvE hE rfl rfl
  intro t' v' hd
  induction hd with
  | refl => intro hne; exact absurd ⟨rfl, rfl⟩ hne
  | step t₁ v₁ t₂ v₂ hd₁ hp ih =>
    intro _ hint srcE sE ptE pvE hE ht hv
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    have hpar : Parent W t₁ v₁ t₂ v₂ := ⟨src₁, s₁, hs₁, h1, h2⟩
    obtain ⟨-, -, e3, e4⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hE hs₁ (ht.trans h1.symm) (hv.trans h2.symm)
    have hDpos := (hinv.pub_wf _ _ _ _ hD).2.1
    have hEv := (hinv.pub_wf _ _ _ _ hE).2.2.2.1
    have ht₁ : 1 ≤ t₁ := by
      rcases inv_descends_key P W hinv _ _ _ _ hd₁ with ⟨h5, -⟩ | ⟨h5, -⟩ <;> omega
    obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, hR1, hR2⟩ := hinv.pub_parent _ _ _ _ hE (by omega)
    have h3' : s₂.term = t₁ := h3.trans e3
    have h4' : s₂.version = v₁ := h4.trans e4
    by_cases hD1 : sD.term = t₁ ∧ sD.version = v₁
    · -- the parent of `E` is `D`
      obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hD hs₂ (hD1.1.trans h3'.symm)
        (hD1.2.trans h4'.symm)
      by_cases hac : sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration
      · exact Or.inr hac
      · exact Or.inl (hR2 hac)
    · -- the parent is strictly between `D` and `E`, hence not committed
      have hnc : ¬ Committed W t₁ v₁ := by
        intro hc
        rcases hint t₁ v₁ hc hd₁ (.step _ _ _ _ _ _ (.refl _ _) hpar) with h5 | ⟨-, h5⟩
        · exact hD1 ⟨h5.1.symm, h5.2.symm⟩
        · omega
      have hl : sE.lastCommittedConfiguration = s₂.lastCommittedConfiguration := by
        rcases hR1 with hl | ⟨-, hc⟩
        · exact hl
        · rw [e3, e4] at hc; exact absurd hc hnc
      have ih' := ih hD1 (fun ft fv hfc hf1 hf2 => by
          rcases hint ft fv hfc hf1 (.step _ _ _ _ _ _ hf2 hpar) with h5 | ⟨-, h5⟩
          · exact Or.inl h5
          · exfalso
            rcases inv_descends_key P W hinv _ _ _ _ hf2 with ⟨-, h6⟩ | ⟨-, h6⟩ <;> omega)
        src₂ s₂ pt₂ pv₂ hs₂ h3' h4'
      rcases ih' with h5 | h5
      · exact Or.inl (hl.trans h5)
      · by_cases hac : sE.lastAcceptedConfiguration = s₂.lastAcceptedConfiguration
        · exact Or.inr (hac.trans h5)
        · exact Or.inl ((hR2 hac).trans h5)
