-- Prove2me | solution 1 for OpenSearchSafety.inv_elc
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:53:49.860199+00:00
-- url     : https://prove2.me/submissions/80168a22-7f90-48d7-92f7-5c3034320ae2

import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_descends_trans
import Theorems.Thm_OpenSearchSafety_inv_commit_quorum_after
import Theorems.Thm_OpenSearchSafety_inv_commit_quorum_first
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_first_committed
import Theorems.Thm_OpenSearchSafety_inv_first_committed_after
import Theorems.Thm_OpenSearchSafety_inv_pivot
import Theorems.Thm_OpenSearchSafety_inv_reign_first

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

/-- (Election leader completeness: design 2's L6, the core of design 1's Theorem LC) The base of every election record
for term `t` descends from every committed key of an older term. Proof: strong induction on `t`; the pivot of the base
and the first committed key above it (or above a root) have quorums of a common configuration (or of two compatible
bootstrap configurations), so some voter accepted that key before voting in `t` (`join_after_response`), which bounds
the base from below; the induction hypothesis or `pub_same_term` then makes the key an ancestor of the base. -/
theorem solution {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V) (hinv : Inv P W)
    (L : NodeId) (t bt : Nat) (bv : Int) (x y : VotingConfiguration) (J : List NodeId)
    (hrec : ElectionRecord P W L t bt bv x y J) (ct : Nat) (cv : Int) (hc : Committed W ct cv) (hlt : ct < t) :
    Descends W ct cv bt bv := by
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d e₁ e₂
    rcases inv_descends_key P W hinv _ _ _ _ e₁ with h | ⟨-, e₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ e₂ with ⟨h, h'⟩ | ⟨-, e₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  have hle : ∀ a b c d, Descends W a b c d → a ≤ c := by
    intro a b c d e
    rcases inv_descends_key P W hinv _ _ _ _ e with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  induction t using Nat.strongRecOn generalizing L bt bv x y J ct cv with
  | ind t IH =>
  obtain ⟨hbt, hr, hJ, hqx, hqy⟩ := id hrec
  -- leader completeness below `t`
  have LC : ∀ ct cv, Committed W ct cv → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → ct < s.term →
      s.term < t → Descends W ct cv s.term s.version := by
    intro ct cv hc src s pt pv hs h1 h2
    obtain ⟨L', F, pt', pv', hF, hFt, hFpt, hFd⟩ := inv_reign_first P W hinv src s pt pv hs
    obtain ⟨y', J', hrec'⟩ := hinv.pub_election L' F pt' pv' hF hFpt
    have := IH F.term (by omega) L' pt' pv' F.lastCommittedConfiguration y' J' hrec' ct cv hc (by omega)
    exact descends_trans W _ _ _ _ _ _ (.step _ _ _ _ _ _ this ⟨L', F, hF, rfl, rfl⟩) hFd
  -- committed keys below `t` are comparable
  have S3 : ∀ t₁ v₁ t₂ v₂, Committed W t₁ v₁ → Committed W t₂ v₂ → t₁ < t → t₂ < t →
      Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
    intro t₁ v₁ t₂ v₂ h₁ h₂ ht₁ ht₂
    obtain ⟨-, src₁, s₁, pt₁, pv₁, hs₁, e1, f1⟩ := inv_committed_published P W hinv _ _ h₁
    obtain ⟨-, src₂, s₂, pt₂, pv₂, hs₂, e2, f2⟩ := inv_committed_published P W hinv _ _ h₂
    rcases Nat.lt_trichotomy t₁ t₂ with h | h | h
    · left; have := LC _ _ h₁ _ _ _ _ hs₂ (by omega) (by omega); rwa [e2, f2] at this
    · rcases hinv.pub_same_term _ _ _ _ _ _ _ _ hs₁ hs₂ (by omega) with h' | h'
      · left; rwa [e1, f1, e2, f2] at h'
      · right; rwa [e1, f1, e2, f2] at h'
    · right; have := LC _ _ h₂ _ _ _ _ hs₁ (by omega) (by omega); rwa [e1, f1] at this
  -- a committed key of an older term accepted by a voter of `J` is an ancestor of the base
  have finish : ∀ c't c'v, Committed W c't c'v → c't < t →
      (∃ m, m ∈ J ∧ ∃ d, W.sent (.publishResponse m d ⟨c't, c'v⟩)) → Descends W c't c'v bt bv := by
    intro c't c'v hc' hlt' ⟨m, hmJ, d, hmr⟩
    obtain ⟨hme, j, hj, hjs, -, hjt, hjb⟩ := hJ m hmJ
    have hk := hinv.join_after_response j m d ⟨c't, c'v⟩ hj hmr hjs hme (by dsimp only; omega)
    obtain ⟨hc'pos, srcC, sC, ptC, pvC, hsC, eC, fC⟩ := inv_committed_published P W hinv _ _ hc'
    unfold KeyLE at hk
    unfold Below at hjb
    dsimp only at hk
    rcases hr with ⟨h0, -⟩ | ⟨srcB, sB, ptB, pvB, hsB, hBt, hBv, -⟩
    · exfalso; omega
    · rcases Nat.lt_or_ge c't bt with h5 | h5
      · have := LC _ _ hc' _ _ _ _ hsB (by omega) (by omega)
        rwa [hBt, hBv] at this
      · have h7 : c'v ≤ bv := by omega
        rcases hinv.pub_same_term _ _ _ _ _ _ _ _ hsC hsB (by omega) with h' | h'
        · rwa [eC, fC, hBt, hBv] at h'
        · rw [eC, fC, hBt, hBv] at h'
          rcases inv_descends_key P W hinv _ _ _ _ h' with ⟨h8, h9⟩ | ⟨-, h9⟩
          · rw [← h8, ← h9]; exact .refl _ _
          · omega
  rcases inv_pivot P W hinv bt bv x y hr with ⟨srcD, sD, ptD, pvD, hD, hcD, hdD, hmax, hk⟩ | ⟨hnone, hX⟩
  · -- (I) the base has a deepest committed ancestor `D`
    have hDt : sD.term < t := by have := hle _ _ _ _ hdD; omega
    rcases S3 _ _ _ _ hcD hc hDt hlt with hDC | hCD
    · by_cases heq : sD.term = ct ∧ sD.version = cv
      · rw [← heq.1, ← heq.2]; exact hdD
      · -- the first committed key `C'` after `D` on the way to the committed key
        obtain ⟨c't, c'v, hc', hdc', hne', hc'c, hint⟩ := inv_first_committed_after P W hinv _ _ _ _ hDC heq hc
        obtain ⟨A, hA, hqA⟩ := inv_commit_quorum_after P W hinv srcD sD ptD pvD hD c't c'v hc' hdc' hne' hint
        have hqJ : sD.lastAcceptedConfiguration.hasQuorum J = true := by
          rcases hk with h | h <;> rw [← h] <;> assumption
        obtain ⟨m, -, hmA, hmJ⟩ := quorum_intersect _ _ _ hqA hqJ
        have hb := finish c't c'v hc' (by have := hle _ _ _ _ hc'c; omega) ⟨m, hmJ, (hA m hmA).2⟩
        -- but `C'` lies strictly below the deepest committed ancestor `D`: contradiction
        exact absurd (hanti _ _ _ _ hdc' (hmax _ _ hc' hb)) hne'
    · exact descends_trans W _ _ _ _ _ _ hCD hdD
  · -- (II) the base has no committed ancestor: the first committed key of the committed key's branch
    obtain ⟨c't, c'v, hc', hc'c, hmin⟩ := inv_first_committed P W hinv ct cv hc
    obtain ⟨X', A, hX', hA, hqA⟩ := inv_commit_quorum_first P W hinv c't c'v hc' hmin
    obtain ⟨m, hmJ, hmA⟩ := hP x X' hX hX' J A (fun z hz => (hJ z hz).1) (fun z hz => (hA z hz).1) hqx hqA
    exact absurd (finish c't c'v hc' (by have := hle _ _ _ _ hc'c; omega) ⟨m, hmJ, (hA m hmA).2⟩)
      (hnone c't c'v hc')
