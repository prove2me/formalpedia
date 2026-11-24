-- Prove2me | solution 1 for TenChallenges.challenge_03_r2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:07:59.23672+00:00
-- url     : https://prove2.me/submissions/beb41613-3f8f-483c-8cd5-4ecd0852b484

import Definitions.Def_TenChallenges_Challenge_03
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
open TenChallenges

/-! ## Closed walks -/

/-- A closed walk of length `L` for the relation `R`. -/
private def CW {V : Type} (R : V → V → Prop) (L : ℕ) : Prop :=
  ∃ f : ℕ → V, f L = f 0 ∧ ∀ i < L, R (f i) (f (i + 1))

private lemma cw_sub {V : Type} {R : V → V → Prop} {L : ℕ} {f : ℕ → V}
    (hf : ∀ i < L, R (f i) (f (i + 1))) {a b : ℕ} (hab : a ≤ b) (hbL : b ≤ L)
    (he : f a = f b) : CW R (b - a) := by
  refine ⟨fun k => f (a + k), ?_, ?_⟩
  · simp only [Nat.add_zero]
    rw [Nat.add_sub_cancel' hab]
    exact he.symm
  · intro i hi
    have := hf (a + i) (by omega)
    simpa [Nat.add_assoc] using this

private lemma cw_rot {V : Type} {R : V → V → Prop} {L : ℕ} {f : ℕ → V}
    (h0 : f L = f 0) (hf : ∀ i < L, R (f i) (f (i + 1))) (i : ℕ) (hi : i < L) :
    ∃ g : ℕ → V, g 0 = f i ∧ g L = g 0 ∧ ∀ k < L, R (g k) (g (k + 1)) := by
  refine ⟨fun k => f ((i + k) % L), by simp [Nat.mod_eq_of_lt hi], by simp, ?_⟩
  intro k _
  have hL : 0 < L := by omega
  have key : (i + (k + 1)) % L = ((i + k) % L + 1) % L := by
    rw [Nat.mod_add_mod, Nat.add_assoc]
  have hm : (i + k) % L < L := Nat.mod_lt _ hL
  simp only
  rw [key]
  by_cases h : (i + k) % L + 1 < L
  · rw [Nat.mod_eq_of_lt h]
    exact hf _ hm
  · have h' : (i + k) % L + 1 = L := by omega
    rw [h', Nat.mod_self, ← h0]
    have := hf ((i + k) % L) hm
    rwa [h'] at this

private lemma cw_min {V : Type} {R : V → V → Prop} {L : ℕ} (hL : 1 ≤ L) (h : CW R L) :
    ∃ M, 1 ≤ M ∧ M ≤ L ∧ CW R M ∧ ∀ M', 1 ≤ M' → M' < M → ¬ CW R M' := by
  classical
  have hex : ∃ M, 1 ≤ M ∧ CW R M := ⟨L, hL, h⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hL, h⟩,
    (Nat.find_spec hex).2, ?_⟩
  intro M' h1 h2 hc
  exact Nat.find_min hex h2 ⟨h1, hc⟩

/-- Lifting a closed walk through a contraction of `y` into `x`. -/
private lemma cw_lift {V : Type} {N N' : V → Finset V} {x y : V} (hy : x ∈ N y)
    (h1 : ∀ v w, w ∈ N' v → w ≠ x → w ∈ N v)
    (h2 : ∀ v, x ∈ N' v → x ∈ N v ∨ y ∈ N v)
    {L : ℕ} (hL : 1 ≤ L) (h : CW (fun u w => w ∈ N' u) L) :
    ∃ L', 1 ≤ L' ∧ L' ≤ L + 1 ∧ CW (fun u w => w ∈ N u) L' := by
  classical
  obtain ⟨M, hM1, hML, ⟨f, hf0, hf⟩, hmin⟩ := cw_min hL h
  by_cases hx : ∃ i < M, f i = x
  · obtain ⟨i, hi, hfi⟩ := hx
    obtain ⟨g, hg0, hgM, hg⟩ := cw_rot (R := fun u w => w ∈ N' u) hf0 hf i hi
    rw [hfi] at hg0
    have hgx : ∀ b, 0 < b → b < M → g b ≠ x := by
      intro b hb1 hb2 hgb
      have := cw_sub (R := fun u w => w ∈ N' u) (f := g) hg (Nat.zero_le b) hb2.le (by rw [hg0, hgb])
      exact hmin (b - 0) (by omega) (by omega) this
    have hlast := hg (M - 1) (by omega)
    have hM' : M - 1 + 1 = M := by omega
    rw [hM', hgM, hg0] at hlast
    rcases h2 _ hlast with hxN | hyN
    · refine ⟨M, hM1, by omega, g, hgM, ?_⟩
      intro k hk
      by_cases hk' : k + 1 < M
      · exact h1 _ _ (hg k hk) (hgx _ (by omega) hk')
      · have : k = M - 1 := by omega
        subst this
        rw [hM', hgM, hg0]
        exact hxN
    · refine ⟨M + 1, by omega, by omega,
        fun k => if k < M then g k else if k = M then y else x, ?_, ?_⟩
      · simp [hg0]
        intro h; omega
      · intro k hk
        by_cases hk1 : k + 1 < M
        · simp only [show k < M by omega, hk1, if_true]
          exact h1 _ _ (hg k (by omega)) (hgx _ (by omega) hk1)
        · by_cases hk2 : k + 1 = M
          · have : k = M - 1 := by omega
            subst this
            simp only [show M - 1 < M by omega, if_true, hM', lt_irrefl, if_false]
            exact hyN
          · have : k = M := by omega
            subst this
            simp only [lt_irrefl, if_false, if_true, show ¬ (k + 1 < k) by omega,
              show ¬ (k + 1 = k) by omega]
            exact hy
  · push Not at hx
    refine ⟨M, hM1, by omega, f, hf0, ?_⟩
    intro k hk
    apply h1 _ _ (hf k hk)
    by_cases hk' : k + 1 < M
    · exact hx _ hk'
    · have : k + 1 = M := by omega
      rw [this, hf0]
      exact hx 0 (by omega)

/-- From a closed walk to a cycle. -/
private lemma cw_cycle {V : Type} (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v) {L : ℕ}
    (hL : 1 ≤ L) (h : CW G.Adj L) : ∃ ℓ, 2 ≤ ℓ ∧ ℓ ≤ L ∧ G.HasCycleOfLength ℓ := by
  obtain ⟨M, hM1, hML, ⟨f, hf0, hf⟩, hmin⟩ := cw_min hL h
  have hinj : ∀ a b, a < b → b < M → f a ≠ f b := by
    intro a b hab hbM he
    exact hmin (b - a) (by omega) (by omega) (cw_sub hf hab.le hbM.le he)
  have hM2 : 2 ≤ M := by
    by_contra hc
    have : M = 1 := by omega
    subst this
    have := hf 0 (by omega)
    rw [hf0] at this
    exact hloop _ this
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  refine ⟨k + 1, hM2, hML, fun i => f i, ?_, ?_⟩
  · intro i j hij
    simp only at hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hinj _ _ hlt j.isLt hij
    · exact hinj _ _ hlt i.isLt hij.symm
  · intro i
    simp only
    rw [finRotate_apply, Fin.val_add_one]
    split_ifs with hi
    · have := hf i i.isLt
      have hi' : (i : ℕ) = k := by rw [hi]; simp
      rw [hi', hf0] at this
      rwa [hi']
    · exact hf i i.isLt

private lemma cw_mono {V : Type} {R R' : V → V → Prop} (hR : ∀ u w, R u w → R' u w) {L : ℕ}
    (h : CW R L) : CW R' L := by
  obtain ⟨f, h0, hf⟩ := h
  exact ⟨f, h0, fun i hi => hR _ _ (hf i hi)⟩

/-! ## The induction on finite digraphs with out-degrees in `{1, 2}` -/

/-- Number of vertices of out-degree one. -/
private def tc {V : Type} [DecidableEq V] (S : Finset V) (N : V → Finset V) : ℕ :=
  (S.filter (fun v => (N v).card = 1)).card

/-- In-degree. -/
private def ind {V : Type} [DecidableEq V] (S : Finset V) (N : V → Finset V) (x : V) : ℕ :=
  (S.filter (fun v => x ∈ N v)).card

private def Valid {V : Type} (S : Finset V) (N : V → Finset V) : Prop :=
  ∀ v ∈ S, N v ⊆ S ∧ v ∉ N v ∧ 1 ≤ (N v).card ∧ (N v).card ≤ 2

private def Concl {V : Type} [DecidableEq V] (S : Finset V) (N : V → Finset V) : Prop :=
  ∃ L, 1 ≤ L ∧ 2 * L ≤ S.card + max (tc S N) 1 ∧ CW (fun u w => w ∈ N u) L

private lemma sum_ind {V : Type} [DecidableEq V] {S : Finset V} {N : V → Finset V}
    (hv : Valid S N) : (∑ x ∈ S, ind S N x) + tc S N = 2 * S.card := by
  have e1 : (∑ x ∈ S, ind S N x) = ∑ v ∈ S, (N v).card := by
    have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := S) (t := S)
      (r := fun v x => x ∈ N v)
    unfold ind
    change ∑ b ∈ S, (Finset.bipartiteBelow (fun v x => x ∈ N v) S b).card = _
    rw [← this]
    apply Finset.sum_congr rfl
    intro v hvS
    unfold Finset.bipartiteAbove
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hv v hvS).1]
  rw [e1, tc, Finset.card_filter, ← Finset.sum_add_distrib]
  rw [show 2 * S.card = ∑ v ∈ S, 2 by simp [mul_comm]]
  apply Finset.sum_congr rfl
  intro v hvS
  obtain ⟨_, _, h3, h4⟩ := hv v hvS
  split_ifs <;> omega

private lemma step {V : Type} [DecidableEq V] (n : ℕ)
    (IH : ∀ m < n, ∀ (S : Finset V) (N : V → Finset V), S.card = m → S.Nonempty →
      Valid S N → Concl S N)
    (S : Finset V) (N : V → Finset V) (hn : S.card = n) (hne : S.Nonempty) (hv : Valid S N)
    (ht : 1 ≤ tc S N) : Concl S N := by
  have hsum := sum_ind hv
  have hmax : max (tc S N) 1 = tc S N := max_eq_left ht
  have hnpos : 0 < n := hn ▸ Finset.card_pos.mpr hne
  -- Case A: a vertex of in-degree zero.
  by_cases hA : ∃ x ∈ S, ind S N x = 0
  · obtain ⟨x, hxS, hx0⟩ := hA
    have hxN : ∀ v ∈ S, x ∉ N v := by
      intro v hv' hxv
      have hmem : v ∈ S.filter (fun v => x ∈ N v) := Finset.mem_filter.mpr ⟨hv', hxv⟩
      unfold ind at hx0
      rw [Finset.card_eq_zero] at hx0
      rw [hx0] at hmem
      simp at hmem
    have hv' : Valid (S.erase x) N := by
      intro v hv2
      obtain ⟨_, hvS⟩ := Finset.mem_erase.mp hv2
      obtain ⟨h1, h2, h3, h4⟩ := hv v hvS
      refine ⟨?_, h2, h3, h4⟩
      intro w hw
      exact Finset.mem_erase.mpr ⟨fun hwx => hxN v hvS (hwx ▸ hw), h1 hw⟩
    have hne' : (S.erase x).Nonempty := by
      obtain ⟨h1, h2, h3, _⟩ := hv x hxS
      obtain ⟨w, hw⟩ := Finset.card_pos.mp h3
      exact ⟨w, Finset.mem_erase.mpr ⟨fun h => h2 (h ▸ hw), h1 hw⟩⟩
    have hcard : (S.erase x).card = n - 1 := by rw [Finset.card_erase_of_mem hxS, hn]
    obtain ⟨L, hL1, hL2, hL3⟩ := IH (n - 1) (by omega) _ _ hcard hne' hv'
    have htc : tc (S.erase x) N ≤ tc S N :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
    have hm : max (tc (S.erase x) N) 1 ≤ max (tc S N) 1 := max_le_max htc le_rfl
    refine ⟨L, hL1, ?_, hL3⟩
    rw [hcard] at hL2
    omega
  push Not at hA
  -- Case B: a vertex of in-degree one whose in-neighbour has out-degree two.
  by_cases hB : ∃ x ∈ S, ∃ y ∈ S, x ∈ N y ∧ (N y).card = 2 ∧ ∀ v ∈ S, x ∈ N v → v = y
  · obtain ⟨x, hxS, y, hyS, hxy, hy2, huniq⟩ := hB
    have hyx : y ≠ x := fun h => (hv y hyS).2.1 (h ▸ hxy)
    set N' : V → Finset V := fun v => (N v).erase x with hN'
    have hN'eq : ∀ v ∈ S, v ≠ y → N' v = N v := by
      intro v hvS hvy
      exact Finset.erase_eq_of_notMem (fun h => hvy (huniq v hvS h))
    have hv' : Valid (S.erase x) N' := by
      intro v hv2
      obtain ⟨hvx, hvS⟩ := Finset.mem_erase.mp hv2
      obtain ⟨h1, h2, h3, h4⟩ := hv v hvS
      refine ⟨Finset.erase_subset_erase _ h1, fun h => h2 (Finset.mem_of_mem_erase h), ?_, ?_⟩
      · by_cases hvy : v = y
        · subst hvy
          simp only [hN', Finset.card_erase_of_mem hxy, hy2]
          omega
        · rw [hN'eq v hvS hvy]; exact h3
      · exact (Finset.card_erase_le).trans h4
    have hne' : (S.erase x).Nonempty := ⟨y, Finset.mem_erase.mpr ⟨hyx, hyS⟩⟩
    have hcard : (S.erase x).card = n - 1 := by rw [Finset.card_erase_of_mem hxS, hn]
    obtain ⟨L, hL1, hL2, hL3⟩ := IH (n - 1) (by omega) _ _ hcard hne' hv'
    have htc : tc (S.erase x) N' ≤ tc S N + 1 := by
      unfold tc
      refine (Finset.card_le_card ?_).trans (Finset.card_insert_le y _)
      intro v hv2
      rw [Finset.mem_filter] at hv2
      obtain ⟨hv3, hv4⟩ := hv2
      obtain ⟨_, hvS⟩ := Finset.mem_erase.mp hv3
      by_cases hvy : v = y
      · exact Finset.mem_insert.mpr (Or.inl hvy)
      · rw [hN'eq v hvS hvy] at hv4
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hvS, hv4⟩))
    have hm : max (tc (S.erase x) N') 1 ≤ tc S N + 1 := max_le htc (by omega)
    refine ⟨L, hL1, ?_, cw_mono (fun u w h => Finset.mem_of_mem_erase h) hL3⟩
    rw [hcard] at hL2
    omega
  push Not at hB
  -- Case C: some vertex of in-degree at most one.
  have hlt : ∑ x ∈ S, ind S N x < ∑ x ∈ S, 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    omega
  obtain ⟨x, hxS, hx2⟩ := Finset.exists_lt_of_sum_lt hlt
  have hx1 : ind S N x = 1 := by have := hA x hxS; omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hx1
  have hyF : y ∈ S.filter (fun v => x ∈ N v) := by rw [hy]; exact Finset.mem_singleton_self y
  have hyS : y ∈ S := (Finset.mem_filter.mp hyF).1
  have hxy : x ∈ N y := (Finset.mem_filter.mp hyF).2
  have huniq : ∀ v ∈ S, x ∈ N v → v = y := by
    intro v hvS hxv
    have : v ∈ S.filter (fun v => x ∈ N v) := Finset.mem_filter.mpr ⟨hvS, hxv⟩
    rw [hy] at this
    exact Finset.mem_singleton.mp this
  have hy1 : (N y).card = 1 := by
    obtain ⟨_, _, h3, h4⟩ := hv y hyS
    have := hB x hxS y hyS hxy
    by_contra hc
    have h2 : (N y).card = 2 := by omega
    obtain ⟨v, hvS, hxv, hvy⟩ := this h2
    exact hvy (huniq v hvS hxv)
  have hNy : N y = {x} := by
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hy1
    rw [hz] at hxy ⊢
    rw [Finset.mem_singleton.mp hxy]
  have hyx : y ≠ x := fun h => (hv y hyS).2.1 (h ▸ hxy)
  have hytc : y ∈ S.filter (fun v => (N v).card = 1) := Finset.mem_filter.mpr ⟨hyS, hy1⟩
  by_cases ht2 : 2 ≤ tc S N
  · -- Case C1: contract `y` into `x`.
    by_cases hyxN : y ∈ N x
    · have hpair : ({x, y} : Finset V) ⊆ S := by
        intro w hw
        rcases Finset.mem_insert.mp hw with h | h
        · exact h ▸ hxS
        · exact (Finset.mem_singleton.mp h) ▸ hyS
      have h2 : 2 ≤ n := by
        have := Finset.card_le_card hpair
        rw [Finset.card_pair hyx.symm] at this
        omega
      refine ⟨2, by omega, by omega, fun k => if k = 1 then y else x, by simp, ?_⟩
      intro i hi
      rcases (show i = 0 ∨ i = 1 by omega) with h | h
      · subst h; simpa using hyxN
      · subst h; simpa using hxy
    · set N' : V → Finset V := fun v => if y ∈ N v then insert x ((N v).erase y) else N v
        with hN'
      have hcardeq : ∀ v ∈ S, v ≠ y → (N' v).card = (N v).card := by
        intro v hvS hvy
        simp only [hN']
        split_ifs with h
        · have hxv : x ∉ (N v).erase y := fun h' =>
            hvy (huniq v hvS (Finset.mem_of_mem_erase h'))
          rw [Finset.card_insert_of_notMem hxv, Finset.card_erase_of_mem h]
          have := Finset.card_pos.mpr ⟨y, h⟩
          omega
        · rfl
      have hv' : Valid (S.erase y) N' := by
        intro v hv2
        obtain ⟨hvy, hvS⟩ := Finset.mem_erase.mp hv2
        obtain ⟨h1, h2, h3, h4⟩ := hv v hvS
        refine ⟨?_, ?_, by rw [hcardeq v hvS hvy]; exact h3, by rw [hcardeq v hvS hvy]; exact h4⟩
        · simp only [hN']
          split_ifs with h
          · intro w hw
            rcases Finset.mem_insert.mp hw with hw | hw
            · exact hw ▸ Finset.mem_erase.mpr ⟨hyx.symm, hxS⟩
            · exact Finset.erase_subset_erase _ h1 hw
          · intro w hw
            exact Finset.mem_erase.mpr ⟨fun hwy => h (hwy ▸ hw), h1 hw⟩
        · simp only [hN']
          split_ifs with h
          · intro hm
            rcases Finset.mem_insert.mp hm with hm | hm
            · exact hyxN (hm ▸ h)
            · exact h2 (Finset.mem_of_mem_erase hm)
          · exact h2
      have hne' : (S.erase y).Nonempty := ⟨x, Finset.mem_erase.mpr ⟨hyx.symm, hxS⟩⟩
      have hcard : (S.erase y).card = n - 1 := by rw [Finset.card_erase_of_mem hyS, hn]
      obtain ⟨L, hL1, hL2, hL3⟩ := IH (n - 1) (by omega) _ _ hcard hne' hv'
      have htc : tc (S.erase y) N' ≤ tc S N - 1 := by
        unfold tc
        have : (S.erase y).filter (fun v => (N' v).card = 1) ⊆
            (S.filter (fun v => (N v).card = 1)).erase y := by
          intro v hv2
          rw [Finset.mem_filter] at hv2
          obtain ⟨hv3, hv4⟩ := hv2
          obtain ⟨hvy, hvS⟩ := Finset.mem_erase.mp hv3
          rw [hcardeq v hvS hvy] at hv4
          exact Finset.mem_erase.mpr ⟨hvy, Finset.mem_filter.mpr ⟨hvS, hv4⟩⟩
        refine (Finset.card_le_card this).trans ?_
        rw [Finset.card_erase_of_mem hytc]
      have hm : max (tc (S.erase y) N') 1 ≤ tc S N - 1 := max_le htc (by omega)
      have h1 : ∀ v w, w ∈ N' v → w ≠ x → w ∈ N v := by
        intro v w hw hwx
        simp only [hN'] at hw
        split_ifs at hw
        · rcases Finset.mem_insert.mp hw with hw | hw
          · exact absurd hw hwx
          · exact Finset.mem_of_mem_erase hw
        · exact hw
      have h2 : ∀ v, x ∈ N' v → x ∈ N v ∨ y ∈ N v := by
        intro v hv2
        simp only [hN'] at hv2
        split_ifs at hv2 with h
        · exact Or.inr h
        · exact Or.inl hv2
      obtain ⟨L', hL'1, hL'2, hL'3⟩ := cw_lift hxy h1 h2 hL1 hL3
      refine ⟨L', hL'1, ?_, hL'3⟩
      rw [hcard] at hL2
      omega
  · -- Case C2: `y` is the only vertex of out-degree one; delete `x` and `y`.
    have ht1 : tc S N = 1 := by omega
    have hfil : S.filter (fun v => (N v).card = 1) = {y} := by
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp ht1
      rw [hz] at hytc ⊢
      rw [Finset.mem_singleton.mp hytc]
    have hdeg2 : ∀ v ∈ S, v ≠ y → (N v).card = 2 := by
      intro v hvS hvy
      obtain ⟨_, _, h3, h4⟩ := hv v hvS
      by_contra hc
      have h1' : (N v).card = 1 := by omega
      have : v ∈ S.filter (fun v => (N v).card = 1) := Finset.mem_filter.mpr ⟨hvS, h1'⟩
      rw [hfil] at this
      exact hvy (Finset.mem_singleton.mp this)
    have hin2 : ∀ v ∈ S, v ≠ x → 2 ≤ ind S N v := by
      intro v hvS hvx
      by_contra hc
      have hv1 : ind S N v = 1 := by have := hA v hvS; omega
      obtain ⟨y', hy'⟩ := Finset.card_eq_one.mp hv1
      have hy'F : y' ∈ S.filter (fun w => v ∈ N w) := by
        rw [hy']; exact Finset.mem_singleton_self y'
      have hy'S : y' ∈ S := (Finset.mem_filter.mp hy'F).1
      have hvy' : v ∈ N y' := (Finset.mem_filter.mp hy'F).2
      have huniq' : ∀ w ∈ S, v ∈ N w → w = y' := by
        intro w hwS hvw
        have : w ∈ S.filter (fun w => v ∈ N w) := Finset.mem_filter.mpr ⟨hwS, hvw⟩
        rw [hy'] at this
        exact Finset.mem_singleton.mp this
      have hy'1 : (N y').card ≠ 2 := by
        intro h2
        obtain ⟨w, hwS, hvw, hwy⟩ := hB v hvS y' hy'S hvy' h2
        exact hwy (huniq' w hwS hvw)
      have hy'y : y' = y := by
        by_contra hne
        exact hy'1 (hdeg2 y' hy'S hne)
      rw [hy'y, hNy] at hvy'
      exact hvx (Finset.mem_singleton.mp hvy')
    have hyS' : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hyx, hyS⟩
    set T := (S.erase x).erase y with hT
    have hTcard : T.card = n - 2 := by
      rw [hT, Finset.card_erase_of_mem hyS', Finset.card_erase_of_mem hxS, hn]
      omega
    have hindy : ind S N y ≤ 2 := by
      rw [← Finset.add_sum_erase S _ hxS, ← Finset.add_sum_erase (S.erase x) _ hyS'] at hsum
      have hT2 : T.card • 2 ≤ ∑ v ∈ T, ind S N v := by
        apply Finset.card_nsmul_le_sum
        intro v hvT
        obtain ⟨_, hv2⟩ := Finset.mem_erase.mp hvT
        obtain ⟨hvx, hvS⟩ := Finset.mem_erase.mp hv2
        exact hin2 v hvS hvx
      rw [nsmul_eq_mul, Nat.cast_id, hTcard] at hT2
      rw [hx1] at hsum
      have hn2 : 2 ≤ n := by
        have := Finset.card_le_card (show ({x, y} : Finset V) ⊆ S by
          intro w hw
          rcases Finset.mem_insert.mp hw with h | h
          · exact h ▸ hxS
          · exact (Finset.mem_singleton.mp h) ▸ hyS)
        rw [Finset.card_pair hyx.symm] at this
        omega
      rw [← hT, hn] at hsum
      have : (n - 2) * 2 = 2 * n - 4 := by omega
      omega
    have hxnot : ∀ v ∈ T, x ∉ N v := by
      intro v hvT hxv
      obtain ⟨hvy, hv2⟩ := Finset.mem_erase.mp hvT
      obtain ⟨_, hvS⟩ := Finset.mem_erase.mp hv2
      exact hvy (huniq v hvS hxv)
    set N' : V → Finset V := fun v => ((N v).erase x).erase y with hN'
    have hN'eq : ∀ v ∈ T, N' v = (N v).erase y := by
      intro v hvT
      simp only [hN', Finset.erase_eq_of_notMem (hxnot v hvT)]
    have hv' : Valid T N' := by
      intro v hvT
      obtain ⟨hvy, hv2⟩ := Finset.mem_erase.mp hvT
      obtain ⟨hvx, hvS⟩ := Finset.mem_erase.mp hv2
      obtain ⟨h1, h2, _, _⟩ := hv v hvS
      have hc2 := hdeg2 v hvS hvy
      refine ⟨Finset.erase_subset_erase _ (Finset.erase_subset_erase _ h1),
        fun h => h2 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)), ?_, ?_⟩
      · rw [hN'eq v hvT]
        have := Finset.pred_card_le_card_erase (s := N v) (a := y)
        omega
      · rw [hN'eq v hvT]
        exact (Finset.card_erase_le).trans hc2.le
    have hyin : 1 < (S.filter (fun v => y ∈ N v)).card := by
      have := hin2 y hyS hyx
      unfold ind at this
      omega
    obtain ⟨v, hvF, hvx⟩ := Finset.exists_mem_ne hyin x
    obtain ⟨hvS, hyv⟩ := Finset.mem_filter.mp hvF
    have hvy : v ≠ y := fun h => (hv v hvS).2.1 (h ▸ hyv)
    have hne' : T.Nonempty :=
      ⟨v, Finset.mem_erase.mpr ⟨hvy, Finset.mem_erase.mpr ⟨hvx, hvS⟩⟩⟩
    obtain ⟨L, hL1, hL2, hL3⟩ := IH (n - 2) (by omega) _ _ hTcard hne' hv'
    have htc : tc T N' ≤ ind S N y := by
      unfold tc ind
      apply Finset.card_le_card
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwT, hw1⟩ := hw
      obtain ⟨hwy, hw2⟩ := Finset.mem_erase.mp hwT
      obtain ⟨_, hwS⟩ := Finset.mem_erase.mp hw2
      refine Finset.mem_filter.mpr ⟨hwS, ?_⟩
      by_contra hyw
      rw [hN'eq w hwT, Finset.erase_eq_of_notMem hyw, hdeg2 w hwS hwy] at hw1
      omega
    have hm : max (tc T N') 1 ≤ 2 := max_le (by omega) (by omega)
    refine ⟨L, hL1, ?_,
      cw_mono (fun u w h => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)) hL3⟩
    rw [hTcard] at hL2
    rw [ht1]
    omega

private lemma main_ind {V : Type} [DecidableEq V] (n : ℕ) : ∀ (S : Finset V) (N : V → Finset V),
    S.card = n → S.Nonempty → Valid S N → Concl S N := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S N hn hne hv
    by_cases ht : 1 ≤ tc S N
    · exact step n IH S N hn hne hv ht
    · -- No vertex of out-degree one: delete one arc.
      have ht0 : tc S N = 0 := by omega
      have hno : ∀ v ∈ S, (N v).card ≠ 1 := by
        intro v hvS h1
        have : v ∈ S.filter (fun v => (N v).card = 1) := Finset.mem_filter.mpr ⟨hvS, h1⟩
        unfold tc at ht0
        rw [Finset.card_eq_zero] at ht0
        rw [ht0] at this
        simp at this
      obtain ⟨a, haS⟩ := hne
      obtain ⟨_, _, h3, h4⟩ := hv a haS
      have ha2 : (N a).card = 2 := by have := hno a haS; omega
      obtain ⟨b, hb⟩ := Finset.card_pos.mp h3
      set N' : V → Finset V := Function.update N a ((N a).erase b) with hN'
      have hsub : ∀ v, N' v ⊆ N v := by
        intro v
        by_cases hva : v = a
        · subst hva; simp only [hN', Function.update_self]; exact Finset.erase_subset _ _
        · simp only [hN', Function.update_of_ne hva]; exact le_rfl
      have hv' : Valid S N' := by
        intro v hvS
        obtain ⟨h1, h2, h3, h4⟩ := hv v hvS
        refine ⟨(hsub v).trans h1, fun h => h2 (hsub v h), ?_,
          (Finset.card_le_card (hsub v)).trans h4⟩
        by_cases hva : v = a
        · subst hva
          simp only [hN', Function.update_self, Finset.card_erase_of_mem hb, ha2]
          omega
        · simp only [hN', Function.update_of_ne hva]; exact h3
      have ht' : 1 ≤ tc S N' := by
        unfold tc
        apply Finset.card_pos.mpr
        refine ⟨a, Finset.mem_filter.mpr ⟨haS, ?_⟩⟩
        simp only [hN', Function.update_self, Finset.card_erase_of_mem hb, ha2]
      have ht'1 : tc S N' ≤ 1 := by
        unfold tc
        refine (Finset.card_le_card ?_).trans (Finset.card_singleton a).le
        intro v hv2
        rw [Finset.mem_filter] at hv2
        obtain ⟨hvS, hv1⟩ := hv2
        by_contra hva
        rw [Finset.mem_singleton] at hva
        simp only [hN', Function.update_of_ne hva] at hv1
        exact hno v hvS hv1
      obtain ⟨L, hL1, hL2, hL3⟩ := step n IH S N' hn ⟨a, haS⟩ hv' ht'
      refine ⟨L, hL1, ?_, cw_mono (fun u w h => hsub u h) hL3⟩
      rw [ht0]
      have : max (tc S N') 1 = 1 := by omega
      omega

theorem solution : TenChallenges.statement_03 2 := by
  intro _ V _ _ G hloop hdeg
  classical
  have hN : ∀ v, ∃ s : Finset V, s ⊆ Finset.univ.filter (fun w => G.Adj v w) ∧ s.card = 2 := by
    intro v
    apply Finset.exists_subset_card_eq
    have := hdeg v
    unfold Digraph.outDegree at this
    have e : {w | G.Adj v w} = ↑(Finset.univ.filter (fun w => G.Adj v w)) := by ext; simp
    rw [e, Set.ncard_coe_finset] at this
    exact this
  choose N hN1 hN2 using hN
  have hadj : ∀ u w, w ∈ N u → G.Adj u w := by
    intro u w h
    have := hN1 u h
    simpa using this
  have hv : Valid Finset.univ N := by
    intro v _
    refine ⟨Finset.subset_univ _, fun h => hloop v (hadj v v h), by rw [hN2]; omega, by rw [hN2]⟩
  obtain ⟨L, hL1, hL2, hL3⟩ := main_ind _ Finset.univ N rfl Finset.univ_nonempty hv
  have htc : tc Finset.univ N = 0 := by
    unfold tc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    rw [hN2]
    omega
  obtain ⟨ℓ, h2, hle, hcyc⟩ := cw_cycle G hloop hL1 (cw_mono hadj hL3)
  refine ⟨ℓ, h2, ?_, hcyc⟩
  rw [htc, Finset.card_univ] at hL2
  have : max 0 1 = 1 := rfl
  omega
