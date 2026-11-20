-- Prove2me | solution 1 for OPG37271.two_regular_connected_iso_cycleGraph
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:16:21.193913+00:00
-- url     : https://prove2.me/submissions/51682fdb-e889-4e03-957f-cb5e5e1c62e7

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

set_option autoImplicit false

open OPG37271

universe u

/-!
# Part 1: Every Finite Connected 2-Regular Simple Graph is Isomorphic to a Cycle Graph

Let `H : SimpleGraph W` on `[Fintype W]` be connected and 2-regular
(`∀ w : W, (H.neighborSet w).encard = 2`). Then `3 ≤ Fintype.card W` and `H` is isomorphic to
`SimpleGraph.fromRel (fun i j : Fin (Fintype.card W) => (i.val + 1) % Fintype.card W = j.val)`.
-/


private lemma two_neighbors_of_encard_eq_two {W : Type u} {H : SimpleGraph W} {w : W}
    (h2 : (H.neighborSet w).encard = 2) :
    ∃ a b : W, a ≠ b ∧ ∀ z : W, H.Adj w z ↔ z = a ∨ z = b := by
  rw [Set.encard_eq_two] at h2
  obtain ⟨a, b, hab, hset⟩ := h2
  refine ⟨a, b, hab, ?_⟩
  intro z
  change z ∈ H.neighborSet w ↔ z = a ∨ z = b
  rw [hset]
  simp

private lemma exists_unique_other_neighbor {W : Type u} {H : SimpleGraph W}
    (hreg : ∀ w : W, (H.neighborSet w).encard = 2) {u v : W} (huv : H.Adj u v) :
    ∃ x : W, H.Adj v x ∧ x ≠ u ∧ ∀ z : W, H.Adj v z → (z = u ∨ z = x) := by
  obtain ⟨a, b, hab, hiff⟩ := two_neighbors_of_encard_eq_two (hreg v)
  have hvu : H.Adj v u := huv.symm
  rcases (hiff u).mp hvu with rfl | rfl
  · refine ⟨b, (hiff b).mpr (Or.inr rfl), hab.symm, ?_⟩
    intro z hz
    exact (hiff z).mp hz
  · refine ⟨a, (hiff a).mpr (Or.inl rfl), hab, ?_⟩
    intro z hz
    rcases (hiff z).mp hz with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

private noncomputable def stepDart {W : Type u} {H : SimpleGraph W}
    (hreg : ∀ w : W, (H.neighborSet w).encard = 2)
    (d : {p : W × W // H.Adj p.1 p.2}) : {p : W × W // H.Adj p.1 p.2} :=
  let h := exists_unique_other_neighbor hreg d.2
  ⟨(d.1.2, Classical.choose h), (Classical.choose_spec h).1⟩

private lemma stepDart_fst {W : Type u} {H : SimpleGraph W}
    (hreg : ∀ w : W, (H.neighborSet w).encard = 2)
    (d : {p : W × W // H.Adj p.1 p.2}) :
    (stepDart hreg d).1.1 = d.1.2 := rfl

private lemma stepDart_snd_spec {W : Type u} {H : SimpleGraph W}
    (hreg : ∀ w : W, (H.neighborSet w).encard = 2)
    (d : {p : W × W // H.Adj p.1 p.2}) :
    H.Adj d.1.2 (stepDart hreg d).1.2 ∧
    (stepDart hreg d).1.2 ≠ d.1.1 ∧
    (∀ z : W, H.Adj d.1.2 z → z = d.1.1 ∨ z = (stepDart hreg d).1.2) :=
  Classical.choose_spec (exists_unique_other_neighbor hreg d.2)

/-- Every finite connected 2-regular simple graph has at least 3 vertices and is isomorphic to
the standard cycle graph on `Fin (Fintype.card W)`. -/
theorem solution
    {W : Type u} [Fintype W] (H : SimpleGraph W)
    (hne : Nonempty W) (hconn : H.Connected)
    (hreg : ∀ w : W, (H.neighborSet w).encard = 2) :
    3 ≤ Fintype.card W ∧
    Nonempty (H ≃g SimpleGraph.fromRel
      (fun i j : Fin (Fintype.card W) => (i.val + 1) % Fintype.card W = j.val)) := by
  classical
  obtain ⟨v₀⟩ := hne
  obtain ⟨v₁, v₂_init, hv12_ne, hv0_iff⟩ := two_neighbors_of_encard_eq_two (hreg v₀)
  have hv01 : H.Adj v₀ v₁ := (hv0_iff v₁).mpr (Or.inl rfl)
  have hv02 : H.Adj v₀ v₂_init := (hv0_iff v₂_init).mpr (Or.inr rfl)
  -- First prove `3 ≤ Fintype.card W` directly from `[v₀, v₁, v₂_init].Nodup`.
  have hcard3 : 3 ≤ Fintype.card W := by
    have hnd : [v₀, v₁, v₂_init].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        or_false, not_or, and_true, not_false_eq_true]
      exact ⟨⟨hv01.ne, hv02.ne⟩, hv12_ne⟩
    exact hnd.length_le_card
  -- Build the greedy dart orbit starting at `d₀ = (v₀, v₁)`.
  let d₀ : {p : W × W // H.Adj p.1 p.2} := ⟨(v₀, v₁), hv01⟩
  let D : ℕ → {p : W × W // H.Adj p.1 p.2} := fun k => (stepDart hreg)^[k] d₀
  let seq : ℕ → W := fun k => (D k).1.1
  have hD_step : ∀ k : ℕ, D (k + 1) = stepDart hreg (D k) := fun k =>
    Function.iterate_succ_apply' (stepDart hreg) k d₀
  have hD_snd : ∀ k : ℕ, (D k).1.2 = seq (k + 1) := by
    intro k
    change (D k).1.2 = (D (k + 1)).1.1
    rw [hD_step k, stepDart_fst]
  have hseq_adj : ∀ k : ℕ, H.Adj (seq k) (seq (k + 1)) := by
    intro k
    rw [← hD_snd k]
    exact (D k).2
  have hseq_ne_two : ∀ k : ℕ, seq (k + 2) ≠ seq k := by
    intro k
    have hspec := (stepDart_snd_spec hreg (D k)).2.1
    rwa [← hD_step k, hD_snd (k + 1)] at hspec
  have hseq_nbhd : ∀ k : ℕ, ∀ z : W,
      H.Adj (seq (k + 1)) z ↔ z = seq k ∨ z = seq (k + 2) := by
    intro k z
    have hspec := stepDart_snd_spec hreg (D k)
    have hsnd1 : (D k).1.2 = seq (k + 1) := hD_snd k
    have hsnd2 : (stepDart hreg (D k)).1.2 = seq (k + 2) := by
      rw [← hD_step k]
      exact hD_snd (k + 1)
    constructor
    · intro hz
      rw [← hsnd1] at hz
      rcases hspec.2.2 z hz with h1 | h2
      · exact Or.inl h1
      · rw [hsnd2] at h2
        exact Or.inr h2
    · rintro (rfl | rfl)
      · exact (hseq_adj k).symm
      · exact hseq_adj (k + 1)
  -- By Pigeonhole on `Fin (Fintype.card W + 1) → W`, `seq` must repeat.
  have hex_rep : ∃ m : ℕ, 0 < m ∧ ∃ i : ℕ, i < m ∧ seq m = seq i := by
    have hnot_inj : ¬ Function.Injective (fun k : Fin (Fintype.card W + 1) => seq k.val) := by
      intro hinj
      have hle := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_fin] at hle
      omega
    unfold Function.Injective at hnot_inj
    have hex_pair : ∃ a b : Fin (Fintype.card W + 1), seq a.val = seq b.val ∧ a ≠ b := by
      by_contra hall
      apply hnot_inj
      intro a b heq
      by_contra hne
      exact hall ⟨a, b, heq, hne⟩
    obtain ⟨a, b, hab_eq, hab_ne⟩ := hex_pair
    have hval_ne : a.val ≠ b.val := fun h => hab_ne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hval_ne with hlt | hgt
    · exact ⟨b.val, by omega, a.val, hlt, hab_eq.symm⟩
    · exact ⟨a.val, by omega, b.val, hgt, hab_eq⟩
  -- Let `m` be the smallest positive index that repeats an earlier vertex.
  obtain ⟨m, ⟨hm_pos, i₀, hi₀_lt, hseq_mi⟩, hmin_m⟩ :
      ∃ m : ℕ, (0 < m ∧ ∃ i : ℕ, i < m ∧ seq m = seq i) ∧
        ∀ k < m, ¬ (0 < k ∧ ∃ i : ℕ, i < k ∧ seq k = seq i) :=
    ⟨Nat.find hex_rep, Nat.find_spec hex_rep, fun k hk => Nat.find_min hex_rep hk⟩
  -- All indices `< m` have pairwise distinct `seq` values by minimality of `m`.
  have hinj_lt : ∀ a b : ℕ, a < m → b < m → seq a = seq b → a = b := by
    intro a b ha hb hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hmin_m b hb ⟨by omega, a, hlt, hab.symm⟩
    · exact hmin_m a ha ⟨by omega, b, hgt, hab⟩
  -- Prove `i₀ = 0` (the first repeat MUST return to `seq 0` by degree 2!).
  have hi₀_zero : i₀ = 0 := by
    by_contra hi₀_ne
    obtain ⟨i', rfl⟩ : ∃ i', i₀ = i' + 1 := ⟨i₀ - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hadj_prev : H.Adj (seq (i' + 1)) (seq m') := by
      rw [← hseq_mi]
      exact (hseq_adj m').symm
    rcases (hseq_nbhd i' (seq m')).mp hadj_prev with hprev1 | hprev2
    · have heq_idx := hinj_lt m' i' (by omega) (by omega) hprev1
      omega
    · by_cases hi2_lt : i' + 2 < m' + 1
      · have heq_idx : m' = i' + 2 := hinj_lt m' (i' + 2) (by omega) hi2_lt hprev2
        subst heq_idx
        exact hseq_ne_two (i' + 1) hseq_mi
      · have hm_eq : m' = i' + 1 := by omega
        subst hm_eq
        exact (hseq_adj (i' + 1)).ne hseq_mi.symm
  subst hi₀_zero
  -- Hence `seq m = seq 0`! Moreover `3 ≤ m` since `seq 1 ≠ seq 0` and `seq 2 ≠ seq 0`.
  have hm_ge3 : 3 ≤ m := by
    by_contra hlt3
    have hcases : m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl
    · exact (hseq_adj 0).ne hseq_mi.symm
    · exact hseq_ne_two 0 hseq_mi
  -- Let `C = Finset.image seq (Finset.range m)` be the cycle vertices.
  let C : Finset W := (Finset.range m).image seq
  -- Every vertex in `C` has BOTH of its `H`-neighbors in `C`!
  have hC_closed : ∀ x ∈ C, ∀ y : W, H.Adj x y → y ∈ C := by
    intro x hx y hxy
    rcases Finset.mem_image.mp hx with ⟨k, hk_mem, rfl⟩
    rw [Finset.mem_range] at hk_mem
    by_cases hk0 : k = 0
    · subst hk0
      -- `seq 0` has two distinct neighbors in `C`: `seq 1` and `seq (m - 1)`!
      have hadj1 : H.Adj (seq 0) (seq 1) := hseq_adj 0
      have hadjm1 : H.Adj (seq 0) (seq (m - 1)) := by
        rw [← hseq_mi]
        have hm1 : m - 1 + 1 = m := by omega
        simpa [hm1] using (hseq_adj (m - 1)).symm
      have hne_1_m1 : seq 1 ≠ seq (m - 1) := by
        intro heq
        have hidx := hinj_lt 1 (m - 1) (by omega) (by omega) heq
        omega
      -- Since `(H.neighborSet (seq 0)).encard = 2`, any neighbor `y` of `seq 0` is `seq 1` or `seq (m - 1)`!
      obtain ⟨a, b, _, hab_iff⟩ := two_neighbors_of_encard_eq_two (hreg (seq 0))
      have hsub : y = seq 1 ∨ y = seq (m - 1) := by
        have h1 := (hab_iff (seq 1)).mp hadj1
        have hm1 := (hab_iff (seq (m - 1))).mp hadjm1
        have hy := (hab_iff y).mp hxy
        rcases h1 with rfl | rfl <;> rcases hm1 with hA | hB
        · exact absurd hA.symm hne_1_m1
        · subst hB; exact hy
        · subst hA; exact hy.symm
        · exact absurd hB.symm hne_1_m1
      rcases hsub with rfl | rfl
      · exact Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rcases (hseq_nbhd k' y).mp hxy with rfl | rfl
      · exact Finset.mem_image.mpr ⟨k', Finset.mem_range.mpr (by omega), rfl⟩
      · by_cases hk2 : k' + 2 < m
        · exact Finset.mem_image.mpr ⟨k' + 2, Finset.mem_range.mpr hk2, rfl⟩
        · have hk2_eq : k' + 2 = m := by omega
          rw [hk2_eq, hseq_mi]
          exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  -- By connectedness of `H`, EVERY `w : W` lies in `C`!
  have hC_univ : ∀ w : W, w ∈ C := by
    intro w
    have hreach : H.Reachable (seq 0) w := hconn.preconnected (seq 0) w
    refine hreach.elim (fun p => ?_)
    have hwalk : ∀ {a b : W} (q : H.Walk a b), a ∈ C → b ∈ C := by
      intro a b q ha
      induction q with
      | nil => exact ha
      | cons hab _ ih => exact ih (hC_closed _ ha _ hab)
    exact hwalk p (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩)
  -- Therefore `C = Finset.univ`, so `m = Fintype.card W`!
  have hC_eq_univ : C = Finset.univ := Finset.eq_univ_iff_forall.mpr hC_univ
  have hC_card : C.card = m := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range m
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_range] at ha hb
      exact hinj_lt a b ha hb hab
  have hm_card : m = Fintype.card W := by
    rw [← hC_card, hC_eq_univ, Finset.card_univ]
  -- Construct the bijection `f : Fin (Fintype.card W) ≃ W` via `i ↦ seq i.val`.
  let fFun : Fin (Fintype.card W) → W := fun i => seq i.val
  have hf_inj : Function.Injective fFun := by
    intro i j hij
    have hi_lt : i.val < m := by have := i.isLt; omega
    have hj_lt : j.val < m := by have := j.isLt; omega
    exact Fin.ext (hinj_lt i.val j.val hi_lt hj_lt hij)
  have hf_bij : Function.Bijective fFun :=
    (Fintype.bijective_iff_injective_and_card fFun).mpr ⟨hf_inj, Fintype.card_fin _⟩
  let eqv : Fin (Fintype.card W) ≃ W := Equiv.ofBijective fFun hf_bij
  -- Verify adjacency preservation: `H.Adj (eqv i) (eqv j) ↔ CycleGraph.Adj i j`!
  let Cyc := SimpleGraph.fromRel
    (fun i j : Fin (Fintype.card W) => (i.val + 1) % Fintype.card W = j.val)
  have hcyc_fwd : ∀ i : Fin (Fintype.card W), H.Adj (eqv i) (eqv ⟨(i.val + 1) % Fintype.card W,
      Nat.mod_lt _ (by omega)⟩) := by
    intro i
    change H.Adj (seq i.val) (seq ((i.val + 1) % Fintype.card W))
    have hmod_eq : (i.val + 1) % Fintype.card W = (i.val + 1) % m := by rw [hm_card]
    rw [hmod_eq]
    by_cases hlast : i.val + 1 = m
    · rw [hlast, Nat.mod_self, ← hseq_mi, ← hlast]
      exact hseq_adj i.val
    · have hlt : i.val + 1 < m := by have := i.isLt; omega
      rw [Nat.mod_eq_of_lt hlt]
      exact hseq_adj i.val
  have hadj_map : ∀ i j : Fin (Fintype.card W), H.Adj (eqv i) (eqv j) ↔ Cyc.Adj i j := by
    intro i j
    rw [SimpleGraph.fromRel_adj]
    constructor
    · intro hij
      refine ⟨fun heq => hij.ne (congrArg eqv heq), ?_⟩
      -- The two distinct neighbors of `eqv i` in `H` are `eqv ((i + 1) % n)` and `eqv ((i + n - 1) % n)`!
      let inext : Fin (Fintype.card W) := ⟨(i.val + 1) % Fintype.card W, Nat.mod_lt _ (by omega)⟩
      let iprev : Fin (Fintype.card W) := ⟨(i.val + Fintype.card W - 1) % Fintype.card W, Nat.mod_lt _ (by omega)⟩
      have hprev_succ : (iprev.val + 1) % Fintype.card W = i.val := by
        have hi := i.isLt
        dsimp [iprev]
        by_cases hi0 : i.val = 0
        · rw [hi0]
          have h1 : (0 + Fintype.card W - 1) % Fintype.card W = Fintype.card W - 1 := by
            rw [Nat.zero_add]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_self]
        · have h1 : (i.val + Fintype.card W - 1) % Fintype.card W = i.val - 1 := by
            have heq : i.val + Fintype.card W - 1 = (i.val - 1) + Fintype.card W := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hi]
      have hadj_next : H.Adj (eqv i) (eqv inext) := hcyc_fwd i
      have hadj_prev : H.Adj (eqv i) (eqv iprev) := by
        have h := (hcyc_fwd iprev).symm
        have heq_fin : (⟨(iprev.val + 1) % Fintype.card W, Nat.mod_lt _ (by omega)⟩ : Fin (Fintype.card W)) = i :=
          Fin.ext hprev_succ
        rwa [heq_fin] at h
      have hne_np : inext ≠ iprev := by
        intro heq
        have hv : (i.val + 1) % Fintype.card W = (i.val + Fintype.card W - 1) % Fintype.card W :=
          congrArg Fin.val heq
        have hi := i.isLt
        by_cases hi0 : i.val = 0
        · rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)] at hv
          omega
        · by_cases hilast : i.val + 1 = Fintype.card W
          · have h1 : (i.val + 1) % Fintype.card W = 0 := by rw [hilast, Nat.mod_self]
            have h2 : (i.val + Fintype.card W - 1) % Fintype.card W = Fintype.card W - 2 := by
              have heq2 : i.val + Fintype.card W - 1 = (Fintype.card W - 2) + Fintype.card W := by omega
              rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
          · have h1 : (i.val + 1) % Fintype.card W = i.val + 1 := Nat.mod_eq_of_lt (by omega)
            have h2 : (i.val + Fintype.card W - 1) % Fintype.card W = i.val - 1 := by
              have heq2 : i.val + Fintype.card W - 1 = (i.val - 1) + Fintype.card W := by omega
              rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
      have hne_val : eqv inext ≠ eqv iprev := fun h => hne_np (eqv.injective h)
      -- Since `deg(eqv i) = 2`, `eqv j` must equal `eqv inext` or `eqv iprev`!
      obtain ⟨a, b, _, hab_iff⟩ := two_neighbors_of_encard_eq_two (hreg (eqv i))
      have hj_or : eqv j = eqv inext ∨ eqv j = eqv iprev := by
        have hn := (hab_iff (eqv inext)).mp hadj_next
        have hp := (hab_iff (eqv iprev)).mp hadj_prev
        have hj := (hab_iff (eqv j)).mp hij
        rcases hn with rfl | rfl <;> rcases hp with hA | hB
        · exact absurd hA.symm hne_val
        · subst hB; exact hj
        · subst hA; exact hj.symm
        · exact absurd hB.symm hne_val
      rcases hj_or with hj1 | hj2
      · left
        have hji : j = inext := eqv.injective hj1
        simpa [inext] using (congrArg Fin.val hji).symm
      · right
        have hji : j = iprev := eqv.injective hj2
        rw [hji]
        exact hprev_succ
    · rintro ⟨_, h1 | h2⟩
      · have hj : j = ⟨(i.val + 1) % Fintype.card W, Nat.mod_lt _ (by omega)⟩ :=
          Fin.ext h1.symm
        rw [hj]
        exact hcyc_fwd i
      · have hi : i = ⟨(j.val + 1) % Fintype.card W, Nat.mod_lt _ (by omega)⟩ :=
          Fin.ext h2.symm
        rw [hi]
        exact (hcyc_fwd j).symm
  -- Turn `eqv.symm : W ≃ Fin (Fintype.card W)` into `H ≃g Cyc`!
  refine ⟨hcard3, ⟨{
    toEquiv := eqv.symm
    map_rel_iff' := by
      intro x y
      change Cyc.Adj (eqv.symm x) (eqv.symm y) ↔ H.Adj x y
      rw [← hadj_map (eqv.symm x) (eqv.symm y), eqv.apply_symm_apply, eqv.apply_symm_apply]
  }⟩⟩

