-- Prove2me | solution 1 for StableCount.proposition_2_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:45:38.413202+00:00
-- url     : https://prove2.me/submissions/da9d848f-fa48-4c26-a9e6-2ca0daf21624

import Mathlib
import Definitions.Def_StableCount_Rotation
import Theorems.Thm_StableMatching_stable_matchings_distribLattice
import Theorems.Thm_StableMatching_stable_matching_exists
import Theorems.Thm_StableCount_proposition_2_3

section
/-!
# Rotation core for `StableCount` (Proposition 2.3 and its consumers)

Basic facts about stable matchings, `sMu`, exposed rotations and their elimination.
-/

namespace StableCount

open StableMatching

namespace Dev.RC

variable {n : ℕ}

/-! ## Basic facts on stable matchings -/

theorem mem_manPartners {I : Instance n} {v w : Fin n} :
    w ∈ manPartners I v ↔ ∃ μ : Matching n, I.IsStable μ ∧ μ v = w := by
  unfold manPartners; simp

theorem mem_womanPartners {I : Instance n} {w v : Fin n} :
    v ∈ womanPartners I w ↔ ∃ μ : Matching n, I.IsStable μ ∧ μ.symm w = v := by
  unfold womanPartners; simp

theorem manRank_inj (I : Instance n) (v : Fin n) {w w' : Fin n}
    (h : I.manRank v w = I.manRank v w') : w = w' := (I.manRank v).injective h

theorem womanRank_inj (I : Instance n) (w : Fin n) {v v' : Fin n}
    (h : I.womanRank w v = I.womanRank w v') : v = v' := (I.womanRank w).injective h

/-- (OPP) If `μ ≤ η` are stable, every woman weakly prefers her `η`-partner. -/
theorem woman_le_of_le {I : Instance n} {μ η : Matching n} (hη : I.IsStable η)
    (hle : MatchingLE I μ η) (w : Fin n) :
    I.womanRank w (η.symm w) ≤ I.womanRank w (μ.symm w) := by
  by_contra hc
  push Not at hc
  set m := μ.symm w with hm
  have hμm : μ m = w := by simp [hm]
  have hne : η m ≠ w := by
    intro h
    have : η.symm w = m := by rw [← h]; simp
    rw [this] at hc
    exact lt_irrefl _ hc
  have h1 : I.manRank m (μ m) < I.manRank m (η m) :=
    lt_of_le_of_ne (hle m) (fun h => hne (by rw [← hμm]; exact (manRank_inj I m h).symm))
  rw [hμm] at h1
  exact hη m w ⟨h1, hc⟩

/-- Converse of (OPP): if every woman weakly prefers her `η`-partner and `μ` is stable, then
`μ ≤ η`. -/
theorem le_of_woman_le {I : Instance n} {μ η : Matching n} (hμ : I.IsStable μ)
    (h : ∀ w, I.womanRank w (η.symm w) ≤ I.womanRank w (μ.symm w)) : MatchingLE I μ η := by
  intro m
  by_contra hc
  push Not at hc
  set w := η m with hw
  have hηw : η.symm w = m := by simp [hw]
  have hne : μ.symm w ≠ m := by
    intro h'
    have : μ m = w := by rw [← h']; simp
    rw [this] at hc
    exact lt_irrefl _ hc
  have h1 := h w
  rw [hηw] at h1
  have h2 : I.womanRank w m < I.womanRank w (μ.symm w) :=
    lt_of_le_of_ne h1 (fun h' => hne (womanRank_inj I w h').symm)
  exact hμ m w ⟨hc, h2⟩

theorem le_of_womanOptimal {I : Instance n} {μW η : Matching n} (hW : IsWomanOptimal I μW)
    (hη : I.IsStable η) : MatchingLE I η μW :=
  le_of_woman_le hη (fun w => hW.2 η hη w)

/-- Decomposition lemma (counting): if `μ, η` are stable and man `v` strictly prefers `μ v` to
`η v`, then woman `η v` strictly prefers `v` to her `μ`-partner. -/
theorem decomp {I : Instance n} {μ η : Matching n} (hμ : I.IsStable μ) (hη : I.IsStable η)
    {v : Fin n} (hv : I.manPrefers v (μ v) (η v)) :
    I.womanPrefers (η v) v (μ.symm (η v)) := by
  classical
  set M : Finset (Fin n) := Finset.univ.filter fun m => I.manPrefers m (μ m) (η m) with hM
  set W : Finset (Fin n) := Finset.univ.filter fun w => I.womanPrefers w (η.symm w) (μ.symm w)
    with hW
  have ha : ∀ m ∈ M, μ m ∈ W := by
    intro m hm
    simp only [hM, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hc
    unfold Instance.womanPrefers at hc
    push Not at hc
    simp only [Equiv.symm_apply_apply] at hc
    have hne : η.symm (μ m) ≠ m := by
      intro h
      have : η m = μ m := ((Equiv.symm_apply_eq η).mp h).symm
      unfold Instance.manPrefers at hm
      rw [this] at hm
      exact lt_irrefl _ hm
    have h2 : I.womanRank (μ m) m < I.womanRank (μ m) (η.symm (μ m)) :=
      lt_of_le_of_ne hc (fun h => hne (womanRank_inj I _ h).symm)
    exact hη m (μ m) ⟨hm, h2⟩
  have hb : ∀ w ∈ W, η.symm w ∈ M := by
    intro w hw
    simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [hM, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hc
    unfold Instance.manPrefers at hc
    push Not at hc
    simp only [Equiv.apply_symm_apply] at hc
    have hne : μ (η.symm w) ≠ w := by
      intro h
      have : μ.symm w = η.symm w := (Equiv.symm_apply_eq μ).mpr h.symm
      unfold Instance.womanPrefers at hw
      rw [this] at hw
      exact lt_irrefl _ hw
    have h2 : I.manRank (η.symm w) w < I.manRank (η.symm w) (μ (η.symm w)) :=
      lt_of_le_of_ne hc (fun h => hne (manRank_inj I _ h).symm)
    exact hμ (η.symm w) w ⟨h2, hw⟩
  have hcard1 : M.card ≤ W.card := by
    calc M.card = (M.image μ).card := (Finset.card_image_of_injective _ μ.injective).symm
      _ ≤ W.card := Finset.card_le_card (fun x hx => by
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
          exact ha m hm)
  have hsub : W.image η.symm ⊆ M := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact hb w hw
  have heq : W.image η.symm = M := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ η.symm.injective]; exact hcard1)
  have hvM : v ∈ M := by simp [hM, hv]
  rw [← heq] at hvM
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvM
  have : η v = w := by rw [← hwv]; simp
  rw [this]
  simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rw [← hwv]
  exact hw

/-! ## `sMu` -/

theorem mem_sCandidates {I : Instance n} {μ : Matching n} {v w : Fin n} :
    w ∈ sCandidates I μ v ↔ I.manPrefers v (μ v) w ∧ I.womanPrefers w v (μ.symm w) := by
  unfold sCandidates; simp

theorem sMu_spec {I : Instance n} {μ : Matching n} {v s : Fin n} (h : sMu I μ v = some s) :
    s ∈ sCandidates I μ v ∧ ∀ w ∈ sCandidates I μ v, I.manRank v s ≤ I.manRank v w := by
  unfold sMu at h
  split_ifs at h with hne
  obtain rfl := Option.some.inj h
  set c := sCandidates I μ v
  have hmin := Finset.min'_mem (c.image (I.manRank v)) (hne.image _)
  obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hmin
  refine ⟨?_, fun w' hw' => ?_⟩
  · rw [← hwe]; simpa using hw
  · simp only [Equiv.apply_symm_apply]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hw')

theorem sMu_isSome {I : Instance n} {μ : Matching n} {v w : Fin n} (hw : w ∈ sCandidates I μ v) :
    ∃ s, sMu I μ v = some s := by
  unfold sMu
  rw [dif_pos ⟨w, hw⟩]
  exact ⟨_, rfl⟩

theorem sMu_eq_some_iff {I : Instance n} {μ : Matching n} {v s : Fin n} :
    sMu I μ v = some s ↔
      s ∈ sCandidates I μ v ∧ ∀ w ∈ sCandidates I μ v, I.manRank v s ≤ I.manRank v w := by
  refine ⟨sMu_spec, fun ⟨hs, hmin⟩ => ?_⟩
  obtain ⟨s', hs'⟩ := sMu_isSome hs
  obtain ⟨h1, h2⟩ := sMu_spec hs'
  rw [hs', manRank_inj I v (le_antisymm (h2 s hs) (hmin s' h1))]

theorem sMu_prefers {I : Instance n} {μ : Matching n} {v s : Fin n} (h : sMu I μ v = some s) :
    I.manPrefers v (μ v) s := (mem_sCandidates.mp (sMu_spec h).1).1

/-- (A) If `μ, η` are stable and `v` strictly prefers `μ v` to `η v`, then `η v` is an
`s`-candidate of `v` in `μ`. -/
theorem cand_of_prefers {I : Instance n} {μ η : Matching n} (hμ : I.IsStable μ)
    (hη : I.IsStable η) {v : Fin n} (hv : I.manPrefers v (μ v) (η v)) :
    η v ∈ sCandidates I μ v :=
  mem_sCandidates.mpr ⟨hv, decomp hμ hη hv⟩

theorem prefers_of_le_ne {I : Instance n} {μ η : Matching n} (hle : MatchingLE I μ η) {v : Fin n}
    (hne : μ v ≠ η v) : I.manPrefers v (μ v) (η v) :=
  lt_of_le_of_ne (hle v) (fun h => hne (manRank_inj I v h))

/-- (A) for `μ ≤ η`: `sMu μ v` is defined and weakly preferred to `η v`. -/
theorem sMu_le_of_le {I : Instance n} {μ η : Matching n} (hμ : I.IsStable μ)
    (hη : I.IsStable η) (hle : MatchingLE I μ η) {v : Fin n} (hne : μ v ≠ η v) :
    ∃ s, sMu I μ v = some s ∧ I.manRank v s ≤ I.manRank v (η v) := by
  have hc := cand_of_prefers hμ hη (prefers_of_le_ne hle hne)
  obtain ⟨s, hs⟩ := sMu_isSome hc
  exact ⟨s, hs, (sMu_spec hs).2 _ hc⟩


/-! ## List plumbing -/

theorem gidx {α : Type*} (l : List α) {a b : ℕ} (ha : a < l.length) (hb : b < l.length)
    (h : a = b) : l[a] = l[b] := by subst h; rfl

theorem succ_mod_inj {L i j : ℕ} (hi : i < L) (hj : j < L) (h : (i + 1) % L = (j + 1) % L) :
    i = j := by
  rcases Nat.lt_or_ge (i + 1) L with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) L with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · have e : j + 1 = L := by omega
    rw [Nat.mod_eq_of_lt h1, e, Nat.mod_self] at h; omega
  · have e : i + 1 = L := by omega
    rw [Nat.mod_eq_of_lt h2, e, Nat.mod_self] at h; omega
  · omega

/-- A cyclic successor property of a list is invariant under rotation. -/
theorem cyc_rotate {α : Type*} (P : α → α → Prop) (l : List α)
    (h : ∀ (i : ℕ) (hi : i < l.length), P l[i] (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))))
    (k : ℕ) : ∀ (i : ℕ) (hi : i < (l.rotate k).length),
      P (l.rotate k)[i] ((l.rotate k)[(i + 1) % (l.rotate k).length]'(Nat.mod_lt _ (by omega))) := by
  intro i hi
  have hL : (l.rotate k).length = l.length := List.length_rotate ..
  have hpos : 0 < l.length := by omega
  rw [List.getElem_rotate, List.getElem_rotate]
  have e : ((i + 1) % (l.rotate k).length + k) % l.length = ((i + k) % l.length + 1) % l.length := by
    rw [hL, Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_right_comm]
  rw [gidx l _ (Nat.mod_lt _ hpos) e]
  exact h ((i + k) % l.length) (Nat.mod_lt _ hpos)

theorem mem_fst_iff {l : List (Fin n × Fin n)} {v : Fin n} :
    v ∈ l.map Prod.fst ↔ ∃ (i : ℕ) (hi : i < l.length), l[i].1 = v := by
  constructor
  · intro hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map_of_mem (List.getElem_mem hi)

theorem getElem_fst_mem (l : List (Fin n × Fin n)) (i : ℕ) (hi : i < l.length) :
    l[i].1 ∈ l.map Prod.fst := mem_fst_iff.mpr ⟨i, hi, rfl⟩

/-- In a list of pairs of a matching, the men determine the positions. -/
theorem fst_inj {μ : Matching n} {l : List (Fin n × Fin n)} (hnd : l.Nodup)
    (hμ : ∀ p ∈ l, μ p.1 = p.2) {a b : ℕ} (ha : a < l.length) (hb : b < l.length)
    (h : l[a].1 = l[b].1) : a = b := by
  have hpa := hμ l[a] (List.getElem_mem ha)
  have hpb := hμ l[b] (List.getElem_mem hb)
  have : l[a] = l[b] := Prod.ext h (by rw [← hpa, ← hpb, h])
  exact hnd.getElem_inj_iff.mp this

theorem isExposedList_rotate {I : Instance n} {μ : Matching n} {l : List (Fin n × Fin n)}
    (h : IsExposedList I μ l) (k : ℕ) : IsExposedList I μ (l.rotate k) := by
  obtain ⟨hs, h2, hnd, hμ, hsm⟩ := h
  refine ⟨hs, by rw [List.length_rotate]; exact h2, List.nodup_rotate.mpr hnd,
    fun p hp => hμ p (List.mem_rotate.mp hp), ?_⟩
  intro i hi
  have := cyc_rotate (fun p q => sMu I μ p.1 = some q.2) l hsm k i hi
  exact this

/-- An exposed rotation and its elimination can be described by one common list. -/
theorem common_list {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) :
    ∃ l : List (Fin n × Fin n), (l : Cycle (Fin n × Fin n)) = ρ ∧ IsExposedList I μ l ∧
      IsElimList μ l ν := by
  obtain ⟨l1, rfl, he⟩ := h1
  obtain ⟨l2, hl2, hel⟩ := h2
  obtain ⟨k, hk⟩ := Cycle.coe_eq_coe.mp hl2.symm
  refine ⟨l2, hl2, ?_, hel⟩
  rw [← hk]; exact isExposedList_rotate he k

theorem sMu_of_mem {I : Instance n} {μ ν : Matching n} {l : List (Fin n × Fin n)}
    (he : IsExposedList I μ l) (hel : IsElimList μ l ν) {v : Fin n} (hv : v ∈ l.map Prod.fst) :
    sMu I μ v = some (ν v) := by
  obtain ⟨i, hi, rfl⟩ := mem_fst_iff.mp hv
  rw [he.2.2.2.2 i hi, hel.1 i hi]

/-- The successor map of an elimination: `v ↦ μ⁻¹(ν v)`. -/
def nxt (μ ν : Matching n) (v : Fin n) : Fin n := μ.symm (ν v)

theorem iterate_nxt_list {μ ν : Matching n} {l : List (Fin n × Fin n)}
    (hμ : ∀ p ∈ l, μ p.1 = p.2) (hel : IsElimList μ l ν) (i : ℕ) (hi : i < l.length) :
    ∀ k : ℕ, (nxt μ ν)^[k] l[i].1 = (l[(i + k) % l.length]'(Nat.mod_lt _ (by omega))).1 := by
  intro k
  have hpos : 0 < l.length := by omega
  induction k with
  | zero => simp only [Function.iterate_zero, id, Nat.add_zero]; rw [gidx l hi _ (Nat.mod_eq_of_lt hi).symm]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold nxt
    rw [hel.1 _ (Nat.mod_lt _ hpos), Equiv.symm_apply_eq, hμ _ (List.getElem_mem _)]
    congr 1
    exact gidx l _ _ (by rw [Nat.mod_add_mod, Nat.add_assoc])

theorem orbit_list {μ ν : Matching n} {l : List (Fin n × Fin n)}
    (hμ : ∀ p ∈ l, μ p.1 = p.2) (hel : IsElimList μ l ν) {x y : Fin n}
    (hx : x ∈ l.map Prod.fst) (hy : y ∈ l.map Prod.fst) : ∃ k, (nxt μ ν)^[k] x = y := by
  obtain ⟨i, hi, rfl⟩ := mem_fst_iff.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_fst_iff.mp hy
  refine ⟨j + l.length - i, ?_⟩
  rw [iterate_nxt_list hμ hel i hi]
  congr 1
  exact gidx l _ _ (by
    rw [show i + (j + l.length - i) = j + l.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj])

/-! ## Eliminations described by a set of men -/

section Spec

variable {I : Instance n} {μ ν : Matching n} (P : Fin n → Prop)

theorem moves_of_spec (h1 : ∀ v, P v → sMu I μ v = some (ν v)) {v : Fin n} (hv : P v) :
    μ v ≠ ν v := by
  intro h
  have := sMu_prefers (h1 v hv)
  rw [h] at this
  exact lt_irrefl _ this

theorem le_of_spec (h1 : ∀ v, P v → sMu I μ v = some (ν v)) (h2 : ∀ v, ¬ P v → ν v = μ v) :
    MatchingLE I μ ν := by
  intro v
  by_cases hv : P v
  · exact (sMu_prefers (h1 v hv)).le
  · rw [h2 v hv]

theorem woman_better_of_spec (h1 : ∀ v, P v → sMu I μ v = some (ν v))
    (h2 : ∀ v, ¬ P v → ν v = μ v) (w : Fin n) :
    I.womanRank w (ν.symm w) ≤ I.womanRank w (μ.symm w) := by
  by_cases hu : P (ν.symm w)
  · have := (mem_sCandidates.mp (sMu_spec (h1 _ hu)).1).2
    simp only [Equiv.apply_symm_apply] at this
    exact this.le
  · have e := h2 _ hu
    simp only [Equiv.apply_symm_apply] at e
    have : μ.symm w = ν.symm w := by rw [Equiv.symm_apply_eq]; exact e
    rw [this]

/-- (B) Eliminating along a set of men with `ν v = s_μ(v)` gives a stable matching. -/
theorem stable_of_spec (hμ : I.IsStable μ) (h1 : ∀ v, P v → sMu I μ v = some (ν v))
    (h2 : ∀ v, ¬ P v → ν v = μ v) : I.IsStable ν := by
  intro m w ⟨hb1, hb2⟩
  have hwm : I.womanPrefers w m (μ.symm w) :=
    lt_of_lt_of_le hb2 (woman_better_of_spec P h1 h2 w)
  by_cases hm : P m
  · obtain ⟨hcand, hmin⟩ := sMu_spec (h1 m hm)
    rcases lt_trichotomy (I.manRank m w) (I.manRank m (μ m)) with hlt | heq | hgt
    · exact hμ m w ⟨hlt, hwm⟩
    · obtain rfl : w = μ m := manRank_inj I m heq
      have hPu : P (ν.symm (μ m)) := by
        by_contra hPu
        have e := h2 _ hPu
        simp only [Equiv.apply_symm_apply] at e
        have : ν.symm (μ m) = m := μ.injective e.symm
        exact hPu (by rw [this]; exact hm)
      have := (mem_sCandidates.mp (sMu_spec (h1 _ hPu)).1).2
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at this
      exact lt_asymm this hb2
    · have hc : w ∈ sCandidates I μ m := mem_sCandidates.mpr ⟨hgt, hwm⟩
      exact absurd (hmin w hc) (not_le.mpr hb1)
  · rw [Instance.manPrefers, h2 m hm] at hb1
    exact hμ m w ⟨hb1, hwm⟩

/-- (C) If moreover the men of `P` form one orbit of `nxt μ ν`, then `ν` covers `μ`. -/
theorem covers_of_spec (hμ : I.IsStable μ) (h1 : ∀ v, P v → sMu I μ v = some (ν v))
    (h2 : ∀ v, ¬ P v → ν v = μ v) (hne : ∃ x, P x)
    (horb : ∀ x y, P x → P y → ∃ k, (nxt μ ν)^[k] x = y) : Covers I μ ν := by
  have hν := stable_of_spec P hμ h1 h2
  have hle := le_of_spec P h1 h2
  refine ⟨hμ, hν, ⟨hle, ?_⟩, ?_⟩
  · intro heq
    obtain ⟨x, hx⟩ := hne
    exact moves_of_spec P h1 hx (by rw [heq])
  · rintro η hη ⟨⟨hle1, hne1⟩, ⟨hle2, hne2⟩⟩
    have key : ∀ v, η v ≠ μ v → P v ∧ η v = ν v := by
      intro v hv
      have hPv : P v := by
        by_contra hP
        have e := h2 v hP
        have h3 := hle2 v
        rw [e] at h3
        exact hv (manRank_inj I v (le_antisymm h3 (hle1 v)))
      refine ⟨hPv, ?_⟩
      have hc := cand_of_prefers hμ hη (prefers_of_le_ne hle1 (Ne.symm hv))
      exact manRank_inj I v (le_antisymm (hle2 v) ((sMu_spec (h1 v hPv)).2 _ hc))
    obtain ⟨x, hx⟩ : ∃ x, η x ≠ μ x := by
      by_contra hc
      push Not at hc
      exact hne1 (Equiv.ext fun v => (hc v).symm)
    have clos : ∀ v, η v ≠ μ v → η (nxt μ ν v) ≠ μ (nxt μ ν v) := by
      intro v hv heq
      obtain ⟨hP, hην⟩ := key v hv
      have h3 : μ (nxt μ ν v) = ν v := by simp [nxt]
      rw [h3, ← hην] at heq
      have e := η.injective heq
      rw [e] at h3
      exact moves_of_spec P h1 hP h3
    have hiter : ∀ k, η ((nxt μ ν)^[k] x) ≠ μ ((nxt μ ν)^[k] x) := by
      intro k
      induction k with
      | zero => exact hx
      | succ k ih => rw [Function.iterate_succ_apply']; exact clos _ ih
    apply hne2
    apply Equiv.ext
    intro v
    by_cases hv : P v
    · obtain ⟨k, rfl⟩ := horb x v (key x hx).1 hv
      exact (key _ (hiter k)).2
    · have e := h2 v hv
      have h3 := hle2 v
      rw [e] at h3
      rw [manRank_inj I v (le_antisymm h3 (hle1 v)), e]

end Spec

/-! ## Exposed rotations: elimination exists, is stable, and is a cover -/

theorem exists_elimList {I : Instance n} {μ : Matching n} {l : List (Fin n × Fin n)}
    (he : IsExposedList I μ l) : ∃ ν, IsElimList μ l ν := by
  classical
  obtain ⟨_, _, hnd, hμ, hsm⟩ := he
  let h : Fin n → Fin n := fun v =>
    if v ∈ l.map Prod.fst then μ.symm ((sMu I μ v).getD v) else v
  have hval : ∀ (i : ℕ) (hi : i < l.length),
      h l[i].1 = (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))).1 := by
    intro i hi
    simp only [h, if_pos (getElem_fst_mem l i hi), hsm i hi, Option.getD_some]
    rw [Equiv.symm_apply_eq, hμ _ (List.getElem_mem _)]
  have hoff : ∀ v, v ∉ l.map Prod.fst → h v = v := by
    intro v hv; simp only [h, if_neg hv]
  have hinj : Function.Injective h := by
    intro a b hab
    by_cases ha : a ∈ l.map Prod.fst <;> by_cases hb : b ∈ l.map Prod.fst
    · obtain ⟨i, hi, rfl⟩ := mem_fst_iff.mp ha
      obtain ⟨j, hj, rfl⟩ := mem_fst_iff.mp hb
      rw [hval, hval] at hab
      have := succ_mod_inj hi hj (fst_inj hnd hμ _ _ hab)
      subst this; rfl
    · obtain ⟨i, hi, rfl⟩ := mem_fst_iff.mp ha
      rw [hval, hoff b hb] at hab
      exact absurd (hab ▸ getElem_fst_mem l _ _) hb
    · obtain ⟨j, hj, rfl⟩ := mem_fst_iff.mp hb
      rw [hval, hoff a ha] at hab
      exact absurd (hab ▸ getElem_fst_mem l _ _) ha
    · rwa [hoff a ha, hoff b hb] at hab
  let e := Equiv.ofBijective h (Finite.injective_iff_bijective.mp hinj)
  refine ⟨e.trans μ, ?_, ?_⟩
  · intro i hi
    simp only [Equiv.trans_apply, e, Equiv.ofBijective_apply, hval i hi]
    exact hμ _ (List.getElem_mem _)
  · intro v hv
    simp only [Equiv.trans_apply, e, Equiv.ofBijective_apply, hoff v hv]

theorem covers_of_list {I : Instance n} {μ ν : Matching n} {l : List (Fin n × Fin n)}
    (he : IsExposedList I μ l) (hel : IsElimList μ l ν) : Covers I μ ν :=
  covers_of_spec (fun v => v ∈ l.map Prod.fst) he.1 (fun v hv => sMu_of_mem he hel hv) hel.2
    ⟨_, getElem_fst_mem l 0 (by have := he.2.1; omega)⟩
    (fun _ _ hx hy => orbit_list he.2.2.2.1 hel hx hy)

/-- (C) Eliminating an exposed rotation gives a cover. -/
theorem covers_of_elim {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) : Covers I μ ν := by
  obtain ⟨l, -, he, hel⟩ := common_list h1 h2
  exact covers_of_list he hel

/-! ## (D) Every cover is the elimination of an exposed rotation -/

/-- `v ↦ μ⁻¹(s_μ(v))` (identity where `s_μ(v)` is undefined). -/
noncomputable def gmap (I : Instance n) (μ : Matching n) (v : Fin n) : Fin n :=
  μ.symm ((sMu I μ v).getD (μ v))

/-- (D) If `ν` covers `μ`, then `ν = μ/ρ` for a rotation `ρ` exposed in `μ`. -/
theorem exists_rot_of_covers {I : Instance n} {μ ν : Matching n} (hc : Covers I μ ν) :
    ∃ ρ, IsExposed I μ ρ ∧ IsElim μ ρ ν := by
  classical
  obtain ⟨hμ, hν, ⟨hle, hne⟩, hcov⟩ := hc
  have hA : ∀ v, μ v ≠ ν v → ∃ s, sMu I μ v = some s ∧ I.manRank v s ≤ I.manRank v (ν v) :=
    fun v hv => sMu_le_of_le hμ hν hle hv
  have hg : ∀ v s, sMu I μ v = some s → gmap I μ v = μ.symm s := by
    intro v s hs; simp [gmap, hs]
  have hgM : ∀ v, μ v ≠ ν v → μ (gmap I μ v) ≠ ν (gmap I μ v) := by
    intro v hv heq
    obtain ⟨s, hs, hsle⟩ := hA v hv
    rw [hg v s hs, Equiv.apply_symm_apply] at heq
    have hνu : ν (μ.symm s) = s := heq.symm
    have hsν : s ≠ ν v := by
      intro h'
      have hu : μ.symm s = v := ν.injective (by rw [hνu, h'])
      have hμv : μ v = s := by rw [← hu]; simp
      have hp := sMu_prefers hs
      rw [hμv] at hp
      exact lt_irrefl _ hp
    have hlt : I.manRank v s < I.manRank v (ν v) :=
      lt_of_le_of_ne hsle (fun h => hsν (manRank_inj I v h))
    have hcand := (mem_sCandidates.mp (sMu_spec hs).1).2
    have e : ν.symm s = μ.symm s := by rw [Equiv.symm_apply_eq]; exact hνu.symm
    exact hν v s ⟨hlt, by rw [e]; exact hcand⟩
  have hgne : ∀ v, μ v ≠ ν v → gmap I μ v ≠ v := by
    intro v hv h
    obtain ⟨s, hs, -⟩ := hA v hv
    rw [hg v s hs] at h
    have hμv : μ v = s := by rw [← h]; simp
    have hp := sMu_prefers hs
    rw [hμv] at hp
    exact lt_irrefl _ hp
  have hiter : ∀ k v, μ v ≠ ν v → μ ((gmap I μ)^[k] v) ≠ ν ((gmap I μ)^[k] v) := by
    intro k
    induction k with
    | zero => intro v hv; exact hv
    | succ k ih => intro v hv; rw [Function.iterate_succ_apply']; exact hgM _ (ih v hv)
  obtain ⟨v0, hv0⟩ : ∃ v, μ v ≠ ν v := by
    by_contra hc; push Not at hc; exact hne (Equiv.ext hc)
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (gmap I μ)^[k] v0)
  obtain ⟨x, d, hxM, hd, hper⟩ : ∃ x d, μ x ≠ ν x ∧ 0 < d ∧ (gmap I μ)^[d] x = x := by
    rcases lt_or_gt_of_ne hab with h | h
    · refine ⟨(gmap I μ)^[a] v0, b - a, hiter a v0 hv0, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact hfab.symm
    · refine ⟨(gmap I μ)^[b] v0, a - b, hiter b v0 hv0, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact hfab
  have hperiodic : Function.IsPeriodicPt (gmap I μ) d x := hper
  have hLpos : 0 < Function.minimalPeriod (gmap I μ) x := hperiodic.minimalPeriod_pos hd
  have hL2 : 2 ≤ Function.minimalPeriod (gmap I μ) x := by
    by_contra hc
    have hL1 : Function.minimalPeriod (gmap I μ) x = 1 := by omega
    have := Function.isPeriodicPt_minimalPeriod (gmap I μ) x
    rw [hL1] at this
    exact hgne x hxM this
  set l : List (Fin n × Fin n) := (List.range (Function.minimalPeriod (gmap I μ) x)).map
    fun k => ((gmap I μ)^[k] x, μ ((gmap I μ)^[k] x)) with hl
  have hlen : l.length = Function.minimalPeriod (gmap I μ) x := by simp [hl]
  have hget : ∀ (i : ℕ) (hi : i < l.length), l[i] = ((gmap I μ)^[i] x, μ ((gmap I μ)^[i] x)) := by
    intro i hi; simp [hl]
  have hmen : ∀ v, v ∈ l.map Prod.fst → μ v ≠ ν v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_fst_iff.mp hv
    rw [hget]; exact hiter i x hxM
  have he : IsExposedList I μ l := by
    refine ⟨hμ, by omega, ?_, ?_, ?_⟩
    · rw [hl]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro a ha b hb hab'
      exact Function.iterate_injOn_Iio_minimalPeriod (List.mem_range.mp ha)
        (List.mem_range.mp hb) (Prod.mk.inj hab').1
    · intro p hp
      rw [hl, List.mem_map] at hp
      obtain ⟨k, -, rfl⟩ := hp
      rfl
    · intro i hi
      rw [hget, hget]
      simp only
      rw [hlen, Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']
      obtain ⟨s, hs, -⟩ := hA _ (hiter i x hxM)
      rw [hs, hg _ s hs, Equiv.apply_symm_apply]
  obtain ⟨ν', hel⟩ := exists_elimList he
  have hcov' := covers_of_list he hel
  have hle' : MatchingLE I ν' ν := by
    intro v
    by_cases hv : v ∈ l.map Prod.fst
    · obtain ⟨s, hs, hsle⟩ := hA v (hmen v hv)
      rw [sMu_of_mem he hel hv] at hs
      obtain rfl := Option.some.inj hs
      exact hsle
    · rw [hel.2 v hv]; exact hle v
  have : ν' = ν := by
    by_contra hne'
    exact hcov ν' hcov'.2.1 ⟨hcov'.2.2.1, ⟨hle', hne'⟩⟩
  subst this
  exact ⟨l, ⟨l, rfl, he⟩, ⟨l, rfl, hel⟩⟩

/-! ## Proposition 2.3 (ii): partners move to the adjacent stable partner -/

theorem stable_of_exposed {I : Instance n} {μ : Matching n} {ρ : Rot n} (h : IsExposed I μ ρ) :
    I.IsStable μ := by
  obtain ⟨l, -, he⟩ := h; exact he.1

/-! ## Canonical form of an exposed rotation -/

end Dev.RC

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.Opt

variable {n : ℕ}

theorem exists_manOptimal (I : Instance n) : ∃ μ, IsManOptimal I μ := by
  obtain ⟨L, hL⟩ := StableMatching.stable_matchings_distribLattice I
  obtain ⟨μ0, hμ0⟩ := StableMatching.stable_matching_exists I
  letI := L
  haveI : Nonempty {μ : Matching n // I.IsStable μ} := ⟨⟨μ0, hμ0⟩⟩
  let b : {μ : Matching n // I.IsStable μ} := Finset.univ.inf' Finset.univ_nonempty id
  refine ⟨b.1, b.2, fun ν hν m => ?_⟩
  have hle : b ≤ ⟨ν, hν⟩ := Finset.inf'_le id (Finset.mem_univ _)
  exact (hL b ⟨ν, hν⟩).1 hle m

theorem exists_womanOptimal (I : Instance n) : ∃ μ, IsWomanOptimal I μ := by
  obtain ⟨L, hL⟩ := StableMatching.stable_matchings_distribLattice I
  obtain ⟨μ0, hμ0⟩ := StableMatching.stable_matching_exists I
  letI := L
  haveI : Nonempty {μ : Matching n // I.IsStable μ} := ⟨⟨μ0, hμ0⟩⟩
  let t : {μ : Matching n // I.IsStable μ} := Finset.univ.sup' Finset.univ_nonempty id
  refine ⟨t.1, t.2, fun ν hν w => ?_⟩
  have hle : (⟨ν, hν⟩ : {μ : Matching n // I.IsStable μ}) ≤ t :=
    Finset.le_sup' id (Finset.mem_univ (⟨ν, hν⟩ : {μ : Matching n // I.IsStable μ}))
  exact Dev.RC.woman_le_of_le t.2 ((hL _ t).1 hle) w

end Dev.Opt

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.P25

variable {n : ℕ}

/-! ## The reordered list -/

theorem key_inj (r : Fin n ≃ Fin n) (S : Finset (Fin n)) : Function.Injective (reorderKey r S) := by
  intro x y h
  unfold reorderKey at h
  have := (r x).isLt
  have := (r y).isLt
  split_ifs at h <;> exact r.injective (Fin.ext (by omega))

theorem ro_lt (r : Fin n ≃ Fin n) (S : Finset (Fin n)) (x y : Fin n) :
    reorder r S x < reorder r S y ↔ reorderKey r S x < reorderKey r S y := by
  have hk := key_inj r S
  have hm := Tuple.monotone_sort (reorderKey r S)
  have hx : Tuple.sort (reorderKey r S) (reorder r S x) = x := Equiv.apply_symm_apply _ _
  have hy : Tuple.sort (reorderKey r S) (reorder r S y) = y := Equiv.apply_symm_apply _ _
  constructor
  · intro h
    have h1 : reorderKey r S x ≤ reorderKey r S y := by
      have := hm h.le
      simpa only [Function.comp_apply, hx, hy] using this
    refine lt_of_le_of_ne h1 (fun he => ?_)
    have := hk he
    subst this
    exact lt_irrefl _ h
  · intro h
    by_contra hc
    push Not at hc
    have := hm hc
    simp only [Function.comp_apply, hx, hy] at this
    omega

variable {r : Fin n ≃ Fin n} {S : Finset (Fin n)}

theorem K1 {x y : Fin n} (hx : x ∈ S) (hy : y ∈ S) :
    reorder r S x < reorder r S y ↔ r x < r y := by
  rw [ro_lt]
  unfold reorderKey
  rw [if_pos hx, if_pos hy]
  exact Fin.lt_def.symm

theorem K2 {x y : Fin n} (hx : x ∈ S) (hy : y ∉ S) : reorder r S x < reorder r S y := by
  rw [ro_lt]
  unfold reorderKey
  rw [if_pos hx, if_neg hy]
  have := (r x).isLt
  omega

theorem K3 {x y : Fin n} (h : reorder r S x ≤ reorder r S y) (hy : y ∈ S) : x ∈ S := by
  by_contra hx
  exact absurd h (not_le.mpr (K2 hy hx))

theorem K5 {x y : Fin n} (h : reorder r S x < reorder r S y) (hy : y ∈ S) : x ∈ S ∧ r x < r y :=
  have hx := K3 h.le hy
  ⟨hx, (K1 hx hy).mp h⟩

theorem K4 {y : Fin n} (hy : y ∈ S) (hmin : ∀ z ∈ S, r y ≤ r z) (x : Fin n) :
    reorder r S y ≤ reorder r S x := by
  by_cases hx : x ∈ S
  · rw [← not_lt, K1 hx hy, not_lt]
    exact hmin x hx
  · exact (K2 hy hx).le

/-! ## Transfer to the normalized instance -/

variable {I : Instance n}

theorem nm (I : Instance n) (v : Fin n) :
    (normalize I).manRank v = reorder (I.manRank v) (manPartners I v) := rfl

theorem nw (I : Instance n) (w : Fin n) :
    (normalize I).womanRank w = reorder (I.womanRank w) (womanPartners I w) := rfl

theorem pm {μ : Matching n} (hμ : I.IsStable μ) (m : Fin n) : μ m ∈ manPartners I m :=
  Dev.RC.mem_manPartners.mpr ⟨μ, hμ, rfl⟩

theorem pw {μ : Matching n} (hμ : I.IsStable μ) (w : Fin n) : μ.symm w ∈ womanPartners I w :=
  Dev.RC.mem_womanPartners.mpr ⟨μ, hμ, rfl⟩

theorem stable_norm {μ : Matching n} (hμ : I.IsStable μ) : (normalize I).IsStable μ := by
  intro m w ⟨h1, h2⟩
  unfold Instance.manPrefers at h1
  unfold Instance.womanPrefers at h2
  rw [nm] at h1
  rw [nw] at h2
  exact hμ m w ⟨(K5 h1 (pm hμ m)).2, (K5 h2 (pw hμ w)).2⟩

theorem manOpt_norm {μ : Matching n} (h : IsManOptimal I μ) : IsManOptimal (normalize I) μ := by
  refine ⟨stable_norm h.1, fun ν _ m => ?_⟩
  rw [nm]
  refine K4 (pm h.1 m) (fun z hz => ?_) (ν m)
  obtain ⟨η, hη, rfl⟩ := Dev.RC.mem_manPartners.mp hz
  exact h.2 η hη m

theorem womanOpt_norm {μ : Matching n} (h : IsWomanOptimal I μ) :
    IsWomanOptimal (normalize I) μ := by
  refine ⟨stable_norm h.1, fun ν _ w => ?_⟩
  rw [nw]
  refine K4 (pw h.1 w) (fun z hz => ?_) (ν.symm w)
  obtain ⟨η, hη, rfl⟩ := Dev.RC.mem_womanPartners.mp hz
  exact h.2 η hη w

theorem man_mem {η : Matching n} (hη : (normalize I).IsStable η) (m : Fin n) :
    η m ∈ manPartners I m := by
  obtain ⟨μW, hW⟩ := Dev.Opt.exists_womanOptimal I
  have hle := Dev.RC.le_of_womanOptimal (womanOpt_norm hW) hη m
  rw [nm] at hle
  exact K3 hle (pm hW.1 m)

theorem woman_mem {η : Matching n} (hη : (normalize I).IsStable η) (w : Fin n) :
    η.symm w ∈ womanPartners I w := by
  obtain ⟨μM, hM⟩ := Dev.Opt.exists_manOptimal I
  have hle := Dev.RC.woman_le_of_le hη ((manOpt_norm hM).2 η hη) w
  rw [nw] at hle
  exact K3 hle (pw hM.1 w)

theorem manPartners_eq (v : Fin n) : manPartners (normalize I) v = manPartners I v := by
  ext w
  rw [Dev.RC.mem_manPartners]
  constructor
  · rintro ⟨η, hη, rfl⟩
    exact man_mem hη v
  · intro hw
    obtain ⟨η, hη, rfl⟩ := Dev.RC.mem_manPartners.mp hw
    exact ⟨η, stable_norm hη, rfl⟩

theorem womanPartners_eq (w : Fin n) : womanPartners (normalize I) w = womanPartners I w := by
  ext v
  rw [Dev.RC.mem_womanPartners]
  constructor
  · rintro ⟨η, hη, rfl⟩
    exact woman_mem hη w
  · intro hv
    obtain ⟨η, hη, rfl⟩ := Dev.RC.mem_womanPartners.mp hv
    exact ⟨η, stable_norm hη, rfl⟩

theorem normalized_norm : IsNormalized (normalize I) := by
  constructor
  · intro v w w' hw hw'
    rw [manPartners_eq] at hw hw'
    unfold Instance.manPrefers
    rw [nm]
    exact K2 hw hw'
  · intro w v v' hv hv'
    rw [womanPartners_eq] at hv hv'
    unfold Instance.womanPrefers
    rw [nw]
    exact K2 hv hv'

/-- In the normalized instance, `s_μ(v)` is still the next woman for each man of an exposed
rotation. -/
theorem sMu_norm {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ) (h2 : IsElim μ ρ ν)
    {v : Fin n} (hv : μ v ≠ ν v) : sMu (normalize I) μ v = some (ν v) := by
  obtain ⟨-, -, hcl⟩ := proposition_2_3 I
  obtain ⟨hm, hw⟩ := hcl μ ν ρ h1 h2
  obtain ⟨hνS, hpref, hbetw⟩ := hm v hv
  have hμst : I.IsStable μ := Dev.RC.stable_of_exposed h1
  have hνsymm : ν.symm (ν v) = v := by simp
  have hwv : μ.symm (ν v) ≠ ν.symm (ν v) := by
    rw [hνsymm]
    intro h
    exact hv ((Equiv.symm_apply_eq μ).mp h).symm
  obtain ⟨hνSw, hprefw, -⟩ := hw (ν v) hwv
  rw [hνsymm] at hνSw hprefw
  rw [Dev.RC.sMu_eq_some_iff]
  refine ⟨Dev.RC.mem_sCandidates.mpr ⟨?_, ?_⟩, fun w' hw' => ?_⟩
  · unfold Instance.manPrefers
    rw [nm, K1 (pm hμst v) hνS]
    exact hpref
  · unfold Instance.womanPrefers
    rw [nw, K1 hνSw (pw hμst (ν v))]
    exact hprefw
  · obtain ⟨c1, -⟩ := Dev.RC.mem_sCandidates.mp hw'
    by_contra hc
    push Not at hc
    rw [nm] at hc
    obtain ⟨hw'S, hlt⟩ := K5 hc hνS
    unfold Instance.manPrefers at c1
    rw [nm, K1 (pm hμst v) hw'S] at c1
    exact hbetw w' hw'S ⟨c1, hlt⟩

theorem exposed_norm {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ) (h2 : IsElim μ ρ ν) :
    IsExposed (normalize I) μ ρ := by
  obtain ⟨l, hl, he, hel⟩ := Dev.RC.common_list h1 h2
  refine ⟨l, hl, stable_norm he.1, he.2.1, he.2.2.1, he.2.2.2.1, fun i hi => ?_⟩
  have hv := Dev.RC.getElem_fst_mem l i hi
  rw [← hel.1 i hi]
  apply sMu_norm h1 h2
  intro h
  have := Dev.RC.sMu_prefers (Dev.RC.sMu_of_mem he hel hv)
  rw [h] at this
  exact lt_irrefl _ this

end Dev.P25

open Dev.P25 in
theorem chk_proposition_2_5 {n : ℕ} (I : Instance n) :
    (∀ μ, I.IsStable μ → (normalize I).IsStable μ) ∧
    (∀ v, manPartners (normalize I) v = manPartners I v) ∧
    (∀ w, womanPartners (normalize I) w = womanPartners I w) ∧
    (∀ {R : ℕ} (μ : Fin (R + 1) → Matching n), IsMaximalChain I μ →
      IsMaximalChain (normalize I) μ ∧
        ∀ (i : Fin R) (ρ : Rot n), IsExposed I (μ i.castSucc) ρ →
          IsElim (μ i.castSucc) ρ (μ i.succ) → IsExposed (normalize I) (μ i.castSucc) ρ) ∧
    IsNormalized (normalize I) ∧ numStable I ≤ numStable (normalize I) := by
  refine ⟨fun μ hμ => stable_norm hμ, manPartners_eq, womanPartners_eq, ?_, normalized_norm, ?_⟩
  · intro R μ hmc
    refine ⟨⟨manOpt_norm hmc.1, womanOpt_norm hmc.2.1, fun i => ?_⟩,
      fun i ρ h1 h2 => exposed_norm h1 h2⟩
    obtain ⟨ρ, h1, h2⟩ := Dev.RC.exists_rot_of_covers (hmc.2.2 i)
    exact Dev.RC.covers_of_elim (exposed_norm h1 h2) h2
  · unfold numStable
    exact Fintype.card_le_of_injective (fun x => ⟨x.1, stable_norm x.2⟩)
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

end StableCount
end

theorem solution : type_of% @StableCount.chk_proposition_2_5 := @StableCount.chk_proposition_2_5
