-- Prove2me | solution 1 for StableCount.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T23:14:43.034149+00:00
-- url     : https://prove2.me/submissions/55df741c-e3f2-4539-910c-a9b11c7f0a35

import Mathlib
import Definitions.Def_StableCount_Rotation
import Definitions.Def_StableCount_Groups
import Definitions.Def_StableCount_Member
import Theorems.Thm_StableCount_proposition_2_3
import Theorems.Thm_StableCount_lemma_2_4

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

/-- For stable matchings, `MatchingLE` is equivalent to the reverse order for the women. -/
theorem le_iff_woman {I : Instance n} {μ η : Matching n} (hμ : I.IsStable μ) (hη : I.IsStable η) :
    MatchingLE I μ η ↔ ∀ w, I.womanRank w (η.symm w) ≤ I.womanRank w (μ.symm w) :=
  ⟨fun h => woman_le_of_le hη h, fun h => le_of_woman_le hμ h⟩

theorem le_trans' {I : Instance n} {a b c : Matching n} (h1 : MatchingLE I a b)
    (h2 : MatchingLE I b c) : MatchingLE I a c := fun m => (h1 m).trans (h2 m)

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

/-- Pointwise description of `μ/ρ`: a man `v` moves iff he is a man of `ρ`, and then he moves to
`s_μ(v)`. -/
theorem elim_spec {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) (v : Fin n) :
    (μ v ≠ ν v → sMu I μ v = some (ν v)) ∧ (μ v = ν v ∨ sMu I μ v = some (ν v)) := by
  obtain ⟨l, -, he, hel⟩ := common_list h1 h2
  by_cases hv : v ∈ l.map Prod.fst
  · exact ⟨fun _ => sMu_of_mem he hel hv, Or.inr (sMu_of_mem he hel hv)⟩
  · exact ⟨fun h => absurd (hel.2 v hv).symm h, Or.inl (hel.2 v hv).symm⟩

/-- (B) The elimination of an exposed rotation is stable. -/
theorem stable_of_elim {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) : I.IsStable ν := by
  obtain ⟨l, -, he, hel⟩ := common_list h1 h2
  exact stable_of_spec (fun v => v ∈ l.map Prod.fst) he.1 (fun v hv => sMu_of_mem he hel hv)
    hel.2

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

/-- NEXT for men: a moving man goes to his next stable partner. -/
theorem next_man {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) {v : Fin n} (hv : μ v ≠ ν v) :
    ν v ∈ manPartners I v ∧ I.manPrefers v (μ v) (ν v) ∧
      ∀ w ∈ manPartners I v, ¬ (I.manPrefers v (μ v) w ∧ I.manPrefers v w (ν v)) := by
  have hμ := stable_of_exposed h1
  have hν := stable_of_elim h1 h2
  have hs := (elim_spec h1 h2 v).1 hv
  refine ⟨mem_manPartners.mpr ⟨ν, hν, rfl⟩, sMu_prefers hs, ?_⟩
  intro w hw ⟨hw1, hw2⟩
  obtain ⟨η, hη, rfl⟩ := mem_manPartners.mp hw
  have hc := cand_of_prefers hμ hη hw1
  exact absurd ((sMu_spec hs).2 _ hc) (not_le.mpr hw2)

/-- The instance with men and women exchanged. -/
def swapInst (I : Instance n) : Instance n := ⟨I.womanRank, I.manRank⟩

theorem swap_stable (I : Instance n) (ν : Matching n) :
    (swapInst I).IsStable ν ↔ I.IsStable ν.symm := by
  unfold Instance.IsStable Instance.IsBlockingPair Instance.manPrefers Instance.womanPrefers
  constructor
  · intro h m w ⟨h1, h2⟩
    exact h w m ⟨h2, h1⟩
  · intro h m w ⟨h1, h2⟩
    exact h w m ⟨h2, h1⟩

theorem swap_le {I : Instance n} {a b : Matching n} (ha : I.IsStable a) (hb : I.IsStable b) :
    MatchingLE (swapInst I) b.symm a.symm ↔ MatchingLE I a b :=
  (le_iff_woman ha hb).symm

theorem swap_covers {I : Instance n} {μ ν : Matching n} (h : Covers I μ ν) :
    Covers (swapInst I) ν.symm μ.symm := by
  obtain ⟨hμ, hν, ⟨hle, hne⟩, hcov⟩ := h
  refine ⟨(swap_stable I _).mpr (by simpa using hν), (swap_stable I _).mpr (by simpa using hμ),
    ⟨(swap_le hμ hν).mpr hle, fun h => hne (Equiv.symm_bijective.injective h).symm⟩, ?_⟩
  rintro η hη ⟨⟨l1, n1⟩, ⟨l2, n2⟩⟩
  have hη' : I.IsStable η.symm := (swap_stable I η).mp hη
  refine hcov η.symm hη' ⟨⟨(swap_le hμ hη').mp (by simpa using l2), ?_⟩,
    ⟨(swap_le hη' hν).mp (by simpa using l1), ?_⟩⟩
  · intro h; apply n2; rw [h]; simp
  · intro h; apply n1; rw [← h]; simp

theorem mem_manPartners_swap {I : Instance n} {w v : Fin n} :
    v ∈ manPartners (swapInst I) w ↔ v ∈ womanPartners I w := by
  rw [mem_manPartners, mem_womanPartners]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨μ.symm, (swap_stable I μ).mp hμ, by simp⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨μ.symm, (swap_stable I μ.symm).mpr (by simpa using hμ), rfl⟩

/-- NEXT for women: a moving woman goes to her next stable partner (upwards in her list). -/
theorem next_woman {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) {w : Fin n} (hw : μ.symm w ≠ ν.symm w) :
    ν.symm w ∈ womanPartners I w ∧ I.womanPrefers w (ν.symm w) (μ.symm w) ∧
      ∀ v ∈ womanPartners I w,
        ¬ (I.womanPrefers w (ν.symm w) v ∧ I.womanPrefers w v (μ.symm w)) := by
  have hν := stable_of_elim h1 h2
  have hc := swap_covers (covers_of_elim h1 h2)
  obtain ⟨ρ', h1', h2'⟩ := exists_rot_of_covers hc
  obtain ⟨-, hp, hb⟩ := next_man h1' h2' (Ne.symm hw)
  exact ⟨mem_womanPartners.mpr ⟨ν, hν, rfl⟩, hp, fun v hv => hb v (mem_manPartners_swap.mpr hv)⟩

theorem adj_unique (r : Fin n ≃ Fin n) (S : Finset (Fin n)) {a b b' : Fin n} (hb : b ∈ S)
    (hb' : b' ∈ S) (h : r a < r b) (h' : r a < r b') (hn : ∀ w ∈ S, ¬ (r a < r w ∧ r w < r b))
    (hn' : ∀ w ∈ S, ¬ (r a < r w ∧ r w < r b')) : b = b' := by
  rcases lt_trichotomy (r b) (r b') with hl | he | hg
  · exact absurd ⟨h, hl⟩ (hn' b hb)
  · exact r.injective he
  · exact absurd ⟨h', hg⟩ (hn b' hb')

/-- Two exposed rotations (in possibly different stable matchings) through a common pair
`(x, μ x)`: the next pair is common too. -/
theorem step_agree {I : Instance n} {μ ν η ν' : Matching n} {ρ σ : Rot n}
    (hρ : IsExposed I μ ρ) (hν : IsElim μ ρ ν) (hσ : IsExposed I η σ) (hν' : IsElim η σ ν')
    {x : Fin n} (hx : μ x = η x) (h1 : μ x ≠ ν x) (h2 : η x ≠ ν' x) :
    nxt μ ν x = nxt η ν' x ∧ μ (nxt μ ν x) = η (nxt μ ν x) ∧
      μ (nxt μ ν x) ≠ ν (nxt μ ν x) ∧ η (nxt μ ν x) ≠ ν' (nxt μ ν x) := by
  have hμ := stable_of_exposed hρ
  have hη := stable_of_exposed hσ
  obtain ⟨a1, a2, a3⟩ := next_man hρ hν h1
  obtain ⟨b1, b2, b3⟩ := next_man hσ hν' h2
  rw [← hx] at b2 b3
  have hw : ν x = ν' x := adj_unique (I.manRank x) (manPartners I x) a1 b1 a2 b2 a3 b3
  have e1 : ν.symm (ν x) = x := by simp
  have e2 : ν'.symm (ν x) = x := by rw [hw]; simp
  have hm1 : μ.symm (ν x) ≠ x := by
    intro h; rw [Equiv.symm_apply_eq] at h; exact h1 h.symm
  have hm2 : η.symm (ν x) ≠ x := by
    intro h; rw [Equiv.symm_apply_eq, hw] at h; exact h2 h.symm
  obtain ⟨-, c2, c3⟩ := next_woman hρ hν (w := ν x) (by rw [e1]; exact hm1)
  obtain ⟨-, d2, d3⟩ := next_woman hσ hν' (w := ν x) (by rw [e2]; exact hm2)
  rw [e1] at c2 c3
  rw [e2] at d2 d3
  have hy : μ.symm (ν x) = η.symm (ν x) :=
    adj_unique (I.womanRank (ν x)) (womanPartners I (ν x))
      (mem_womanPartners.mpr ⟨μ, hμ, rfl⟩) (mem_womanPartners.mpr ⟨η, hη, rfl⟩) c2 d2 c3 d3
  have hn1 : nxt μ ν x = μ.symm (ν x) := rfl
  have hn2 : nxt η ν' x = η.symm (ν x) := by rw [nxt, hw]
  refine ⟨by rw [hn1, hn2, hy],
    by rw [hn1, Equiv.apply_symm_apply, hy, Equiv.apply_symm_apply], ?_, ?_⟩
  · rw [hn1, Equiv.apply_symm_apply]
    intro h
    exact hm1 (ν.injective h.symm)
  · rw [hn1, hy, Equiv.apply_symm_apply]
    intro h
    exact hm2 (ν'.injective (h.symm.trans hw))

/-! ## Canonical form of an exposed rotation -/

/-- The list `((x, μ x), (g x, μ (g x)), …)` of length `L` for `g = nxt μ ν`. -/
def orbitList (μ ν : Matching n) (x : Fin n) (L : ℕ) : List (Fin n × Fin n) :=
  (List.range L).map fun k => ((nxt μ ν)^[k] x, μ ((nxt μ ν)^[k] x))

/-- The rotation through `x` determined by `μ` and `ν = μ/ρ`. -/
noncomputable def orbitCycle (μ ν : Matching n) (x : Fin n) : Rot n :=
  (orbitList μ ν x (Function.minimalPeriod (nxt μ ν) x) : Cycle (Fin n × Fin n))

/-- An exposed rotation is the orbit of any of its men. -/
theorem eq_orbitCycle {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) {x : Fin n} (hx : μ x ≠ ν x) : ρ = orbitCycle μ ν x := by
  obtain ⟨l, rfl, he, hel⟩ := common_list h1 h2
  have hxm : x ∈ l.map Prod.fst := by by_contra hc; exact hx (hel.2 x hc).symm
  obtain ⟨i, hi, rfl⟩ := mem_fst_iff.mp hxm
  have hμl := he.2.2.2.1
  have hit := iterate_nxt_list hμl hel i hi
  have hpos : 0 < l.length := by omega
  have hper : Function.IsPeriodicPt (nxt μ ν) l.length l[i].1 := by
    show (nxt μ ν)^[l.length] l[i].1 = l[i].1
    rw [hit]; congr 1; exact gidx l _ _ (by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi])
  have hmp : Function.minimalPeriod (nxt μ ν) l[i].1 = l.length := by
    apply le_antisymm (hper.minimalPeriod_le hpos)
    by_contra hc
    push Not at hc
    have hmpos : 0 < Function.minimalPeriod (nxt μ ν) l[i].1 := hper.minimalPeriod_pos hpos
    have h4 : (nxt μ ν)^[Function.minimalPeriod (nxt μ ν) l[i].1] l[i].1 = l[i].1 :=
      Function.isPeriodicPt_minimalPeriod (nxt μ ν) l[i].1
    rw [hit] at h4
    have h5 := fst_inj he.2.2.1 hμl _ hi h4
    generalize Function.minimalPeriod (nxt μ ν) l[i].1 = m at hmpos hc h5
    rcases Nat.lt_or_ge (i + m) l.length with h6 | h6
    · rw [Nat.mod_eq_of_lt h6] at h5; omega
    · rw [Nat.mod_eq_sub_mod h6, Nat.mod_eq_of_lt (by omega)] at h5; omega
  have hrot : l.rotate i = orbitList μ ν l[i].1 l.length := by
    apply List.ext_getElem
    · simp [orbitList]
    · intro k hk1 hk2
      rw [List.getElem_rotate]
      simp only [orbitList, List.getElem_map, List.getElem_range]
      rw [hit k]
      have e : (k + i) % l.length = (i + k) % l.length := by rw [Nat.add_comm]
      rw [gidx l _ (Nat.mod_lt _ hpos) e]
      exact Prod.ext rfl (hμl _ (List.getElem_mem _)).symm
  unfold orbitCycle
  rw [hmp, ← hrot]
  exact Cycle.coe_eq_coe.mpr ⟨i, rfl⟩

theorem orbitCycle_congr {μ ν η ν' : Matching n} {x : Fin n}
    (h1 : ∀ k, (nxt μ ν)^[k] x = (nxt η ν')^[k] x)
    (h2 : ∀ k, μ ((nxt μ ν)^[k] x) = η ((nxt μ ν)^[k] x)) :
    orbitCycle μ ν x = orbitCycle η ν' x := by
  have hmp : Function.minimalPeriod (nxt μ ν) x = Function.minimalPeriod (nxt η ν') x := by
    rw [Function.minimalPeriod_eq_minimalPeriod_iff]
    intro k
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [h1 k]
  unfold orbitCycle orbitList
  rw [hmp]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [h2 k, h1 k]

end Dev.RC

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.L52

variable {n : ℕ}

/-- the partner of the person `p` of sex `s` in the `m`-th matching of the chain -/
def partner (Q : Member n) : Sex → Fin (Q.R + 1) → Fin n → Fin n
  | .man, m, p => Q.μ m p
  | .woman, m, p => (Q.μ m).symm p

theorem moves_iff (Q : Member n) (s : Sex) (i : Fin Q.R) (p : Fin n) :
    Q.moves s i p ↔ partner Q s i.castSucc p ≠ partner Q s i.succ p := by
  cases s <;> rfl

/-- no move before `m` means the partner is the initial one -/
theorem partner_eq_zero (Q : Member n) (s : Sex) (p : Fin n) (m : Fin (Q.R + 1))
    (h : ∀ k : Fin Q.R, (k : ℕ) < m → ¬ Q.moves s k p) : partner Q s m p = partner Q s 0 p := by
  obtain ⟨m, hm⟩ := m
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmR : m < Q.R := by omega
    have h1 := ih (by omega) (fun k hk => h k (by simp only [Fin.val_mk] at hk ⊢; omega))
    have h2 := h ⟨m, hmR⟩ (by simp)
    rw [moves_iff] at h2
    push_neg at h2
    rw [← h1]
    exact h2.symm

/-- no move between `a` and `b` -/
theorem partner_eq_of_no_move (Q : Member n) (s : Sex) (p : Fin n) (a b : Fin (Q.R + 1))
    (hab : a ≤ b) (h : ∀ k : Fin Q.R, (a : ℕ) ≤ k → (k : ℕ) < b → ¬ Q.moves s k p) :
    partner Q s b p = partner Q s a p := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => rfl
  | succ b hab' ih =>
    have hbR : b < Q.R := by omega
    have h1 := ih (by omega) (Fin.mk_le_mk.mpr hab')
      (fun k hk1 hk2 => h k hk1 (by simp only [Fin.val_mk] at hk2 ⊢; omega))
    have h2 := h ⟨b, hbR⟩ (by simpa using hab') (by simp)
    rw [moves_iff] at h2
    push_neg at h2
    rw [← h1]
    exact h2.symm

end Dev.L52

end StableCount
end

section
/-!
# Linear extensions of the chain order (shared helpers for Lemmas 3.2 and 3.6)

In a normalized instance, applying the chain steps of a downset of `Q.le` in any order whose
prefixes are downsets is a valid rotation elimination sequence, and it ends at the canonical
matching of the downset.
-/

namespace StableCount

open StableMatching

namespace Dev.LE

open Dev.RC

variable {n : ℕ}

/-! ## The order `Q.le` -/

theorem le_le (Q : Member n) {a b : Fin Q.R} (h : Q.le a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hr ih => exact ih.trans hr.1.le

theorem le_of_man (Q : Member n) {i j : Fin Q.R} {v : Fin n} (hij : i < j)
    (hi : Q.moves .man i v) (hj : Q.moves .man j v) : Q.le i j :=
  Relation.ReflTransGen.single ⟨hij, v, hi, hj⟩

/-- A downset of `Q.le` (in the whole poset). -/
def IsDown (Q : Member n) (S : Finset (Fin Q.R)) : Prop := ∀ a ∈ S, ∀ b, Q.le b a → b ∈ S

theorem isDown_iff (Q : Member n) (S : Finset (Fin Q.R)) :
    Q.IsDownsetIn Finset.univ S ↔ IsDown Q S :=
  ⟨fun h a ha b hb => h.2 a ha b (Finset.mem_univ _) hb,
    fun h => ⟨Finset.subset_univ _, fun a ha b _ hb => h a ha b hb⟩⟩

/-! ## Step permutations -/

theorem stepPerm_apply (Q : Member n) (i : Fin Q.R) (v : Fin n) :
    Q.stepPerm i v = (Q.μ i.castSucc).symm (Q.μ i.succ v) := rfl

theorem step_eq (Q : Member n) (i : Fin Q.R) (v : Fin n) :
    Q.μ i.succ v = Q.μ i.castSucc (Q.stepPerm i v) := by
  rw [stepPerm_apply, Equiv.apply_symm_apply]

theorem stepPerm_fix (Q : Member n) (i : Fin Q.R) (v : Fin n) :
    Q.stepPerm i v = v ↔ ¬ Q.moves .man i v := by
  show _ ↔ ¬ (Q.μ i.castSucc v ≠ Q.μ i.succ v)
  rw [not_not, stepPerm_apply, Equiv.symm_apply_eq]
  exact eq_comm

theorem stepPerm_mover (Q : Member n) (i : Fin Q.R) {v : Fin n} (hv : Q.moves .man i v) :
    Q.moves .man i (Q.stepPerm i v) := by
  rw [← not_not (a := Q.moves .man i _), ← stepPerm_fix]
  intro h
  exact ((stepPerm_fix Q i v).mp (Q.stepPerm i |>.injective h)) hv

theorem stepPerm_eq_nxt (Q : Member n) (i : Fin Q.R) :
    ⇑(Q.stepPerm i) = nxt (Q.μ i.castSucc) (Q.μ i.succ) := rfl

/-! ## Monotone chains -/

theorem chain_le {I : Instance n} {R : ℕ} (μ : Fin (R + 1) → Matching n)
    (h : ∀ k : Fin R, MatchingLE I (μ k.castSucc) (μ k.succ)) (a b : Fin (R + 1)) (hab : a ≤ b) :
    MatchingLE I (μ a) (μ b) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact fun m => le_refl _
  | succ b hab' ih =>
    have h1 := ih (by omega) (Fin.mk_le_mk.mpr hab')
    have h2 := h ⟨b, by omega⟩
    exact Dev.RC.le_trans' h1 h2

/-! ## The canonical matching of a downset -/

/-- `ζ` gives every man `v` his chain partner just after his last step in `S`. -/
def Good (Q : Member n) (S : Finset (Fin Q.R)) (ζ : Matching n) : Prop :=
  ∀ (v : Fin n) (t : Fin (Q.R + 1)),
    (∀ j : Fin Q.R, Q.moves .man j v → (j ∈ S ↔ (j : ℕ) < t)) → ζ v = Q.μ t v

theorem good_zero (Q : Member n) : Good Q ∅ (Q.μ 0) := by
  intro v t ht
  have := Dev.L52.partner_eq_zero Q .man v t (fun k hk hmv => by
    have := (ht k hmv).mpr hk
    simp at this)
  simpa [Dev.L52.partner] using this.symm

theorem no_move_between (Q : Member n) (v : Fin n) (a b : Fin (Q.R + 1)) (hab : a ≤ b)
    (h : ∀ k : Fin Q.R, (a : ℕ) ≤ k → (k : ℕ) < b → ¬ Q.moves .man k v) : Q.μ b v = Q.μ a v := by
  have := Dev.L52.partner_eq_of_no_move Q .man v a b hab h
  simpa [Dev.L52.partner] using this

/-- On the men of step `i`, a good matching agrees with `μ i`. -/
theorem agree (Q : Member n) {S : Finset (Fin Q.R)} {ζ : Matching n} (hg : Good Q S ζ)
    (hS : IsDown Q S) {i : Fin Q.R} (hi : i ∉ S) (hSi : IsDown Q (insert i S)) {v : Fin n}
    (hv : Q.moves .man i v) : ζ v = Q.μ i.castSucc v := by
  apply hg v i.castSucc
  intro j hj
  simp only [Fin.val_castSucc]
  constructor
  · intro hjS
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with hlt | heq
    · exact hi (hS j hjS i (le_of_man Q (Fin.lt_def.mpr hlt) hv hj))
    · exact hi (Fin.ext heq ▸ hjS)
  · intro hlt
    have := hSi i (Finset.mem_insert_self _ _) j (le_of_man Q (Fin.lt_def.mpr hlt) hj hv)
    rcases Finset.mem_insert.mp this with h | h
    · exact absurd h (Fin.ne_of_lt (Fin.lt_def.mpr hlt))
    · exact h

theorem good_step (Q : Member n) {S : Finset (Fin Q.R)} {ζ : Matching n} (hg : Good Q S ζ)
    (hS : IsDown Q S) {i : Fin Q.R} (hi : i ∉ S) (hSi : IsDown Q (insert i S)) :
    Good Q (insert i S) ((Q.stepPerm i).trans ζ) := by
  intro v t ht
  rw [Equiv.trans_apply]
  by_cases hv : Q.moves .man i v
  · have hit : (i : ℕ) < t := (ht i hv).mp (Finset.mem_insert_self _ _)
    rw [agree Q hg hS hi hSi (stepPerm_mover Q i hv), ← step_eq]
    symm
    apply no_move_between Q v i.succ t (Fin.le_def.mpr (by simp; omega))
    intro k hk1 hk2 hkv
    have hk : k ∈ insert i S := (ht k hkv).mpr hk2
    rcases Finset.mem_insert.mp hk with h | h
    · subst h; simp at hk1
    · exact hi (hS k h i (le_of_man Q (Fin.lt_def.mpr (by simp at hk1; omega)) hv hkv))
  · rw [(stepPerm_fix Q i v).mpr hv]
    apply hg v t
    intro j hj
    rw [← ht j hj, Finset.mem_insert]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact absurd (h ▸ hj) hv
      · exact h

theorem good_unique (Q : Member n) {S : Finset (Fin Q.R)} (hS : IsDown Q S) {ζ ζ' : Matching n}
    (h1 : Good Q S ζ) (h2 : Good Q S ζ') : ζ = ζ' := by
  classical
  ext v
  congr 1
  set C := S.filter fun j => Q.moves .man j v with hC
  by_cases hne : C.Nonempty
  · set m := C.max' hne
    have hm : m ∈ C := Finset.max'_mem _ _
    rw [hC, Finset.mem_filter] at hm
    have key : ∀ j : Fin Q.R, Q.moves .man j v → (j ∈ S ↔ (j : ℕ) < m.succ) := by
      intro j hj
      simp only [Fin.val_succ]
      constructor
      · intro hjS
        have : j ≤ m := Finset.le_max' _ _ (by rw [hC, Finset.mem_filter]; exact ⟨hjS, hj⟩)
        rw [Fin.le_def] at this; omega
      · intro hlt
        rcases (Nat.lt_succ_iff.mp hlt).lt_or_eq with h | h
        · exact hS m hm.1 j (le_of_man Q (Fin.lt_def.mpr h) hj hm.2)
        · exact (Fin.ext h) ▸ hm.1
    rw [h1 v _ key, h2 v _ key]
  · have key : ∀ j : Fin Q.R, Q.moves .man j v → (j ∈ S ↔ (j : ℕ) < (0 : Fin (Q.R + 1))) := by
      intro j hj
      simp only [Fin.val_zero, Nat.not_lt_zero, iff_false]
      intro hjS
      exact hne ⟨j, by rw [hC, Finset.mem_filter]; exact ⟨hjS, hj⟩⟩
    rw [h1 v _ key, h2 v _ key]

/-! ## Rotations through a common pair coincide -/

theorem same_rot {I : Instance n} {η η1 μ μ1 : Matching n} {ρ σ : Rot n}
    (h1 : IsExposed I η ρ) (h2 : IsElim η ρ η1) (h3 : IsExposed I μ σ) (h4 : IsElim μ σ μ1)
    {x : Fin n} (hx : η x = μ x) (hx1 : η x ≠ η1 x) (hx2 : μ x ≠ μ1 x) : ρ = σ := by
  have H : ∀ k, (nxt η η1)^[k] x = (nxt μ μ1)^[k] x ∧ η ((nxt η η1)^[k] x) = μ ((nxt η η1)^[k] x) ∧
      η ((nxt η η1)^[k] x) ≠ η1 ((nxt η η1)^[k] x) ∧ μ ((nxt η η1)^[k] x) ≠ μ1 ((nxt η η1)^[k] x) := by
    intro k
    induction k with
    | zero => exact ⟨rfl, hx, hx1, hx2⟩
    | succ k ih =>
      obtain ⟨a1, a2, a3, a4⟩ := ih
      obtain ⟨b1, b2, b3, b4⟩ := step_agree h1 h2 h3 h4 a2 a3 a4
      simp only [Function.iterate_succ_apply']
      rw [← a1, ← b1]
      exact ⟨rfl, b2, b3, b4⟩
  rw [eq_orbitCycle h1 h2 hx1, eq_orbitCycle h3 h4 hx2]
  exact orbitCycle_congr (fun k => (H k).1) (fun k => (H k).2.1)

/-! ## Validity of a step at a good matching -/

theorem mem_iff_moves (Q : Member n) {i : Fin Q.R} {l : List (Fin n × Fin n)}
    (he : IsExposedList Q.I (Q.μ i.castSucc) l) (hel : IsElimList (Q.μ i.castSucc) l (Q.μ i.succ))
    (v : Fin n) : Q.moves .man i v ↔ v ∈ l.map Prod.fst := by
  constructor
  · intro hv
    by_contra hc
    exact hv (hel.2 v hc).symm
  · intro hv h
    have := sMu_prefers (sMu_of_mem he hel hv)
    show False
    have h' : Q.μ i.castSucc v = Q.μ i.succ v := h
    unfold Instance.manPrefers at this
    rw [h'] at this
    exact lt_irrefl _ this

theorem valid_step (Q : Member n) {i : Fin Q.R} {ρ : Rot n}
    (hrot : IsExposed Q.I (Q.μ i.castSucc) ρ ∧ IsElim (Q.μ i.castSucc) ρ (Q.μ i.succ))
    {ζ : Matching n} (hζ : Q.I.IsStable ζ)
    (hag : ∀ v, Q.moves .man i v → ζ v = Q.μ i.castSucc v) :
    IsExposed Q.I ζ ρ ∧ IsElim ζ ρ ((Q.stepPerm i).trans ζ) ∧
      Covers Q.I ζ ((Q.stepPerm i).trans ζ) := by
  set ζ' := (Q.stepPerm i).trans ζ with hζ'
  have hag2 : ∀ v, Q.moves .man i v → ζ' v = Q.μ i.succ v := by
    intro v hv
    rw [hζ', Equiv.trans_apply, hag _ (stepPerm_mover Q i hv), ← step_eq]
  have hfix : ∀ v, ¬ Q.moves .man i v → ζ' v = ζ v := by
    intro v hv
    rw [hζ', Equiv.trans_apply, (stepPerm_fix Q i v).mpr hv]
  obtain ⟨l, -, he, hel⟩ := common_list hrot.1 hrot.2
  have hmem := mem_iff_moves Q he hel
  have h1 : ∀ v, Q.moves .man i v → sMu Q.I ζ v = some (ζ' v) := by
    intro v hv
    rw [hag2 v hv, sMu_eq_some_iff]
    have hs := sMu_spec (sMu_of_mem he hel ((hmem v).mp hv))
    have hζv : ζ v = Q.μ i.castSucc v := hag v hv
    have hζs : ζ.symm (Q.μ i.succ v) = (Q.μ i.castSucc).symm (Q.μ i.succ v) := by
      rw [step_eq, Equiv.symm_apply_apply, Equiv.symm_apply_eq,
        hag _ (stepPerm_mover Q i hv)]
    rw [mem_sCandidates] at hs
    constructor
    · rw [mem_sCandidates, hζv, hζs]
      exact hs.1
    · intro w hw
      rw [mem_sCandidates, hζv] at hw
      by_contra hlt
      push Not at hlt
      obtain ⟨hsP, -, hbtw⟩ := next_man hrot.1 hrot.2 (v := v) hv
      by_cases hwP : w ∈ manPartners Q.I v
      · exact hbtw w hwP ⟨hw.1, hlt⟩
      · have := Q.normalized.1 v _ w hsP hwP
        unfold Instance.manPrefers at this
        exact lt_asymm this hlt
  have hlen := he.2.1
  have hne : ∃ x, Q.moves .man i x :=
    ⟨(l[0]'(by omega)).1, (hmem _).mpr (getElem_fst_mem l 0 (by omega))⟩
  have hnxt : nxt ζ ζ' = nxt (Q.μ i.castSucc) (Q.μ i.succ) := by
    funext v
    show ζ.symm (ζ (Q.stepPerm i v)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hcov : Covers Q.I ζ ζ' := by
    apply covers_of_spec (fun v => Q.moves .man i v) hζ h1 hfix hne
    intro x y hx hy
    rw [hnxt]
    exact orbit_list he.2.2.2.1 hel ((hmem x).mp hx) ((hmem y).mp hy)
  obtain ⟨ρ', hρ1, hρ2⟩ := exists_rot_of_covers hcov
  obtain ⟨x, hx⟩ := hne
  have heq : ρ' = ρ := same_rot hρ1 hρ2 hrot.1 hrot.2 (hag x hx)
    (moves_of_spec (fun v => Q.moves .man i v) h1 hx) hx
  subst heq
  exact ⟨hρ1, hρ2, hcov⟩

theorem stepPerm_isCycle (Q : Member n) {i : Fin Q.R} {ρ : Rot n}
    (hrot : IsExposed Q.I (Q.μ i.castSucc) ρ ∧ IsElim (Q.μ i.castSucc) ρ (Q.μ i.succ)) :
    (Q.stepPerm i).IsCycle := by
  obtain ⟨l, -, he, hel⟩ := common_list hrot.1 hrot.2
  have hmem := mem_iff_moves Q he hel
  have hlen := he.2.1
  set x := (l[0]'(by omega)).1
  have hx : Q.moves .man i x := (hmem _).mpr (getElem_fst_mem l 0 (by omega))
  refine ⟨x, fun h => ((stepPerm_fix Q i x).mp h) hx, fun y hy => ?_⟩
  have hy' : Q.moves .man i y := fun h => hy ((stepPerm_fix Q i y).mpr (not_not.mpr h))
  obtain ⟨k, hk⟩ := orbit_list he.2.2.2.1 hel ((hmem x).mp hx) ((hmem y).mp hy')
  refine ⟨k, ?_⟩
  rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow, stepPerm_eq_nxt]
  exact hk

/-- Applying step `i` at a matching agreeing with `μ i` on the men of step `i` moves the same
people as step `i` itself. -/
theorem moves_man_transfer (Q : Member n) (i : Fin Q.R) (ζ : Matching n) (p : Fin n) :
    ζ p ≠ ((Q.stepPerm i).trans ζ) p ↔ Q.moves .man i p := by
  rw [Equiv.trans_apply, Ne, ζ.injective.eq_iff, eq_comm, stepPerm_fix, not_not]

theorem moves_woman_transfer (Q : Member n) (i : Fin Q.R) {ζ : Matching n}
    (hag : ∀ v, Q.moves .man i v → ζ v = Q.μ i.castSucc v) (p : Fin n) :
    ζ.symm p ≠ ((Q.stepPerm i).trans ζ).symm p ↔ Q.moves .woman i p := by
  have hμ : Q.μ i.succ = (Q.stepPerm i).trans (Q.μ i.castSucc) := Equiv.ext (step_eq Q i)
  show ζ.symm p ≠ ((Q.stepPerm i).trans ζ).symm p ↔
    (Q.μ i.castSucc).symm p ≠ (Q.μ i.succ).symm p
  rw [hμ, Equiv.symm_trans_apply, Equiv.symm_trans_apply]
  have key : ∀ x, x ≠ (Q.stepPerm i).symm x ↔ Q.moves .man i x := by
    intro x
    rw [Ne, Equiv.eq_symm_apply, stepPerm_fix, not_not]
  rw [key, key]
  constructor
  · intro h
    have := hag _ h
    rw [Equiv.apply_symm_apply] at this
    have e : (Q.μ i.castSucc).symm p = ζ.symm p := by rw [Equiv.symm_apply_eq]; exact this
    rwa [e]
  · intro h
    have := hag _ h
    rw [Equiv.apply_symm_apply] at this
    have e : ζ.symm p = (Q.μ i.castSucc).symm p := by rw [Equiv.symm_apply_eq]; exact this.symm
    rwa [e]

/-! ## Folding steps along a linear extension -/

/-- `L` can be applied after the downset `S`: every prefix of `S ++ L` is a downset. -/
def Hyp (Q : Member n) (S : Finset (Fin Q.R)) (L : List (Fin Q.R)) : Prop :=
  IsDown Q S ∧ IsDown Q (S ∪ L.toFinset) ∧ L.Nodup ∧ Disjoint S L.toFinset ∧
    L.Pairwise fun a b => ¬ Q.le b a

theorem ins_union {R : ℕ} (a : Fin R) (S : Finset (Fin R)) (L : List (Fin R)) :
    insert a S ∪ L.toFinset = S ∪ (a :: L).toFinset := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
  tauto

theorem hyp_cons (Q : Member n) {S : Finset (Fin Q.R)} {a : Fin Q.R} {L : List (Fin Q.R)}
    (h : Hyp Q S (a :: L)) : IsDown Q (insert a S) ∧ a ∉ S ∧ Hyp Q (insert a S) L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [List.nodup_cons] at h3
  rw [List.pairwise_cons] at h5
  have haS : a ∉ S := fun h => Finset.disjoint_left.mp h4 h (by simp)
  have hD : IsDown Q (insert a S) := by
    intro x hx b hb
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have := h2 x (by simp) b hb
      rw [Finset.mem_union, List.mem_toFinset, List.mem_cons] at this
      rcases this with h | rfl | h
      · exact Finset.mem_insert_of_mem h
      · exact Finset.mem_insert_self _ _
      · exact absurd hb (h5.1 b h)
    · exact Finset.mem_insert_of_mem (h1 x hx b hb)
  refine ⟨hD, haS, hD, (ins_union a S L) ▸ h2, h3.2, ?_, h5.2⟩
  rw [Finset.disjoint_insert_left]
  refine ⟨by simpa using h3.1, Finset.disjoint_of_subset_right ?_ h4⟩
  intro x hx
  simp only [List.mem_toFinset, List.mem_cons] at hx ⊢
  exact Or.inr hx

theorem hyp_append (Q : Member n) (L2 : List (Fin Q.R)) :
    ∀ (L1 : List (Fin Q.R)) (S : Finset (Fin Q.R)), Hyp Q S (L1 ++ L2) →
      Hyp Q S L1 ∧ Hyp Q (S ∪ L1.toFinset) L2 := by
  intro L1
  induction L1 with
  | nil =>
    intro S h
    refine ⟨⟨h.1, by simpa using h.1, List.nodup_nil, by simp, List.Pairwise.nil⟩, by simpa using h⟩
  | cons a L1 ih =>
    intro S h
    rw [List.cons_append] at h
    have hpw := (List.pairwise_cons.mp h.2.2.2.2).1
    obtain ⟨hD, haS, h'⟩ := hyp_cons Q h
    obtain ⟨k1, k2⟩ := ih (insert a S) h'
    refine ⟨⟨h.1, (ins_union a S L1) ▸ k1.2.1, ?_, ?_, ?_⟩, (ins_union a S L1) ▸ k2⟩
    · have haL : a ∉ L1 := fun hm =>
        Finset.disjoint_left.mp k1.2.2.2.1 (Finset.mem_insert_self a S) (by simpa using hm)
      exact List.nodup_cons.mpr ⟨haL, k1.2.2.1⟩
    · rw [List.toFinset_cons, Finset.disjoint_insert_right]
      exact ⟨haS, Finset.disjoint_of_subset_left (Finset.subset_insert _ _) k1.2.2.2.1⟩
    · exact List.pairwise_cons.mpr ⟨fun b hb => hpw b (List.mem_append_left _ hb), k1.2.2.2.2⟩

theorem fold_main (Q : Member n) {rot : Fin Q.R → Rot n}
    (hrot : ∀ i, IsExposed Q.I (Q.μ i.castSucc) (rot i) ∧ IsElim (Q.μ i.castSucc) (rot i) (Q.μ i.succ)) :
    ∀ (L : List (Fin Q.R)) (S : Finset (Fin Q.R)) (ζ : Matching n), Hyp Q S L → Good Q S ζ →
      Q.I.IsStable ζ →
      Good Q (S ∪ L.toFinset) (L.foldl (fun ν i => (Q.stepPerm i).trans ν) ζ) ∧
      Q.I.IsStable (L.foldl (fun ν i => (Q.stepPerm i).trans ν) ζ) ∧
      IsElimSeq Q.I ζ (L.map rot) (L.foldl (fun ν i => (Q.stepPerm i).trans ν) ζ) := by
  intro L
  induction L with
  | nil =>
    intro S ζ _ hg hst
    refine ⟨by simpa using hg, hst, rfl⟩
  | cons a L ih =>
    intro S ζ h hg hst
    obtain ⟨hD, haS, h'⟩ := hyp_cons Q h
    have hag := fun v (hv : Q.moves .man a v) => agree Q hg h.1 haS hD hv
    obtain ⟨e1, e2, e3⟩ := valid_step Q (hrot a) hst hag
    have hg' := good_step Q hg h.1 haS hD
    obtain ⟨k1, k2, k3⟩ := ih (insert a S) _ h' hg' e3.2.1
    exact ⟨(ins_union a S L) ▸ k1, k2, e1, _, e2, k3⟩

theorem hyp_sort (Q : Member n) (S X : Finset (Fin Q.R)) (hS : IsDown Q S)
    (hSX : IsDown Q (S ∪ X)) (hd : Disjoint S X) : Hyp Q S (X.sort (· ≤ ·)) := by
  refine ⟨hS, by rwa [Finset.sort_toFinset], Finset.sort_nodup _ _, by rwa [Finset.sort_toFinset], ?_⟩
  exact (Finset.sortedLT_sort X).pairwise.imp fun hab hba => absurd (le_le Q hba) (not_le.mpr hab)

theorem matchingOf_good (Q : Member n) {rot : Fin Q.R → Rot n}
    (hrot : ∀ i, IsExposed Q.I (Q.μ i.castSucc) (rot i) ∧ IsElim (Q.μ i.castSucc) (rot i) (Q.μ i.succ))
    (X : Finset (Fin Q.R)) (hX : IsDown Q X) :
    Good Q X (Q.matchingOf X) ∧ Q.I.IsStable (Q.matchingOf X) ∧
      IsElimSeq Q.I (Q.μ 0) ((X.sort (· ≤ ·)).map rot) (Q.matchingOf X) := by
  have h := fold_main Q hrot (X.sort (· ≤ ·)) ∅ (Q.μ 0)
    (hyp_sort Q ∅ X (fun _ h => by simp at h) (by simpa using hX) (by simp))
    (good_zero Q) Q.chain.1.1
  rw [Finset.sort_toFinset, Finset.empty_union] at h
  exact h

end Dev.LE

end StableCount
end

section
/-!
# Lemma 3.6: restricting the rotation poset to an order-convex set
-/

namespace StableCount

open StableMatching

namespace Dev.L36

open Dev.RC Dev.LE

variable {n : ℕ}

/-- The steps of `P = Q \ (D ∪ U)` applied in increasing order after the downset `D`. -/
def zeta (Q : Member n) (D U : Finset (Fin Q.R)) (k : ℕ) : Matching n :=
  (((Finset.univ \ (D ∪ U)).sort (· ≤ ·)).take k).foldl (fun ν i => (Q.stepPerm i).trans ν)
    (Q.matchingOf D)

section

variable (Q : Member n) {rot : Fin Q.R → Rot n}
  (hrot : ∀ i, IsExposed Q.I (Q.μ i.castSucc) (rot i) ∧ IsElim (Q.μ i.castSucc) (rot i) (Q.μ i.succ))
  {D U : Finset (Fin Q.R)} (hD : IsDown Q D) (hU : Q.IsUpset U) (hDU : Disjoint D U)

include hD hU in
theorem isDown_DP : IsDown Q (D ∪ (Finset.univ \ (D ∪ U))) := by
  intro a ha b hb
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
  rcases ha with ha | ha
  · exact Or.inl (hD a ha b hb)
  · by_cases hbD : b ∈ D
    · exact Or.inl hbD
    · refine Or.inr fun h => ?_
      rcases h with h | h
      · exact hbD h
      · exact ha (Or.inr (hU b h a hb))

include hD hU in
theorem hypL : Hyp Q D ((Finset.univ \ (D ∪ U)).sort (· ≤ ·)) := by
  apply hyp_sort Q D _ hD (isDown_DP Q hD hU)
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hb
  exact hb (Or.inl ha)

include hrot hD hU in
theorem zeta_facts (k : ℕ) :
    Good Q (D ∪ (((Finset.univ \ (D ∪ U)).sort (· ≤ ·)).take k).toFinset) (zeta Q D U k) ∧
      Q.I.IsStable (zeta Q D U k) := by
  have h := hypL Q hD hU
  rw [← List.take_append_drop k ((Finset.univ \ (D ∪ U)).sort (· ≤ ·))] at h
  obtain ⟨h1, -⟩ := hyp_append Q _ _ D h
  obtain ⟨g0, s0, -⟩ := matchingOf_good Q hrot D hD
  obtain ⟨g, s, -⟩ := fold_main Q hrot _ D _ h1 g0 s0
  exact ⟨g, s⟩

include hrot hD hU in
theorem step_facts (k : ℕ) (hk : k < ((Finset.univ \ (D ∪ U)).sort (· ≤ ·)).length) :
    zeta Q D U (k + 1) =
        (Q.stepPerm (((Finset.univ \ (D ∪ U)).sort (· ≤ ·))[k])).trans (zeta Q D U k) ∧
      (∀ v, Q.moves .man (((Finset.univ \ (D ∪ U)).sort (· ≤ ·))[k]) v →
        zeta Q D U k v = Q.μ (((Finset.univ \ (D ∪ U)).sort (· ≤ ·))[k]).castSucc v) ∧
      Covers Q.I (zeta Q D U k) (zeta Q D U (k + 1)) := by
  set L := (Finset.univ \ (D ∪ U)).sort (· ≤ ·) with hL
  have heq : zeta Q D U (k + 1) = (Q.stepPerm L[k]).trans (zeta Q D U k) := by
    unfold zeta
    rw [← hL, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hk]
    rfl
  have h := hypL Q hD hU
  rw [← hL, ← List.take_append_drop k L, List.drop_eq_getElem_cons hk] at h
  obtain ⟨-, h2⟩ := hyp_append Q _ _ D h
  obtain ⟨hD', hnot, -⟩ := hyp_cons Q h2
  obtain ⟨g, s⟩ := zeta_facts Q hrot hD hU k
  have hag : ∀ v, Q.moves .man L[k] v → zeta Q D U k v = Q.μ L[k].castSucc v :=
    fun v hv => agree Q g h2.1 hnot hD' hv
  refine ⟨heq, hag, ?_⟩
  rw [heq]
  exact (valid_step Q (hrot _) s hag).2.2

end

theorem bijOn (Q : Member n) {D U : Finset (Fin Q.R)} (hD : IsDown Q D) (hU : Q.IsUpset U)
    (hDU : Disjoint D U) :
    Set.BijOn (fun K => D ∪ K) {K | Q.IsDownsetIn (Finset.univ \ (D ∪ U)) K}
      {K | Q.IsDownsetIn Finset.univ K ∧ D ⊆ K ∧ Disjoint K U} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro K ⟨hKP, hK⟩
    refine ⟨(isDown_iff Q _).mpr ?_, Finset.subset_union_left, ?_⟩
    · intro a ha b hb
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.mem_union_left _ (hD a ha b hb)
      · by_cases hbD : b ∈ D
        · exact Finset.mem_union_left _ hbD
        · have haP := hKP ha
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at haP
          refine Finset.mem_union_right _ (hK a ha b ?_ hb)
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
          rintro (h | h)
          · exact hbD h
          · exact haP (Or.inr (hU b h a hb))
    · rw [Finset.disjoint_union_left]
      refine ⟨hDU, Finset.disjoint_left.mpr fun a ha haU => ?_⟩
      have := hKP ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at this
      exact this (Or.inr haU)
  · rintro K1 ⟨hK1, -⟩ K2 ⟨hK2, -⟩ h
    simp only at h
    ext x
    constructor
    · intro hx
      have hxP := hK1 hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hxP
      have : x ∈ D ∪ K2 := h ▸ Finset.mem_union_right _ hx
      rcases Finset.mem_union.mp this with h' | h'
      · exact absurd (Or.inl h') hxP
      · exact h'
    · intro hx
      have hxP := hK2 hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hxP
      have : x ∈ D ∪ K1 := h.symm ▸ Finset.mem_union_right _ hx
      rcases Finset.mem_union.mp this with h' | h'
      · exact absurd (Or.inl h') hxP
      · exact h'
  · rintro K' ⟨hK', hDK, hKU⟩
    refine ⟨K' \ D, ⟨?_, ?_⟩, Finset.union_sdiff_of_subset hDK⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
      rintro (h | h)
      · exact hx.2 h
      · exact Finset.disjoint_left.mp hKU hx.1 h
    · intro a ha b hb hba
      rw [Finset.mem_sdiff] at ha ⊢
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hb
      exact ⟨hK'.2 a ha.1 b (Finset.mem_univ _) hba, fun h => hb (Or.inl h)⟩

end Dev.L36

open Dev.RC Dev.LE Dev.L36 in
theorem chk_lemma_3_6 {n : ℕ} (Q : Member n) (D U : Finset (Fin Q.R))
    (hD : Q.IsDownsetIn Finset.univ D) (hU : Q.IsUpset U) (hDU : Disjoint D U) :
    ∃ (QP : Member n) (e : {i // i ∈ Finset.univ \ (D ∪ U)} ≃ Fin QP.R),
      Q.IsRestriction (Finset.univ \ (D ∪ U)) QP e ∧
      Set.BijOn (fun K => D ∪ K) {K | Q.IsDownsetIn (Finset.univ \ (D ∪ U)) K}
        {K | Q.IsDownsetIn Finset.univ K ∧ D ⊆ K ∧ Disjoint K U} ∧
      ∀ K' : Finset (Fin QP.R), QP.IsDownsetIn Finset.univ K' →
        QP.matchingOf K' = Q.matchingOf (D ∪ K'.image fun j => (e.symm j : Fin Q.R)) := by
  have hD' : IsDown Q D := (isDown_iff Q D).mp hD
  obtain ⟨-, h2, -⟩ := proposition_2_3 Q.I
  obtain ⟨rot, hrot, -, -, -⟩ := h2 Q.μ Q.chain
  set P := Finset.univ \ (D ∪ U) with hP
  set L := P.sort (· ≤ ·) with hL
  have hLlen : L.length = P.card := Finset.length_sort _
  set μ' : Fin (P.card + 1) → Matching n := fun k => zeta Q D U k with hμ'
  have hst : ∀ k, Q.I.IsStable (μ' k) := fun k => (zeta_facts Q hrot hD' hU k).2
  have hjL : ∀ j : Fin P.card, (j : ℕ) < L.length := fun j => by rw [hLlen]; exact j.2
  have hsf : ∀ j : Fin P.card, μ' j.succ = (Q.stepPerm (L[(j : ℕ)]'(hjL j))).trans (μ' j.castSucc) :=
    fun j => (step_facts Q hrot hD' hU j (hjL j)).1
  have hcov : ∀ j : Fin P.card, Covers Q.I (μ' j.castSucc) (μ' j.succ) :=
    fun j => (step_facts Q hrot hD' hU j (hjL j)).2.2
  have hagr : ∀ j : Fin P.card, ∀ v, Q.moves .man ((L[(j : ℕ)]'(hjL j))) v →
      μ' j.castSucc v = Q.μ ((L[(j : ℕ)]'(hjL j))).castSucc v :=
    fun j => (step_facts Q hrot hD' hU j (hjL j)).2.1
  have hmono : ∀ k : Fin P.card, MatchingLE Q.I (μ' k.castSucc) (μ' k.succ) :=
    fun k => (hcov k).2.2.1.1
  have hcycle : ∀ i : Fin P.card, ∃ c : Equiv.Perm (Fin n), c.IsCycle ∧
      ∀ v, μ' i.succ v = μ' i.castSucc (c v) :=
    fun i => ⟨_, stepPerm_isCycle Q (hrot _), fun v => by rw [hsf i]; rfl⟩
  have hman : ∀ (v : Fin n) (i j k : Fin (P.card + 1)), i ≤ j → j ≤ k → μ' i v = μ' k v →
      μ' j v = μ' i v := by
    intro v i j k hij hjk heq
    have a1 := chain_le μ' hmono i j hij v
    have a2 := chain_le μ' hmono j k hjk v
    rw [← heq] at a2
    exact manRank_inj _ _ (le_antisymm a2 a1)
  have hwoman : ∀ (w : Fin n) (i j k : Fin (P.card + 1)), i ≤ j → j ≤ k →
      (μ' i).symm w = (μ' k).symm w → (μ' j).symm w = (μ' i).symm w := by
    intro w i j k hij hjk heq
    have a1 := woman_le_of_le (hst j) (chain_le μ' hmono i j hij) w
    have a2 := woman_le_of_le (hst k) (chain_le μ' hmono j k hjk) w
    rw [← heq] at a2
    exact womanRank_inj _ _ (le_antisymm a1 a2)
  obtain ⟨I', hn, hc, -, -⟩ := lemma_2_4 μ' hcycle hman hwoman
  let QP : Member n := ⟨I', P.card, μ', hn, hc⟩
  let e : {i // i ∈ P} ≃ Fin QP.R := (P.orderIsoOfFin rfl).symm.toEquiv
  have hes : ∀ j : Fin QP.R, ((e.symm j : {i // i ∈ P}) : Fin Q.R) = P.orderEmbOfFin rfl j :=
    fun j => rfl
  have hesL : ∀ j : Fin QP.R, ((e.symm j : {i // i ∈ P}) : Fin Q.R) = (L[(j : ℕ)]'(hjL j)) :=
    fun j => rfl
  -- step permutations and moves agree
  have hstep : ∀ j : Fin QP.R, QP.stepPerm j = Q.stepPerm (e.symm j : Fin Q.R) := by
    intro j
    show (μ' j.succ).trans (μ' j.castSucc).symm = _
    rw [hsf j, hesL]
    ext v
    simp
  have hmoves : ∀ (s : Sex) (p : Fin n) (j : Fin QP.R),
      QP.moves s j p ↔ Q.moves s (e.symm j : Fin Q.R) p := by
    intro s p j
    rw [hesL]
    cases s
    · show μ' j.castSucc p ≠ μ' j.succ p ↔ _
      rw [hsf j]
      exact moves_man_transfer Q _ _ p
    · show (μ' j.castSucc).symm p ≠ (μ' j.succ).symm p ↔ _
      rw [hsf j]
      exact moves_woman_transfer Q _ (hagr j) p
  have hlt : ∀ x y : Fin QP.R, x < y ↔ (e.symm x : Fin Q.R) < (e.symm y : Fin Q.R) := by
    intro x y
    rw [hes, hes, OrderEmbedding.lt_iff_lt]
  have hrel : ∀ x y : Fin QP.R, (x < y ∧ QP.sharesMan x y) ↔
      ((e.symm x : Fin Q.R) < (e.symm y : Fin Q.R) ∧
        Q.sharesMan (e.symm x : Fin Q.R) (e.symm y : Fin Q.R)) := by
    intro x y
    unfold Member.sharesMan
    simp only [hmoves, hlt]
  have hmemP : ∀ x : Fin Q.R, x ∈ P ↔ x ∉ D ∧ x ∉ U := by
    intro x
    simp [hP]
  -- the orders agree
  have hle : ∀ a b : {i // i ∈ P}, Q.le a b ↔ QP.le (e a) (e b) := by
    intro a b
    constructor
    · have key : ∀ c, Q.le (a : Fin Q.R) c → ∀ hc : c ∈ P, QP.le (e a) (e ⟨c, hc⟩) := by
        intro c h
        induction h with
        | refl => intro _; exact Relation.ReflTransGen.refl
        | @tail c d hac hr ih =>
          intro hd
          have hcP : c ∈ P := by
            rw [hmemP]
            refine ⟨fun hcD => ?_, fun hcU => ?_⟩
            · exact ((hmemP a).mp a.2).1 (hD' c hcD a hac)
            · exact ((hmemP d).mp hd).2 (hU c hcU d (Relation.ReflTransGen.single hr))
          refine Relation.ReflTransGen.tail (ih hcP) ((hrel _ _).mpr ?_)
          simpa using hr
      intro h
      exact key b h b.2
    · have key : ∀ y, QP.le (e a) y → Q.le (a : Fin Q.R) (e.symm y : Fin Q.R) := by
        intro y h
        induction h with
        | refl =>
          rw [Equiv.symm_apply_apply]
          exact Relation.ReflTransGen.refl
        | tail _ hr ih => exact Relation.ReflTransGen.tail ih ((hrel _ _).mp hr)
      intro h
      simpa using key _ h
  refine ⟨QP, e, ⟨hle, fun s p i => by simpa using hmoves s p (e i)⟩, bijOn Q hD' hU hDU, ?_⟩
  intro K' hK'
  set g : Fin QP.R → Fin Q.R := fun j => (e.symm j : Fin Q.R) with hg
  have hginj : Function.Injective g := fun x y h => e.symm.injective (Subtype.ext h)
  set X := K'.image g with hX
  have hXP : Q.IsDownsetIn P X := by
    refine ⟨fun x hx => ?_, fun a ha b hb hba => ?_⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      exact (e.symm j).2
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      have h1 := (hle ⟨b, hb⟩ (e.symm j)).mp hba
      rw [Equiv.apply_symm_apply] at h1
      have h2 := hK'.2 j hj _ (Finset.mem_univ _) h1
      exact Finset.mem_image.mpr ⟨_, h2, by simp [hg]⟩
  have hDX : IsDown Q (D ∪ X) := ((isDown_iff Q _).mp ((bijOn Q hD' hU hDU).1 hXP).1)
  have hR := (matchingOf_good Q hrot (D ∪ X) hDX).1
  have hfun : (fun (ν : Matching n) (i : Fin QP.R) => (QP.stepPerm i).trans ν) =
      (fun (ν : Matching n) (i : Fin QP.R) => (Q.stepPerm (g i)).trans ν) := by
    funext ν i
    rw [hstep]
  have hL0 : QP.μ 0 = Q.matchingOf D := by
    show zeta Q D U 0 = _
    simp [zeta]
  have hlhs : QP.matchingOf K' =
      ((K'.sort (· ≤ ·)).map g).foldl (fun ν i => (Q.stepPerm i).trans ν) (Q.matchingOf D) := by
    unfold Member.matchingOf
    rw [hfun, hL0, List.foldl_map]
    rfl
  have htf : ((K'.sort (· ≤ ·)).map g).toFinset = X := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_sort, hX, Finset.mem_image]
  have hhyp : Hyp Q D ((K'.sort (· ≤ ·)).map g) := by
    refine ⟨hD', by rw [htf]; exact hDX, (Finset.sort_nodup _ _).map hginj, ?_, ?_⟩
    · rw [htf, Finset.disjoint_left]
      intro x hxD hxX
      exact ((hmemP x).mp (hXP.1 hxX)).1 hxD
    · rw [List.pairwise_map]
      exact (Finset.sortedLT_sort K').pairwise.imp fun hab hba =>
        absurd (le_le Q hba) (not_le.mpr ((hlt _ _).mp hab))
  obtain ⟨g0, s0, -⟩ := matchingOf_good Q hrot D hD'
  have hL := (fold_main Q hrot _ D _ hhyp g0 s0).1
  rw [htf, ← hlhs] at hL
  exact good_unique Q hDX hL hR

end StableCount
end

theorem solution : type_of% @StableCount.chk_lemma_3_6 := @StableCount.chk_lemma_3_6
