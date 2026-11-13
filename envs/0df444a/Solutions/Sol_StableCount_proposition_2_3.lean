-- Prove2me | solution 1 for StableCount.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:28:18.089659+00:00
-- url     : https://prove2.me/submissions/4f2f61c2-0493-44d7-bbae-98cb78caf7ac

import Mathlib
import Definitions.Def_StableCount_Rotation

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

theorem le_of_womanOptimal {I : Instance n} {μW η : Matching n} (hW : IsWomanOptimal I μW)
    (hη : I.IsStable η) : MatchingLE I η μW :=
  le_of_woman_le hη (fun w => hW.2 η hη w)

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

theorem exists_elim {I : Instance n} {μ : Matching n} {ρ : Rot n} (h : IsExposed I μ ρ) :
    ∃ ν, IsElim μ ρ ν := by
  obtain ⟨l, hl, he⟩ := h
  obtain ⟨ν, hν⟩ := exists_elimList he
  exact ⟨ν, l, hl, hν⟩

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

/-- Membership of a pair in an exposed rotation: its man moves, and it is a pair of `μ`. -/
theorem mem_rot_iff {I : Instance n} {μ ν : Matching n} {ρ : Rot n} (h1 : IsExposed I μ ρ)
    (h2 : IsElim μ ρ ν) (p : Fin n × Fin n) : p ∈ ρ ↔ μ p.1 = p.2 ∧ μ p.1 ≠ ν p.1 := by
  obtain ⟨l, rfl, he, hel⟩ := common_list h1 h2
  rw [Cycle.mem_coe_iff]
  constructor
  · intro hp
    have hm : p.1 ∈ l.map Prod.fst := List.mem_map_of_mem hp
    exact ⟨he.2.2.2.1 p hp, fun h => sMu_prefers (sMu_of_mem he hel hm) |>.ne
      (by rw [h])⟩
  · rintro ⟨hp, hmv⟩
    have hm : p.1 ∈ l.map Prod.fst := by
      by_contra hc; exact hmv (hel.2 _ hc).symm
    obtain ⟨i, hi, hi1⟩ := mem_fst_iff.mp hm
    have : l[i] = p := Prod.ext hi1 (by rw [← he.2.2.2.1 _ (List.getElem_mem hi), hi1, hp])
    rw [← this]; exact List.getElem_mem hi

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

namespace Dev.P23

open Dev.RC

variable {n : ℕ}

theorem pi_finite (I : Instance n) : (Pi I).Finite := by
  apply ((List.finite_length_le (Fin n × Fin n) (Fintype.card (Fin n × Fin n))).image
    (fun l : List (Fin n × Fin n) => (l : Cycle (Fin n × Fin n)))).subset
  rintro ρ ⟨μ, l, rfl, he⟩
  exact ⟨l, he.2.2.1.length_le_card, rfl⟩

theorem exists_step {R : ℕ} (p : Fin (R + 1) → Prop) (h0 : ¬ p 0) (hl : p (Fin.last R)) :
    ∃ i : Fin R, ¬ p i.castSucc ∧ p i.succ := by
  by_contra hc
  push Not at hc
  have : ∀ i : Fin (R + 1), ¬ p i := by
    intro i
    induction i using Fin.induction with
    | zero => exact h0
    | succ i ih => exact hc i ih
  exact this _ hl

theorem chain_le {I : Instance n} {R : ℕ} {μ : Fin (R + 1) → Matching n}
    (hc : ∀ i : Fin R, Covers I (μ i.castSucc) (μ i.succ)) (a b : Fin (R + 1)) (hab : a ≤ b) :
    MatchingLE I (μ a) (μ b) := by
  induction b using Fin.induction with
  | zero =>
    have : a = 0 := le_antisymm hab (Fin.zero_le _)
    subst this; exact fun m => le_rfl
  | succ i ih =>
    rcases eq_or_lt_of_le hab with h | h
    · subst h; exact fun m => le_rfl
    · exact le_trans' (ih (Fin.le_castSucc_iff.mpr h)) (hc i).2.2.1.1

end Dev.P23

open Dev.RC Dev.P23

theorem chk_proposition_2_3 {n : ℕ} (I : Instance n) :
    (Pi I).Finite ∧
    (∀ {R : ℕ} (μ : Fin (R + 1) → Matching n), IsMaximalChain I μ →
      ∃ rot : Fin R → Rot n,
        (∀ i, IsExposed I (μ i.castSucc) (rot i) ∧ IsElim (μ i.castSucc) (rot i) (μ i.succ)) ∧
        Function.Injective rot ∧ Set.range rot = Pi I ∧ R = (Pi I).ncard) ∧
    (∀ (μ ν : Matching n) (ρ : Rot n), IsExposed I μ ρ → IsElim μ ρ ν →
      (∀ v, μ v ≠ ν v →
        ν v ∈ manPartners I v ∧ I.manPrefers v (μ v) (ν v) ∧
          ∀ w ∈ manPartners I v, ¬ (I.manPrefers v (μ v) w ∧ I.manPrefers v w (ν v))) ∧
      (∀ w, μ.symm w ≠ ν.symm w →
        ν.symm w ∈ womanPartners I w ∧ I.womanPrefers w (ν.symm w) (μ.symm w) ∧
          ∀ v ∈ womanPartners I w,
            ¬ (I.womanPrefers w (ν.symm w) v ∧ I.womanPrefers w v (μ.symm w)))) := by
  refine ⟨pi_finite I, ?_, fun μ ν ρ h1 h2 =>
    ⟨fun v hv => next_man h1 h2 hv, fun w hw => next_woman h1 h2 hw⟩⟩
  intro R μ hch
  obtain ⟨hM, hW, hc⟩ := hch
  have hrot : ∀ i : Fin R, ∃ ρ, IsExposed I (μ i.castSucc) ρ ∧
      IsElim (μ i.castSucc) ρ (μ i.succ) := fun i => exists_rot_of_covers (hc i)
  choose rot hrot using hrot
  have hinj : Function.Injective rot := by
    intro j k hjk
    by_contra hne
    wlog hlt : j < k generalizing j k
    · exact this hjk.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    obtain ⟨x, hx⟩ : ∃ x, μ j.castSucc x ≠ μ j.succ x := by
      by_contra hc'
      push Not at hc'
      exact (hc j).2.2.1.2 (Equiv.ext hc')
    have hmem : (x, μ j.castSucc x) ∈ rot j :=
      (mem_rot_iff (hrot j).1 (hrot j).2 _).mpr ⟨rfl, hx⟩
    rw [hjk] at hmem
    have hk : μ k.castSucc x = μ j.castSucc x :=
      ((mem_rot_iff (hrot k).1 (hrot k).2 _).mp hmem).1
    have hle1 := chain_le hc j.succ k.castSucc (Fin.succ_le_castSucc_iff.mpr hlt) x
    have hle2 := (hc j).2.2.1.1 x
    rw [hk] at hle1
    exact hx (manRank_inj I x (le_antisymm hle2 hle1))
  have hrange : Set.range rot = Pi I := by
    ext σ
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, (hrot j).1⟩
    · rintro ⟨η, hσ⟩
      obtain ⟨ν', hν'⟩ := exists_elim hσ
      have hηs := stable_of_exposed hσ
      have hν's := stable_of_elim hσ hν'
      obtain ⟨v0, hv0⟩ : ∃ v, η v ≠ ν' v := by
        by_contra hc'
        push Not at hc'
        exact (covers_of_elim hσ hν').2.2.1.2 (Equiv.ext hc')
      obtain ⟨-, hpref, -⟩ := next_man hσ hν' hv0
      obtain ⟨j, hnp, hp⟩ := exists_step
        (fun k => I.manRank v0 (η v0) < I.manRank v0 (μ k v0))
        (not_lt.mpr (hM.2 η hηs v0))
        (lt_of_lt_of_le hpref (le_of_womanOptimal hW hν's v0))
      have hj0 : μ j.castSucc v0 = η v0 := by
        by_contra hne'
        have hlt : I.manRank v0 (μ j.castSucc v0) < I.manRank v0 (η v0) :=
          lt_of_le_of_ne (not_lt.mp hnp) (fun h => hne' (manRank_inj I v0 h))
        have hmv : μ j.castSucc v0 ≠ μ j.succ v0 := by
          intro h; rw [h] at hlt; exact lt_asymm hlt hp
        obtain ⟨-, -, hb⟩ := next_man (hrot j).1 (hrot j).2 hmv
        exact hb (η v0) (mem_manPartners.mpr ⟨η, hηs, rfl⟩) ⟨hlt, hp⟩
      have hmov : μ j.castSucc v0 ≠ μ j.succ v0 := by
        rw [hj0]; intro h; rw [h] at hp; exact lt_irrefl _ hp
      have key : ∀ k, (nxt (μ j.castSucc) (μ j.succ))^[k] v0 = (nxt η ν')^[k] v0 ∧
          μ j.castSucc ((nxt (μ j.castSucc) (μ j.succ))^[k] v0) =
            η ((nxt (μ j.castSucc) (μ j.succ))^[k] v0) ∧
          μ j.castSucc ((nxt (μ j.castSucc) (μ j.succ))^[k] v0) ≠
            μ j.succ ((nxt (μ j.castSucc) (μ j.succ))^[k] v0) ∧
          η ((nxt (μ j.castSucc) (μ j.succ))^[k] v0) ≠
            ν' ((nxt (μ j.castSucc) (μ j.succ))^[k] v0) := by
        intro k
        induction k with
        | zero => exact ⟨rfl, hj0, hmov, hv0⟩
        | succ k ih =>
          obtain ⟨i1, i2, i3, i4⟩ := ih
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← i1]
          exact step_agree (hrot j).1 (hrot j).2 hσ hν' i2 i3 i4
      refine ⟨j, ?_⟩
      rw [eq_orbitCycle (hrot j).1 (hrot j).2 hmov, eq_orbitCycle hσ hν' hv0]
      exact orbitCycle_congr (fun k => (key k).1) (fun k => (key k).2.1)
  refine ⟨rot, hrot, hinj, hrange, ?_⟩
  rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

end StableCount
end

theorem solution : type_of% @StableCount.chk_proposition_2_3 := @StableCount.chk_proposition_2_3
