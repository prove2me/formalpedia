-- Prove2me | solution 1 for StableCount.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:45:38.49233+00:00
-- url     : https://prove2.me/submissions/632e6cb2-eaa3-4224-91cc-ee9cd173ca7f

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

/-- For stable matchings, `MatchingLE` is equivalent to the reverse order for the women. -/
theorem le_iff_woman {I : Instance n} {μ η : Matching n} (hμ : I.IsStable μ) (hη : I.IsStable η) :
    MatchingLE I μ η ↔ ∀ w, I.womanRank w (η.symm w) ≤ I.womanRank w (μ.symm w) :=
  ⟨fun h => woman_le_of_le hη h, fun h => le_of_woman_le hμ h⟩

theorem le_trans' {I : Instance n} {a b c : Matching n} (h1 : MatchingLE I a b)
    (h2 : MatchingLE I b c) : MatchingLE I a c := fun m => (h1 m).trans (h2 m)

theorem le_antisymm' {I : Instance n} {a b : Matching n} (h1 : MatchingLE I a b)
    (h2 : MatchingLE I b a) : a = b :=
  Equiv.ext fun m => manRank_inj I m (le_antisymm (h1 m) (h2 m))

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

end Dev.Opt

end StableCount
end

section
/-!
# Lemma 3.1 (Irving–Leather): downsets of the full rotation poset ↔ stable matchings
-/

namespace StableCount

open StableMatching

namespace Dev.L31

open Dev.RC

variable {n : ℕ} {I : Instance n}

/-! ## Elimination sequences -/

theorem seq_append {μ ν : Matching n} (l₁ l₂ : List (Rot n)) :
    IsElimSeq I μ (l₁ ++ l₂) ν ↔ ∃ η, IsElimSeq I μ l₁ η ∧ IsElimSeq I η l₂ ν := by
  induction l₁ generalizing μ with
  | nil =>
    simp only [List.nil_append, IsElimSeq]
    exact ⟨fun h => ⟨μ, rfl, h⟩, fun ⟨η, h1, h2⟩ => h1 ▸ h2⟩
  | cons ρ l ih =>
    simp only [List.cons_append, IsElimSeq]
    constructor
    · rintro ⟨he, μ', hel, hs⟩
      obtain ⟨η, h1, h2⟩ := (ih (μ := μ')).mp hs
      exact ⟨η, ⟨he, μ', hel, h1⟩, h2⟩
    · rintro ⟨η, ⟨he, μ', hel, h1⟩, h2⟩
      exact ⟨he, μ', hel, (ih (μ := μ')).mpr ⟨η, h1, h2⟩⟩

theorem seq_snoc {μ η η' : Matching n} {l : List (Rot n)} {σ : Rot n}
    (h : IsElimSeq I μ l η) (he : IsExposed I η σ) (hel : IsElim η σ η') :
    IsElimSeq I μ (l ++ [σ]) η' :=
  (seq_append l [σ]).mpr ⟨η, h, by simp only [IsElimSeq]; exact ⟨he, η', hel, rfl⟩⟩

theorem seq_stable_le {μ ν : Matching n} {l : List (Rot n)} (hμ : I.IsStable μ)
    (h : IsElimSeq I μ l ν) : I.IsStable ν ∧ MatchingLE I μ ν := by
  induction l generalizing μ with
  | nil =>
    simp only [IsElimSeq] at h
    subst h
    exact ⟨hμ, fun _ => le_rfl⟩
  | cons ρ l ih =>
    simp only [IsElimSeq] at h
    obtain ⟨he, μ', hel, hs⟩ := h
    have hc := covers_of_elim he hel
    obtain ⟨h1, h2⟩ := ih (μ := μ') hc.2.1 hs
    exact ⟨h1, le_trans' hc.2.2.1.1 h2⟩

theorem mem_seq_pi {μ ν : Matching n} {l : List (Rot n)} (h : IsElimSeq I μ l ν) {σ : Rot n}
    (hσ : σ ∈ l) : σ ∈ Pi I := by
  induction l generalizing μ with
  | nil => simp at hσ
  | cons ρ l ih =>
    simp only [IsElimSeq] at h
    obtain ⟨he, μ', hel, hs⟩ := h
    rcases List.mem_cons.mp hσ with rfl | hσ'
    · exact ⟨μ, he⟩
    · exact ih (μ := μ') hs hσ'

theorem seq_pair_worse {μ ν : Matching n} {l : List (Rot n)} (hμ : I.IsStable μ)
    (h : IsElimSeq I μ l ν) {σ : Rot n} (hσ : σ ∈ l) {p : Fin n × Fin n} (hp : p ∈ σ) :
    I.manPrefers p.1 p.2 (ν p.1) := by
  induction l generalizing μ with
  | nil => simp at hσ
  | cons ρ l ih =>
    simp only [IsElimSeq] at h
    obtain ⟨he, μ', hel, hs⟩ := h
    have hc := covers_of_elim he hel
    rcases List.mem_cons.mp hσ with rfl | hσ'
    · obtain ⟨h1, h2⟩ := (mem_rot_iff he hel p).mp hp
      have hle := (seq_stable_le hc.2.1 hs).2
      have : I.manPrefers p.1 p.2 (μ' p.1) := by
        rw [← h1]; exact prefers_of_le_ne hc.2.2.1.1 h2
      unfold Instance.manPrefers at this ⊢
      exact lt_of_lt_of_le this (hle p.1)
    · exact ih (μ := μ') hc.2.1 hs hσ'

theorem exists_pair {σ : Rot n} (h : σ ∈ Pi I) : ∃ p, p ∈ σ := by
  obtain ⟨μ, l, rfl, he⟩ := h
  have h2 := he.2.1
  exact ⟨l[0], Cycle.mem_coe_iff.mpr (List.getElem_mem (by omega))⟩

/-- A man passes through every stable partner between his current and final partners. -/
theorem visit {μ ν : Matching n} {l : List (Rot n)} (hμ : I.IsStable μ) (h : IsElimSeq I μ l ν)
    {v w : Fin n} (hw : w ∈ manPartners I v) (h1 : I.manRank v (μ v) ≤ I.manRank v w)
    (h2 : I.manPrefers v w (ν v)) :
    ∃ l₁ l₂ τ η η', l = l₁ ++ τ :: l₂ ∧ IsElimSeq I μ l₁ η ∧ IsExposed I η τ ∧
      IsElim η τ η' ∧ η v = w ∧ η' v ≠ w := by
  induction l generalizing μ with
  | nil =>
    simp only [IsElimSeq] at h
    subst h
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  | cons ρ l ih =>
    simp only [IsElimSeq] at h
    obtain ⟨he, μ', hel, hs⟩ := h
    have hc := covers_of_elim he hel
    by_cases hstop : μ v = w ∧ μ' v ≠ w
    · exact ⟨[], l, ρ, μ, μ', rfl, by simp only [IsElimSeq], he, hel, hstop.1, hstop.2⟩
    · have h1' : I.manRank v (μ' v) ≤ I.manRank v w := by
        by_cases hm : μ v = μ' v
        · rw [← hm]; exact h1
        · obtain ⟨-, -, a3⟩ := next_man he hel hm
          by_cases hvw : μ v = w
          · have : μ' v = w := by
              by_contra hne; exact hstop ⟨hvw, hne⟩
            exact le_of_eq (by rw [this])
          · have hlt : I.manPrefers v (μ v) w :=
              lt_of_le_of_ne h1 (fun e => hvw (manRank_inj I v e))
            by_contra hc'
            push Not at hc'
            exact a3 w hw ⟨hlt, hc'⟩
      obtain ⟨l₁, l₂, τ, η, η', hl, hs1, rest⟩ := ih (μ := μ') hc.2.1 hs h1'
      refine ⟨ρ :: l₁, l₂, τ, η, η', by rw [hl]; rfl, ?_, rest⟩
      simp only [IsElimSeq]
      exact ⟨he, μ', hel, hs1⟩

/-- Two exposed rotations moving a common man out of a common pair are equal. -/
theorem same_rot {μ ν η ν' : Matching n} {ρ σ : Rot n}
    (hρ : IsExposed I μ ρ) (hν : IsElim μ ρ ν) (hσ : IsExposed I η σ) (hν' : IsElim η σ ν')
    {x : Fin n} (hx : μ x = η x) (h1 : μ x ≠ ν x) (h2 : η x ≠ ν' x) : ρ = σ := by
  have key : ∀ k, (nxt μ ν)^[k] x = (nxt η ν')^[k] x ∧
      μ ((nxt μ ν)^[k] x) = η ((nxt μ ν)^[k] x) ∧
      μ ((nxt μ ν)^[k] x) ≠ ν ((nxt μ ν)^[k] x) ∧
      η ((nxt μ ν)^[k] x) ≠ ν' ((nxt μ ν)^[k] x) := by
    intro k
    induction k with
    | zero => exact ⟨rfl, hx, h1, h2⟩
    | succ k ih =>
      obtain ⟨e, a, b, c⟩ := ih
      obtain ⟨e', a', b', c'⟩ := step_agree hρ hν hσ hν' a b c
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← e]
      exact ⟨e', a', b', c'⟩
  rw [eq_orbitCycle hρ hν h1, eq_orbitCycle hσ hν' h2]
  exact orbitCycle_congr (fun k => (key k).1) (fun k => (key k).2.1)

/-! ## Reachability -/

def rsum (I : Instance n) (ν : Matching n) : ℕ := ∑ v, (I.manRank v (ν v)).val

theorem rsum_lt {μ ν : Matching n} (h : MatchingLT I μ ν) : rsum I μ < rsum I ν := by
  obtain ⟨hle, hne⟩ := h
  have : ∃ v, μ v ≠ ν v := by
    by_contra hc
    push Not at hc
    exact hne (Equiv.ext hc)
  obtain ⟨v, hv⟩ := this
  have hlt : I.manRank v (μ v) < I.manRank v (ν v) :=
    lt_of_le_of_ne (hle v) (fun e => hv (manRank_inj I v e))
  unfold rsum
  exact Finset.sum_lt_sum (fun i _ => hle i) ⟨v, Finset.mem_univ _, hlt⟩

theorem reach {μM : Matching n} (hM : IsManOptimal I μM) :
    ∀ ν, I.IsStable ν → ∃ l, IsElimSeq I μM l ν := by
  suffices H : ∀ N, ∀ ν, rsum I ν = N → I.IsStable ν → ∃ l, IsElimSeq I μM l ν from
    fun ν hν => H _ ν rfl hν
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro ν hN hν
  by_cases heq : ν = μM
  · exact ⟨[], by simp only [IsElimSeq]; exact heq⟩
  classical
  let S := Finset.univ.filter fun η : Matching n => I.IsStable η ∧ MatchingLT I η ν
  have hS : μM ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM.1, hM.2 ν hν, fun h => heq h.symm⟩
  obtain ⟨η, hηS, hmax⟩ := S.exists_max_image (rsum I) ⟨μM, hS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hηS hmax
  have hcov : Covers I η ν := ⟨hηS.1, hν, hηS.2, fun η' hη' ⟨h1, h2⟩ =>
    absurd (hmax η' ⟨hη', h2⟩) (not_le.mpr (rsum_lt h1))⟩
  obtain ⟨ρ, he, hel⟩ := exists_rot_of_covers hcov
  obtain ⟨l, hl⟩ := ih (rsum I η) (hN ▸ rsum_lt hηS.2) η rfl hηS.1
  exact ⟨l ++ [ρ], seq_snoc hl he hel⟩

/-! ## The canonical set of eliminated rotations -/

/-- The rotations whose men have moved strictly below their pair in `ν`. -/
def Dset (I : Instance n) (ν : Matching n) : Set (Rot n) :=
  {σ | σ ∈ Pi I ∧ ∃ p ∈ σ, I.manPrefers p.1 p.2 (ν p.1)}

/-- Path independence. -/
theorem mem_seq_iff {μM ν : Matching n} {l : List (Rot n)} (hM : IsManOptimal I μM)
    (h : IsElimSeq I μM l ν) (σ : Rot n) : σ ∈ l ↔ σ ∈ Dset I ν := by
  constructor
  · intro hσ
    have hpi := mem_seq_pi h hσ
    obtain ⟨p, hp⟩ := exists_pair hpi
    exact ⟨hpi, p, hp, seq_pair_worse hM.1 h hσ hp⟩
  · rintro ⟨⟨ζ, hζ⟩, p, hp, hlt⟩
    obtain ⟨ζ', hel⟩ := exists_elim hζ
    obtain ⟨h1, h2⟩ := (mem_rot_iff hζ hel p).mp hp
    have hζs := stable_of_exposed hζ
    have hw : p.2 ∈ manPartners I p.1 := mem_manPartners.mpr ⟨ζ, hζs, h1⟩
    have hle : I.manRank p.1 (μM p.1) ≤ I.manRank p.1 p.2 := by
      rw [← h1]; exact hM.2 ζ hζs p.1
    obtain ⟨l₁, l₂, τ, η, η', rfl, -, hτ, hτel, hη, hη'⟩ := visit hM.1 h hw hle hlt
    have : σ = τ := same_rot hζ hel hτ hτel (h1.trans hη.symm) h2
      (by rw [hη]; exact fun e => hη' e.symm)
    subst this
    simp

theorem dset_all {μM ν : Matching n} (hM : IsManOptimal I μM) (hν : I.IsStable ν) {σ : Rot n}
    (hσ : σ ∈ Dset I ν) {p : Fin n × Fin n} (hp : p ∈ σ) : I.manPrefers p.1 p.2 (ν p.1) := by
  obtain ⟨l, hl⟩ := reach hM ν hν
  exact seq_pair_worse hM.1 hl ((mem_seq_iff hM hl σ).mpr hσ) hp

theorem dset_mono {ζ ν : Matching n} (hle : MatchingLE I ζ ν) : Dset I ζ ⊆ Dset I ν := by
  rintro σ ⟨hpi, p, hp, hlt⟩
  refine ⟨hpi, p, hp, ?_⟩
  unfold Instance.manPrefers at hlt ⊢
  exact lt_of_lt_of_le hlt (hle p.1)

theorem le_of_dset {μM ζ ν : Matching n} (hM : IsManOptimal I μM) (hζ : I.IsStable ζ)
    (hν : I.IsStable ν) (hsub : Dset I ζ ⊆ Dset I ν) : MatchingLE I ζ ν := by
  intro v
  by_contra hc
  push Not at hc
  obtain ⟨l, hl⟩ := reach hM ζ hζ
  have hw : ν v ∈ manPartners I v := mem_manPartners.mpr ⟨ν, hν, rfl⟩
  obtain ⟨l₁, l₂, τ, η, η', rfl, -, hτ, hτel, hη, hη'⟩ := visit hM.1 hl hw (hM.2 ν hν v) hc
  have hτD : τ ∈ Dset I ζ := (mem_seq_iff hM hl τ).mp (by simp)
  have hp : (v, ν v) ∈ τ :=
    (mem_rot_iff hτ hτel _).mpr ⟨hη, by rw [hη]; exact fun e => hη' e.symm⟩
  exact lt_irrefl _ (dset_all hM hν (hsub hτD) hp)

theorem dset_inj {μM ζ ν : Matching n} (hM : IsManOptimal I μM) (hζ : I.IsStable ζ)
    (hν : I.IsStable ν) (h : Dset I ζ = Dset I ν) : ζ = ν :=
  le_antisymm' (le_of_dset hM hζ hν h.le) (le_of_dset hM hν hζ h.ge)

theorem dset_downset {μM ν : Matching n} (hM : IsManOptimal I μM) (hν : I.IsStable ν) :
    IsFullDownset I (Dset I ν) := by
  refine ⟨fun σ h => h.1, fun σ hσ ρ _ hlt => ?_⟩
  obtain ⟨l, hl⟩ := reach hM ν hν
  have hσl := (mem_seq_iff hM hl σ).mpr hσ
  obtain ⟨l₁, l₂, hsplit, hρ1⟩ := hlt.2 _ l ν hM hl hσl
  exact (mem_seq_iff hM hl ρ).mp (by rw [hsplit]; exact List.mem_append_left _ hρ1)

theorem not_mem_dset_of_exposed {ζ : Matching n} {σ : Rot n} (h : IsExposed I ζ σ) :
    σ ∉ Dset I ζ := by
  rintro ⟨-, p, hp, hlt⟩
  obtain ⟨l, rfl, he⟩ := h
  rw [Cycle.mem_coe_iff] at hp
  rw [he.2.2.2.1 p hp] at hlt
  exact lt_irrefl _ hlt

/-! ## Meets -/

noncomputable def meetFun (I : Instance n) (ζ₁ ζ₂ : Matching n) (v : Fin n) : Fin n :=
  if I.manRank v (ζ₁ v) ≤ I.manRank v (ζ₂ v) then ζ₁ v else ζ₂ v

theorem cross {ζ₁ ζ₂ : Matching n} (h1 : I.IsStable ζ₁) (h2 : I.IsStable ζ₂) {a b : Fin n}
    (hab : a ≠ b) (ha : I.manRank a (ζ₁ a) ≤ I.manRank a (ζ₂ a))
    (hb : ¬ I.manRank b (ζ₁ b) ≤ I.manRank b (ζ₂ b)) (h : ζ₁ a = ζ₂ b) : False := by
  have e1 : ζ₁.symm (ζ₁ a) = a := by simp
  have e2 : ζ₂.symm (ζ₁ a) = b := by rw [h]; simp
  have hne : ζ₂ a ≠ ζ₁ a := fun e => hab (ζ₂.injective (e.trans h))
  have hpa : I.manPrefers a (ζ₁ a) (ζ₂ a) :=
    lt_of_le_of_ne ha (fun e => hne (manRank_inj I a e).symm)
  have hpb : I.manPrefers b (ζ₁ a) (ζ₁ b) := by
    rw [h]; exact lt_of_not_ge hb
  have c1 : ¬ I.womanPrefers (ζ₁ a) a (ζ₂.symm (ζ₁ a)) := fun hw => h2 a _ ⟨hpa, hw⟩
  have c2 : ¬ I.womanPrefers (ζ₁ a) b (ζ₁.symm (ζ₁ a)) := fun hw => h1 b _ ⟨hpb, hw⟩
  rw [e2] at c1
  rw [e1] at c2
  unfold Instance.womanPrefers at c1 c2
  exact hab (womanRank_inj I _ (le_antisymm (not_lt.mp c2) (not_lt.mp c1)))

theorem meetFun_inj {ζ₁ ζ₂ : Matching n} (h1 : I.IsStable ζ₁) (h2 : I.IsStable ζ₂) :
    Function.Injective (meetFun I ζ₁ ζ₂) := by
  intro a b hab
  by_contra hne
  unfold meetFun at hab
  split_ifs at hab with ha hb hb
  · exact hne (ζ₁.injective hab)
  · exact cross h1 h2 hne ha hb hab
  · exact cross h1 h2 (Ne.symm hne) hb ha hab.symm
  · exact hne (ζ₂.injective hab)

theorem meetFun_le {ζ₁ ζ₂ : Matching n} (v : Fin n) :
    I.manRank v (meetFun I ζ₁ ζ₂ v) ≤ I.manRank v (ζ₁ v) ∧
      I.manRank v (meetFun I ζ₁ ζ₂ v) ≤ I.manRank v (ζ₂ v) := by
  unfold meetFun
  split_ifs with h
  · exact ⟨le_rfl, h⟩
  · exact ⟨(lt_of_not_ge h).le, le_rfl⟩

theorem meetFun_cases {ζ₁ ζ₂ : Matching n} (v : Fin n) :
    meetFun I ζ₁ ζ₂ v = ζ₁ v ∨ meetFun I ζ₁ ζ₂ v = ζ₂ v := by
  unfold meetFun
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_meet {ζ₁ ζ₂ : Matching n} (h1 : I.IsStable ζ₁) (h2 : I.IsStable ζ₂) :
    ∃ m : Matching n, (∀ v, m v = meetFun I ζ₁ ζ₂ v) ∧ I.IsStable m ∧
      MatchingLE I m ζ₁ ∧ MatchingLE I m ζ₂ := by
  let m : Matching n := Equiv.ofBijective _ (meetFun_inj h1 h2).bijective_of_finite
  have hm : ∀ v, m v = meetFun I ζ₁ ζ₂ v := fun v => rfl
  refine ⟨m, hm, ?_, fun v => by rw [hm]; exact (meetFun_le v).1,
    fun v => by rw [hm]; exact (meetFun_le v).2⟩
  intro a w ⟨hb1, hb2⟩
  have hu : m (m.symm w) = w := by simp
  rw [hm] at hu
  rcases meetFun_cases (ζ₁ := ζ₁) (ζ₂ := ζ₂) (I := I) (m.symm w) with hc | hc
  · rw [hc] at hu
    have e : ζ₁.symm w = m.symm w := (Equiv.symm_apply_eq _).mpr hu.symm
    refine h1 a w ⟨?_, ?_⟩
    · unfold Instance.manPrefers at hb1 ⊢
      exact lt_of_lt_of_le hb1 (by rw [hm]; exact (meetFun_le a).1)
    · rw [e]; exact hb2
  · rw [hc] at hu
    have e : ζ₂.symm w = m.symm w := (Equiv.symm_apply_eq _).mpr hu.symm
    refine h2 a w ⟨?_, ?_⟩
    · unfold Instance.manPrefers at hb1 ⊢
      exact lt_of_lt_of_le hb1 (by rw [hm]; exact (meetFun_le a).2)
    · rw [e]; exact hb2

theorem exposed_any_list {μ : Matching n} {ρ : Rot n} (h : IsExposed I μ ρ)
    {l : List (Fin n × Fin n)} (hl : (l : Cycle (Fin n × Fin n)) = ρ) : IsExposedList I μ l := by
  obtain ⟨l', hl', he⟩ := h
  obtain ⟨k, hk⟩ := Cycle.coe_eq_coe.mp (hl'.trans hl.symm)
  rw [← hk]
  exact isExposedList_rotate he k

/-- Transfer of an exposed list to a stable matching containing its pairs, when every candidate
there is a candidate in some matching exposing the list. -/
theorem exposed_transfer {μ η₀ : Matching n} {l : List (Fin n × Fin n)} (hμ : I.IsStable μ)
    (he : IsExposedList I η₀ l) (hpairs : ∀ p ∈ l, μ p.1 = p.2)
    (hcand : ∀ (i : ℕ) (hi : i < l.length), ∀ w ∈ sCandidates I μ (l[i]).1,
      ∃ η, IsExposedList I η l ∧ w ∈ sCandidates I η (l[i]).1) :
    IsExposedList I μ l := by
  obtain ⟨hη₀, h2, hnd, hp0, hs0⟩ := he
  refine ⟨hμ, h2, hnd, hpairs, fun i hi => ?_⟩
  have hj : (i + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  rw [sMu_eq_some_iff]
  have hs := hs0 i hi
  obtain ⟨hc, -⟩ := sMu_spec hs
  rw [mem_sCandidates] at hc
  have a1 := hpairs _ (List.getElem_mem hi)
  have b1 := hp0 _ (List.getElem_mem hi)
  have a2 := hpairs _ (List.getElem_mem hj)
  have b2 := hp0 _ (List.getElem_mem hj)
  refine ⟨mem_sCandidates.mpr ⟨?_, ?_⟩, fun w hw => ?_⟩
  · rw [a1, ← b1]; exact hc.1
  · have e1 : μ.symm (l[(i + 1) % l.length]'hj).2 = (l[(i + 1) % l.length]'hj).1 := by
      rw [← a2]; simp
    have e2 : η₀.symm (l[(i + 1) % l.length]'hj).2 = (l[(i + 1) % l.length]'hj).1 := by
      rw [← b2]; simp
    rw [e1]; rw [e2] at hc; exact hc.2
  · obtain ⟨η, heη, hwη⟩ := hcand i hi w hw
    exact (sMu_spec (heη.2.2.2.2 i hi)).2 w hwη

theorem meet_exposed {ζ₁ ζ₂ m : Matching n} {σ : Rot n} (h1 : IsExposed I ζ₁ σ)
    (h2 : IsExposed I ζ₂ σ) (hm : ∀ v, m v = meetFun I ζ₁ ζ₂ v) (hms : I.IsStable m) :
    IsExposed I m σ := by
  obtain ⟨l, hl, he1⟩ := h1
  have he2 := exposed_any_list h2 hl
  have hpairs : ∀ p ∈ l, m p.1 = p.2 := by
    intro p hp
    rw [hm]
    have a := he1.2.2.2.1 p hp
    have b := he2.2.2.2.1 p hp
    unfold meetFun
    split_ifs
    · exact a
    · exact b
  refine ⟨l, hl, exposed_transfer hms he1 hpairs ?_⟩
  intro i hi w hw
  rw [mem_sCandidates] at hw
  have hv : m (l[i]).1 = (l[i]).2 := hpairs _ (List.getElem_mem hi)
  have hu : m (m.symm w) = w := by simp
  rw [hm] at hu
  rcases meetFun_cases (ζ₁ := ζ₁) (ζ₂ := ζ₂) (I := I) (m.symm w) with hc | hc
  · refine ⟨ζ₁, he1, mem_sCandidates.mpr ⟨?_, ?_⟩⟩
    · rw [he1.2.2.2.1 _ (List.getElem_mem hi), ← hv]; exact hw.1
    · have e : ζ₁.symm w = m.symm w := by
        rw [hc] at hu; exact (Equiv.symm_apply_eq _).mpr hu.symm
      rw [e]; exact hw.2
  · refine ⟨ζ₂, he2, mem_sCandidates.mpr ⟨?_, ?_⟩⟩
    · rw [he2.2.2.2.1 _ (List.getElem_mem hi), ← hv]; exact hw.1
    · have e : ζ₂.symm w = m.symm w := by
        rw [hc] at hu; exact (Equiv.symm_apply_eq _).mpr hu.symm
      rw [e]; exact hw.2

/-- The least stable matching in which a rotation of `Π` is exposed. -/
theorem least_exposer {σ : Rot n} (hσ : σ ∈ Pi I) :
    ∃ ζ, IsExposed I ζ σ ∧ ∀ ζ', IsExposed I ζ' σ → MatchingLE I ζ ζ' := by
  classical
  let S := Finset.univ.filter fun ζ : Matching n => IsExposed I ζ σ
  obtain ⟨ζ0, hζ0⟩ := hσ
  have hS : ζ0 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hζ0⟩
  obtain ⟨ζ, hζS, hmin⟩ := S.exists_min_image (rsum I) ⟨ζ0, hS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hζS hmin
  refine ⟨ζ, hζS, fun ζ' hζ' => ?_⟩
  obtain ⟨m, hm, hms, hle1, hle2⟩ :=
    exists_meet (stable_of_exposed hζS) (stable_of_exposed hζ')
  have hmexp := meet_exposed hζS hζ' hm hms
  have : m = ζ := by
    by_contra hne
    exact absurd (hmin m hmexp) (not_le.mpr (rsum_lt ⟨hle1, hne⟩))
  rw [← this]; exact hle2

theorem fullLT_of_least {σ : Rot n} {ζ : Matching n} (hζ : IsExposed I ζ σ)
    (hleast : ∀ ζ', IsExposed I ζ' σ → MatchingLE I ζ ζ') {ρ : Rot n} (hρ : ρ ∈ Dset I ζ) :
    FullLT I ρ σ := by
  refine ⟨?_, fun μM' l ν hM' hl hσ => ?_⟩
  · rintro rfl
    exact not_mem_dset_of_exposed hζ hρ
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hσ
    obtain ⟨η, hs1, hs2⟩ := (seq_append l₁ (σ :: l₂)).mp hl
    simp only [IsElimSeq] at hs2
    have hle := hleast η hs2.1
    exact ⟨l₁, l₂, rfl, (mem_seq_iff hM' hs1 ρ).mpr (dset_mono hle hρ)⟩

/-- Key lemma: a rotation not yet eliminated whose `≺f`-predecessors all are, is exposed. -/
theorem exposed_of_downset {μM μ : Matching n} (hM : IsManOptimal I μM) {σ : Rot n}
    (hμ : I.IsStable μ) (hσ : σ ∈ Pi I) (hnot : σ ∉ Dset I μ)
    (hdown : ∀ ρ ∈ Pi I, FullLT I ρ σ → ρ ∈ Dset I μ) : IsExposed I μ σ := by
  obtain ⟨ζ, hζ, hleast⟩ := least_exposer hσ
  have hsub : Dset I ζ ⊆ Dset I μ := fun ρ hρ => hdown ρ hρ.1 (fullLT_of_least hζ hleast hρ)
  have hle := le_of_dset hM (stable_of_exposed hζ) hμ hsub
  obtain ⟨l, hl, he⟩ := hζ
  have hpairs : ∀ p ∈ l, μ p.1 = p.2 := by
    intro p hp
    have h1 := he.2.2.2.1 p hp
    have h2 : ¬ I.manPrefers p.1 p.2 (μ p.1) := fun h =>
      hnot ⟨hσ, p, by rw [← hl]; exact Cycle.mem_coe_iff.mpr hp, h⟩
    unfold Instance.manPrefers at h2
    apply manRank_inj I p.1
    apply le_antisymm (not_lt.mp h2)
    rw [← h1]; exact hle p.1
  refine ⟨l, hl, exposed_transfer hμ he hpairs ?_⟩
  intro i hi w hw
  refine ⟨ζ, he, ?_⟩
  rw [mem_sCandidates] at hw ⊢
  have hp := he.2.2.2.1 _ (List.getElem_mem hi)
  refine ⟨by rw [hp, ← hpairs _ (List.getElem_mem hi)]; exact hw.1, ?_⟩
  unfold Instance.womanPrefers at hw ⊢
  exact lt_of_lt_of_le hw.2 (woman_le_of_le hμ hle w)

/-! ## Consistent orders -/

theorem elim_of_consistent {μM : Matching n} (hM : IsManOptimal I μM) {D : Set (Rot n)}
    (hD : IsFullDownset I D) {l : List (Rot n)} (hl : IsConsistentOrder I D l) :
    ∃ ν, IsElimSeq I μM l ν := by
  obtain ⟨hnd, hmem, hpw⟩ := hl
  suffices H : ∀ l₁ l₂, l = l₁ ++ l₂ → ∃ ν, IsElimSeq I μM l₁ ν from H l [] (by simp)
  intro l₁
  induction l₁ using List.reverseRecOn with
  | nil => intro _ _; exact ⟨μM, by simp only [IsElimSeq]⟩
  | append_singleton l₁ σ ih =>
    intro l₂ heq
    have e : l₁ ++ [σ] ++ l₂ = l₁ ++ σ :: l₂ := by simp
    rw [e] at heq
    obtain ⟨ν, hν⟩ := ih (σ :: l₂) heq
    have hνs := (seq_stable_le hM.1 hν).1
    have hσD : σ ∈ D := (hmem σ).mp (by rw [heq]; simp)
    have hexp : IsExposed I ν σ := by
      apply exposed_of_downset hM hνs (hD.1 hσD)
      · intro h
        rw [← mem_seq_iff hM hν] at h
        rw [heq, List.nodup_append] at hnd
        exact hnd.2.2 σ h σ (List.mem_cons_self) rfl
      · intro ρ hρ hlt
        rw [← mem_seq_iff hM hν]
        have hρl : ρ ∈ l := (hmem ρ).mpr (hD.2 σ hσD ρ hρ hlt)
        rw [heq] at hρl hpw
        rw [List.pairwise_append, List.pairwise_cons] at hpw
        rcases List.mem_append.mp hρl with h | h
        · exact h
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h hlt.1
          · exact absurd hlt (hpw.2.1.1 ρ h)
    obtain ⟨ν', hel⟩ := exists_elim hexp
    exact ⟨ν', seq_snoc hν hexp hel⟩

theorem pi_finite (I : Instance n) : (Pi I).Finite := (StableCount.proposition_2_3 I).1

open Classical in
/-- The least stable matching exposing `σ` (junk outside `Π`). -/
noncomputable def zeta (I : Instance n) (σ : Rot n) : Matching n :=
  if h : ∃ ζ, IsExposed I ζ σ ∧ ∀ ζ', IsExposed I ζ' σ → MatchingLE I ζ ζ' then h.choose
  else Equiv.refl _

theorem zeta_spec {σ : Rot n} (hσ : σ ∈ Pi I) :
    IsExposed I (zeta I σ) σ ∧ ∀ ζ', IsExposed I ζ' σ → MatchingLE I (zeta I σ) ζ' := by
  have h := least_exposer hσ
  unfold zeta
  rw [dif_pos h]
  exact h.choose_spec

theorem key_mono {μM : Matching n} (hM : IsManOptimal I μM) {ρ σ : Rot n} (hρ : ρ ∈ Pi I)
    (hσ : σ ∈ Pi I) (hlt : FullLT I ρ σ) : rsum I (zeta I ρ) < rsum I (zeta I σ) := by
  obtain ⟨hζ, -⟩ := zeta_spec hσ
  obtain ⟨hζρ, hleastρ⟩ := zeta_spec hρ
  obtain ⟨l, hl⟩ := reach hM _ (stable_of_exposed hζ)
  obtain ⟨ζ', hel⟩ := exists_elim hζ
  have hseq := seq_snoc hl hζ hel
  obtain ⟨l₁, l₂, hsplit, hρ1⟩ := hlt.2 μM _ ζ' hM hseq (by simp)
  have hρl : ρ ∈ l := by
    have : ρ ∈ l ++ [σ] := by rw [hsplit]; exact List.mem_append_left _ hρ1
    rcases List.mem_append.mp this with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h) hlt.1
  have hρD : ρ ∈ Dset I (zeta I σ) := (mem_seq_iff hM hl ρ).mp hρl
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hρl
  obtain ⟨η, hs1, hs2⟩ := (seq_append a (ρ :: b)).mp hl
  have hηs := (seq_stable_le hM.1 hs1).1
  have hle2 := (seq_stable_le hηs hs2).2
  simp only [IsElimSeq] at hs2
  have hle : MatchingLE I (zeta I ρ) (zeta I σ) := le_trans' (hleastρ η hs2.1) hle2
  refine rsum_lt ⟨hle, fun h => ?_⟩
  rw [← h] at hρD
  exact not_mem_dset_of_exposed hζρ hρD

theorem exists_consistent {μM : Matching n} (hM : IsManOptimal I μM) (D : Set (Rot n))
    (hD : IsFullDownset I D) : ∃ l, IsConsistentOrder I D l := by
  classical
  have hfin : D.Finite := (pi_finite I).subset hD.1
  have H : ∀ s : Finset (Rot n), (↑s ⊆ Pi I) → ∃ l : List (Rot n), l.Nodup ∧
      (∀ ρ, ρ ∈ l ↔ ρ ∈ s) ∧ l.Pairwise (fun ρ σ => ¬ FullLT I σ ρ) := by
    intro s
    induction s using Finset.induction_on_max_value (fun σ => rsum I (zeta I σ)) with
    | empty => intro _; exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    | insert a s ha hmax ih =>
      intro hs
      have hs' : (↑s : Set (Rot n)) ⊆ Pi I := fun x hx => hs (Finset.mem_insert_of_mem hx)
      have haPi : a ∈ Pi I := hs (Finset.mem_insert_self a s)
      obtain ⟨l, hnd, hmem, hpw⟩ := ih hs'
      refine ⟨l ++ [a], ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton a, fun x hx y hy => ?_⟩
        rw [List.mem_singleton] at hy
        subst hy
        intro e; subst e
        exact ha ((hmem x).mp hx)
      · intro ρ
        simp [hmem, or_comm]
      · rw [List.pairwise_append]
        refine ⟨hpw, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
        rw [List.mem_singleton] at hy
        subst hy
        intro hlt
        have hxs := (hmem x).mp hx
        exact absurd (hmax x hxs) (not_le.mpr (key_mono hM haPi (hs' hxs) hlt))
  obtain ⟨l, h1, h2, h3⟩ := H hfin.toFinset (by simpa using hD.1)
  exact ⟨l, h1, fun ρ => by rw [h2]; simp, h3⟩

end Dev.L31

open Dev.L31 Dev.RC in
theorem chk_lemma_3_1 {n : ℕ} (I : Instance n) :
    ∃ μM, IsManOptimal I μM ∧
      ∃ f : {D : Set (Rot n) // IsFullDownset I D} ≃ {μ : Matching n // I.IsStable μ},
        (∀ D, (∃ l, IsConsistentOrder I D.1 l) ∧
          ∀ l, IsConsistentOrder I D.1 l → IsElimSeq I μM l (f D).1) ∧
        {D : Set (Rot n) | IsFullDownset I D}.Finite ∧
        numStable I = {D : Set (Rot n) | IsFullDownset I D}.ncard := by
  obtain ⟨μM, hM⟩ := Dev.Opt.exists_manOptimal I
  refine ⟨μM, hM, ?_⟩
  let g : {μ : Matching n // I.IsStable μ} → {D : Set (Rot n) // IsFullDownset I D} :=
    fun ν => ⟨Dset I ν.1, dset_downset hM ν.2⟩
  have haux : ∀ D : {D : Set (Rot n) // IsFullDownset I D}, ∀ l, IsConsistentOrder I D.1 l →
      ∃ ν, IsElimSeq I μM l ν ∧ Dset I ν = D.1 := by
    intro D l hl
    obtain ⟨ν, hν⟩ := elim_of_consistent hM D.2 hl
    refine ⟨ν, hν, Set.ext fun σ => ?_⟩
    rw [← mem_seq_iff hM hν]
    exact hl.2.1 σ
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => ?_, fun D => ?_⟩
    · have : Dset I a.1 = Dset I b.1 := congrArg Subtype.val hab
      exact Subtype.ext (dset_inj hM a.2 b.2 this)
    · obtain ⟨l, hl⟩ := exists_consistent hM D.1 D.2
      obtain ⟨ν, hν, hD⟩ := haux D l hl
      exact ⟨⟨ν, (seq_stable_le hM.1 hν).1⟩, Subtype.ext hD⟩
  let e := Equiv.ofBijective g hg
  refine ⟨e.symm, fun D => ⟨exists_consistent hM D.1 D.2, fun l hl => ?_⟩, ?_, ?_⟩
  · obtain ⟨ν, hν, hD⟩ := haux D l hl
    have : e.symm D = ⟨ν, (seq_stable_le hM.1 hν).1⟩ := by
      rw [Equiv.symm_apply_eq]; exact Subtype.ext hD.symm
    rw [this]; exact hν
  · have : Finite {D : Set (Rot n) // IsFullDownset I D} := Finite.of_equiv _ e
    exact Set.finite_coe_iff.mp this
  · unfold numStable
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    exact Nat.card_congr e

end StableCount
end

theorem solution : type_of% @StableCount.chk_lemma_3_1 := @StableCount.chk_lemma_3_1
