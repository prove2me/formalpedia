-- Prove2me | solution 1 for StableCount.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:45:37.456351+00:00
-- url     : https://prove2.me/submissions/0e19513d-2bf8-4e5a-bdd2-84d56a1d9845

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

/-! ## Canonical form of an exposed rotation -/

end Dev.RC

end StableCount
end

section
namespace StableCount

open StableMatching

namespace Dev.L24

variable {n : ℕ}

/-! ## Rank bijections from injective keys -/

/-- The rank bijection of an injective sort key. -/
noncomputable def rk (key : Fin n → ℕ) : Fin n ≃ Fin n := (Tuple.sort key).symm

theorem rk_lt {key : Fin n → ℕ} (hk : Function.Injective key) (x y : Fin n) :
    rk key x < rk key y ↔ key x < key y := by
  have hm := Tuple.monotone_sort key
  have hx : Tuple.sort key (rk key x) = x := Equiv.apply_symm_apply _ _
  have hy : Tuple.sort key (rk key y) = y := Equiv.apply_symm_apply _ _
  constructor
  · intro h
    have h1 : key x ≤ key y := by
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

theorem rk_le {key : Fin n → ℕ} (hk : Function.Injective key) (x y : Fin n) :
    rk key x ≤ rk key y ↔ key x ≤ key y := by
  rw [← not_lt, ← not_lt, rk_lt hk]

/-! ## First times -/

section

variable {R : ℕ} (μ : Fin (R + 1) → Matching n)

theorem exists_first (P : Fin (R + 1) → Prop) (h : ∃ i, P i) :
    ∃ i, P i ∧ ∀ j, P j → i ≤ j := by
  classical
  have hne : (Finset.univ.filter P).Nonempty := by
    obtain ⟨i, hi⟩ := h; exact ⟨i, by simp [hi]⟩
  exact ⟨_, (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2,
    fun j hj => Finset.min'_le _ _ (by simp [hj])⟩

open Classical in
/-- Man `v`'s key for woman `w`: the first time she is his partner, or `R + 1 + w`. -/
noncomputable def mkey (v w : Fin n) : ℕ :=
  if h : ∃ i, μ i v = w then ((exists_first (fun i => μ i v = w) h).choose : ℕ) else R + 1 + w

open Classical in
/-- Woman `w`'s key for man `m`: `R` minus the first time he is her partner, or `R + 1 + m`. -/
noncomputable def wkey (w m : Fin n) : ℕ :=
  if h : ∃ i, (μ i).symm w = m then R - ((exists_first (fun i => (μ i).symm w = m) h).choose : ℕ)
  else R + 1 + m

theorem mkey_of {v w : Fin n} {i : Fin (R + 1)} (h : μ i v = w)
    (hmin : ∀ j, μ j v = w → i ≤ j) : mkey μ v w = i := by
  unfold mkey
  rw [dif_pos ⟨i, h⟩]
  have hs := (exists_first (fun i => μ i v = w) ⟨i, h⟩).choose_spec
  exact congrArg Fin.val (le_antisymm (hs.2 i h) (hmin _ hs.1))

theorem mkey_not {v w : Fin n} (h : ∀ i, μ i v ≠ w) : mkey μ v w = R + 1 + w := by
  unfold mkey
  rw [dif_neg (by push Not; exact h)]

theorem mkey_exists {v w : Fin n} (h : ∃ i, μ i v = w) :
    ∃ i, μ i v = w ∧ (∀ j, μ j v = w → i ≤ j) ∧ mkey μ v w = i := by
  obtain ⟨i, hi, hmin⟩ := exists_first (fun i => μ i v = w) h
  exact ⟨i, hi, hmin, mkey_of μ hi hmin⟩

theorem mkey_le_of {v w : Fin n} {i : Fin (R + 1)} (h : μ i v = w) : mkey μ v w ≤ i := by
  obtain ⟨t, -, htmin, hk⟩ := mkey_exists μ ⟨i, h⟩
  rw [hk]; exact Fin.le_iff_val_le_val.mp (htmin i h)

theorem enc_of_mkey {v w : Fin n} (h : mkey μ v w ≤ R) : ∃ i, μ i v = w := by
  by_contra hc
  push Not at hc
  rw [mkey_not μ hc] at h
  omega

theorem mkey_inj (v : Fin n) : Function.Injective (mkey μ v) := by
  intro w w' he
  by_cases h : ∃ i, μ i v = w <;> by_cases h' : ∃ i, μ i v = w'
  · obtain ⟨i, hi, -, hk⟩ := mkey_exists μ h
    obtain ⟨i', hi', -, hk'⟩ := mkey_exists μ h'
    rw [hk, hk'] at he
    rw [← hi, ← hi', Fin.ext he]
  · push Not at h'
    obtain ⟨i, -, -, hk⟩ := mkey_exists μ h
    rw [hk, mkey_not μ h'] at he
    have := i.isLt; omega
  · push Not at h
    obtain ⟨i, -, -, hk⟩ := mkey_exists μ h'
    rw [hk, mkey_not μ h] at he
    have := i.isLt; omega
  · push Not at h h'
    rw [mkey_not μ h, mkey_not μ h'] at he
    exact Fin.ext (by omega)

theorem wkey_of {w m : Fin n} {i : Fin (R + 1)} (h : (μ i).symm w = m)
    (hmin : ∀ j, (μ j).symm w = m → i ≤ j) : wkey μ w m = R - i := by
  unfold wkey
  rw [dif_pos ⟨i, h⟩]
  have hs := (exists_first (fun i => (μ i).symm w = m) ⟨i, h⟩).choose_spec
  rw [le_antisymm (hs.2 i h) (hmin _ hs.1)]

theorem wkey_not {w m : Fin n} (h : ∀ i, (μ i).symm w ≠ m) : wkey μ w m = R + 1 + m := by
  unfold wkey
  rw [dif_neg (by push Not; exact h)]

theorem wkey_exists {w m : Fin n} (h : ∃ i, (μ i).symm w = m) :
    ∃ i, (μ i).symm w = m ∧ (∀ j, (μ j).symm w = m → i ≤ j) ∧ wkey μ w m = R - i := by
  obtain ⟨i, hi, hmin⟩ := exists_first (fun i => (μ i).symm w = m) h
  exact ⟨i, hi, hmin, wkey_of μ hi hmin⟩

theorem wkey_le {w m : Fin n} (h : ∃ i, (μ i).symm w = m) : wkey μ w m ≤ R := by
  obtain ⟨i, -, -, hk⟩ := wkey_exists μ h
  omega

theorem enc_of_wkey {w m : Fin n} (h : wkey μ w m ≤ R) : ∃ i, (μ i).symm w = m := by
  by_contra hc
  push Not at hc
  rw [wkey_not μ hc] at h
  omega

theorem wkey_inj (w : Fin n) : Function.Injective (wkey μ w) := by
  intro m m' he
  by_cases h : ∃ i, (μ i).symm w = m <;> by_cases h' : ∃ i, (μ i).symm w = m'
  · obtain ⟨i, hi, -, hk⟩ := wkey_exists μ h
    obtain ⟨i', hi', -, hk'⟩ := wkey_exists μ h'
    rw [hk, hk'] at he
    have := i.isLt; have := i'.isLt
    rw [← hi, ← hi', Fin.ext (show (i : ℕ) = i' by omega)]
  · push Not at h'
    obtain ⟨i, -, -, hk⟩ := wkey_exists μ h
    rw [hk, wkey_not μ h'] at he
    omega
  · push Not at h
    obtain ⟨i, -, -, hk⟩ := wkey_exists μ h'
    rw [hk, wkey_not μ h] at he
    omega
  · push Not at h h'
    rw [wkey_not μ h, wkey_not μ h'] at he
    exact Fin.ext (by omega)

/-- The constructed instance. -/
noncomputable def inst : Instance n := ⟨fun v => rk (mkey μ v), fun w => rk (wkey μ w)⟩

theorem mp_iff {v a b : Fin n} : (inst μ).manPrefers v a b ↔ mkey μ v a < mkey μ v b :=
  rk_lt (mkey_inj μ v) a b

theorem wp_iff {w a b : Fin n} : (inst μ).womanPrefers w a b ↔ wkey μ w a < wkey μ w b :=
  rk_lt (wkey_inj μ w) a b

theorem mr_le_iff {v a b : Fin n} :
    (inst μ).manRank v a ≤ (inst μ).manRank v b ↔ mkey μ v a ≤ mkey μ v b :=
  rk_le (mkey_inj μ v) a b

theorem wr_le_iff {w a b : Fin n} :
    (inst μ).womanRank w a ≤ (inst μ).womanRank w b ↔ wkey μ w a ≤ wkey μ w b :=
  rk_le (wkey_inj μ w) a b

/-! ## The chain in the constructed instance -/

variable (hman : ∀ (v : Fin n) (i j k : Fin (R + 1)), i ≤ j → j ≤ k → μ i v = μ k v → μ j v = μ i v)
  (hwoman : ∀ (w : Fin n) (i j k : Fin (R + 1)), i ≤ j → j ≤ k →
      (μ i).symm w = (μ k).symm w → (μ j).symm w = (μ i).symm w)

include hwoman in
theorem stable_i (i : Fin (R + 1)) : (inst μ).IsStable (μ i) := by
  intro m w ⟨h1, h2⟩
  rw [mp_iff] at h1
  rw [wp_iff] at h2
  have hle := mkey_le_of μ (rfl : μ i m = μ i m)
  have henc : ∃ t, μ t m = w := enc_of_mkey μ (by have := i.isLt; omega)
  obtain ⟨t, ht, -, hkt⟩ := mkey_exists μ henc
  have hti : (t : ℕ) < i := by omega
  have hwt : (μ t).symm w = m := by rw [Equiv.symm_apply_eq]; exact ht.symm
  obtain ⟨s', hs', hs'min, hks'⟩ := wkey_exists μ ⟨t, hwt⟩
  obtain ⟨s, hs, -, hks⟩ := wkey_exists μ ⟨i, rfl⟩
  rw [hks', hks] at h2
  have hs'le := Fin.le_iff_val_le_val.mp (hs'min t hwt)
  have hss : (s : ℕ) < s' := by have := s'.isLt; have := s.isLt; omega
  have e := hwoman w s s' i (Fin.le_iff_val_le_val.mpr hss.le)
    (Fin.le_iff_val_le_val.mpr (by omega)) hs
  rw [hs', hs] at e
  have : μ i m = w := by rw [e]; simp
  rw [this] at h1
  exact lt_irrefl _ h1

include hwoman in
theorem manOpt0 : IsManOptimal (inst μ) (μ 0) := by
  refine ⟨stable_i μ hwoman 0, fun ν _ m => (mr_le_iff μ).mpr ?_⟩
  rw [mkey_of μ (i := 0) rfl (fun j _ => Fin.zero_le j)]
  simp

include hwoman in
theorem womanOptLast : IsWomanOptimal (inst μ) (μ (Fin.last R)) := by
  refine ⟨stable_i μ hwoman _, fun ν _ w => (wr_le_iff μ).mpr ?_⟩
  obtain ⟨s', hs', hs'min, hks'⟩ := wkey_exists μ ⟨Fin.last R, rfl⟩
  rw [hks']
  by_cases h : ∃ i, (μ i).symm w = ν.symm w
  · obtain ⟨s, hs, hsmin, hks⟩ := wkey_exists μ h
    rw [hks]
    by_contra hc
    have hlt : (s' : ℕ) < s := by have := s.isLt; have := s'.isLt; omega
    have e := hwoman w s' s (Fin.last R) (Fin.le_iff_val_le_val.mpr hlt.le) (Fin.le_last _) hs'
    rw [hs, hs'] at e
    have := Fin.le_iff_val_le_val.mp (hsmin s' (by rw [hs', e]))
    omega
  · push Not at h
    rw [wkey_not μ h]
    omega

include hwoman in
theorem man_enc_of_stable {η : Matching n} (hη : (inst μ).IsStable η) (m : Fin n) :
    ∃ i, μ i m = η m := by
  have hle := Dev.RC.le_of_womanOptimal (womanOptLast μ hwoman) hη m
  rw [mr_le_iff] at hle
  have := mkey_le_of μ (rfl : μ (Fin.last R) m = μ (Fin.last R) m)
  simp only [Fin.val_last] at this
  exact enc_of_mkey μ (by omega)

include hwoman in
theorem woman_enc_of_stable {η : Matching n} (hη : (inst μ).IsStable η) (w : Fin n) :
    ∃ i, (μ i).symm w = η.symm w := by
  have hle := Dev.RC.woman_le_of_le hη ((manOpt0 μ hwoman).2 η hη) w
  rw [wr_le_iff] at hle
  have := wkey_le μ (⟨0, rfl⟩ : ∃ i, (μ i).symm w = (μ 0).symm w)
  exact enc_of_wkey μ (by omega)

include hwoman in
theorem manPartners_iff (m w : Fin n) : w ∈ manPartners (inst μ) m ↔ ∃ i, μ i m = w := by
  rw [Dev.RC.mem_manPartners]
  constructor
  · rintro ⟨η, hη, rfl⟩
    exact man_enc_of_stable μ hwoman hη m
  · rintro ⟨i, rfl⟩
    exact ⟨μ i, stable_i μ hwoman i, rfl⟩

include hwoman in
theorem womanPartners_iff (w m : Fin n) :
    m ∈ womanPartners (inst μ) w ↔ ∃ i, (μ i).symm w = m := by
  rw [Dev.RC.mem_womanPartners]
  constructor
  · rintro ⟨η, hη, rfl⟩
    exact woman_enc_of_stable μ hwoman hη w
  · rintro ⟨i, rfl⟩
    exact ⟨μ i, stable_i μ hwoman i, rfl⟩

include hwoman in
theorem normalized : IsNormalized (inst μ) := by
  constructor
  · intro v w w' hw hw'
    rw [manPartners_iff μ hwoman] at hw hw'
    push Not at hw'
    rw [mp_iff, mkey_not μ hw']
    obtain ⟨i, -, -, hk⟩ := mkey_exists μ hw
    have := i.isLt
    omega
  · intro w v v' hv hv'
    rw [womanPartners_iff μ hwoman] at hv hv'
    push Not at hv'
    rw [wp_iff, wkey_not μ hv']
    have := wkey_le μ hv
    omega

include hman hwoman in
theorem step_covers (i : Fin R) (c : Equiv.Perm (Fin n)) (hc : c.IsCycle)
    (hcv : ∀ v, μ i.succ v = μ i.castSucc (c v)) :
    Covers (inst μ) (μ i.castSucc) (μ i.succ) := by
  have hsuc : ((i.succ : Fin (R + 1)) : ℕ) = i + 1 := Fin.val_succ i
  have hcs : ((i.castSucc : Fin (R + 1)) : ℕ) = i := Fin.val_castSucc i
  have hiR : (i : ℕ) + 1 ≤ R := i.isLt
  -- anything before `i.succ` is at most `i.castSucc`
  have hbefore : ∀ j : Fin (R + 1), ¬ i.succ ≤ j → j ≤ i.castSucc := by
    intro j hj
    rw [Fin.le_iff_val_le_val] at hj ⊢
    omega
  refine Dev.RC.covers_of_spec (fun v => c v ≠ v) (stable_i μ hwoman _) ?_ ?_ ?_ ?_
  · intro v hv
    have hne : μ i.castSucc v ≠ μ i.succ v := by
      rw [hcv]; exact fun h => hv ((μ i.castSucc).injective h).symm
    rw [Dev.RC.sMu_eq_some_iff]
    -- first time of `v` with his new partner is `i + 1`
    have hk1 : mkey μ v (μ i.succ v) = i + 1 := by
      rw [mkey_of μ (i := i.succ) rfl, hsuc]
      intro j hj
      by_contra hcon
      have := hman v j i.castSucc i.succ (hbefore j hcon) (Fin.castSucc_le_succ i) hj
      rw [hj] at this
      exact hne this
    have hk0 := mkey_le_of μ (rfl : μ i.castSucc v = μ i.castSucc v)
    rw [hcs] at hk0
    -- the woman's side
    have hsym1 : (μ i.succ).symm (μ i.succ v) = v := by simp
    have hsym0 : (μ i.castSucc).symm (μ i.succ v) = c v := by rw [hcv]; simp
    have hw1 : wkey μ (μ i.succ v) v = R - (i + 1) := by
      rw [wkey_of μ (i := i.succ) hsym1, hsuc]
      intro j hj
      by_contra hcon
      have := hwoman (μ i.succ v) j i.castSucc i.succ (hbefore j hcon) (Fin.castSucc_le_succ i)
        (by rw [hj, hsym1])
      rw [hj, hsym0] at this
      exact hv this
    obtain ⟨s, -, hsmin, hks⟩ := wkey_exists μ ⟨i.castSucc, hsym0⟩
    have hsle := Fin.le_iff_val_le_val.mp (hsmin _ hsym0)
    rw [hcs] at hsle
    refine ⟨Dev.RC.mem_sCandidates.mpr ⟨(mp_iff μ).mpr (by omega),
      (wp_iff μ).mpr (by rw [hw1, hsym0, hks]; omega)⟩, fun w hw => ?_⟩
    obtain ⟨hw1', -⟩ := Dev.RC.mem_sCandidates.mp hw
    rw [mp_iff] at hw1'
    rw [mr_le_iff, hk1]
    by_contra hlt
    push Not at hlt
    obtain ⟨s, hs, -, hks⟩ := mkey_exists μ (enc_of_mkey μ (show mkey μ v w ≤ R by omega))
    obtain ⟨t0, ht0, -, hkt0⟩ := mkey_exists μ ⟨i.castSucc, rfl⟩
    rw [hks, hkt0] at hw1'
    have e := hman v t0 s i.castSucc (Fin.le_iff_val_le_val.mpr hw1'.le)
      (Fin.le_iff_val_le_val.mpr (by omega)) ht0
    rw [hs, ht0] at e
    rw [e, hkt0] at hks
    omega
  · intro v hv
    push Not at hv
    rw [hcv, hv]
  · obtain ⟨x, hx, -⟩ := hc
    exact ⟨x, hx⟩
  · intro x y hx hy
    have hn : Dev.RC.nxt (μ i.castSucc) (μ i.succ) = c := by
      funext v; simp [Dev.RC.nxt, hcv]
    obtain ⟨k, hk⟩ := (hc.sameCycle hx hy).exists_nat_pow_eq
    exact ⟨k, by rw [hn, Equiv.Perm.iterate_eq_pow]; exact hk⟩

end

end Dev.L24

open Dev.L24 in
theorem chk_lemma_2_4 {n R : ℕ} (μ : Fin (R + 1) → Matching n)
    (hcycle : ∀ i : Fin R, ∃ c : Equiv.Perm (Fin n), c.IsCycle ∧
      ∀ v, μ i.succ v = μ i.castSucc (c v))
    (hman : ∀ (v : Fin n) (i j k : Fin (R + 1)), i ≤ j → j ≤ k → μ i v = μ k v → μ j v = μ i v)
    (hwoman : ∀ (w : Fin n) (i j k : Fin (R + 1)), i ≤ j → j ≤ k →
      (μ i).symm w = (μ k).symm w → (μ j).symm w = (μ i).symm w) :
    ∃ I : Instance n, IsNormalized I ∧ IsMaximalChain I μ ∧
      (∀ i : Fin R, ∃ ρ, IsExposed I (μ i.castSucc) ρ ∧ IsElim (μ i.castSucc) ρ (μ i.succ)) ∧
      ∀ m w, w ∈ manPartners I m ↔ ∃ i, μ i m = w := by
  have hcov : ∀ i : Fin R, Covers (inst μ) (μ i.castSucc) (μ i.succ) := by
    intro i
    obtain ⟨c, hc, hcv⟩ := hcycle i
    exact step_covers μ hman hwoman i c hc hcv
  exact ⟨inst μ, normalized μ hwoman, ⟨manOpt0 μ hwoman, womanOptLast μ hwoman, hcov⟩,
    fun i => Dev.RC.exists_rot_of_covers (hcov i), manPartners_iff μ hwoman⟩

end StableCount
end

theorem solution : type_of% @StableCount.chk_lemma_2_4 := @StableCount.chk_lemma_2_4
