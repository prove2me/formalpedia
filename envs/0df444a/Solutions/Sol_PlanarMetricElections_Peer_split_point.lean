-- Prove2me | solution 1 for PlanarMetricElections.Peer.split_point
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:19:06.033194+00:00
-- url     : https://prove2.me/submissions/66310d4c-f07c-4539-bdb1-8cb5e94e3272

import Mathlib
import Definitions.Def_PlanarMetricElections_Peer_Mass

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev.SplitPoint
open PlanarMetricElections.Peer

/-- the `p` largest elements of `X` for an injective key -/
theorem top_set {α : Type*} [LinearOrder α] (X : Finset Plane) (key : Plane → α)
    (hkey : Function.Injective key) (p : ℕ) (hp : p ≤ X.card) :
    ∃ T ⊆ X, T.card = p ∧ ∀ z ∈ T, ∀ y ∈ X, key z < key y → y ∈ T := by
  let r : Plane → ℕ := fun x => (X.filter (fun y => key x < key y)).card
  have hr_lt : ∀ x ∈ X, r x < X.card := by
    intro x hx
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have := h hx
    simp at this
  have hr_strict : ∀ x ∈ X, ∀ x' ∈ X, key x < key x' → r x' < r x := by
    intro x hx x' hx' hlt
    apply Finset.card_lt_card
    refine ⟨?_, fun h => ?_⟩
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, lt_trans hlt hy.2⟩
    · have := h (show x' ∈ X.filter (fun y => key x < key y) by simp [hx', hlt])
      simp at this
  have hinj : Set.InjOn r X := by
    intro x hx x' hx' h
    by_contra hne
    rcases lt_trichotomy (key x) (key x') with h1 | h1 | h1
    · have := hr_strict x hx x' hx' h1; omega
    · exact hne (hkey h1)
    · have := hr_strict x' hx' x hx h1; omega
  have himg : X.image r = Finset.range X.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro n hn
      simp only [Finset.mem_image] at hn
      obtain ⟨x, hx, rfl⟩ := hn
      simpa using hr_lt x hx
    · rw [Finset.card_image_of_injOn hinj]; simp
  refine ⟨X.filter (fun x => r x < p), Finset.filter_subset _ _, ?_, ?_⟩
  · have : (X.filter (fun x => r x < p)).image r = Finset.range p := by
      ext n
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
      · intro hn
        have : n ∈ X.image r := by rw [himg]; simp; omega
        simp only [Finset.mem_image] at this
        obtain ⟨x, hx, rfl⟩ := this
        exact ⟨x, ⟨hx, hn⟩, rfl⟩
    rw [← Finset.card_image_of_injOn (f := r) (hinj.mono (by intro x hx; exact (Finset.mem_filter.1 hx).1)), this]
    simp
  · intro z hz y hy hlt
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hy, lt_of_lt_of_le (hr_strict z hz.1 y hy hlt) hz.2.le⟩

theorem mass_inter_filter (V X : Finset Plane) (hXV : X ⊆ V) (P : Plane → Prop) :
    mass V ((↑X : Set Plane) ∩ {v | P v}) = ((X.filter P).card : ℝ) / (V.card : ℝ) := by
  unfold mass
  congr 2
  apply congrArg
  ext v
  simp only [Finset.mem_filter, Set.mem_inter_iff, Finset.mem_coe, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨hXV h1, h1, h2⟩

theorem mass_self (V X : Finset Plane) (hXV : X ⊆ V) :
    mass V (↑X : Set Plane) = (X.card : ℝ) / (V.card : ℝ) := by
  have := mass_inter_filter V X hXV (fun _ => True)
  simpa using this

theorem main (V X : Finset Plane)
    (hXV : X ⊆ V) (hX : X.Nonempty) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ mass V (↑X : Set Plane)) :
    ∃ z ∈ X,
      mass V ((↑X : Set Plane) ∩ {v | z.1 < v.1}) ≤ mass V (↑X : Set Plane) - a ∧
      mass V ((↑X : Set Plane) ∩ {v | v.2 < z.2}) ≤ mass V (↑X : Set Plane) - b := by
  have hm : 0 < X.card := Finset.card_pos.2 hX
  have hN : (0 : ℝ) < V.card := by
    exact_mod_cast lt_of_lt_of_le hm (Finset.card_le_card hXV)
  rw [mass_self V X hXV] at hab ⊢
  set N : ℝ := (V.card : ℝ) with hNdef
  set m : ℕ := X.card with hmdef
  have hab' : a * N + b * N ≤ m := by
    have := (le_div_iff₀ hN).1 hab
    linarith
  set α : ℝ := a * N with hα
  set β : ℝ := b * N with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  set c : ℕ := max 1 ⌈α⌉₊ with hc
  have hαm : ⌈α⌉₊ ≤ m := by
    rw [Nat.ceil_le]; linarith
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcm : c ≤ m := max_le hm hαm
  have hαc : α ≤ c := le_trans (Nat.le_ceil α) (by exact_mod_cast le_max_right _ _)
  have hcβ : (c : ℝ) - 1 ≤ m - β := by
    rcases max_choice 1 ⌈α⌉₊ with h | h
    · have : (c : ℝ) = 1 := by rw [hc, h]; simp
      rw [this]; linarith
    · have : (c : ℝ) = ⌈α⌉₊ := by rw [hc, h]
      have h2 := Nat.ceil_lt_add_one hα0
      rw [this]; linarith
  obtain ⟨TE, hTE, hTEc, hTEup⟩ := top_set X (fun x : Plane => toLex (x.1, x.2))
    (by intro x y h; simpa [Prod.ext_iff] using h) (m + 1 - c) (by omega)
  obtain ⟨TS, hTS, hTSc, hTSup⟩ := top_set X (fun x : Plane => toLex (-x.2, -x.1))
    (by intro x y h; simp [Prod.ext_iff] at h; exact Prod.ext h.2 h.1) c hcm
  have hne : (TE ∩ TS).Nonempty := by
    apply Finset.inter_nonempty_of_card_lt_card_add_card hTE hTS
    omega
  obtain ⟨z, hz⟩ := hne
  rw [Finset.mem_inter] at hz
  refine ⟨z, hTE hz.1, ?_, ?_⟩
  · rw [mass_inter_filter V X hXV]
    have hsub : X.filter (fun v => z.1 < v.1) ⊆ TE.erase z := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      rw [Finset.mem_erase]
      refine ⟨?_, hTEup z hz.1 y hy.1 ?_⟩
      · rintro rfl; exact lt_irrefl _ hy.2
      · rw [Prod.Lex.lt_iff]; left; exact hy.2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hz.1, hTEc] at h1
    rw [div_sub' hN.ne', div_le_div_iff_of_pos_right hN]
    have : ((X.filter (fun v => z.1 < v.1)).card : ℝ) ≤ ((m + 1 - c - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub (by omega)] at this
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    nlinarith
  · rw [mass_inter_filter V X hXV]
    have hsub : X.filter (fun v => v.2 < z.2) ⊆ TS.erase z := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      rw [Finset.mem_erase]
      refine ⟨?_, hTSup z hz.2 y hy.1 ?_⟩
      · rintro rfl; exact lt_irrefl _ hy.2
      · rw [Prod.Lex.lt_iff]; left; simpa using hy.2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hz.2, hTSc] at h1
    rw [div_sub' hN.ne', div_le_div_iff_of_pos_right hN]
    have : ((X.filter (fun v => v.2 < z.2)).card : ℝ) ≤ ((c - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    nlinarith

end PlanarMetricElections.Peer.Dev.SplitPoint

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev.SplitPoint in
theorem chk_split_point (V X : Finset Plane)
    (hXV : X ⊆ V) (hX : X.Nonempty) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ mass V (↑X : Set Plane)) :
    ∃ z ∈ X,
      mass V ((↑X : Set Plane) ∩ {v | z.1 < v.1}) ≤ mass V (↑X : Set Plane) - a ∧
      mass V ((↑X : Set Plane) ∩ {v | v.2 < z.2}) ≤ mass V (↑X : Set Plane) - b :=
  main V X hXV hX a b ha hb hab

end PlanarMetricElections.Peer
end
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_split_point := @PlanarMetricElections.Peer.chk_split_point
