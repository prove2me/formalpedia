-- Prove2me | solution 1 for ShannonColouring.exists_properOn_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:40:08.063184+00:00
-- url     : https://prove2.me/submissions/8e688cac-1d4a-4fa1-8ff5-a2e6cd2cf50c

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
public import Theorems.Thm_ShannonColouring_card_misses_ge
public import Theorems.Thm_ShannonColouring_card_misses_ge_of_incident
public import Theorems.Thm_ShannonColouring_Misses_kempeSwap_of_mem
public import Theorems.Thm_ShannonColouring_Misses_kempeSwap_of_notMem
public import Theorems.Thm_ShannonColouring_ProperOn_extend
public import Theorems.Thm_ShannonColouring_ProperOn_recolour_extend
public import Theorems.Thm_ShannonColouring_kempeClosed_reachable
public import Theorems.Thm_ShannonColouring_kempeGraph_degree_le
public import Theorems.Thm_ShannonColouring_not_three_ends_in_component


set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
namespace ShannonColouring
theorem _root_.solution [Fintype V] {k Δ : ℕ} {ends : ι → V × V}
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ Δ) (hk : 3 * Δ ≤ 2 * k + 1)
    {s : Finset ι} {e : ι} (he : e ∉ s) {c : ι → Fin k} (hc : ProperOn ends s c) :
    ∃ c' : ι → Fin k, ProperOn ends (insert e s) c' := by
  set u := (ends e).1 with hu_def
  set v := (ends e).2 with hv_def
  have huv : u ≠ v := hloop e
  have hAu := card_misses_ge_of_incident hΔ he c (x := u) (Or.inl rfl)
  have hAv := card_misses_ge_of_incident hΔ he c (x := v) (Or.inr rfl)
  -- Step 1: a common missing colour.
  by_cases h1 : ∃ δ, Misses ends s c u δ ∧ Misses ends s c v δ
  · obtain ⟨δ, h1u, h1v⟩ := h1
    exact ⟨_, hc.extend he h1u h1v⟩
  push_neg at h1
  -- choose `β ∈ M(v)` and the `β`-edge `f` at `u`
  obtain ⟨β, hβ⟩ : (Finset.univ.filter (Misses ends s c v)).Nonempty := by
    rw [← Finset.card_pos]
    convert (show 0 < _ by omega : 0 < (Finset.univ.filter (Misses ends s c v)).card)
  have hβv : Misses ends s c v β := by simpa using hβ
  have hβu : ¬ Misses ends s c u β := fun h => h1 β h hβv
  simp only [Misses, not_forall, not_not] at hβu
  obtain ⟨f, hf, hfu, hcf⟩ := hβu
  set w := if (ends f).1 = u then (ends f).2 else (ends f).1 with hw_def
  have hfends : ∀ x, Incident ends f x → x = u ∨ x = w := by
    rintro x (rfl | rfl)
    · by_cases h : (ends f).1 = u
      · exact Or.inl h
      · right; simp [w, h]
    · by_cases h : (ends f).1 = u
      · right; simp [w, h]
      · left
        rcases hfu with h' | h'
        · exact absurd h' h
        · exact h'
  have hfw : Incident ends f w := by
    by_cases h : (ends f).1 = u
    · right; simp [w, h]
    · left; simp [w, h]
  have hwu : w ≠ u := by
    intro h
    by_cases h' : (ends f).1 = u
    · exact hloop f (h'.trans (by simpa [w, h'] using h.symm))
    · simp [w, h'] at h
  have hwv : w ≠ v := by
    intro h
    exact hβv f hf (h ▸ hfw) hcf
  -- Step 2: a colour missing at `u` and `w`.
  by_cases h2 : ∃ α, Misses ends s c u α ∧ Misses ends s c w α
  · obtain ⟨α, h2u, h2w⟩ := h2
    refine hc.recolour_extend he hf hfu hcf (α := α) ?_ hβv
    intro x hx
    rcases hfends x hx with rfl | rfl
    · exact h2u
    · exact h2w
  push_neg at h2
  -- Step 3: counting gives `γ ∈ M(v) ∩ M(w)`.
  have hAw := card_misses_ge hΔ s c w
  obtain ⟨γ, hγv, hγw⟩ : ∃ γ, Misses ends s c v γ ∧ Misses ends s c w γ := by
    by_contra h3
    push_neg at h3
    have d1 : Disjoint (Finset.univ.filter (Misses ends s c u))
        (Finset.univ.filter (Misses ends s c v) ∪ Finset.univ.filter (Misses ends s c w)) := by
      rw [Finset.disjoint_union_right]
      constructor
      · rw [Finset.disjoint_filter]; exact fun δ _ h => h1 δ h
      · rw [Finset.disjoint_filter]; exact fun δ _ h => h2 δ h
    have d2 : Disjoint (Finset.univ.filter (Misses ends s c v))
        (Finset.univ.filter (Misses ends s c w)) := by
      rw [Finset.disjoint_filter]; exact fun δ _ h => h3 δ h
    have hcard := Finset.card_le_univ (Finset.univ.filter (Misses ends s c u) ∪
      (Finset.univ.filter (Misses ends s c v) ∪ Finset.univ.filter (Misses ends s c w)))
    rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2,
      Fintype.card_fin] at hcard
    omega
  -- choose `α ∈ M(u)`
  obtain ⟨α, hα⟩ : (Finset.univ.filter (Misses ends s c u)).Nonempty := by
    rw [← Finset.card_pos]
    convert (show 0 < _ by omega : 0 < (Finset.univ.filter (Misses ends s c u)).card)
  have hαu : Misses ends s c u α := by simpa using hα
  -- the Kempe graph of `α`, `γ`
  set H := kempeGraph ends s c α γ with hH
  have hdeg : ∀ x, H.degree x ≤ 2 := fun x =>
    (kempeGraph_degree_le hc x {α, γ} (fun i _ _ hci => by
      rcases hci with h | h <;> simp [h])).trans Finset.card_le_two
  have hdu : H.degree u ≤ 1 := by
    refine (kempeGraph_degree_le hc u {γ} (fun i hi hiu hci => ?_)).trans
      (Finset.card_singleton _).le
    rcases hci with h | h
    · exact absurd h (hαu i hi hiu)
    · simp [h]
  have hdv : H.degree v ≤ 1 := by
    refine (kempeGraph_degree_le hc v {α} (fun i hi hiv hci => ?_)).trans
      (Finset.card_singleton _).le
    rcases hci with h | h
    · simp [h]
    · exact absurd h (hγv i hi hiv)
  have hdw : H.degree w ≤ 1 := by
    refine (kempeGraph_degree_le hc w {α} (fun i hi hiw hci => ?_)).trans
      (Finset.card_singleton _).le
    rcases hci with h | h
    · simp [h]
    · exact absurd h (hγw i hi hiw)
  by_cases hr1 : H.Reachable v u
  · by_cases hr2 : H.Reachable v w
    · exact (not_three_ends_in_component H hdeg huv.symm hwv.symm hwu.symm hr1 hr2 hdv hdu
        hdw).elim
    · -- Kempe change at the component of `w`, then recolour `f`.
      set T : Set V := {x | H.Reachable w x}
      have hT : KempeClosed ends s c α γ T := kempeClosed_reachable hloop w
      have huT : u ∉ T := fun h => hr2 (hr1.trans h.symm)
      have hvT : v ∉ T := fun h => hr2 h.symm
      have hwT : w ∈ T := SimpleGraph.Reachable.refl w
      have hc' := hc.kempeSwap hT
      have hβα : β ≠ α := fun h => hαu f hf hfu (hcf.trans h)
      have hβγ : β ≠ γ := fun h => hγw f hf hfw (hcf.trans h)
      have hcf' : kempeSwap ends c α γ T f = β := by
        rw [kempeSwap_of_not (by rw [hcf]; tauto)]; exact hcf
      refine hc'.recolour_extend he hf hfu hcf' (α := α) ?_ (hβv.kempeSwap_of_notMem hT hvT)
      intro x hx
      rcases hfends x hx with rfl | rfl
      · exact hαu.kempeSwap_of_notMem hT huT
      · exact Misses.kempeSwap_of_mem hT hwT (by rw [Equiv.swap_apply_left]; exact hγw)
  · -- Kempe change at the component of `v`, then colour `e` with `α`.
    set T : Set V := {x | H.Reachable v x}
    have hT : KempeClosed ends s c α γ T := kempeClosed_reachable hloop v
    have hvT : v ∈ T := SimpleGraph.Reachable.refl v
    have hc' := hc.kempeSwap hT
    exact ⟨_, hc'.extend he (hαu.kempeSwap_of_notMem hT hr1)
      (Misses.kempeSwap_of_mem hT hvT (by rw [Equiv.swap_apply_left]; exact hγv))⟩
end ShannonColouring
