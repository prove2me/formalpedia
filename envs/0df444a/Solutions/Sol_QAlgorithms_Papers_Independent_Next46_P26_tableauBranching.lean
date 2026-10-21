-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P26.tableauBranching
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:43:20.325516+00:00
-- url     : https://prove2.me/submissions/98ed0bff-c8c5-4666-a3bb-c19bb25f88ed

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P26
open QAlgorithms.Papers.Independent.Dependency50.P31
open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem g61a_corner_mem {lam : YoungDiagram} {c : ℕ × ℕ} (hc : c ∈ corners lam) : c ∈ lam.cells :=
  (Finset.mem_filter.mp hc).1

theorem g61a_corner_row {lam : YoungDiagram} {c z : ℕ × ℕ} (hc : c ∈ corners lam)
    (hz : z ∈ lam.cells) (h1 : c.1 ≤ z.1) (h2 : c.2 < z.2) : False := by
  have h := (Finset.mem_filter.mp hc).2.2
  apply h
  rw [YoungDiagram.mem_cells] at hz
  refine lam.up_left_mem (i2 := z.1) (j2 := z.2) h1 ?_ (by simpa using hz)
  omega

theorem g61a_corner_col {lam : YoungDiagram} {c z : ℕ × ℕ} (hc : c ∈ corners lam)
    (hz : z ∈ lam.cells) (h1 : c.1 < z.1) (h2 : c.2 ≤ z.2) : False := by
  have h := (Finset.mem_filter.mp hc).2.1
  apply h
  rw [YoungDiagram.mem_cells] at hz
  refine lam.up_left_mem (i2 := z.1) (j2 := z.2) ?_ h2 (by simpa using hz)
  omega

/-- Removing a corner. -/
def g61a_er (lam : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ corners lam) : YoungDiagram :=
  ⟨lam.cells.erase c, by
    intro b a hab hb
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hb ⊢
    refine ⟨lam.isLowerSet hab hb.1, fun hac => ?_⟩
    subst hac
    have hne := hb.2
    obtain ⟨h1, h2⟩ := hab
    by_cases h : a.1 < b.1
    · exact g61a_corner_col hc hb.1 h h2
    · have e1 : a.1 = b.1 := by omega
      have : a.2 < b.2 := by
        rcases Nat.lt_or_eq_of_le h2 with h' | h'
        · exact h'
        · exact absurd (Prod.ext e1 h').symm hne
      exact g61a_corner_row hc hb.1 (by omega) this⟩

theorem g61a_er_cells (lam : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ corners lam) :
    (g61a_er lam c hc).cells = lam.cells.erase c := rfl

theorem g61a_fwd (lam : YoungDiagram) (n : ℕ) (c : ℕ × ℕ) (hc : c ∈ corners lam)
    (t : Fin (n + 1) → ℕ × ℕ) (ht : IsTableau lam t) (hl : t (Fin.last n) = c) :
    IsTableau (g61a_er lam c hc) (Fin.init t) := by
  obtain ⟨hinj, him, hr, hcl⟩ := ht
  refine ⟨fun a b h => Fin.castSucc_injective _ (hinj h), ?_, ?_, ?_⟩
  · ext z
    rw [g61a_er_cells, Finset.mem_erase, ← him]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.init]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨fun h => ?_, a.castSucc, rfl⟩
      rw [← hl] at h
      exact (Fin.castSucc_lt_last a).ne (hinj h)
    · rintro ⟨hne, i, rfl⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact ⟨j, rfl⟩
      · exact absurd hl hne
  · intro i j h1 h2; exact Fin.castSucc_lt_castSucc_iff.mp (hr _ _ h1 h2)
  · intro i j h1 h2; exact Fin.castSucc_lt_castSucc_iff.mp (hcl _ _ h1 h2)

theorem g61a_bwd (lam : YoungDiagram) (n : ℕ) (c : ℕ × ℕ) (hc : c ∈ corners lam)
    (s : Fin n → ℕ × ℕ) (hs : IsTableau (g61a_er lam c hc) s) :
    IsTableau lam (Fin.snoc (α := fun _ => ℕ × ℕ) s c) := by
  obtain ⟨hinj, him, hr, hcl⟩ := hs
  have hsmem : ∀ a, s a ∈ lam.cells.erase c := fun a => by
    rw [← g61a_er_cells lam c hc, ← him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hsne : ∀ a, s a ≠ c := fun a => (Finset.mem_erase.mp (hsmem a)).1
  have hsin : ∀ a, s a ∈ lam.cells := fun a => (Finset.mem_erase.mp (hsmem a)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
    · rw [hinj h]
    · exact absurd h (hsne a)
    · exact absurd h.symm (hsne b)
    · rfl
  · ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_fin_succ',
      Fin.snoc_castSucc, Fin.snoc_last]
    constructor
    · rintro (⟨a, rfl⟩ | rfl)
      · exact hsin a
      · exact g61a_corner_mem hc
    · intro hz
      by_cases hzc : z = c
      · exact Or.inr hzc.symm
      · left
        have : z ∈ (g61a_er lam c hc).cells := by
          rw [g61a_er_cells]; exact Finset.mem_erase.mpr ⟨hzc, hz⟩
        rw [← him] at this
        simpa using this
  · intro i j h1 h2
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h1 h2
    · exact Fin.castSucc_lt_castSucc_iff.mpr (hr i j h1 h2)
    · exact Fin.castSucc_lt_last i
    · exact (g61a_corner_row hc (hsin j) h1.le h2).elim
    · exact absurd h2 (lt_irrefl _)
  · intro i j h1 h2
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h1 h2
    · exact Fin.castSucc_lt_castSucc_iff.mpr (hcl i j h1 h2)
    · exact Fin.castSucc_lt_last i
    · exact (g61a_corner_col hc (hsin j) h2 h1.le).elim
    · exact absurd h2 (lt_irrefl _)

def g61a_T (mu : YoungDiagram) (n : ℕ) : ℕ :=
  Fintype.card {t : Fin n → {z : ℕ × ℕ // z ∈ mu.cells} // IsTableau mu (fun i => (t i).val)}

theorem g61a_count (mu : YoungDiagram) (n : ℕ) (h : mu.card = n) :
    tableauCount mu = g61a_T mu n := by
  subst h; rfl

theorem g61a_fiber (lam : YoungDiagram) (n : ℕ) (c : ℕ × ℕ) (hc : c ∈ corners lam) :
    ((Finset.univ : Finset (Fin (n + 1) → {z : ℕ × ℕ // z ∈ lam.cells})).filter
      (fun t => IsTableau lam (fun i => (t i).val) ∧ (t (Fin.last n)).val = c)).card =
    g61a_T (g61a_er lam c hc) n := by
  unfold g61a_T
  rw [Fintype.card_subtype]
  refine Finset.card_bij' (fun t ht => fun j => ⟨(t j.castSucc).val, ?_⟩)
    (fun s hs => fun k => ⟨Fin.snoc (α := fun _ => ℕ × ℕ) (fun i => (s i).val) c k, ?_⟩)
    ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hf := g61a_fwd lam n c hc _ ht.1 ht.2
    rw [← hf.2.1]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hb := g61a_bwd lam n c hc _ hs
    rw [← hb.2.1]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact g61a_fwd lam n c hc _ ht.1 ht.2
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨g61a_bwd lam n c hc _ hs, by simp⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    funext k
    apply Subtype.ext
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
    · simp
    · simp [ht.2]
  · intro s hs
    funext k
    apply Subtype.ext
    simp

theorem g61a_last_corner (lam : YoungDiagram) (n : ℕ) (t : Fin (n + 1) → ℕ × ℕ)
    (ht : IsTableau lam t) : t (Fin.last n) ∈ corners lam := by
  obtain ⟨hinj, him, hr, hcl⟩ := ht
  have hmem : ∀ z, z ∈ lam.cells → ∃ i, t i = z := fun z hz => by
    rw [← him] at hz; simpa using hz
  unfold corners
  rw [Finset.mem_filter]
  refine ⟨by rw [← him]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_, ?_⟩
  · intro h
    obtain ⟨i, hi⟩ := hmem _ (by simpa using h)
    have := hcl (Fin.last n) i (by rw [hi]) (by rw [hi]; simp)
    exact absurd (Fin.le_last i) (not_le.mpr this)
  · intro h
    obtain ⟨i, hi⟩ := hmem _ (by simpa using h)
    have := hr (Fin.last n) i (by rw [hi]) (by rw [hi]; simp)
    exact absurd (Fin.le_last i) (not_le.mpr this)

theorem g61a_split (lam : YoungDiagram) (n : ℕ) :
    g61a_T lam (n + 1) = ∑ x ∈ (corners lam).attach, g61a_T (g61a_er lam x.1 x.2) n := by
  unfold g61a_T
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => (t (Fin.last n)).val) (t := corners lam)
    (fun t ht => g61a_last_corner lam n _ (Finset.mem_filter.mp ht).2)]
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.filter_filter]
  exact g61a_fiber lam n x.1 x.2

theorem g61a_obp (lam : YoungDiagram) :
    ∑ x ∈ (corners lam).attach, tableauCount (g61a_er lam x.1 x.2) =
      ∑ mu ∈ oneBoxPredecessors lam, tableauCount mu := by
  refine Finset.sum_bij (fun x _ => g61a_er lam x.1 x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x _
    unfold oneBoxPredecessors
    rw [Finset.mem_image]
    refine ⟨⟨lam.cells.erase x.1, ?_⟩, Finset.mem_attach _ _, rfl⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.erase_subset _ _, ?_, (g61a_er lam x.1 x.2).isLowerSet⟩
    exact Finset.card_erase_add_one (g61a_corner_mem x.2)
  · intro x _ y _ hxy
    have h := congrArg YoungDiagram.cells hxy
    rw [g61a_er_cells, g61a_er_cells] at h
    apply Subtype.ext
    by_contra hne
    have : y.1 ∈ lam.cells.erase x.1 := Finset.mem_erase.mpr ⟨Ne.symm hne, g61a_corner_mem y.2⟩
    rw [h] at this
    simp at this
  · intro mu hmu
    unfold oneBoxPredecessors at hmu
    rw [Finset.mem_image] at hmu
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := hmu
    rw [Finset.mem_filter, Finset.mem_powerset] at ha
    obtain ⟨hsub, hcard, hlow⟩ := ha
    have hsd : (lam.cells \ a).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub]; simp only [YoungDiagram.card] at hcard; omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hsd
    have hcmem : c ∈ lam.cells \ a := by rw [hc]; simp
    rw [Finset.mem_sdiff] at hcmem
    have key : ∀ z ∈ lam.cells, z ∉ a → z = c := fun z hz hza => by
      have : z ∈ lam.cells \ a := Finset.mem_sdiff.mpr ⟨hz, hza⟩
      rw [hc] at this; simpa using this
    have hcor : c ∈ corners lam := by
      unfold corners
      rw [Finset.mem_filter]
      refine ⟨hcmem.1, fun h => ?_, fun h => ?_⟩
      · rw [← YoungDiagram.mem_cells] at h
        by_cases hza : (c.1 + 1, c.2) ∈ a
        · exact hcmem.2 (hlow (show c ≤ (c.1 + 1, c.2) from ⟨by simp, le_refl _⟩) hza)
        · have := key _ h hza
          have := congrArg Prod.fst this; simp at this
      · rw [← YoungDiagram.mem_cells] at h
        by_cases hza : (c.1, c.2 + 1) ∈ a
        · exact hcmem.2 (hlow (show c ≤ (c.1, c.2 + 1) from ⟨le_refl _, by simp⟩) hza)
        · have := key _ h hza
          have := congrArg Prod.snd this; simp at this
    refine ⟨⟨c, hcor⟩, Finset.mem_attach _ _, ?_⟩
    apply YoungDiagram.ext
    rw [g61a_er_cells]
    ext z
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hzc, hz⟩
      by_contra hza
      exact hzc (key z hz hza)
    · intro hza
      refine ⟨fun h => hcmem.2 ?_, hsub hza⟩
      rw [h] at hza; exact hza

theorem solution (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    tableauCount lam = ∑ mu ∈ oneBoxPredecessors lam, tableauCount mu := by
  obtain ⟨n, hn⟩ : ∃ n, lam.card = n + 1 := ⟨lam.card - 1, by
    have := hne.card_pos; simp only [YoungDiagram.card]; omega⟩
  rw [g61a_count lam (n + 1) hn, g61a_split, ← g61a_obp]
  refine Finset.sum_congr rfl fun x _ => (g61a_count _ n ?_).symm
  simp only [YoungDiagram.card, g61a_er_cells]
  rw [Finset.card_erase_of_mem (g61a_corner_mem x.2)]
  simp only [YoungDiagram.card] at hn; omega

end
