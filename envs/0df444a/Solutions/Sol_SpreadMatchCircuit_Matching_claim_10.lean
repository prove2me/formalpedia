-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.claim_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:37:52.951457+00:00
-- url     : https://prove2.me/submissions/b9f87ec5-2d4e-443f-aa5f-5b0eab21aa01

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Encoding

section
namespace SpreadMatchCircuit.Matching.Dev.C10

open Finset

variable {n : ℕ}

lemma mem_incident {W : Finset (Fin n)} {e : Edge n} :
    e ∈ incident W ↔ ¬ Disjoint (endpoints e) W := by
  simp [incident]

lemma mem_endpoints {e : Edge n} {v : Fin n} : v ∈ endpoints e ↔ v ∈ e.1 := by
  simp [endpoints, Sym2.mem_toFinset]

lemma endpoints_card (e : Edge n) : (endpoints e).card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _ e.2

lemma edge_eq_of_endpoints_subset {e e' : Edge n} (h : endpoints e ⊆ endpoints e') : e = e' := by
  have h2 : endpoints e = endpoints e' :=
    Finset.eq_of_subset_of_card_le h (by rw [endpoints_card, endpoints_card])
  apply Subtype.ext
  apply Sym2.ext
  intro x
  have := Finset.ext_iff.mp h2 x
  simpa [mem_endpoints] using this

lemma endpoints_nonempty (e : Edge n) : (endpoints e).Nonempty := by
  rw [← Finset.card_pos, endpoints_card]; norm_num

lemma firstOf_mem {α : Type} (ord : LinearOrder α) (F : Finset α) (d : α) (h : F.Nonempty) :
    firstOf ord F d ∈ F := by
  unfold firstOf
  rw [dif_pos h]
  exact @Finset.min'_mem α ord F h

/-- properties of `chooseMu`. -/
lemma chooseMu_spec (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (prev : Finset (Edge n) → Finset (Edge n)) (Gℓ : Finset (Edge n)) (b : ℕ)
    (z : Finset (Edge n)) (hz : z ∈ 𝒵) (hb : (prev z).card ≤ b) :
    chooseMu ord 𝒵 prev Gℓ b z ∈ 𝒵 ∧ prev (chooseMu ord 𝒵 prev Gℓ b z) ⊆ Gℓ ∪ prev z ∧
      (prev (chooseMu ord 𝒵 prev Gℓ b z)).card ≤ b ∧
      ∀ u ∈ 𝒵, prev u ⊆ Gℓ ∪ prev z → (prev u).card ≤ b →
        (prev (chooseMu ord 𝒵 prev Gℓ b z) \ Gℓ).card ≤ (prev u \ Gℓ).card := by
  set F := 𝒵.filter fun u => prev u ⊆ Gℓ ∪ prev z ∧ (prev u).card ≤ b with hF
  have hzF : z ∈ F := by
    rw [hF, Finset.mem_filter]; exact ⟨hz, Finset.subset_union_right, hb⟩
  have hFne : F.Nonempty := ⟨z, hzF⟩
  set F' := F.filter fun u => ∀ v ∈ F, (prev u \ Gℓ).card ≤ (prev v \ Gℓ).card with hF'
  have hF'ne : F'.Nonempty := by
    obtain ⟨u, huF, hu⟩ := Finset.exists_min_image F (fun u => (prev u \ Gℓ).card) hFne
    exact ⟨u, by rw [hF', Finset.mem_filter]; exact ⟨huF, hu⟩⟩
  have hmem : chooseMu ord 𝒵 prev Gℓ b z ∈ F' := firstOf_mem ord F' z hF'ne
  have hmemF : chooseMu ord 𝒵 prev Gℓ b z ∈ F := (Finset.mem_filter.mp hmem).1
  have h1 := Finset.mem_filter.mp hmemF
  refine ⟨h1.1, h1.2.1, h1.2.2, ?_⟩
  intro u hu h1u h2u
  exact (Finset.mem_filter.mp hmem).2 u (by rw [hF, Finset.mem_filter]; exact ⟨hu, h1u, h2u⟩)


lemma flatWbar_succ (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (m : ℕ) :
    flatWbar t ε W (m + 1) = flatWbar t ε W m ∪ flatW t ε W (m + 1) := by
  unfold flatWbar
  have : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [this, Finset.biUnion_insert, Finset.union_comm]

theorem main (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n)))
    (t ε : ℝ) (W : ℕ → ℕ → Finset (Fin n)) (m : ℕ) (z : Finset (Edge n)) (hz : z ∈ 𝒵)
    (a : ℕ) (S : Finset (Fin n)) (f : Fin n → Fin a)
    (hE : EventE ord 𝒵 t ε W (m + 1) a z)
    (hD : IsConsistent ord 𝒵 t ε W (m + 1) z S f) :
    residual ord 𝒵 t ε W (m + 1) z ⊆
      residual ord 𝒵 t ε W m
        (decode ord 𝒵 t ε W (m + 1)
          (flatW t ε W (m + 1) ∪ verts (residual ord 𝒵 t ε W (m + 1) z)) S f) := by
  set ℓ := m + 1 with hℓ
  have hsub : ℓ - 1 = m := by omega
  set prev := residual ord 𝒵 t ε W m with hprev
  set Gℓ := incident (flatWbar t ε W ℓ) with hG
  set b := stageBudget t ε ℓ with hb
  have hzb : (prev z).card ≤ b := by
    have := hE.2.2.1; rwa [hsub] at this
  have hres : residual ord 𝒵 t ε W ℓ z = prev (chooseMu ord 𝒵 prev Gℓ b z) \ Gℓ := rfl
  have hmu : stageMu ord 𝒵 t ε W ℓ z = chooseMu ord 𝒵 prev Gℓ b z := by
    simp only [stageMu, hsub]; rfl
  obtain ⟨hμ𝒵, hμsub, hμb, hmin⟩ := chooseMu_spec ord 𝒵 prev Gℓ b z hz hzb
  set μ := chooseMu ord 𝒵 prev Gℓ b z with hμdef
  set π := residual ord 𝒵 t ε W ℓ z with hπ
  have hπμ : π = prev μ \ Gℓ := hres
  set T := flatW t ε W ℓ ∪ verts π with hT
  have hπprev : π ⊆ prev z := by
    intro e he
    rw [hπμ, Finset.mem_sdiff] at he
    rcases Finset.mem_union.mp (hμsub he.1) with h | h
    · exact absurd h he.2
    · exact h
  have hD1 : ∀ e ∈ prev μ,
      (endpoints e ⊆ S ∧ e ∈ π ∧ ∀ u ∈ endpoints e, ∀ v ∈ endpoints e, f u = f v) ∨
      (Disjoint (endpoints e) S ∧ e ∉ π) := by
    have := hD.1
    rw [hmu, hsub] at this
    exact this
  have hD2 := hD.2
  have hWbar : flatWbar t ε W (ℓ - 1) ∪ T = flatWbar t ε W ℓ ∪ verts π := by
    rw [hsub, hT, hℓ, flatWbar_succ]
    ext x; simp only [Finset.mem_union]; tauto
  have hWsub : flatWbar t ε W (ℓ - 1) ∪ flatW t ε W ℓ = flatWbar t ε W ℓ := by
    rw [hsub, hℓ, flatWbar_succ]
  -- μ satisfies the decoder's condition
  have hμC : μ ∈ 𝒵.filter fun u =>
      (residual ord 𝒵 t ε W (ℓ - 1) u).card ≤ stageBudget t ε ℓ ∧
      residual ord 𝒵 t ε W (ℓ - 1) u ⊆ incident (flatWbar t ε W (ℓ - 1) ∪ T) ∧
      ∀ e ∈ residual ord 𝒵 t ε W (ℓ - 1) u,
        (endpoints e ⊆ S ∧ (∀ v ∈ endpoints e, ∀ w ∈ endpoints e, f v = f w) ∧ endpoints e ⊆ T) ∨
        Disjoint (endpoints e) S := by
    rw [Finset.mem_filter]
    refine ⟨hμ𝒵, ?_⟩
    rw [hsub]
    refine ⟨hμb, ?_, ?_⟩
    · intro e he
      by_cases hGe : e ∈ Gℓ
      · rw [mem_incident] at hGe ⊢
        intro hd
        apply hGe
        rw [← hWsub] at *
        refine Finset.disjoint_of_subset_right ?_ hd
        intro x hx
        rw [hG, ← hWsub] at *
        simp only [Finset.mem_union] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_union_left _ h)
      · have heπ : e ∈ π := by rw [hπμ, Finset.mem_sdiff]; exact ⟨he, hGe⟩
        rw [mem_incident, Finset.not_disjoint_iff]
        obtain ⟨v, hv⟩ := endpoints_nonempty e
        exact ⟨v, hv, Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨e, heπ, hv⟩))⟩
    · intro e he
      rcases hD1 e he with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨h1, fun v hv w hw => h3 v hv w hw, ?_⟩
        intro x hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, h2, hx⟩)
      · exact Or.inr h1
  -- z' is the decoded matching
  have hne : (𝒵.filter fun u =>
      (residual ord 𝒵 t ε W (ℓ - 1) u).card ≤ stageBudget t ε ℓ ∧
      residual ord 𝒵 t ε W (ℓ - 1) u ⊆ incident (flatWbar t ε W (ℓ - 1) ∪ T) ∧
      ∀ e ∈ residual ord 𝒵 t ε W (ℓ - 1) u,
        (endpoints e ⊆ S ∧ (∀ v ∈ endpoints e, ∀ w ∈ endpoints e, f v = f w) ∧ endpoints e ⊆ T) ∨
        Disjoint (endpoints e) S).Nonempty := ⟨μ, hμC⟩
  have hz'mem := Finset.mem_filter.mp (firstOf_mem ord _ ∅ hne)
  have hdec : decode ord 𝒵 t ε W ℓ T S f = firstOf ord (𝒵.filter fun u =>
      (residual ord 𝒵 t ε W (ℓ - 1) u).card ≤ stageBudget t ε ℓ ∧
      residual ord 𝒵 t ε W (ℓ - 1) u ⊆ incident (flatWbar t ε W (ℓ - 1) ∪ T) ∧
      ∀ e ∈ residual ord 𝒵 t ε W (ℓ - 1) u,
        (endpoints e ⊆ S ∧ (∀ v ∈ endpoints e, ∀ w ∈ endpoints e, f v = f w) ∧ endpoints e ⊆ T) ∨
        Disjoint (endpoints e) S) ∅ := rfl
  rw [← hdec] at hz'mem
  set z' := decode ord 𝒵 t ε W ℓ T S f with hz'
  have hz'𝒵 : z' ∈ 𝒵 := hz'mem.1
  have hz'b : (prev z').card ≤ b := hz'mem.2.1
  have hz'inc : prev z' ⊆ incident (flatWbar t ε W (ℓ - 1) ∪ T) := hz'mem.2.2.1
  have hz'C : ∀ e ∈ prev z',
        (endpoints e ⊆ S ∧ (∀ v ∈ endpoints e, ∀ w ∈ endpoints e, f v = f w) ∧ endpoints e ⊆ T) ∨
        Disjoint (endpoints e) S := hz'mem.2.2.2
  -- vertices of π lie in S
  have hVS : ∀ u ∈ verts π, u ∈ S := by
    intro u hu
    obtain ⟨e', he', hue⟩ := Finset.mem_biUnion.mp hu
    have he'prev : e' ∈ prev μ := by
      have := he'; rw [hπμ, Finset.mem_sdiff] at this; exact this.1
    rcases hD1 e' he'prev with ⟨h1, _, _⟩ | ⟨_, h2⟩
    · exact h1 hue
    · exact absurd he' h2
  have hflat : flatW t ε W ℓ ⊆ flatWbar t ε W ℓ := by
    rw [← hWsub]; exact Finset.subset_union_right
  -- prev z' ⊆ Gℓ ∪ π
  have hz'sub : prev z' ⊆ Gℓ ∪ π := by
    intro e he
    by_cases hGe : e ∈ Gℓ
    · exact Finset.mem_union_left _ hGe
    · apply Finset.mem_union_right
      have hinc := hz'inc he
      rw [mem_incident, Finset.not_disjoint_iff] at hinc
      obtain ⟨u, hu1, hu2⟩ := hinc
      have hGe' : Disjoint (endpoints e) (flatWbar t ε W ℓ) := by
        by_contra hc; exact hGe (mem_incident.mpr hc)
      have huπ : u ∈ verts π := by
        rw [hWbar] at hu2
        rcases Finset.mem_union.mp hu2 with h | h
        · exact absurd h (Finset.disjoint_left.mp hGe' hu1)
        · exact h
      have huS := hVS u huπ
      rcases hz'C e he with ⟨h1, h2, h3⟩ | h
      · have hev : ∀ v ∈ endpoints e, v ∈ verts π := by
          intro v hv
          rcases Finset.mem_union.mp (h3 hv) with h | h
          · exact absurd (hflat h) (Finset.disjoint_left.mp hGe' hv)
          · exact h
        obtain ⟨e', he'π, hue'⟩ := Finset.mem_biUnion.mp huπ
        have : endpoints e ⊆ endpoints e' := by
          intro v hv
          obtain ⟨e'', he''π, hve''⟩ := Finset.mem_biUnion.mp (hev v hv)
          by_cases hee : e' = e''
          · rw [hee]; exact hve''
          · exact absurd (h2 u hu1 v hv) (hD2 e' he'π e'' he''π hee u hue' v hve'')
        rw [edge_eq_of_endpoints_subset this]; exact he'π
      · exact absurd huS (Finset.disjoint_left.mp h hu1)
  -- π ⊆ prev z'
  intro e heπ
  by_contra hcon
  have hsubset : prev z' \ Gℓ ⊆ π.erase e := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · rintro rfl; exact hcon hx.1
    · rcases Finset.mem_union.mp (hz'sub hx.1) with h | h
      · exact absurd h hx.2
      · exact h
  have hlt : (prev z' \ Gℓ).card < π.card :=
    lt_of_le_of_lt (Finset.card_le_card hsubset) (Finset.card_erase_lt_of_mem heπ)
  have hz'sub2 : prev z' ⊆ Gℓ ∪ prev z := fun x hx => by
    rcases Finset.mem_union.mp (hz'sub hx) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hπprev h)
  have := hmin z' hz'𝒵 hz'sub2 hz'b
  rw [← hπμ] at this
  omega

end SpreadMatchCircuit.Matching.Dev.C10

namespace SpreadMatchCircuit.Matching

theorem chk_claim_10 {n : ℕ} (ord : LinearOrder (Finset (Edge n))) (μ : PMF (Finset (Edge n)))
    (t ε γ : ℝ) (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (hμ : IsBoundedMatchingLaw μ t)
    (W : ℕ → ℕ → Finset (Fin n)) (hW : IsStageFamily t ε γ W)
    (ℓ : ℕ) (hℓ₁ : 1 ≤ ℓ) (hℓ₂ : ℓ ≤ numStages t ε)
    (z : Finset (Edge n)) (hz : z ∈ lawSupport μ)
    (a : ℕ) (S : Finset (Fin n)) (f : Fin n → Fin a)
    (hE : EventE ord (lawSupport μ) t ε W ℓ a z)
    (hD : IsConsistent ord (lawSupport μ) t ε W ℓ z S f) :
    residual ord (lawSupport μ) t ε W ℓ z ⊆
      residual ord (lawSupport μ) t ε W (ℓ - 1)
        (decode ord (lawSupport μ) t ε W ℓ
          (flatW t ε W ℓ ∪ verts (residual ord (lawSupport μ) t ε W ℓ z)) S f) := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  simpa using Dev.C10.main ord (lawSupport μ) t ε W m z hz a S f hE hD

end SpreadMatchCircuit.Matching
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.chk_claim_10 := @SpreadMatchCircuit.Matching.chk_claim_10
