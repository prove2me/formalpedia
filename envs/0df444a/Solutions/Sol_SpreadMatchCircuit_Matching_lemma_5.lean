-- Prove2me | solution 1 for SpreadMatchCircuit.Matching.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:46:37.680521+00:00
-- url     : https://prove2.me/submissions/89f4cf97-be1c-49ca-9fef-e77fd8875e9e

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

end SpreadMatchCircuit.Matching
end

section
namespace SpreadMatchCircuit.Matching.Dev.Eq3

open Finset

variable {n : ℕ}

section Basic
variable (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n))) (t ε : ℝ)

lemma chooseMu_cases (prev : Finset (Edge n) → Finset (Edge n)) (G : Finset (Edge n)) (b : ℕ)
    (z : Finset (Edge n)) :
    (chooseMu ord 𝒵 prev G b z ∈ 𝒵 ∧ prev (chooseMu ord 𝒵 prev G b z) ⊆ G ∪ prev z) ∨
      chooseMu ord 𝒵 prev G b z = z := by
  unfold chooseMu firstOf
  dsimp only
  split_ifs with h
  · left
    have h' := @Finset.min'_mem _ ord _ h
    rw [mem_filter, mem_filter] at h'
    exact ⟨h'.1.1, h'.1.2.1⟩
  · right; rfl

lemma residual_succ_subset (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ) (z : Finset (Edge n)) :
    residual ord 𝒵 t ε W (ℓ + 1) z ⊆ residual ord 𝒵 t ε W ℓ z := by
  simp only [residual]
  rcases chooseMu_cases ord 𝒵 (residual ord 𝒵 t ε W ℓ) (incident (flatWbar t ε W (ℓ + 1)))
    (stageBudget t ε (ℓ + 1)) z with h | h
  · intro e he
    rw [mem_sdiff] at he
    rcases mem_union.1 (h.2 he.1) with h' | h'
    · exact absurd h' he.2
    · exact h'
  · rw [h]; exact sdiff_subset

lemma residual_anti (W : ℕ → ℕ → Finset (Fin n)) (z : Finset (Edge n)) {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') :
    residual ord 𝒵 t ε W ℓ' z ⊆ residual ord 𝒵 t ε W ℓ z := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (residual_succ_subset ord 𝒵 t ε W _ z).trans ih

lemma residual_subset (W : ℕ → ℕ → Finset (Fin n)) (j : ℕ) (z : Finset (Edge n)) :
    residual ord 𝒵 t ε W j z ⊆ z :=
  residual_anti ord 𝒵 t ε W z (Nat.zero_le j)

lemma residual_empty (W : ℕ → ℕ → Finset (Fin n)) (j : ℕ) :
    residual ord 𝒵 t ε W j ∅ = ∅ :=
  subset_empty.1 (residual_subset ord 𝒵 t ε W j ∅)

lemma residual_congr (W W' : ℕ → ℕ → Finset (Fin n)) (k : ℕ)
    (h : ∀ ℓ' ∈ Icc 1 k, flatW t ε W ℓ' = flatW t ε W' ℓ') :
    ∀ ℓ ≤ k, residual ord 𝒵 t ε W ℓ = residual ord 𝒵 t ε W' ℓ := by
  have hbar : ∀ ℓ ≤ k, flatWbar t ε W ℓ = flatWbar t ε W' ℓ := by
    intro ℓ hℓ
    unfold flatWbar
    apply biUnion_congr rfl
    intro x hx
    exact h x (by simp at hx ⊢; omega)
  intro ℓ hℓ
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    funext z
    simp only [residual]
    rw [ih (by omega), hbar (ℓ + 1) hℓ]

lemma flatWbar_congr (W W' : ℕ → ℕ → Finset (Fin n)) (k : ℕ)
    (h : ∀ ℓ' ∈ Icc 1 k, flatW t ε W ℓ' = flatW t ε W' ℓ') :
    flatWbar t ε W k = flatWbar t ε W' k := by
  unfold flatWbar
  exact biUnion_congr rfl (fun x hx => h x hx)

lemma decode_congr (W W' : ℕ → ℕ → Finset (Fin n)) (k : ℕ)
    (h : ∀ ℓ' ∈ Icc 1 k, flatW t ε W ℓ' = flatW t ε W' ℓ')
    (T : Finset (Fin n)) {a : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin a) :
    decode ord 𝒵 t ε W (k + 1) T S f = decode ord 𝒵 t ε W' (k + 1) T S f := by
  unfold decode
  simp only [Nat.add_sub_cancel, residual_congr ord 𝒵 t ε W W' k h k le_rfl,
    flatWbar_congr t ε W W' k h]

lemma decode_card (W : ℕ → ℕ → Finset (Fin n)) (k : ℕ)
    (T : Finset (Fin n)) {a : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin a) :
    (residual ord 𝒵 t ε W k (decode ord 𝒵 t ε W (k + 1) T S f)).card ≤
      stageBudget t ε (k + 1) := by
  unfold decode firstOf
  split_ifs with h
  · have h' := @Finset.min'_mem _ ord _ h
    rw [mem_filter] at h'
    simpa using h'.2.1
  · rw [residual_empty]; simp

end Basic

section Graph

lemma isMatching_mono {m m' : Finset (Edge n)} (h : m ⊆ m') (hm : IsMatching m') :
    IsMatching m := fun e he e' he' hne => hm e (h he) e' (h he') hne

lemma card_verts_le (m : Finset (Edge n)) : (verts m).card ≤ 2 * m.card := by
  unfold verts
  calc _ ≤ ∑ e ∈ m, (endpoints e).card := card_biUnion_le
    _ = 2 * m.card := by simp [C10.endpoints_card, mul_comm]

lemma card_verts_of_matching {m : Finset (Edge n)} (hm : IsMatching m) :
    (verts m).card = 2 * m.card := by
  unfold verts
  rw [card_biUnion (fun e he e' he' hne => hm e he e' he' hne)]
  simp [C10.endpoints_card, mul_comm]

end Graph

section Prob
variable {α : Type} [Fintype α] (μ : PMF α)

open scoped Classical in
lemma lawProb_eq (A : α → Prop) : lawProb μ A = ∑ x, if A x then (μ x).toReal else 0 := by
  unfold lawProb; rw [sum_filter]

lemma lawProb_eq' (A : α → Prop) [DecidablePred A] :
    lawProb μ A = ∑ x, if A x then (μ x).toReal else 0 := by
  unfold lawProb; rw [sum_filter]; apply sum_congr rfl; intro x _; split_ifs <;> rfl

lemma sum_toReal : ∑ x, (μ x).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top μ x)]
  have := μ.tsum_coe
  rw [tsum_fintype] at this
  rw [this]; simp

lemma lawProb_le_one (A : α → Prop) : lawProb μ A ≤ 1 := by
  classical
  rw [lawProb_eq, ← sum_toReal μ]
  apply sum_le_sum; intro x _
  split_ifs <;> simp

lemma lawProb_mono {A B : α → Prop} (h : ∀ x, A x → B x) : lawProb μ A ≤ lawProb μ B := by
  classical
  rw [lawProb_eq, lawProb_eq]
  apply sum_le_sum; intro x _
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h x h1) h2
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

lemma lawProb_union {ι : Type} (s : Finset ι) (A : ι → α → Prop) :
    lawProb μ (fun x => ∃ i ∈ s, A i x) ≤ ∑ i ∈ s, lawProb μ (A i) := by
  classical
  simp only [lawProb_eq]
  rw [sum_comm]
  apply sum_le_sum; intro x _
  split_ifs with h
  · obtain ⟨i, hi, hA⟩ := h
    calc (μ x).toReal = if A i x then (μ x).toReal else 0 := by rw [if_pos hA]
      _ ≤ _ := single_le_sum (f := fun i => if A i x then (μ x).toReal else 0)
          (fun j _ => by split_ifs <;> simp) hi
  · exact sum_nonneg fun j _ => by split_ifs <;> simp

end Prob

section Count
open scoped Classical

/-- The admissible colours of a vertex `x` for the colouring `β` of the edges of `m`. -/
noncomputable def tcol (m : Finset (Edge n)) {a : ℕ} (β : m ≃ Fin a) (x : Fin n) :
    Finset (Fin a) :=
  if x ∈ verts m then (m.attach.filter fun e => x ∈ endpoints e.1).image β else univ

lemma tcol_eq (m : Finset (Edge n)) (hm : IsMatching m) {a : ℕ} (β : m ≃ Fin a)
    (e : Edge n) (he : e ∈ m) (x : Fin n) (hx : x ∈ endpoints e) :
    tcol m β x = {β ⟨e, he⟩} := by
  have hxv : x ∈ verts m := mem_biUnion.2 ⟨e, he, hx⟩
  rw [tcol, if_pos hxv]
  have : (m.attach.filter fun e' => x ∈ endpoints e'.1) = {⟨e, he⟩} := by
    ext ⟨e', he'⟩
    simp only [mem_filter, mem_attach, true_and, mem_singleton, Subtype.mk.injEq]
    constructor
    · intro hx'
      by_contra hne
      exact disjoint_left.1 (hm e' he' e he hne) hx' hx
    · rintro rfl; exact hx
  rw [this, image_singleton]

lemma card_prod_tcol (m : Finset (Edge n)) (hm : IsMatching m) {a : ℕ} (β : m ≃ Fin a) :
    ∏ x, (tcol m β x).card = a ^ (univ \ verts m).card := by
  calc ∏ x, (tcol m β x).card = ∏ x, (if x ∈ verts m then 1 else a) := by
        apply prod_congr rfl
        intro x _
        by_cases hx : x ∈ verts m
        · obtain ⟨e, he, hxe⟩ := mem_biUnion.1 hx
          rw [tcol_eq m hm β e he x hxe, if_pos hx, card_singleton]
        · rw [tcol, if_neg hx, if_neg hx, card_univ, Fintype.card_fin]
    _ = a ^ (univ \ verts m).card := by
        rw [prod_ite]
        simp only [prod_const_one, prod_const, one_mul]
        rw [filter_not]
        congr 2; ext x; simp

/-- The sets `S` with `S ∩ A = C`. -/
noncomputable def SSet (A C : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (univ \ A).powerset.image (· ∪ C)

lemma card_SSet {A C : Finset (Fin n)} (hCA : C ⊆ A) :
    (SSet A C).card = 2 ^ (univ \ A).card := by
  rw [SSet, card_image_of_injOn, card_powerset]
  intro S1 h1 S2 h2 h
  simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at h1 h2
  ext x
  have hx := congrArg (x ∈ ·) h
  simp only [mem_union, eq_iff_iff] at hx
  by_cases hC : x ∈ C
  · have hA := hCA hC
    constructor
    · intro hS; have := h1 hS; simp at this; exact absurd hA this
    · intro hS; have := h2 hS; simp at this; exact absurd hA this
  · simpa [hC] using hx

theorem card_cons {a : ℕ} (ha : 1 ≤ a) (P m : Finset (Edge n)) (hmP : m ⊆ P) (hP : IsMatching P)
    (hma : m.card = a) (D : Finset (Fin n) → (Fin n → Fin a) → Prop)
    (hD : ∀ S f, ((∀ e ∈ P, (endpoints e ⊆ S ∧ e ∈ m ∧
        ∀ u ∈ endpoints e, ∀ v ∈ endpoints e, f u = f v) ∨
        (Disjoint (endpoints e) S ∧ e ∉ m)) ∧
      (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → ∀ u ∈ endpoints e, ∀ v ∈ endpoints e', f u ≠ f v)) →
      D S f) :
    (a.factorial : ℝ) * 2 ^ n * (a : ℝ) ^ n ≤
      ((univ.filter fun p : Finset (Fin n) × (Fin n → Fin a) => D p.1 p.2).card : ℝ) *
        2 ^ (2 * P.card) * (a : ℝ) ^ (2 * a) := by
  have hm : IsMatching m := isMatching_mono hmP hP
  set A := verts P with hA
  set C := verts m with hC
  have hCA : C ⊆ A := biUnion_subset_biUnion_of_subset_left _ hmP
  set B := (univ : Finset (m ≃ Fin a)).biUnion
    (fun β => SSet A C ×ˢ Fintype.piFinset (tcol m β)) with hB
  have hBsub : B ⊆ univ.filter fun p : Finset (Fin n) × (Fin n → Fin a) => D p.1 p.2 := by
    intro p hp
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    obtain ⟨β, -, hβ⟩ := mem_biUnion.1 hp
    rw [mem_product] at hβ
    obtain ⟨hS, hf⟩ := hβ
    obtain ⟨S', hS', hSeq⟩ := mem_image.1 hS
    rw [mem_powerset] at hS'
    rw [Fintype.mem_piFinset] at hf
    have hfe : ∀ e (he : e ∈ m), ∀ x ∈ endpoints e, p.2 x = β ⟨e, he⟩ := by
      intro e he x hx
      have := hf x
      rw [tcol_eq m hm β e he x hx, mem_singleton] at this
      exact this
    apply hD
    refine ⟨?_, ?_⟩
    · intro e he
      by_cases hem : e ∈ m
      · left
        refine ⟨?_, hem, ?_⟩
        · intro x hx
          rw [← hSeq]
          exact mem_union_right _ (mem_biUnion.2 ⟨e, hem, hx⟩)
        · intro u hu v hv
          rw [hfe e hem u hu, hfe e hem v hv]
      · right
        refine ⟨?_, hem⟩
        rw [← hSeq, disjoint_union_right]
        constructor
        · rw [disjoint_left]
          intro x hx hxS
          have := hS' hxS
          simp only [mem_sdiff, mem_univ, true_and] at this
          exact this (mem_biUnion.2 ⟨e, he, hx⟩)
        · rw [disjoint_left]
          intro x hx hxC
          obtain ⟨e', he', hxe'⟩ := mem_biUnion.1 hxC
          have hne : e ≠ e' := fun h => hem (h ▸ he')
          exact disjoint_left.1 (hP e he e' (hmP he') hne) hx hxe'
    · intro e he e' he' hne u hu v hv
      rw [hfe e he u hu, hfe e' he' v hv]
      intro h
      exact hne (congrArg Subtype.val (β.injective h))
  have hBcard : B.card = a.factorial * (2 ^ (univ \ A).card * a ^ (univ \ C).card) := by
    rw [hB, card_biUnion]
    · simp only [card_product, card_SSet hCA, Fintype.card_piFinset, card_prod_tcol m hm]
      rw [sum_const, card_univ, smul_eq_mul]
      congr 1
      have e0 : (m : Type) ≃ Fin a := Fintype.equivFinOfCardEq (by simpa using hma)
      rw [Fintype.card_equiv e0]
      simp [hma]
    · intro β _ β' _ hne
      rw [Function.onFun, disjoint_left]
      intro p hp hp'
      apply hne
      ext ⟨e, he⟩
      obtain ⟨x, hx⟩ := C10.endpoints_nonempty e
      have h1 := (Fintype.mem_piFinset.1 (mem_product.1 hp).2) x
      have h2 := (Fintype.mem_piFinset.1 (mem_product.1 hp').2) x
      rw [tcol_eq m hm _ e he x hx, mem_singleton] at h1 h2
      rw [← h1, ← h2]
  have hcard := card_le_card hBsub
  have hAn : (univ \ A).card + A.card = n := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have := card_le_univ A
    simp at this; omega
  have hCn : (univ \ C).card + C.card = n := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have := card_le_univ C
    simp at this; omega
  have hA2 : A.card ≤ 2 * P.card := card_verts_le P
  have hC2 : C.card ≤ 2 * a := hma ▸ card_verts_le m
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have e1 : (2 : ℝ) ^ n ≤ 2 ^ (univ \ A).card * 2 ^ (2 * P.card) := by
    rw [← pow_add]; apply pow_le_pow_right₀ (by norm_num); omega
  have e2 : (a : ℝ) ^ n ≤ (a : ℝ) ^ (univ \ C).card * (a : ℝ) ^ (2 * a) := by
    rw [← pow_add]; apply pow_le_pow_right₀ ha'; omega
  have hcardR : (B.card : ℝ) ≤
      ((univ.filter fun p : Finset (Fin n) × (Fin n → Fin a) => D p.1 p.2).card : ℝ) := by
    exact_mod_cast hcard
  rw [hBcard] at hcardR
  push_cast at hcardR
  calc (a.factorial : ℝ) * 2 ^ n * (a : ℝ) ^ n
      ≤ (a.factorial : ℝ) * (2 ^ (univ \ A).card * 2 ^ (2 * P.card)) *
          ((a : ℝ) ^ (univ \ C).card * (a : ℝ) ^ (2 * a)) := by gcongr
    _ = ((a.factorial : ℝ) * (2 ^ (univ \ A).card * (a : ℝ) ^ (univ \ C).card)) *
          2 ^ (2 * P.card) * (a : ℝ) ^ (2 * a) := by ring
    _ ≤ _ := by gcongr

end Count

section Main
open scoped Classical
variable (ord : LinearOrder (Finset (Edge n))) (μ : PMF (Finset (Edge n))) (t ε : ℝ)
  (W : Finset (Fin n) → ℕ → ℕ → Finset (Fin n)) (k : ℕ)

/-- The event `E_{ℓ,a}` (with `ℓ = k + 1`), restricted to the support. -/
def Ea (a : ℕ) (X : Finset (Fin n)) (z : Finset (Edge n)) : Prop :=
  z ∈ lawSupport μ ∧ EventE ord (lawSupport μ) t ε (W X) (k + 1) a z

/-- The pairs `(W_ℓ, π_ℓ(z))` produced within `E_{ℓ,a} ∧ D_{S,f}`. -/
noncomputable def Good (s a : ℕ) (R : Finset (Fin n)) (S : Finset (Fin n)) (f : Fin n → Fin a) :
    Finset (Finset (Fin n) × Finset (Edge n)) :=
  ((powersetCard s R) ×ˢ (univ : Finset (Finset (Edge n)))).filter fun p =>
    ∃ z, Ea ord μ t ε W k a p.1 z ∧ IsConsistent ord (lawSupport μ) t ε (W p.1) (k + 1) z S f ∧
      residual ord (lawSupport μ) t ε (W p.1) (k + 1) z = p.2

variable (hW : ∀ X Y, ∀ ℓ' ∈ Icc 1 k, flatW t ε (W X) ℓ' = flatW t ε (W Y) ℓ')
  (hX : ∀ X, flatW t ε (W X) (k + 1) = X) (hμ : IsBoundedMatchingLaw μ t)

include hW hX in
lemma bar_succ (X : Finset (Fin n)) :
    flatWbar t ε (W X) (k + 1) = flatWbar t ε (W ∅) k ∪ X := by
  rw [C10.flatWbar_succ, hX, flatWbar_congr t ε (W X) (W ∅) k (hW X ∅)]

include hW hX in
lemma res_disj (X : Finset (Fin n)) (z : Finset (Edge n)) (e : Edge n)
    (he : e ∈ residual ord (lawSupport μ) t ε (W X) (k + 1) z) :
    Disjoint (endpoints e) (flatWbar t ε (W ∅) k ∪ X) := by
  rw [← bar_succ t ε W k hW hX X]
  simp only [residual] at he
  rw [mem_sdiff, C10.mem_incident, not_not] at he
  exact he.2

lemma stageMu_facts (X : Finset (Fin n)) (z : Finset (Edge n)) (hz : z ∈ lawSupport μ)
    (hb : (residual ord (lawSupport μ) t ε (W X) k z).card ≤ stageBudget t ε (k + 1)) :
    stageMu ord (lawSupport μ) t ε (W X) (k + 1) z ∈ lawSupport μ ∧
    (residual ord (lawSupport μ) t ε (W X) k
      (stageMu ord (lawSupport μ) t ε (W X) (k + 1) z)).card ≤ stageBudget t ε (k + 1) ∧
    residual ord (lawSupport μ) t ε (W X) (k + 1) z ⊆
      residual ord (lawSupport μ) t ε (W X) k (stageMu ord (lawSupport μ) t ε (W X) (k + 1) z) := by
  have h := C10.chooseMu_spec ord (lawSupport μ) (residual ord (lawSupport μ) t ε (W X) k)
    (incident (flatWbar t ε (W X) (k + 1))) (stageBudget t ε (k + 1)) z hz hb
  exact ⟨h.1, h.2.2.1, sdiff_subset⟩

include hW hX hμ in
lemma mem_Good_facts (s a : ℕ) (R : Finset (Fin n)) (S : Finset (Fin n)) (f : Fin n → Fin a)
    (p : Finset (Fin n) × Finset (Edge n)) (hp : p ∈ Good ord μ t ε W k s a R S f) :
    p.1 ⊆ R ∧ p.1.card = s ∧ IsMatching p.2 ∧ p.2.card = a ∧
      Disjoint (verts p.2) (flatWbar t ε (W ∅) k ∪ p.1) ∧
      p.2 ⊆ residual ord (lawSupport μ) t ε (W ∅) k
        (decode ord (lawSupport μ) t ε (W ∅) (k + 1) (p.1 ∪ verts p.2) S f) := by
  rw [Good, mem_filter, mem_product, mem_powersetCard] at hp
  obtain ⟨⟨⟨hXR, hXs⟩, -⟩, z, ⟨hz, hE⟩, hD, hres⟩ := hp
  have hm : IsMatching p.2 :=
    hres ▸ isMatching_mono (residual_subset ord _ t ε _ _ z) (hμ z hz).1
  have hcardm : p.2.card = a := hres ▸ hE.2.2.2
  have hVd : Disjoint (verts p.2) (flatWbar t ε (W ∅) k ∪ p.1) := by
    rw [verts, disjoint_biUnion_left]
    intro e he
    exact res_disj ord μ t ε W k hW hX p.1 z e (hres ▸ he)
  refine ⟨hXR, hXs, hm, hcardm, hVd, ?_⟩
  have := C10.main ord (lawSupport μ) t ε (W p.1) k z hz a S f hE hD
  rw [hX, hres] at this
  rwa [residual_congr ord _ t ε (W p.1) (W ∅) k (hW _ _) k le_rfl,
    decode_congr ord _ t ε (W p.1) (W ∅) k (hW _ _)] at this

include hW hX hμ in
lemma card_Good (s a : ℕ) (R : Finset (Fin n)) (hR : R = univ \ flatWbar t ε (W ∅) k)
    (S : Finset (Fin n)) (f : Fin n → Fin a) :
    (Good ord μ t ε W k s a R S f).card ≤
      R.card.choose (s + 2 * a) * 2 ^ stageBudget t ε (k + 1) := by
  set Tgt := (powersetCard (s + 2 * a) R).sigma fun T =>
    (residual ord (lawSupport μ) t ε (W ∅) k
      (decode ord (lawSupport μ) t ε (W ∅) (k + 1) T S f)).powerset with hTgt
  have h1 : (Good ord μ t ε W k s a R S f).card ≤ Tgt.card := by
    apply card_le_card_of_injOn
      (fun p => (⟨p.1 ∪ verts p.2, p.2⟩ : Σ _ : Finset (Fin n), Finset (Edge n)))
    · intro p hp
      obtain ⟨hXR, hXs, hm, hcardm, hVd, hsub⟩ :=
        mem_Good_facts ord μ t ε W k hW hX hμ s a R S f p hp
      simp only [hTgt, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_powersetCard, mem_powerset]
      refine ⟨⟨?_, ?_⟩, hsub⟩
      · apply union_subset hXR
        intro x hx
        rw [hR, mem_sdiff]
        exact ⟨mem_univ _, fun hxb => disjoint_left.1 hVd hx (mem_union_left _ hxb)⟩
      · rw [card_union_of_disjoint (disjoint_union_right.1 hVd).2.symm, hXs,
          card_verts_of_matching hm, hcardm]
    · intro p hp p' hp' heq
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨h1, h2⟩ := heq
      have d1 := (disjoint_union_right.1
        (mem_Good_facts ord μ t ε W k hW hX hμ s a R S f p hp).2.2.2.2.1).2
      have d2 := (disjoint_union_right.1
        (mem_Good_facts ord μ t ε W k hW hX hμ s a R S f p' hp').2.2.2.2.1).2
      apply Prod.ext _ h2
      rw [← union_sdiff_cancel_right d1.symm, ← union_sdiff_cancel_right d2.symm, h1, h2]
  refine h1.trans ?_
  rw [hTgt, card_sigma]
  calc _ ≤ ∑ T ∈ powersetCard (s + 2 * a) R, 2 ^ stageBudget t ε (k + 1) := by
        apply sum_le_sum
        intro T _
        rw [card_powerset]
        exact Nat.pow_le_pow_right two_pos (decode_card ord _ t ε (W ∅) k T S f)
    _ = _ := by rw [sum_const, card_powersetCard, smul_eq_mul]

include hW hX hμ in
lemma sum_omega (s a : ℕ) (R : Finset (Fin n)) (hR : R = univ \ flatWbar t ε (W ∅) k)
    (r : ℝ) (hr : 0 < r) (hsp : IsSpread μ r) (S : Finset (Fin n)) (f : Fin n → Fin a) :
    ∑ X ∈ powersetCard s R, ∑ z, (if Ea ord μ t ε W k a X z ∧
        IsConsistent ord (lawSupport μ) t ε (W X) (k + 1) z S f then (μ z).toReal else 0) ≤
      ((R.card.choose (s + 2 * a) * 2 ^ stageBudget t ε (k + 1) : ℕ) : ℝ) * (r ^ a)⁻¹ := by
  set Q := fun X z => Ea ord μ t ε W k a X z ∧
    IsConsistent ord (lawSupport μ) t ε (W X) (k + 1) z S f with hQ
  have step1 : ∀ X z, (if Q X z then (μ z).toReal else 0) = ∑ m : Finset (Edge n),
      if Q X z ∧ residual ord (lawSupport μ) t ε (W X) (k + 1) z = m then (μ z).toReal else 0 := by
    intro X z
    by_cases h : Q X z <;> simp [h]
  have step2 : ∀ p ∈ powersetCard s R ×ˢ (univ : Finset (Finset (Edge n))),
      ∑ z, (if Q p.1 z ∧ residual ord (lawSupport μ) t ε (W p.1) (k + 1) z = p.2 then
        (μ z).toReal else 0) ≤ if p ∈ Good ord μ t ε W k s a R S f then (r ^ a)⁻¹ else 0 := by
    intro p hp
    split_ifs with hG
    · obtain ⟨-, -, hm, hcardm, -, -⟩ := mem_Good_facts ord μ t ε W k hW hX hμ s a R S f p hG
      calc _ ≤ ∑ z, (if p.2 ⊆ z then (μ z).toReal else 0) := by
            apply sum_le_sum
            intro z _
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd (h1.2 ▸ residual_subset ord _ t ε _ _ z) h2
            · exact ENNReal.toReal_nonneg
            · exact le_rfl
        _ = lawProb μ (fun z => p.2 ⊆ z) := (lawProb_eq' μ _).symm
        _ ≤ (r ^ p.2.card)⁻¹ := hsp _ hm
        _ = _ := by rw [hcardm]
    · apply le_of_eq
      apply sum_eq_zero
      intro z _
      rw [if_neg]
      rintro ⟨hQz, hres⟩
      exact hG (mem_filter.2 ⟨hp, z, hQz.1, hQz.2, hres⟩)
  calc _ = ∑ X ∈ powersetCard s R, ∑ m : Finset (Edge n), ∑ z,
        (if Q X z ∧ residual ord (lawSupport μ) t ε (W X) (k + 1) z = m then
          (μ z).toReal else 0) := by
        apply sum_congr rfl
        intro X _
        rw [sum_comm]
        exact sum_congr rfl (fun z _ => step1 X z)
    _ = ∑ p ∈ powersetCard s R ×ˢ (univ : Finset (Finset (Edge n))), ∑ z,
        (if Q p.1 z ∧ residual ord (lawSupport μ) t ε (W p.1) (k + 1) z = p.2 then
          (μ z).toReal else 0) := by rw [sum_product]
    _ ≤ ∑ p ∈ powersetCard s R ×ˢ (univ : Finset (Finset (Edge n))),
        if p ∈ Good ord μ t ε W k s a R S f then (r ^ a)⁻¹ else 0 := sum_le_sum step2
    _ = ((Good ord μ t ε W k s a R S f).card : ℝ) * (r ^ a)⁻¹ := by
        have hGsub : powersetCard s R ×ˢ (univ : Finset (Finset (Edge n))) ∩
            Good ord μ t ε W k s a R S f = Good ord μ t ε W k s a R S f :=
          inter_eq_right.2 (filter_subset _ _)
        rw [sum_ite_mem, hGsub, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        exact_mod_cast card_Good ord μ t ε W k hW hX hμ s a R hR S f

include hW hX hμ in
lemma per_a (s a : ℕ) (ha : 1 ≤ a) (R : Finset (Fin n)) (hR : R = univ \ flatWbar t ε (W ∅) k)
    (r : ℝ) (hr : 0 < r) (hsp : IsSpread μ r) :
    (∑ X ∈ powersetCard s R, lawProb μ (Ea ord μ t ε W k a X)) *
        ((a.factorial : ℝ) * 2 ^ n * (a : ℝ) ^ n) ≤
      ((2 : ℝ) ^ (2 * stageBudget t ε (k + 1)) * (a : ℝ) ^ (2 * a)) *
        (((2 : ℝ) ^ n * (a : ℝ) ^ n) *
        (((R.card.choose (s + 2 * a) * 2 ^ stageBudget t ε (k + 1) : ℕ) : ℝ) * (r ^ a)⁻¹)) := by
  set b := stageBudget t ε (k + 1) with hb
  set K := (a.factorial : ℝ) * 2 ^ n * (a : ℝ) ^ n with hK
  set c := (2 : ℝ) ^ (2 * b) * (a : ℝ) ^ (2 * a) with hc
  set Cb := (((R.card.choose (s + 2 * a) * 2 ^ b : ℕ) : ℝ) * (r ^ a)⁻¹) with hCb
  have hptw : ∀ X z, (if Ea ord μ t ε W k a X z then (μ z).toReal else 0) * K ≤
      c * ∑ ω : Finset (Fin n) × (Fin n → Fin a), (if Ea ord μ t ε W k a X z ∧
        IsConsistent ord (lawSupport μ) t ε (W X) (k + 1) z ω.1 ω.2 then (μ z).toReal else 0) := by
    intro X z
    by_cases hE : Ea ord μ t ε W k a X z
    · simp only [hE, if_true, true_and]
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      obtain ⟨hz, hEv⟩ := hE
      have hbz : (residual ord (lawSupport μ) t ε (W X) k z).card ≤ b := hEv.2.2.1
      obtain ⟨hmu, hPb, hmP⟩ := stageMu_facts ord μ t ε W k X z hz hbz
      have hP : IsMatching (residual ord (lawSupport μ) t ε (W X) k
          (stageMu ord (lawSupport μ) t ε (W X) (k + 1) z)) :=
        isMatching_mono (residual_subset ord _ t ε _ _ _) (hμ _ hmu).1
      have hcc := card_cons ha _ _ hmP hP hEv.2.2.2
        (fun S f => IsConsistent ord (lawSupport μ) t ε (W X) (k + 1) z S f)
        (fun S f h => h)
      have h2 : (2 : ℝ) ^ (2 * (residual ord (lawSupport μ) t ε (W X) k
          (stageMu ord (lawSupport μ) t ε (W X) (k + 1) z)).card) ≤ 2 ^ (2 * b) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hw := (ENNReal.toReal_nonneg : 0 ≤ (μ z).toReal)
      set N := ((univ.filter fun p : Finset (Fin n) × (Fin n → Fin a) =>
        IsConsistent ord (lawSupport μ) t ε (W X) (k + 1) z p.1 p.2).card : ℝ)
      have hN : 0 ≤ N := Nat.cast_nonneg _
      calc (μ z).toReal * K ≤ (μ z).toReal * (N * 2 ^ (2 * (residual ord (lawSupport μ) t ε (W X) k
          (stageMu ord (lawSupport μ) t ε (W X) (k + 1) z)).card) * (a : ℝ) ^ (2 * a)) :=
            mul_le_mul_of_nonneg_left hcc hw
        _ ≤ (μ z).toReal * (N * 2 ^ (2 * b) * (a : ℝ) ^ (2 * a)) := by gcongr
        _ = _ := by rw [hc]; ring
    · simp [hE]
  have hcard : ((univ : Finset (Finset (Fin n) × (Fin n → Fin a))).card : ℝ) =
      (2 : ℝ) ^ n * (a : ℝ) ^ n := by
    rw [card_univ]; simp [Fintype.card_prod, Fintype.card_finset]
  have hc0 : 0 ≤ c := by positivity
  calc (∑ X ∈ powersetCard s R, lawProb μ (Ea ord μ t ε W k a X)) * K
      = ∑ X ∈ powersetCard s R, ∑ z, (if Ea ord μ t ε W k a X z then (μ z).toReal else 0) * K := by
        rw [sum_mul]; apply sum_congr rfl; intro X _; rw [lawProb_eq, sum_mul]
    _ ≤ ∑ X ∈ powersetCard s R, ∑ z, c * ∑ ω : Finset (Fin n) × (Fin n → Fin a),
        (if Ea ord μ t ε W k a X z ∧ IsConsistent ord (lawSupport μ) t ε (W X) (k + 1) z ω.1 ω.2
          then (μ z).toReal else 0) := sum_le_sum fun X _ => sum_le_sum fun z _ => hptw X z
    _ = c * ∑ ω : Finset (Fin n) × (Fin n → Fin a), ∑ X ∈ powersetCard s R, ∑ z,
        (if Ea ord μ t ε W k a X z ∧ IsConsistent ord (lawSupport μ) t ε (W X) (k + 1) z ω.1 ω.2
          then (μ z).toReal else 0) := by
        simp only [mul_sum]
        exact (sum_congr rfl (fun X _ => sum_comm)).trans sum_comm
    _ ≤ c * ∑ _ω : Finset (Fin n) × (Fin n → Fin a), Cb := by
        gcongr with ω
        exact sum_omega ord μ t ε W k hW hX hμ s a R hR r hr hsp ω.1 ω.2
    _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]

end Main

section Arith

lemma choose_mul_pow_le (N s : ℕ) : ∀ j, N.choose (s + j) * s ^ j ≤ N.choose s * N ^ j
  | 0 => by simp
  | j + 1 => by
    have ih := choose_mul_pow_le N s j
    have h1 := Nat.choose_succ_right_eq N (s + j)
    calc N.choose (s + (j + 1)) * s ^ (j + 1) = (N.choose (s + j + 1) * s) * s ^ j := by
          rw [← add_assoc, pow_succ]; ring
      _ ≤ (N.choose (s + j + 1) * (s + j + 1)) * s ^ j := by gcongr; omega
      _ = N.choose (s + j) * (N - (s + j)) * s ^ j := by rw [h1]
      _ ≤ N.choose (s + j) * N * s ^ j := by gcongr; exact Nat.sub_le _ _
      _ = (N.choose (s + j) * s ^ j) * N := by ring
      _ ≤ (N.choose s * N ^ j) * N := by gcongr
      _ = N.choose s * N ^ (j + 1) := by ring

lemma pow_self_le (a : ℕ) : (a : ℝ) ^ a ≤ a.factorial * 3 ^ a := by
  have h := Real.pow_div_factorial_le_exp (x := (a : ℝ)) (by positivity) a
  have hf : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  rw [div_le_iff₀ hf] at h
  have he : Real.exp a ≤ 3 ^ a := by
    rw [show (a : ℝ) = a * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num)) a
  calc (a : ℝ) ^ a ≤ Real.exp a * a.factorial := h
    _ ≤ 3 ^ a * a.factorial := by gcongr
    _ = _ := by ring

lemma rpow_half_sq (q i : ℕ) (hi : i ≤ q) :
    ((2 : ℝ) ^ (((q : ℝ) - (i : ℝ)) / 2)) ^ 2 = 2 ^ (q - i) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  congr 1; push_cast [Nat.cast_sub hi]; ring

lemma size_bound (n : ℕ) (t ε γ : ℝ) (hγ : 0 < γ) (i : ℕ) (hi : i ≤ stageCount t)
    (hs : 1 ≤ stageSize n t ε γ i) :
    0 < stageWeight t ε ∧
      (n : ℝ) ^ 2 * 2 ^ (stageCount t - i) * γ ^ 2 ≤
        4 * (stageSize n t ε γ i : ℝ) ^ 2 * stageWeight t ε ^ 2 := by
  set M := stageWeight t ε with hM
  set c := (2 : ℝ) ^ (((stageCount t : ℝ) - (i : ℝ)) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ^ 2 = 2 ^ (stageCount t - i) := rpow_half_sq _ _ hi
  set x := γ * (n : ℝ) * c / M with hx
  have hsx : stageSize n t ε γ i = ⌊x⌋₊ := rfl
  have hM0 : 0 < M := by
    by_contra hneg
    push Not at hneg
    have : x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    rw [hsx, Nat.floor_of_nonpos this] at hs
    omega
  refine ⟨hM0, ?_⟩
  set s := stageSize n t ε γ i
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlt : x < s + 1 := by rw [hsx]; exact Nat.lt_floor_add_one x
  have hx2 : γ * n * c ≤ 2 * s * M := by
    have : x ≤ 2 * s := by linarith
    rw [hx, div_le_iff₀ hM0] at this
    linarith
  have h0 : 0 ≤ γ * n * c := by positivity
  have := pow_le_pow_left₀ h0 hx2 2
  rw [← hc2]
  nlinarith

lemma arith_h2 (P0 r : ℝ) (a b n C2 : ℕ) (ha1 : 1 ≤ a) (hr : 0 < r)
    (h1 : P0 * ((a.factorial : ℝ) * 2 ^ n * (a : ℝ) ^ n) ≤
      ((2 : ℝ) ^ (2 * b) * (a : ℝ) ^ (2 * a)) *
        (((2 : ℝ) ^ n * (a : ℝ) ^ n) * (((C2 * 2 ^ b : ℕ) : ℝ) * (r ^ a)⁻¹))) :
    P0 * a.factorial * r ^ a ≤ 2 ^ (2 * b) * 2 ^ b * (a : ℝ) ^ (2 * a) * C2 := by
  have hZ : (0 : ℝ) < 2 ^ n * (a : ℝ) ^ n := by
    have : (0 : ℝ) < a := by exact_mod_cast ha1
    positivity
  have hra : (0 : ℝ) < r ^ a := by positivity
  have h1' : (P0 * a.factorial) * (2 ^ n * (a : ℝ) ^ n) ≤
      (2 ^ (2 * b) * 2 ^ b * (a : ℝ) ^ (2 * a) * C2 * (r ^ a)⁻¹) * (2 ^ n * (a : ℝ) ^ n) := by
    calc (P0 * a.factorial) * (2 ^ n * (a : ℝ) ^ n) =
        P0 * ((a.factorial : ℝ) * 2 ^ n * (a : ℝ) ^ n) := by ring
      _ ≤ _ := h1
      _ = _ := by push_cast; ring
  have h1'' := le_of_mul_le_mul_right h1' hZ
  calc P0 * a.factorial * r ^ a ≤
      (2 ^ (2 * b) * 2 ^ b * (a : ℝ) ^ (2 * a) * C2 * (r ^ a)⁻¹) * r ^ a := by gcongr
    _ = _ := by field_simp

lemma arith_hsz (a N n s q i : ℕ) (M γ : ℝ) (hγ : 0 < γ) (hNn : N ≤ n)
    (haF : a ≤ 2 * 2 ^ (q - i))
    (hsize : (n : ℝ) ^ 2 * 2 ^ (q - i) * γ ^ 2 ≤ 4 * (s : ℝ) ^ 2 * M ^ 2) :
    (192 : ℝ) * a * (N : ℝ) ^ 2 ≤ 1536 * (s : ℝ) ^ 2 * M ^ 2 / γ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have hN' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have haF' : (a : ℝ) ≤ 2 * 2 ^ (q - i) := by exact_mod_cast haF
  have hN2 : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN' 2
  have e1 : (a : ℝ) * (N : ℝ) ^ 2 * γ ^ 2 ≤ (2 * 2 ^ (q - i)) * ((n : ℝ) ^ 2 * γ ^ 2) := by
    calc (a : ℝ) * (N : ℝ) ^ 2 * γ ^ 2 = a * ((N : ℝ) ^ 2 * γ ^ 2) := by ring
      _ ≤ (2 * 2 ^ (q - i)) * ((N : ℝ) ^ 2 * γ ^ 2) := by gcongr
      _ ≤ (2 * 2 ^ (q - i)) * ((n : ℝ) ^ 2 * γ ^ 2) := by gcongr
  have e2 : (2 * (2 : ℝ) ^ (q - i)) * ((n : ℝ) ^ 2 * γ ^ 2) =
      2 * ((n : ℝ) ^ 2 * 2 ^ (q - i) * γ ^ 2) := by ring
  linarith

lemma arith_core (P0 r M γ : ℝ) (a b s N Pc C2 : ℕ) (hr : 0 < r) (hγ : 0 < γ)
    (ha1 : 1 ≤ a) (hs : 1 ≤ s)
    (h2 : P0 * a.factorial * r ^ a ≤ 2 ^ (2 * b) * 2 ^ b * (a : ℝ) ^ (2 * a) * C2)
    (hbin : (C2 : ℝ) * (s : ℝ) ^ (2 * a) ≤ (Pc : ℝ) * (N : ℝ) ^ (2 * a)) (hb : b ≤ 2 * a)
    (hsz : (192 : ℝ) * a * (N : ℝ) ^ 2 ≤ 1536 * (s : ℝ) ^ 2 * M ^ 2 / γ ^ 2) :
    P0 ≤ (Pc : ℝ) * (1536 * (M ^ 2 / (r * γ ^ 2))) ^ a := by
  have hfact := pow_self_le a
  have h2b : (2 : ℝ) ^ (2 * b) * 2 ^ b ≤ 64 ^ a := by
    rw [← pow_add, show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul]
    apply pow_le_pow_right₀ (by norm_num); omega
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hra : (0 : ℝ) < r ^ a := by positivity
  have hfa : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  have hD : (0 : ℝ) < a.factorial * r ^ a * (s : ℝ) ^ (2 * a) := by positivity
  have hPc : (0 : ℝ) ≤ Pc := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (2 * a) := by positivity
  have ha0 : (0 : ℝ) ≤ (a : ℝ) ^ a := by positivity
  have hC0 : (0 : ℝ) ≤ (C2 : ℝ) * (s : ℝ) ^ (2 * a) := by positivity
  have key : P0 * (a.factorial * r ^ a * (s : ℝ) ^ (2 * a)) ≤
      (a.factorial * r ^ a * (s : ℝ) ^ (2 * a)) * ((Pc : ℝ) * (1536 * (M ^ 2 / (r * γ ^ 2))) ^ a) := by
    calc P0 * (a.factorial * r ^ a * (s : ℝ) ^ (2 * a))
        = (P0 * a.factorial * r ^ a) * (s : ℝ) ^ (2 * a) := by ring
      _ ≤ (2 ^ (2 * b) * 2 ^ b * (a : ℝ) ^ (2 * a) * C2) * (s : ℝ) ^ (2 * a) := by gcongr
      _ = (2 ^ (2 * b) * 2 ^ b) * ((a : ℝ) ^ a * (a : ℝ) ^ a) * (C2 * (s : ℝ) ^ (2 * a)) := by
          rw [two_mul a, pow_add]; ring
      _ ≤ 64 ^ a * ((a.factorial * 3 ^ a) * (a : ℝ) ^ a) * ((Pc : ℝ) * (N : ℝ) ^ (2 * a)) := by
          apply mul_le_mul (mul_le_mul h2b (mul_le_mul_of_nonneg_right hfact ha0)
            (by positivity) (by positivity)) hbin hC0 (by positivity)
      _ = a.factorial * (Pc : ℝ) * (192 * a * (N : ℝ) ^ 2) ^ a := by
          rw [show (192 : ℝ) * a * (N : ℝ) ^ 2 = 64 * 3 * a * (N : ℝ) ^ 2 by norm_num,
            mul_pow, mul_pow, mul_pow, ← pow_mul]
          ring
      _ ≤ a.factorial * (Pc : ℝ) * (1536 * (s : ℝ) ^ 2 * M ^ 2 / γ ^ 2) ^ a := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hsz a
      _ = (a.factorial * r ^ a * (s : ℝ) ^ (2 * a)) *
          ((Pc : ℝ) * (1536 * (M ^ 2 / (r * γ ^ 2))) ^ a) := by
          have hr' : r ≠ 0 := hr.ne'
          have hγ' : γ ≠ 0 := hγ.ne'
          have e3 : (1536 * (s : ℝ) ^ 2 * M ^ 2 / γ ^ 2) ^ a =
              (r ^ a * (s : ℝ) ^ (2 * a)) * (1536 * (M ^ 2 / (r * γ ^ 2))) ^ a := by
            rw [show 1536 * (s : ℝ) ^ 2 * M ^ 2 / γ ^ 2 =
                (r * (s : ℝ) ^ 2) * (1536 * (M ^ 2 / (r * γ ^ 2))) by field_simp,
              mul_pow, mul_pow, ← pow_mul]
          rw [e3]; ring
  rw [mul_comm (a.factorial * r ^ a * (s : ℝ) ^ (2 * a)) _] at key
  exact le_of_mul_le_mul_right key hD

lemma arith_sum (Pc : ℝ) (hPc : 0 ≤ Pc) (u : ℝ) (hu0 : 0 ≤ u) (F : ℕ) (hF1 : 1 ≤ F) (T : ℝ)
    (hT1 : T ≤ Pc * ∑ a ∈ Icc F (2 * F), u ^ a) (hT2 : T ≤ Pc) : T ≤ (2 * u) ^ F * Pc := by
  by_cases hsmall : u ≤ 1 / 2
  · have hg : ∑ a ∈ Icc F (2 * F), u ^ a ≤ 2 * u ^ F := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      have := geom_sum_Ico_le_of_lt_one (m := F) (n := 2 * F + 1) hu0 (by linarith)
      refine this.trans ?_
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ u ^ F := by positivity
      nlinarith
    have h2F : (2 : ℝ) ≤ 2 ^ F := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ F := pow_le_pow_right₀ (by norm_num) hF1
    have huF : 0 ≤ u ^ F := by positivity
    calc T ≤ Pc * ∑ a ∈ Icc F (2 * F), u ^ a := hT1
      _ ≤ Pc * (2 * u ^ F) := mul_le_mul_of_nonneg_left hg hPc
      _ ≤ Pc * (2 ^ F * u ^ F) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2F huF) hPc
      _ = (2 * u) ^ F * Pc := by rw [mul_pow]; ring
  · push Not at hsmall
    have h1 : (1 : ℝ) ≤ (2 * u) ^ F := one_le_pow₀ (by linarith)
    exact hT2.trans (le_mul_of_one_le_left hPc h1)

end Arith

section Final
open scoped Classical

lemma stage_mem (t ε : ℝ) (k : ℕ) (hk : k + 1 ≤ numStages t ε) :
    1 ≤ (stageAt t ε (k + 1)).1 ∧ (stageAt t ε (k + 1)).1 ≤ stageCount t := by
  have hk' : k < (stages t ε).length := by unfold numStages at hk; omega
  have hmem : (stages t ε).getD k (0, 0) ∈ stages t ε := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    exact List.getElem_mem hk'
  unfold stageAt
  simp only [Nat.add_sub_cancel]
  generalize (stages t ε).getD k (0, 0) = p at hmem ⊢
  unfold stages at hmem
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hmem
  obtain ⟨i', hi', j', -, rfl⟩ := hmem
  simp only
  omega

lemma lawProb_supp (μ : PMF (Finset (Edge n))) (A : Finset (Edge n) → Prop) :
    lawProb μ A ≤ lawProb μ (fun z => z ∈ lawSupport μ ∧ A z) := by
  rw [lawProb_eq, lawProb_eq]
  apply sum_le_sum; intro z _
  split_ifs with h1 h2
  · exact le_rfl
  · have : z ∉ lawSupport μ := fun h => h2 ⟨h, h1⟩
    simp only [lawSupport, mem_filter, mem_univ, true_and, PMF.mem_support_iff, not_not] at this
    simp [this]
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- **Eq. (3)**, in the form of `Dev.Lemma5.Eq3Statement` (with `EvK` unfolded). -/
theorem eq3_main :
  ∃ α₃ : ℝ, 0 < α₃ ∧
    ∀ (n : ℕ) (μ : PMF (Finset (Edge n))) (t ε γ r : ℝ) (ord : LinearOrder (Finset (Edge n)))
      (V : ℕ → Finset (Fin n)) (W : Finset (Fin n) → ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ),
      1 < t → 0 < ε → ε < 1 / 2 → 0 < γ → γ ≤ 1 → 0 < r →
      IsBoundedMatchingLaw μ t → IsSpread μ r →
      (∀ i ∈ Icc 1 (stageCount t), 1 ≤ stageSize n t ε γ i) →
      1 ≤ ℓ → ℓ ≤ numStages t ε →
      (∀ X, ∀ ℓ' ∈ Ico 1 ℓ, flatW t ε (W X) ℓ' = V ℓ') →
      (∀ X, flatW t ε (W X) ℓ = X) →
      ∑ X ∈ powersetCard (stageSize n t ε γ (stageAt t ε ℓ).1) (univ \ (Ico 1 ℓ).biUnion V),
          lawProb μ (fun z =>
            (residual ord (lawSupport μ) t ε (W X) (ℓ - 1) z).card ≤ stageBudget t ε ℓ ∧
              stageFloor t ε ℓ ≤ (residual ord (lawSupport μ) t ε (W X) ℓ z).card) ≤
        (α₃ * stageWeight t ε ^ 2 / (r * γ ^ 2)) ^ stageFloor t ε ℓ *
          ((powersetCard (stageSize n t ε γ (stageAt t ε ℓ).1)
            (univ \ (Ico 1 ℓ).biUnion V)).card : ℝ) := by
  refine ⟨3072, by norm_num, ?_⟩
  intro n μ t ε γ r ord V W ℓ ht hε₀ hε hγ₀ hγ₁ hr hμ hsp hS hℓ1 hℓL hV hX
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set i := (stageAt t ε (k + 1)).1 with hi
  obtain ⟨hi1, hiq⟩ := stage_mem t ε k hℓL
  have hs := hS i (mem_Icc.2 ⟨hi1, hiq⟩)
  set s := stageSize n t ε γ i with hsdef
  set q := stageCount t with hq
  obtain ⟨hM0, hsize⟩ := size_bound n t ε γ hγ₀ i hiq hs
  set M := stageWeight t ε with hM
  have hW : ∀ X Y, ∀ ℓ' ∈ Icc 1 k, flatW t ε (W X) ℓ' = flatW t ε (W Y) ℓ' := by
    intro X Y ℓ' h
    rw [hV X ℓ' (by simp at h ⊢; omega), hV Y ℓ' (by simp at h ⊢; omega)]
  have hVbar : (Ico 1 (k + 1)).biUnion V = flatWbar t ε (W ∅) k := by
    unfold flatWbar
    rw [show Ico 1 (k + 1) = Icc 1 k by ext x; simp only [mem_Ico, mem_Icc]; omega]
    exact biUnion_congr rfl (fun ℓ' h => (hV ∅ ℓ' (by simp at h ⊢; omega)).symm)
  set R := univ \ (Ico 1 (k + 1)).biUnion V with hRdef
  have hR : R = univ \ flatWbar t ε (W ∅) k := by rw [hRdef, hVbar]
  set F := stageFloor t ε (k + 1) with hFdef
  have hF : F = 2 ^ (q - i) := rfl
  have hB : stageBudget t ε (k + 1) = 2 * F := by
    simp only [stageBudget, hFdef, stageFloor]; rw [pow_succ]; ring
  have hF1 : 1 ≤ F := Nat.one_le_two_pow
  set y := M ^ 2 / (r * γ ^ 2) with hy
  have hy0 : 0 ≤ y := by positivity
  set P := powersetCard s R with hP
  set N := R.card with hN
  have hNn : N ≤ n := by
    have := card_le_univ R; simpa using this
  have hPcard : P.card = N.choose s := by rw [hP, card_powersetCard]
  -- step 1: split by the value of `a`
  have hsplit : ∀ X ∈ P, lawProb μ (fun z =>
      (residual ord (lawSupport μ) t ε (W X) k z).card ≤ stageBudget t ε (k + 1) ∧
        F ≤ (residual ord (lawSupport μ) t ε (W X) (k + 1) z).card) ≤
      ∑ a ∈ Icc F (2 * F), lawProb μ (Ea ord μ t ε W k a X) := by
    intro X _
    refine (lawProb_supp μ _).trans ((lawProb_mono μ ?_).trans (lawProb_union μ _ _))
    rintro z ⟨hz, hb, hf⟩
    obtain ⟨-, hPb, hsub⟩ := stageMu_facts ord μ t ε W k X z hz hb
    refine ⟨(residual ord (lawSupport μ) t ε (W X) (k + 1) z).card, ?_, hz, ?_⟩
    · rw [mem_Icc]
      refine ⟨hf, ?_⟩
      rw [← hB]; exact (card_le_card hsub).trans hPb
    · refine ⟨hf, (card_le_card hsub).trans hPb, hb, rfl⟩
  -- step 2: the bound for each `a`
  have hper : ∀ a ∈ Icc F (2 * F),
      ∑ X ∈ P, lawProb μ (Ea ord μ t ε W k a X) ≤ (P.card : ℝ) * (1536 * y) ^ a := by
    intro a ha
    rw [mem_Icc] at ha
    have ha1 : 1 ≤ a := le_trans hF1 ha.1
    have h1 := per_a ord μ t ε W k hW hX hμ s a ha1 R hR r hr hsp
    have h2 := arith_h2 _ r a _ n _ ha1 hr h1
    have hbin : ((N.choose (s + 2 * a) : ℕ) : ℝ) * (s : ℝ) ^ (2 * a) ≤
        (P.card : ℝ) * (N : ℝ) ^ (2 * a) := by
      rw [hPcard]; exact_mod_cast choose_mul_pow_le N s (2 * a)
    have haF : a ≤ 2 * 2 ^ (q - i) := hF ▸ ha.2
    have hsz := arith_hsz a N n s q i M γ hγ₀ hNn haF hsize
    exact arith_core _ r M γ a _ s N _ _ hr hγ₀ ha1 hs
      h2 hbin (by rw [hB]; omega) hsz
  -- step 3: sum up
  have htot : ∑ X ∈ P, lawProb μ (fun z =>
      (residual ord (lawSupport μ) t ε (W X) k z).card ≤ stageBudget t ε (k + 1) ∧
        F ≤ (residual ord (lawSupport μ) t ε (W X) (k + 1) z).card) ≤
      (P.card : ℝ) * ∑ a ∈ Icc F (2 * F), (1536 * y) ^ a := by
    calc _ ≤ ∑ X ∈ P, ∑ a ∈ Icc F (2 * F), lawProb μ (Ea ord μ t ε W k a X) :=
          sum_le_sum hsplit
      _ = ∑ a ∈ Icc F (2 * F), ∑ X ∈ P, lawProb μ (Ea ord μ t ε W k a X) := sum_comm
      _ ≤ ∑ a ∈ Icc F (2 * F), (P.card : ℝ) * (1536 * y) ^ a := sum_le_sum hper
      _ = _ := by rw [mul_sum]
  have htot2 : ∑ X ∈ P, lawProb μ (fun z =>
      (residual ord (lawSupport μ) t ε (W X) k z).card ≤ stageBudget t ε (k + 1) ∧
        F ≤ (residual ord (lawSupport μ) t ε (W X) (k + 1) z).card) ≤ (P.card : ℝ) := by
    calc _ ≤ ∑ X ∈ P, (1 : ℝ) := sum_le_sum fun X _ => lawProb_le_one μ _
      _ = (P.card : ℝ) := by simp
  have hrhs : (3072 * M ^ 2 / (r * γ ^ 2)) = 2 * (1536 * y) := by rw [hy]; ring
  rw [hrhs]
  exact arith_sum _ (Nat.cast_nonneg _) _ (by positivity) F hF1 _ htot htot2

end Final

end SpreadMatchCircuit.Matching.Dev.Eq3
end

section
namespace SpreadMatchCircuit.Matching.Dev.Lemma5

open Finset

section Fam
variable {β : Type} [DecidableEq β] [Fintype β] (sz : ℕ → ℕ)

/-- Union of a list of finsets. -/
def U : List (Finset β) → Finset β
  | [] => ∅
  | X :: l => X ∪ U l

omit [Fintype β] in
lemma mem_U {p : List (Finset β)} {x : β} : x ∈ U p ↔ ∃ Y ∈ p, x ∈ Y := by
  induction p with
  | nil => simp [U]
  | cons X l ih => simp [U, ih]

omit [Fintype β] in
lemma U_append (p : List (Finset β)) (X : Finset β) : U (p ++ [X]) = U p ∪ X := by
  ext x; simp [mem_U, or_comm]

/-- Ordered lists of `L` sets, the `k`-th of size `sz (p.length + k)`, pairwise disjoint and
disjoint from the sets of the prefix `p`, sampled one after another. -/
def Fam : List (Finset β) → ℕ → Finset (List (Finset β))
  | _, 0 => {[]}
  | p, L + 1 => (powersetCard (sz p.length) (univ \ U p)).biUnion
      fun X => (Fam (p ++ [X]) L).image (X :: ·)

lemma mem_Fam_succ {p : List (Finset β)} {L : ℕ} {l : List (Finset β)} :
    l ∈ Fam sz p (L + 1) ↔ ∃ X ∈ powersetCard (sz p.length) (univ \ U p),
      ∃ l' ∈ Fam sz (p ++ [X]) L, l = X :: l' := by
  simp only [Fam, mem_biUnion, mem_image]
  constructor
  · rintro ⟨X, hX, l', hl', rfl⟩; exact ⟨X, hX, l', hl', rfl⟩
  · rintro ⟨X, hX, l', hl', rfl⟩; exact ⟨X, hX, l', hl', rfl⟩

lemma Fam_props : ∀ (L : ℕ) (p l : List (Finset β)), l ∈ Fam sz p L →
    l.length = L ∧ Disjoint (U l) (U p) ∧ (U l).card = ∑ k ∈ range L, sz (p.length + k)
  | 0, p, l, h => by simp [Fam] at h; subst h; simp [U]
  | L + 1, p, l, h => by
    obtain ⟨X, hX, l', hl', rfl⟩ := (mem_Fam_succ sz).1 h
    obtain ⟨h1, h2, h3⟩ := Fam_props L _ _ hl'
    rw [mem_powersetCard, subset_sdiff] at hX
    rw [U_append, disjoint_union_right] at h2
    refine ⟨by simp [h1], ?_, ?_⟩
    · simp only [U]; exact disjoint_union_left.2 ⟨hX.1.2, h2.1⟩
    · simp only [U]
      rw [card_union_of_disjoint h2.2.symm, h3, hX.2, sum_range_succ']
      simp only [List.length_append, List.length_singleton, add_zero]
      rw [add_comm]; congr 1; apply sum_congr rfl; intro k _; congr 1; omega

/-- The count of `Fam`. -/
def gF (N : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 1
  | u, m, L + 1 => (N - u).choose (sz m) * gF N (u + sz m) (m + 1) L

lemma card_Fam : ∀ (L : ℕ) (p : List (Finset β)),
    (Fam sz p L).card = gF sz (Fintype.card β) (U p).card p.length L
  | 0, p => by simp [Fam, gF]
  | L + 1, p => by
    rw [Fam, card_biUnion]
    · have : ∀ X ∈ powersetCard (sz p.length) (univ \ U p),
          ((Fam sz (p ++ [X]) L).image (X :: ·)).card =
            gF sz (Fintype.card β) ((U p).card + sz p.length) (p.length + 1) L := by
        intro X hX
        rw [card_image_of_injective _ (List.cons_injective), card_Fam L]
        rw [mem_powersetCard, subset_sdiff] at hX
        rw [U_append, card_union_of_disjoint hX.1.2.symm, hX.2]
        simp
      rw [sum_congr rfl this, sum_const, card_powersetCard, card_univ_sdiff, smul_eq_mul, gF]
    · intro X _ Y _ hXY
      simp only [Function.onFun]
      rw [disjoint_left]
      intro l h1 h2
      simp only [mem_image] at h1 h2
      obtain ⟨_, _, rfl⟩ := h1
      obtain ⟨_, _, h⟩ := h2
      exact hXY (List.cons.inj h).1.symm

lemma gF_pos (N : ℕ) : ∀ (L u m : ℕ), u + ∑ k ∈ range L, sz (m + k) ≤ N → 0 < gF sz N u m L
  | 0, u, m, _ => by simp [gF]
  | L + 1, u, m, h => by
    rw [gF]
    rw [sum_range_succ'] at h
    apply Nat.mul_pos
    · apply Nat.choose_pos; simp at h; omega
    · apply gF_pos N L
      have : ∑ k ∈ range L, sz (m + 1 + k) = ∑ k ∈ range L, sz (m + (k + 1)) :=
        sum_congr rfl fun k _ => by congr 1; omega
      simp only [add_zero] at h
      omega

/-- Exponent bookkeeping. -/
def ex (K : Finset ℕ) (m L : ℕ) : ℕ := ∑ k ∈ range L, if m + k ∈ K then 1 else 0

lemma ex_succ (K : Finset ℕ) (m L : ℕ) :
    ex K m (L + 1) = ex K (m + 1) L + if m ∈ K then 1 else 0 := by
  unfold ex
  rw [sum_range_succ']
  simp only [add_zero]
  congr 1
  apply sum_congr rfl; intro k _
  rw [show m + (k + 1) = m + 1 + k by omega]

open scoped Classical in
/-- The chain (sequential Markov) bound. -/
theorem chain (A : List (Finset β) → Finset β → Prop) (K : Finset ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ p : List (Finset β), p.length ∈ K →
      (((powersetCard (sz p.length) (univ \ U p)).filter (A p)).card : ℝ) ≤
        b * (powersetCard (sz p.length) (univ \ U p)).card) :
    ∀ (L : ℕ) (p : List (Finset β)),
      (((Fam sz p L).filter fun l => ∀ k < L, p.length + k ∈ K →
          A (p ++ l.take k) (l.getD k ∅)).card : ℝ) ≤
        b ^ ex K p.length L * (Fam sz p L).card
  | 0, p => by simp [Fam, ex]
  | L + 1, p => by
    set P := powersetCard (sz p.length) (univ \ U p) with hP
    set c0 := gF sz (Fintype.card β) ((U p).card + sz p.length) (p.length + 1) L
    have hc : ∀ X ∈ P, (Fam sz (p ++ [X]) L).card = c0 := by
      intro X hX
      rw [card_Fam]
      rw [hP, mem_powersetCard, subset_sdiff] at hX
      rw [U_append, card_union_of_disjoint hX.1.2.symm, hX.2]
      simp [c0]
    have hcardF : ((Fam sz p (L + 1)).card : ℝ) = P.card * c0 := by
      rw [card_Fam, gF]; push_cast
      rw [hP, card_powersetCard, card_univ_sdiff]
    set T := fun (q : List (Finset β)) (l : List (Finset β)) =>
      ∀ k < L, q.length + k ∈ K → A (q ++ l.take k) (l.getD k ∅) with hT
    have key : ∀ X ∈ P, ((((Fam sz (p ++ [X]) L).image (X :: ·)).filter fun l =>
        ∀ k < L + 1, p.length + k ∈ K → A (p ++ l.take k) (l.getD k ∅)).card : ℝ) ≤
        (if p.length ∈ K → A p X then 1 else 0) * (b ^ ex K (p.length + 1) L * c0) := by
      intro X hX
      rw [filter_image]
      refine (Nat.cast_le.2 card_image_le).trans ?_
      split_ifs with hAX
      · rw [one_mul]
        have := chain A K b hb hA L (p ++ [X])
        rw [hc X hX] at this
        simp only [List.length_append, List.length_singleton] at this
        refine le_trans (Nat.cast_le.2 (card_le_card ?_)) this
        intro l hl
        simp only [mem_filter] at hl ⊢
        refine ⟨hl.1, fun k hk hkK => ?_⟩
        have := hl.2 (k + 1) (by omega) (by rw [show p.length + (k + 1) = p.length + 1 + k by omega]; exact hkK)
        simpa using this
      · rw [zero_mul]
        push Not at hAX
        have : ((Fam sz (p ++ [X]) L).filter fun a =>
            ∀ k < L + 1, p.length + k ∈ K → A (p ++ (X :: a).take k) ((X :: a).getD k ∅)) = ∅ := by
          apply filter_false_of_mem
          intro l _ h
          have := h 0 (by omega) (by simpa using hAX.1)
          simp at this
          exact hAX.2 this
        rw [this]; simp
    rw [hcardF, Fam, filter_biUnion]
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    refine (sum_le_sum key).trans ?_
    rw [← sum_mul, ex_succ]
    by_cases hK : p.length ∈ K
    · have h1 : (∑ X ∈ P, (if p.length ∈ K → A p X then (1 : ℝ) else 0)) =
          ((P.filter (A p)).card : ℝ) := by
        rw [card_filter]; push_cast
        apply sum_congr rfl; intro X _; simp [hK]
      rw [h1, if_pos hK, pow_succ]
      have := hA p hK
      have hc0 : (0 : ℝ) ≤ c0 := Nat.cast_nonneg _
      have hbp : (0 : ℝ) ≤ b ^ ex K (p.length + 1) L := pow_nonneg hb _
      calc ((P.filter (A p)).card : ℝ) * (b ^ ex K (p.length + 1) L * c0)
          ≤ (b * P.card) * (b ^ ex K (p.length + 1) L * c0) :=
            mul_le_mul_of_nonneg_right this (mul_nonneg hbp hc0)
        _ = _ := by ring
    · have h1 : (∑ X ∈ P, (if p.length ∈ K → A p X then (1 : ℝ) else 0)) = P.card := by
        simp [hK]
      rw [h1, if_neg hK, add_zero]; ring_nf; rfl

/-- Count of members of `Fam` inside a set `Y`. -/
def g2 : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 1
  | a, m, L + 1 => a.choose (sz m) * g2 (a - sz m) (m + 1) L

open scoped Classical in
lemma card_Fam_in (Y : Finset β) : ∀ (L : ℕ) (p : List (Finset β)),
    ((Fam sz p L).filter fun l => U l ⊆ Y).card = g2 sz (Y \ U p).card p.length L
  | 0, p => by simp [Fam, g2, filter_singleton, U]
  | L + 1, p => by
    rw [Fam, filter_biUnion]
    have hsplit : (powersetCard (sz p.length) (univ \ U p)).biUnion (fun X =>
          ((Fam sz (p ++ [X]) L).image (X :: ·)).filter fun l => U l ⊆ Y) =
        (powersetCard (sz p.length) (Y \ U p)).biUnion (fun X =>
          (((Fam sz (p ++ [X]) L).filter fun l => U l ⊆ Y).image (X :: ·))) := by
      ext l
      simp only [mem_biUnion, mem_filter, mem_image, mem_powersetCard, subset_sdiff]
      constructor
      · rintro ⟨X, ⟨⟨_, hd⟩, hc⟩, ⟨l', hl', rfl⟩, hY⟩
        simp only [U, union_subset_iff] at hY
        exact ⟨X, ⟨⟨hY.1, hd⟩, hc⟩, l', ⟨hl', hY.2⟩, rfl⟩
      · rintro ⟨X, ⟨⟨hXY, hd⟩, hc⟩, l', ⟨hl', hY⟩, rfl⟩
        refine ⟨X, ⟨⟨subset_univ _, hd⟩, hc⟩, ⟨l', hl', rfl⟩, ?_⟩
        simp only [U, union_subset_iff]; exact ⟨hXY, hY⟩
    rw [hsplit, card_biUnion]
    · have : ∀ X ∈ powersetCard (sz p.length) (Y \ U p),
          ((((Fam sz (p ++ [X]) L).filter fun l => U l ⊆ Y).image (X :: ·))).card =
            g2 sz ((Y \ U p).card - sz p.length) (p.length + 1) L := by
        intro X hX
        rw [card_image_of_injective _ (List.cons_injective), card_Fam_in Y L]
        rw [mem_powersetCard] at hX
        have hs : Y \ U (p ++ [X]) = (Y \ U p) \ X := by
          ext x; simp only [U_append, mem_sdiff, mem_union]; tauto
        rw [hs, card_sdiff_of_subset hX.1, hX.2]
        simp
      rw [sum_congr rfl this, sum_const, card_powersetCard, smul_eq_mul, g2]
    · intro X _ Z _ hXZ
      simp only [Function.onFun]
      rw [disjoint_left]
      intro l h1 h2
      simp only [mem_image] at h1 h2
      obtain ⟨_, _, rfl⟩ := h1
      obtain ⟨_, _, h⟩ := h2
      exact hXZ (List.cons.inj h).1.symm

/-- Comparison of the uniform `w`-set with the union of a random `Fam`, for a monotone event. -/
theorem compare (Ev : Finset β → Prop) [DecidablePred Ev] (hmono : ∀ Y Y', Y ⊆ Y' → Ev Y → Ev Y') (L w : ℕ)
    (hsum : ∑ k ∈ range L, sz k ≤ w) (hw : w ≤ Fintype.card β) :
    ((powersetCard w (univ : Finset β)).filter fun Y => ¬ Ev Y).card * (Fam sz ([] : List (Finset β)) L).card ≤
      ((Fam sz ([] : List (Finset β)) L).filter fun l => ¬ Ev (U l)).card * (powersetCard w (univ : Finset β)).card := by
  set P := powersetCard w (univ : Finset β)
  set F := Fam sz ([] : List (Finset β)) L
  set N0 := ∑ k ∈ range L, sz k
  have hUl : ∀ l ∈ F, (U l).card = N0 := by
    intro l hl; have := (Fam_props sz L [] l hl).2.2; simpa using this
  -- number of `Y ∈ P` above a given `l`
  set c1 := (Fintype.card β - N0).choose (w - N0)
  have hc1 : ∀ l ∈ F, (P.filter fun Y => U l ⊆ Y).card = c1 := by
    intro l hl
    have : (P.filter fun Y => U l ⊆ Y) =
        (powersetCard (w - N0) (univ \ U l)).image (fun Z => U l ∪ Z) := by
      ext Y
      simp only [P, mem_filter, mem_powersetCard, mem_image, subset_univ, true_and]
      constructor
      · rintro ⟨hY, hsub⟩
        refine ⟨Y \ U l, ⟨sdiff_subset_sdiff (subset_univ _) subset_rfl, ?_⟩, union_sdiff_of_subset hsub⟩
        rw [card_sdiff_of_subset hsub, hY, hUl l hl]
      · rintro ⟨Z, ⟨hZ, hZc⟩, rfl⟩
        rw [subset_sdiff] at hZ
        refine ⟨?_, subset_union_left⟩
        rw [card_union_of_disjoint hZ.2.symm, hUl l hl, hZc]
        have := card_le_univ (U l ∪ Z)
        rw [card_union_of_disjoint hZ.2.symm, hUl l hl, hZc] at this
        omega
    rw [this, card_image_of_injOn, card_powersetCard, card_univ_sdiff, hUl l hl]
    intro Z1 h1 Z2 h2 heq
    have h1 := (mem_powersetCard.1 (mem_coe.1 h1)).1
    have h2 := (mem_powersetCard.1 (mem_coe.1 h2)).1
    rw [subset_sdiff] at h1 h2
    have := congrArg (· \ U l) heq
    simp only [union_sdiff_left] at this
    rwa [sdiff_eq_self_of_disjoint h1.2, sdiff_eq_self_of_disjoint h2.2] at this
  have hc1pos : 0 < c1 := Nat.choose_pos (by omega)
  set c2 := g2 sz w 0 L
  have hc2 : ∀ Y ∈ P, (F.filter fun l => U l ⊆ Y).card = c2 := by
    intro Y hY
    rw [card_Fam_in]; simp only [U, sdiff_empty, List.length_nil]
    rw [mem_powersetCard] at hY; rw [hY.2]
  -- double counting
  have dc : ∀ (Pp : Finset (Finset β)) (Fp : Finset (List (Finset β))),
      ∑ Y ∈ Pp, (Fp.filter fun l => U l ⊆ Y).card = ∑ l ∈ Fp, (Pp.filter fun Y => U l ⊆ Y).card := by
    intro Pp Fp
    simp only [card_filter]
    exact sum_comm
  have e1 : P.card * c2 = F.card * c1 := by
    have := dc P F
    rw [sum_congr rfl hc2, sum_congr rfl hc1, sum_const, sum_const] at this
    simpa using this
  have e2 : (P.filter fun Y => ¬ Ev Y).card * c2 ≤ (F.filter fun l => ¬ Ev (U l)).card * c1 := by
    calc (P.filter fun Y => ¬ Ev Y).card * c2
        = ∑ Y ∈ P.filter (fun Y => ¬ Ev Y), (F.filter fun l => U l ⊆ Y).card := by
          rw [sum_congr rfl (fun Y hY => hc2 Y (mem_filter.1 hY).1), sum_const, smul_eq_mul]
      _ ≤ ∑ Y ∈ P, ((F.filter fun l => ¬ Ev (U l)).filter fun l => U l ⊆ Y).card := by
          refine (sum_le_sum ?_).trans (sum_le_sum_of_subset (filter_subset _ _))
          intro Y hY
          apply card_le_card
          intro l hl
          simp only [mem_filter] at hl ⊢
          exact ⟨⟨hl.1, fun h => (mem_filter.1 hY).2 (hmono _ _ hl.2 h)⟩, hl.2⟩
      _ = ∑ l ∈ F.filter (fun l => ¬ Ev (U l)), (P.filter fun Y => U l ⊆ Y).card := dc _ _
      _ = _ := by
          rw [sum_congr rfl (fun l hl => hc1 l (mem_filter.1 hl).1), sum_const, smul_eq_mul]
  have : (P.filter fun Y => ¬ Ev Y).card * F.card * c1 ≤
      (F.filter fun l => ¬ Ev (U l)).card * P.card * c1 := by
    calc (P.filter fun Y => ¬ Ev Y).card * F.card * c1
        = (P.filter fun Y => ¬ Ev Y).card * (P.card * c2) := by rw [e1]; ring
      _ = (P.filter fun Y => ¬ Ev Y).card * c2 * P.card := by ring
      _ ≤ (F.filter fun l => ¬ Ev (U l)).card * c1 * P.card := Nat.mul_le_mul_right _ e2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hc1pos

end Fam

end SpreadMatchCircuit.Matching.Dev.Lemma5

namespace SpreadMatchCircuit.Matching.Dev.Lemma5

open Finset

section Blk

/-- The schedule list, generically. -/
def blk (J : ℕ → ℕ) (Q : ℕ) : List (ℕ × ℕ) :=
  (List.range Q).flatMap fun i' => (List.range (J (i' + 1))).map fun j' => (i' + 1, j' + 1)

variable (J : ℕ → ℕ)

lemma blk_zero : blk J 0 = [] := by simp [blk]

lemma blk_succ (Q : ℕ) :
    blk J (Q + 1) = blk J Q ++ (List.range (J (Q + 1))).map fun j' => (Q + 1, j' + 1) := by
  simp [blk, List.range_succ, List.flatMap_append]

lemma blk_length (Q : ℕ) : (blk J Q).length = ∑ i ∈ range Q, J (i + 1) := by
  induction Q with
  | zero => simp [blk_zero]
  | succ Q ih => rw [blk_succ, List.length_append, ih, sum_range_succ]; simp

/-- the first coordinate of the `k`-th entry -/
def fst (Q k : ℕ) : ℕ := ((blk J Q).getD k (0, 0)).1

lemma fst_succ_lt (Q k : ℕ) (hk : k < (blk J Q).length) : fst J (Q + 1) k = fst J Q k := by
  unfold fst
  rw [blk_succ, List.getD_eq_getElem?_getD, List.getElem?_append_left hk,
    ← List.getD_eq_getElem?_getD]

lemma fst_succ_ge (Q k : ℕ) (hk : (blk J Q).length ≤ k) (hk2 : k < (blk J (Q + 1)).length) :
    fst J (Q + 1) k = Q + 1 := by
  unfold fst
  have h2 := hk2
  rw [blk_succ, List.length_append] at h2
  rw [blk_succ, List.getD_eq_getElem?_getD, List.getElem?_append_right hk]
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp

lemma fst_bounds (Q k : ℕ) (hk : k < (blk J Q).length) : 1 ≤ fst J Q k ∧ fst J Q k ≤ Q := by
  induction Q with
  | zero => simp [blk_zero] at hk
  | succ Q ih =>
    by_cases h : k < (blk J Q).length
    · rw [fst_succ_lt J Q k h]; have := ih h; omega
    · rw [fst_succ_ge J Q k (by omega) hk]; omega

lemma fst_mono (Q k k' : ℕ) (hkk : k ≤ k') (hk : k' < (blk J Q).length) :
    fst J Q k ≤ fst J Q k' := by
  induction Q with
  | zero => simp [blk_zero] at hk
  | succ Q ih =>
    by_cases h : k' < (blk J Q).length
    · rw [fst_succ_lt J Q k (by omega), fst_succ_lt J Q k' h]; exact ih h
    · rw [fst_succ_ge J Q k' (by omega) hk]
      by_cases h' : k < (blk J Q).length
      · rw [fst_succ_lt J Q k h']; have := fst_bounds J Q k h'; omega
      · rw [fst_succ_ge J Q k (by omega) (by omega)]

lemma fst_last (hJ : ∀ i, 1 ≤ i → 1 ≤ J i) (Q : ℕ) (hQ : 1 ≤ Q) :
    fst J Q ((blk J Q).length - 1) = Q := by
  obtain ⟨Q, rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  have h1 := hJ (Q + 1) (by omega)
  have : (blk J (Q + 1)).length = (blk J Q).length + J (Q + 1) := by
    rw [blk_succ, List.length_append]; simp
  apply fst_succ_ge <;> omega

lemma fst_zero (hJ : ∀ i, 1 ≤ i → 1 ≤ J i) (Q : ℕ) (hQ : 1 ≤ Q) : fst J Q 0 = 1 := by
  induction Q with
  | zero => omega
  | succ Q ih =>
    by_cases hQ0 : Q = 0
    · subst hQ0
      apply fst_succ_ge J 0 0 (by simp [blk_zero])
      rw [blk_succ, List.length_append]; simp [blk_zero]; exact hJ 1 le_rfl
    · have hl : 0 < (blk J Q).length := by
        rw [blk_length]
        exact lt_of_lt_of_le (hJ 1 le_rfl) (single_le_sum (f := fun i => J (i + 1))
          (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)))
      rw [fst_succ_lt J Q 0 hl]; exact ih (by omega)

lemma fst_step (hJ : ∀ i, 1 ≤ i → 1 ≤ J i) (Q k : ℕ) (hk : k + 1 < (blk J Q).length) :
    fst J Q (k + 1) ≤ fst J Q k + 1 := by
  induction Q with
  | zero => simp [blk_zero] at hk
  | succ Q ih =>
    by_cases h : k + 1 < (blk J Q).length
    · rw [fst_succ_lt J Q k (by omega), fst_succ_lt J Q (k + 1) h]; exact ih h
    · rw [fst_succ_ge J Q (k + 1) (by omega) hk]
      by_cases h' : k < (blk J Q).length
      · rw [fst_succ_lt J Q k h']
        have hQ : 1 ≤ Q := by
          by_contra hQ0; push Not at hQ0
          interval_cases Q; simp [blk_zero] at h'
        have := fst_last J hJ Q hQ
        rw [show k = (blk J Q).length - 1 by omega, this]
      · rw [fst_succ_ge J Q k (by omega) (by omega)]; omega

lemma sum_fst (g : ℕ → ℝ) (Q : ℕ) :
    ∑ k ∈ range (blk J Q).length, g (fst J Q k) = ∑ i ∈ range Q, (J (i + 1) : ℝ) * g (i + 1) := by
  induction Q with
  | zero => simp [blk_zero]
  | succ Q ih =>
    have hl : (blk J (Q + 1)).length = (blk J Q).length + J (Q + 1) := by
      rw [blk_succ, List.length_append]; simp
    rw [hl, sum_range_add, sum_range_succ, ← ih]
    congr 1
    · apply sum_congr rfl; intro k hk; rw [fst_succ_lt J Q k (mem_range.1 hk)]
    · rw [sum_congr rfl (g := fun _ => g (Q + 1))]
      · simp
      · intro x hx; rw [fst_succ_ge J Q _ (by omega) (by rw [hl]; simp at hx; omega)]

lemma count_fst (Q i : ℕ) (hi : 1 ≤ i) (hiQ : i ≤ Q) :
    ((range (blk J Q).length).filter fun k => fst J Q k = i).card = J i := by
  have := sum_fst J (fun x => if x = i then 1 else 0) Q
  rw [← Nat.cast_inj (R := ℝ), card_filter]
  push_cast
  rw [this]
  rw [sum_eq_single (i - 1)]
  · rw [show i - 1 + 1 = i by omega]; simp
  · intro b _ hb; rw [if_neg (by omega)]; simp
  · intro h; exact absurd (mem_range.2 (by omega)) h

lemma blk_nodup (Q : ℕ) : (blk J Q).Nodup := by
  induction Q with
  | zero => simp [blk_zero]
  | succ Q ih =>
    rw [blk_succ, List.nodup_append]
    refine ⟨ih, ?_, ?_⟩
    · apply List.Nodup.map (fun a b h => by simpa using h) (List.nodup_range)
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_map, List.mem_range] at hb
      obtain ⟨j, _, rfl⟩ := hb
      obtain ⟨k, hk, hk'⟩ := List.getElem_of_mem ha
      have := fst_bounds J Q k hk
      unfold fst at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] at this
      simp [hk'] at this

end Blk

end SpreadMatchCircuit.Matching.Dev.Lemma5

namespace SpreadMatchCircuit.Matching.Dev.Lemma5

open Finset

section Residual
variable {n : ℕ} (ord : LinearOrder (Finset (Edge n))) (𝒵 : Finset (Finset (Edge n))) (t ε : ℝ)

lemma chooseMu_spec (prev : Finset (Edge n) → Finset (Edge n)) (G : Finset (Edge n)) (b : ℕ)
    (z : Finset (Edge n)) :
    (chooseMu ord 𝒵 prev G b z ∈ 𝒵 ∧ prev (chooseMu ord 𝒵 prev G b z) ⊆ G ∪ prev z) ∨
      chooseMu ord 𝒵 prev G b z = z := by
  unfold chooseMu firstOf
  dsimp only
  split_ifs with h
  · left
    have h' := @Finset.min'_mem _ ord _ h
    rw [mem_filter, mem_filter] at h'
    exact ⟨h'.1.1, h'.1.2.1⟩
  · right; rfl

lemma residual_succ_subset (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ) (z : Finset (Edge n)) :
    residual ord 𝒵 t ε W (ℓ + 1) z ⊆ residual ord 𝒵 t ε W ℓ z := by
  simp only [residual]
  rcases chooseMu_spec ord 𝒵 (residual ord 𝒵 t ε W ℓ) (incident (flatWbar t ε W (ℓ + 1)))
    (stageBudget t ε (ℓ + 1)) z with h | h
  · intro e he
    rw [mem_sdiff] at he
    rcases mem_union.1 (h.2 he.1) with h' | h'
    · exact absurd h' he.2
    · exact h'
  · rw [h]; exact sdiff_subset

lemma incident_mono {A B : Finset (Fin n)} (h : A ⊆ B) : incident A ⊆ incident B := by
  intro e he
  simp only [incident, mem_filter, mem_univ, true_and] at he ⊢
  exact fun hd => he (hd.mono_right h)

lemma flatWbar_mono (W : ℕ → ℕ → Finset (Fin n)) {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') :
    flatWbar t ε W ℓ ⊆ flatWbar t ε W ℓ' := by
  unfold flatWbar
  exact biUnion_subset_biUnion_of_subset_left _ (Icc_subset_Icc le_rfl h)

lemma cover (W : ℕ → ℕ → Finset (Fin n)) :
    ∀ (ℓ : ℕ) (z : Finset (Edge n)), z ∈ 𝒵 → ∃ z' ∈ 𝒵,
      z' ⊆ incident (flatWbar t ε W ℓ) ∪ residual ord 𝒵 t ε W ℓ z
  | 0, z, hz => ⟨z, hz, by simp [residual]⟩
  | ℓ + 1, z, hz => by
    set u := chooseMu ord 𝒵 (residual ord 𝒵 t ε W ℓ) (incident (flatWbar t ε W (ℓ + 1)))
      (stageBudget t ε (ℓ + 1)) z
    have hu : u ∈ 𝒵 := by
      rcases chooseMu_spec ord 𝒵 (residual ord 𝒵 t ε W ℓ) (incident (flatWbar t ε W (ℓ + 1)))
        (stageBudget t ε (ℓ + 1)) z with h | h
      · exact h.1
      · rw [show u = z from h]; exact hz
    obtain ⟨z', hz', hsub⟩ := cover W ℓ u hu
    refine ⟨z', hz', ?_⟩
    have hmono := incident_mono (flatWbar_mono t ε W (Nat.le_succ ℓ))
    intro e he
    rcases mem_union.1 (hsub he) with h | h
    · exact mem_union_left _ (hmono h)
    · by_cases hG : e ∈ incident (flatWbar t ε W (ℓ + 1))
      · exact mem_union_left _ hG
      · apply mem_union_right
        simp only [residual]
        exact mem_sdiff.2 ⟨h, hG⟩

lemma residual_congr (W W' : ℕ → ℕ → Finset (Fin n)) (k : ℕ)
    (h : ∀ ℓ' ∈ Icc 1 k, flatW t ε W ℓ' = flatW t ε W' ℓ') :
    ∀ ℓ ≤ k, residual ord 𝒵 t ε W ℓ = residual ord 𝒵 t ε W' ℓ := by
  have hbar : ∀ ℓ ≤ k, flatWbar t ε W ℓ = flatWbar t ε W' ℓ := by
    intro ℓ hℓ
    unfold flatWbar
    apply biUnion_congr rfl
    intro x hx
    exact h x (by simp at hx ⊢; omega)
  intro ℓ hℓ
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    funext z
    simp only [residual]
    rw [ih (by omega), hbar (ℓ + 1) hℓ]

/-- The paper's event `E_ℓ`: `|π_{ℓ-1}(z)| ≤ 2^{q-i+1}` and `|π_ℓ(z)| ≥ 2^{q-i}`. -/
def EvK (W : ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ) (z : Finset (Edge n)) : Prop :=
  (residual ord 𝒵 t ε W (ℓ - 1) z).card ≤ stageBudget t ε ℓ ∧
    stageFloor t ε ℓ ≤ (residual ord 𝒵 t ε W ℓ z).card

/-- The family `W` built from a list of sets: `W_ℓ = l[ℓ-1]`. -/
noncomputable def Wof (l : List (Finset (Fin n))) : ℕ → ℕ → Finset (Fin n) :=
  fun i j => l.getD ((stages t ε).idxOf (i, j)) ∅

lemma stages_nodup_of (h : (stages t ε).Nodup) (l : List (Finset (Fin n))) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (h2 : ℓ ≤ numStages t ε) : flatW t ε (Wof t ε l) ℓ = l.getD (ℓ - 1) ∅ := by
  unfold flatW Wof stageAt
  have hk : ℓ - 1 < (stages t ε).length := by unfold numStages at h2; omega
  have hs : (stages t ε).getD (ℓ - 1) (0, 0) = (stages t ε)[ℓ - 1] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  rw [hs, Prod.mk.eta, List.Nodup.idxOf_getElem h _ hk]

lemma EvK_take (h : (stages t ε).Nodup) (l : List (Finset (Fin n))) (k : ℕ)
    (hk : k + 1 ≤ numStages t ε) (hkl : k < l.length) :
    EvK ord 𝒵 t ε (Wof t ε l) (k + 1) = EvK ord 𝒵 t ε (Wof t ε (l.take k ++ [l.getD k ∅])) (k + 1) := by
  have hc := residual_congr ord 𝒵 t ε (Wof t ε l) (Wof t ε (l.take k ++ [l.getD k ∅])) (k + 1)
    (by
      intro ℓ' hℓ'
      simp only [mem_Icc] at hℓ'
      rw [stages_nodup_of t ε h _ _ hℓ'.1 (by omega), stages_nodup_of t ε h _ _ hℓ'.1 (by omega)]
      have : l.take k ++ [l.getD k ∅] = l.take (k + 1) := by
        rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl]; simp
      rw [this]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      rw [if_pos (by omega)])
  funext z
  simp only [EvK, Nat.add_sub_cancel, hc k (by omega), hc (k + 1) le_rfl]

end Residual

end SpreadMatchCircuit.Matching.Dev.Lemma5

namespace SpreadMatchCircuit.Matching.Dev.Lemma5

open Finset

section Params
variable {t ε : ℝ}

lemma q_pos (ht : 1 < t) : 1 ≤ stageCount t := by
  unfold stageCount
  apply Nat.one_le_iff_ne_zero.2
  intro h
  rw [Nat.ceil_eq_zero] at h
  have : 0 < Real.logb 2 t := Real.logb_pos (by norm_num) ht
  linarith

lemma t_le_two_pow (ht : 1 < t) : t ≤ 2 ^ stageCount t := by
  have h : Real.logb 2 t ≤ (stageCount t : ℝ) := Nat.le_ceil _
  have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) h
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at this
  simpa using this

lemma two_pow_lt (ht : 1 < t) : (2 : ℝ) ^ stageCount t < 2 * t := by
  have h : (stageCount t : ℝ) < Real.logb 2 t + 1 :=
    Nat.ceil_lt_add_one (Real.logb_pos (by norm_num) ht).le
  have := Real.rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) h
  rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at this
  simpa [mul_comm] using this

lemma Lg_pos (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    0 < Real.log ((stageCount t : ℝ) / ε) := by
  apply Real.log_pos
  rw [one_lt_div hε₀]
  have : (1 : ℝ) ≤ stageCount t := by exact_mod_cast q_pos ht
  linarith

lemma J_pos (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) (i : ℕ) : 1 ≤ stageReps t ε i := by
  unfold stageReps
  apply Nat.one_le_iff_ne_zero.2
  rw [Ne, Nat.ceil_eq_zero, not_le]
  exact mul_pos (zpow_pos (by norm_num) _) (Lg_pos ht hε₀ hε)

lemma J_mul (i : ℕ) (hi : i ≤ stageCount t) :
    Real.log ((stageCount t : ℝ) / ε) ≤ (2 : ℝ) ^ (stageCount t - i) * stageReps t ε i := by
  unfold stageReps
  have h := Nat.le_ceil ((2 : ℝ) ^ ((i : ℤ) - (stageCount t : ℤ)) * Real.log ((stageCount t : ℝ) / ε))
  have h2 : (2 : ℝ) ^ (stageCount t - i) * (2 : ℝ) ^ ((i : ℤ) - (stageCount t : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    push_cast [Nat.cast_sub hi]; ring_nf; simp
  calc Real.log ((stageCount t : ℝ) / ε)
      = (2 : ℝ) ^ (stageCount t - i) *
          ((2 : ℝ) ^ ((i : ℤ) - (stageCount t : ℤ)) * Real.log ((stageCount t : ℝ) / ε)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

lemma rpow_half (q i : ℕ) (hi : i ≤ q) :
    (2 : ℝ) ^ (((q : ℝ) - (i : ℝ)) / 2) = Real.sqrt 2 ^ (q - i) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; push_cast [Nat.cast_sub hi]; ring

lemma M_pos (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) : 0 < stageWeight t ε := by
  unfold stageWeight
  apply sum_pos
  · intro i _
    have := J_pos ht hε₀ hε i
    have : (1 : ℝ) ≤ stageReps t ε i := by exact_mod_cast this
    positivity
  · exact ⟨1, by simp; exact q_pos ht⟩

lemma log_sq_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_sqrt hx0.le] at h1
  have h2 : Real.log x ≤ 2 * Real.sqrt x := by linarith
  have h := Real.log_nonneg hx
  calc Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ h h2 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt hx0.le]; ring

/-- Eq. (1): `M² ≤ C₂ (t + log²(1/ε))`. -/
lemma M_sq_le (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    stageWeight t ε ^ 2 ≤ 600 * (t + Real.log (1 / ε) ^ 2) := by
  set q := stageCount t
  set Lg := Real.log ((q : ℝ) / ε)
  set ρ := Real.sqrt 2
  have hρ2 : ρ ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : 4 / 3 ≤ ρ := by nlinarith
  have hLg := Lg_pos ht hε₀ hε
  -- each term
  have hterm : ∀ i ∈ Icc 1 q, (stageReps t ε i : ℝ) * (2 : ℝ) ^ (((q : ℝ) - (i : ℝ)) / 2) ≤
      ρ ^ (q - i) + Lg * (ρ⁻¹) ^ (q - i) := by
    intro i hi
    rw [mem_Icc] at hi
    rw [rpow_half q i hi.2]
    have hJ : (stageReps t ε i : ℝ) < (2 : ℝ) ^ ((i : ℤ) - (q : ℤ)) * Lg + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (2 : ℝ) ^ ((i : ℤ) - (q : ℤ)) * ρ ^ (q - i) = (ρ⁻¹) ^ (q - i) := by
      rw [← hρ2, ← zpow_natCast, ← zpow_mul, inv_pow, ← zpow_natCast]
      rw [← zpow_neg, ← zpow_add₀ hρ0.ne']
      congr 1; push_cast [Nat.cast_sub hi.2]; ring
    calc (stageReps t ε i : ℝ) * ρ ^ (q - i) ≤ ((2 : ℝ) ^ ((i : ℤ) - (q : ℤ)) * Lg + 1) * ρ ^ (q - i) :=
          mul_le_mul_of_nonneg_right hJ.le (by positivity)
      _ = Lg * ((2 : ℝ) ^ ((i : ℤ) - (q : ℤ)) * ρ ^ (q - i)) + ρ ^ (q - i) := by ring
      _ = _ := by rw [h2]; ring
  have hsum : stageWeight t ε ≤ ∑ i ∈ Icc 1 q, (ρ ^ (q - i) + Lg * (ρ⁻¹) ^ (q - i)) :=
    sum_le_sum hterm
  -- reindex
  have hre : ∀ g : ℕ → ℝ, ∑ i ∈ Icc 1 q, g (q - i) = ∑ m ∈ range q, g m := by
    intro g
    apply sum_nbij' (fun i => q - i) (fun m => q - m)
    · intro i hi; simp at hi ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro i hi; simp at hi ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro i _; rfl
  rw [sum_add_distrib, hre (fun m => ρ ^ m), ← mul_sum, hre (fun m => (ρ⁻¹) ^ m)] at hsum
  have hg1 : ∑ m ∈ range q, ρ ^ m ≤ 3 * ρ ^ q := by
    rw [geom_sum_eq (by nlinarith)]
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [pow_pos hρ0 q]
  have hg2 : ∑ m ∈ range q, (ρ⁻¹) ^ m ≤ 4 := by
    have hi : ρ⁻¹ ≤ 3 / 4 := by rw [inv_le_comm₀ hρ0 (by norm_num)]; linarith
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := q) (inv_nonneg.2 hρ0.le) (by linarith)
    rw [← range_eq_Ico] at this
    refine this.trans ?_
    rw [pow_zero, div_le_iff₀ (by linarith)]; linarith
  have hρq : (ρ ^ q) ^ 2 ≤ 2 * t := by
    rw [← pow_mul, mul_comm, pow_mul, hρ2]; exact (two_pow_lt ht).le
  have hM0 := M_pos ht hε₀ hε
  have hM : stageWeight t ε ≤ 3 * ρ ^ q + 4 * Lg := by nlinarith
  -- Lg² bound
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast q_pos ht
  have hLgeq : Lg = Real.log q + Real.log (1 / ε) := by
    simp only [Lg]
    rw [div_eq_mul_one_div (q : ℝ) ε, Real.log_mul (by positivity) (by positivity)]
  have hlogq : Real.log q ^ 2 ≤ 4 * q := log_sq_le q hq1
  have hqt : (q : ℝ) ≤ 2 * t := by
    have h1 : (q : ℝ) < Real.logb 2 t + 1 := Nat.ceil_lt_add_one (Real.logb_pos (by norm_num) ht).le
    have h2 : Real.logb 2 t ≤ (t - 1) / Real.log 2 := by
      rw [Real.logb]; exact div_le_div_of_nonneg_right (Real.log_le_sub_one_of_pos (by linarith))
        (Real.log_pos (by norm_num)).le
    have h3 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have h4 : (t - 1) / Real.log 2 ≤ 2 * (t - 1) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hle0 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε₀]; linarith)
  nlinarith [sq_nonneg (3 * ρ ^ q - 4 * Lg), sq_nonneg (Real.log q - Real.log (1 / ε)),
    pow_pos hρ0 q]

lemma sum_JS_le {n : ℕ} {γ : ℝ} (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) (hγ : 0 ≤ γ) :
    ∑ i ∈ Icc 1 (stageCount t), (stageReps t ε i : ℝ) * (stageSize n t ε γ i : ℝ) ≤ γ * n := by
  have hM := M_pos ht hε₀ hε
  calc ∑ i ∈ Icc 1 (stageCount t), (stageReps t ε i : ℝ) * (stageSize n t ε γ i : ℝ)
      ≤ ∑ i ∈ Icc 1 (stageCount t), (stageReps t ε i : ℝ) *
          (γ * (n : ℝ) * (2 : ℝ) ^ (((stageCount t : ℝ) - (i : ℝ)) / 2) / stageWeight t ε) := by
        apply sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Nat.floor_le (by positivity)
    _ = γ * n / stageWeight t ε * stageWeight t ε := by
        rw [stageWeight, mul_sum]; apply sum_congr rfl; intro i _; field_simp
    _ = γ * n := by field_simp

lemma S_pos {n : ℕ} {γ : ℝ} (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    (h : stageWeight t ε ≤ γ * n) (i : ℕ) (hi : i ≤ stageCount t) : 1 ≤ stageSize n t ε γ i := by
  have hM := M_pos ht hε₀ hε
  unfold stageSize
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ hM, one_mul]
  have : (1 : ℝ) ≤ (2 : ℝ) ^ (((stageCount t : ℝ) - (i : ℝ)) / 2) := by
    apply Real.one_le_rpow (by norm_num)
    have : (i : ℝ) ≤ stageCount t := by exact_mod_cast hi
    linarith
  nlinarith

end Params

end SpreadMatchCircuit.Matching.Dev.Lemma5

namespace SpreadMatchCircuit.Matching.Dev.Lemma5

open Finset

section Prob
variable {α : Type} [Fintype α] (μ : PMF α)

open scoped Classical in
lemma lawProb_eq (A : α → Prop) : lawProb μ A = ∑ x, if A x then (μ x).toReal else 0 := by
  unfold lawProb; rw [sum_filter]

lemma lawProb_nonneg (A : α → Prop) : 0 ≤ lawProb μ A := by
  unfold lawProb; exact sum_nonneg fun _ _ => ENNReal.toReal_nonneg

lemma sum_toReal : ∑ x, (μ x).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top μ x)]
  have := μ.tsum_coe
  rw [tsum_fintype] at this
  rw [this]; simp

lemma lawProb_mono {A B : α → Prop} (h : ∀ x, A x → B x) : lawProb μ A ≤ lawProb μ B := by
  classical
  rw [lawProb_eq, lawProb_eq]
  apply sum_le_sum; intro x _
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h x h1) h2
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

lemma lawProb_compl (A : α → Prop) : lawProb μ A + lawProb μ (fun x => ¬ A x) = 1 := by
  classical
  rw [lawProb_eq, lawProb_eq, ← sum_add_distrib, ← sum_toReal μ]
  apply sum_congr rfl; intro x _; split_ifs <;> simp

lemma lawProb_union {ι : Type} (s : Finset ι) (A : ι → α → Prop) :
    lawProb μ (fun x => ∃ i ∈ s, A i x) ≤ ∑ i ∈ s, lawProb μ (A i) := by
  classical
  simp only [lawProb_eq]
  rw [sum_comm]
  apply sum_le_sum; intro x _
  split_ifs with h
  · obtain ⟨i, hi, hA⟩ := h
    calc (μ x).toReal = if A i x then (μ x).toReal else 0 := by rw [if_pos hA]
      _ ≤ _ := single_le_sum (f := fun i => if A i x then (μ x).toReal else 0)
          (fun j _ => by split_ifs <;> simp) hi
  · exact sum_nonneg fun j _ => by split_ifs <;> simp

lemma exists_of_lawProb (P : α → Prop) (h : lawProb μ (fun x => ¬ P x) < 1) :
    ∃ x ∈ lawSupport μ, P x := by
  classical
  have h1 := lawProb_compl μ P
  have h2 : 0 < lawProb μ P := by linarith
  rw [lawProb] at h2
  by_contra hne
  push Not at hne
  have : ∑ x ∈ univ.filter P, (μ x).toReal = 0 := by
    apply sum_eq_zero
    intro x hx
    have hP := (mem_filter.1 hx).2
    have : x ∉ lawSupport μ := fun h => hne x h hP
    simp only [lawSupport, mem_filter, mem_univ, true_and, PMF.mem_support_iff, not_not] at this
    simp [this]
  linarith

end Prob

end SpreadMatchCircuit.Matching.Dev.Lemma5

namespace SpreadMatchCircuit.Matching.Dev.Lemma5

open Finset

section Misc
variable {n : ℕ}

lemma card_edge_le : (Fintype.card (Edge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : Fintype.card (Edge n) = (Fintype.card (Fin n)).choose 2 := by
    convert Sym2.card_subtype_not_diag (α := Fin n)
  rw [h, Fintype.card_fin]
  exact_mod_cast Nat.choose_le_pow n 2

lemma r_le (μ : PMF (Finset (Edge n))) (r : ℝ) (hr : 0 < r) (hsp : IsSpread μ r)
    (hne : ∀ z ∈ lawSupport μ, z.Nonempty) : r ≤ (n : ℝ) ^ 2 := by
  classical
  have h1 : ∀ e : Edge n, lawProb μ (fun z => e ∈ z) ≤ r⁻¹ := by
    intro e
    have := hsp {e} (by intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab)
    simpa using this
  have h2 : (1 : ℝ) ≤ ∑ e : Edge n, lawProb μ (fun z => e ∈ z) := by
    simp only [lawProb_eq]
    rw [sum_comm, ← sum_toReal μ]
    apply sum_le_sum; intro z _
    by_cases hz : μ z = 0
    · rw [hz]; simp
    · have hzs : z ∈ lawSupport μ := by
        simp [lawSupport, PMF.mem_support_iff, hz]
      obtain ⟨e, he⟩ := hne z hzs
      calc (μ z).toReal = if e ∈ z then (μ z).toReal else 0 := by rw [if_pos he]
        _ ≤ ∑ x, if x ∈ z then (μ z).toReal else 0 :=
            single_le_sum (f := fun e => if e ∈ z then (μ z).toReal else 0)
            (fun j _ => by split_ifs <;> simp) (mem_univ e)
        _ = _ := by apply sum_congr rfl; intro x _; split_ifs <;> rfl
  have h3 : ∑ e : Edge n, lawProb μ (fun z => e ∈ z) ≤ Fintype.card (Edge n) * r⁻¹ := by
    calc _ ≤ ∑ _e : Edge n, r⁻¹ := sum_le_sum fun e _ => h1 e
      _ = _ := by simp
  have h4 : (1 : ℝ) ≤ Fintype.card (Edge n) * r⁻¹ := h2.trans h3
  rw [← div_eq_mul_inv, le_div_iff₀ hr, one_mul] at h4
  exact h4.trans card_edge_le

/-- Block argument (the paper's final union bound, deterministic part). -/
lemma block_arg (q L : ℕ) (f σ : ℕ → ℕ) (hL : 1 ≤ L) (hf0 : f 0 = 1) (hfL : f (L - 1) = q)
    (hfb : ∀ k < L, 1 ≤ f k ∧ f k ≤ q) (hmono : ∀ k k', k ≤ k' → k' < L → f k ≤ f k')
    (hstep : ∀ k, k + 1 < L → f (k + 1) ≤ f k + 1) (hσ : ∀ k, σ (k + 1) ≤ σ k)
    (hσ0 : σ 0 ≤ 2 ^ q)
    (H : ∀ i ∈ Icc 1 q, ∃ k < L, f k = i ∧ ¬(σ k ≤ 2 ^ (q - f k + 1) ∧ 2 ^ (q - f k) ≤ σ (k + 1))) :
    σ L = 0 := by
  have P : ∀ k < L, σ k ≤ 2 ^ (q - f k + 1) ∧
      ((∃ k' ≤ k, f k' = f k ∧ ¬(σ k' ≤ 2 ^ (q - f k' + 1) ∧ 2 ^ (q - f k') ≤ σ (k' + 1))) →
        σ (k + 1) < 2 ^ (q - f k)) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨by rw [hf0]; have := hfb 0 hL; simpa [Nat.sub_add_cancel (show 1 ≤ q by omega)] using hσ0, ?_⟩
      rintro ⟨k', hk', -, hn⟩
      obtain rfl : k' = 0 := by omega
      have : σ 0 ≤ 2 ^ (q - f 0 + 1) := by
        rw [hf0]; have := hfb 0 hL; simpa [Nat.sub_add_cancel (show 1 ≤ q by omega)] using hσ0
      by_contra hc; exact hn ⟨this, by omega⟩
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hfk := hfb k (by omega)
      have hfk1 := hfb (k + 1) hk
      have hm := hmono k (k + 1) (by omega) hk
      have hs := hstep k hk
      by_cases heq : f (k + 1) = f k
      · have first : σ (k + 1) ≤ 2 ^ (q - f (k + 1) + 1) := by
          rw [heq]; exact (hσ k).trans ih1
        refine ⟨first, ?_⟩
        rintro ⟨k', hk', hfk', hn⟩
        by_cases hkk : k' = k + 1
        · subst hkk
          by_contra hc; exact hn ⟨first, by omega⟩
        · have := ih2 ⟨k', by omega, by rw [hfk', heq], hn⟩
          rw [heq]; exact lt_of_le_of_lt (hσ (k + 1)) this
      · have heq' : f (k + 1) = f k + 1 := by omega
        obtain ⟨k', hk'L, hfk', hn⟩ := H (f k) (by simp; omega)
        have hk'k : k' ≤ k := by
          by_contra hc
          have := hmono (k + 1) k' (by omega) hk'L
          omega
        have hlt := ih2 ⟨k', hk'k, hfk', hn⟩
        have first : σ (k + 1) ≤ 2 ^ (q - f (k + 1) + 1) := by
          rw [heq', show q - (f k + 1) + 1 = q - f k by omega]; exact hlt.le
        refine ⟨first, ?_⟩
        rintro ⟨k'', hk'', hfk'', hn'⟩
        by_cases hkk : k'' = k + 1
        · subst hkk
          by_contra hc; exact hn' ⟨first, by omega⟩
        · have := hmono k'' k (by omega) (by omega)
          omega
  obtain ⟨k', hk'L, hfk', hn⟩ := H q (by simp; have := hfb 0 hL; omega)
  have := (P (L - 1) (by omega)).2 ⟨k', by omega, by rw [hfk', hfL], hn⟩
  rw [hfL, Nat.sub_self, pow_zero, show L - 1 + 1 = L by omega] at this
  omega

lemma U_eq {β : Type} [DecidableEq β] (p : List (Finset β)) :
    U p = (Ico 1 (p.length + 1)).biUnion fun ℓ' => p.getD (ℓ' - 1) ∅ := by
  ext x
  simp only [mem_U, mem_biUnion, mem_Ico]
  constructor
  · rintro ⟨Y, hY, hx⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hY
    refine ⟨k + 1, by omega, ?_⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using hx
  · rintro ⟨ℓ', hℓ', hx⟩
    have hk : ℓ' - 1 < p.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] at hx
    exact ⟨_, List.getElem_mem hk, hx⟩

end Misc

section Assembly
variable {n : ℕ}

lemma stageAt_fst (t ε : ℝ) (k : ℕ) :
    (stageAt t ε (k + 1)).1 = fst (stageReps t ε) (stageCount t) k := by
  simp only [stageAt, fst, Nat.add_sub_cancel]; rfl

lemma stages_nodup (t ε : ℝ) : (stages t ε).Nodup := blk_nodup _ _

lemma flatWbar_Wof (t ε : ℝ) (l : List (Finset (Fin n))) (hl : l.length = numStages t ε) :
    flatWbar t ε (Wof t ε l) (numStages t ε) = U l := by
  unfold flatWbar
  rw [U_eq, hl]
  have : Icc 1 (numStages t ε) = Ico 1 (numStages t ε + 1) := by ext; simp
  rw [this]
  apply biUnion_congr rfl
  intro ℓ hℓ
  simp only [mem_Ico] at hℓ
  exact stages_nodup_of t ε (stages_nodup t ε) l ℓ hℓ.1 (by omega)

lemma good_cover (ord : LinearOrder (Finset (Edge n))) (μ : PMF (Finset (Edge n))) (t ε : ℝ)
    (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) (hμ : IsBoundedMatchingLaw μ t)
    (l : List (Finset (Fin n))) (hl : l.length = numStages t ε) (δ : ℕ → ℝ)
    (hδ : ∑ i ∈ Icc 1 (stageCount t), δ i < 1)
    (hgood : ∀ i ∈ Icc 1 (stageCount t), ∃ k < numStages t ε,
      fst (stageReps t ε) (stageCount t) k = i ∧
      lawProb μ (EvK ord (lawSupport μ) t ε (Wof t ε l) (k + 1)) ≤ δ i) :
    ∃ z ∈ lawSupport μ, z ⊆ incident (U l) := by
  set q := stageCount t with hq
  set J := stageReps t ε with hJdef
  set L := numStages t ε with hLdef
  have hJ : ∀ i, 1 ≤ i → 1 ≤ J i := fun i _ => J_pos ht hε₀ hε i
  have hq1 : 1 ≤ q := q_pos ht
  have hLeq : L = (blk J q).length := rfl
  choose! kf hkf using hgood
  have hL1 : 1 ≤ L := by have := (hkf 1 (by simp; omega)).1; omega
  have key : ∀ z, z ∈ lawSupport μ → residual ord (lawSupport μ) t ε (Wof t ε l) L z ≠ ∅ →
      ∃ i ∈ Icc 1 q, EvK ord (lawSupport μ) t ε (Wof t ε l) (kf i + 1) z := by
    intro z hz hne
    by_contra hcon
    push Not at hcon
    apply hne
    have hσ0 : (z.card) ≤ 2 ^ q := by
      have h1 := (hμ z hz).2
      have h2 := t_le_two_pow ht
      have : (z.card : ℝ) ≤ (2 : ℝ) ^ q := h1.trans h2
      exact_mod_cast this
    have := block_arg q L (fst J q) (fun k => (residual ord (lawSupport μ) t ε (Wof t ε l) k z).card)
      hL1 (fst_zero J hJ q hq1) (by rw [hLeq]; exact fst_last J hJ q hq1)
      (fun k hk => fst_bounds J q k (by rw [← hLeq]; exact hk))
      (fun k k' h h' => fst_mono J q k k' h (by rw [← hLeq]; exact h'))
      (fun k hk => fst_step J hJ q k (by rw [← hLeq]; exact hk))
      (fun k => card_le_card (residual_succ_subset ord _ t ε _ k z))
      (by simpa [residual] using hσ0)
      (fun i hi => ⟨kf i, (hkf i hi).1, (hkf i hi).2.1, by
        have := hcon i hi
        simp only [EvK, stageBudget, stageFloor, stageAt_fst, Nat.add_sub_cancel] at this
        exact this⟩)
    exact card_eq_zero.1 this
  have hprob : lawProb μ (fun z => ¬ (z ∈ lawSupport μ →
      residual ord (lawSupport μ) t ε (Wof t ε l) L z = ∅)) < 1 := by
    calc _ ≤ lawProb μ (fun z => ∃ i ∈ Icc 1 q, EvK ord (lawSupport μ) t ε (Wof t ε l) (kf i + 1) z) :=
          lawProb_mono μ (fun z hz => by
            push Not at hz
            exact key z hz.1 (nonempty_iff_ne_empty.1 hz.2))
      _ ≤ ∑ i ∈ Icc 1 q, lawProb μ (EvK ord (lawSupport μ) t ε (Wof t ε l) (kf i + 1)) :=
          lawProb_union μ _ _
      _ ≤ ∑ i ∈ Icc 1 q, δ i := sum_le_sum fun i hi => (hkf i hi).2.2
      _ < 1 := hδ
  obtain ⟨z, hz, hres⟩ := exists_of_lawProb μ _ hprob
  obtain ⟨z', hz', hsub⟩ := cover ord (lawSupport μ) t ε (Wof t ε l) L z hz
  rw [hres hz, union_empty, flatWbar_Wof t ε l hl] at hsub
  exact ⟨z', hz', hsub⟩

lemma qe_lt (q : ℕ) (ε : ℝ) (hq1 : 1 ≤ q) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    (q : ℝ) * (ε / q) ^ 2 < ε := by
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
  have h1 : (q : ℝ) * ε ^ 2 < q * ε := mul_lt_mul_of_pos_left (by nlinarith) (by linarith)
  have h2 : (q : ℝ) * ε ≤ ε * q ^ 2 := by nlinarith
  linarith

lemma log16 : 2 ≤ Real.log 16 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [Real.exp_pos 1]

lemma delta_pow (t ε : ℝ) (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) (i : ℕ)
    (hi : i ≤ stageCount t) :
    (((16 : ℝ) ^ (2 ^ (stageCount t - i)))⁻¹) ^ stageReps t ε i ≤ (ε / stageCount t) ^ 2 := by
  set q := stageCount t
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast q_pos ht
  have hLg := Lg_pos ht hε₀ hε
  have hN := J_mul (ε := ε) i hi
  rw [← inv_pow, ← pow_mul]
  set N := 2 ^ (q - i) * stageReps t ε i
  have hN' : Real.log ((q : ℝ) / ε) ≤ (N : ℝ) := by simpa [N] using hN
  have h16 : ((q : ℝ) / ε) ^ 2 ≤ (16 : ℝ) ^ N := by
    have e1 : ((q : ℝ) / ε) ^ 2 = Real.exp (2 * Real.log ((q : ℝ) / ε)) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
    have e2 : (16 : ℝ) ^ N = Real.exp (N * Real.log 16) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e1, e2, Real.exp_le_exp]
    have := log16
    nlinarith
  rw [inv_pow, inv_le_comm₀ (by positivity) (by positivity), ← inv_pow, inv_div]
  exact h16

lemma sum_delta (q : ℕ) : ∑ i ∈ Icc 1 q, ((16 : ℝ) ^ (2 ^ (q - i)))⁻¹ < 1 := by
  have h1 : ∀ i ∈ Icc 1 q, ((16 : ℝ) ^ (2 ^ (q - i)))⁻¹ ≤ (1 / 16) * (1 / 16 : ℝ) ^ (q - i) := by
    intro i _
    rw [← pow_succ', one_div_pow, one_div]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.lt_two_pow_self
  have hre : ∑ i ∈ Icc 1 q, (1 / 16 : ℝ) * (1 / 16 : ℝ) ^ (q - i) =
      ∑ m ∈ range q, (1 / 16 : ℝ) * (1 / 16 : ℝ) ^ m := by
    apply sum_nbij' (fun i => q - i) (fun m => q - m)
    · intro i hi; simp at hi ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro i hi; simp at hi ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro i _; rfl
  have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := q) (x := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
  rw [← range_eq_Ico] at hg
  calc _ ≤ _ := sum_le_sum h1
    _ = _ := hre
    _ = (1 / 16) * ∑ m ∈ range q, (1 / 16 : ℝ) ^ m := by rw [mul_sum]
    _ ≤ (1 / 16) * ((1 / 16) ^ 0 / (1 - 1 / 16)) := by gcongr
    _ < 1 := by norm_num

end Assembly

end SpreadMatchCircuit.Matching.Dev.Lemma5

namespace SpreadMatchCircuit.Matching

open Finset Dev.Lemma5

/-- **Eq. (3)** of the source (the key technical bound), stated as a stand-alone statement:
there is a constant `α₃ > 0` such that for every stage `ℓ = k(i, j)`, every choice of the
earlier sets `W_1, …, W_{ℓ-1}` (given by `V`), and every family `W X` whose earlier sets are `V`
and whose `ℓ`-th set is `X`, the average over the `S_i`-subsets `X` of `[n] \ W̄_{ℓ-1}` of the
probability (over `Z ∼ μ`) of `E_ℓ` is at most `(α₃ M² / (r γ²))^{2^{q-i}}`. -/
def Eq3Statement : Prop :=
  ∃ α₃ : ℝ, 0 < α₃ ∧
    ∀ (n : ℕ) (μ : PMF (Finset (Edge n))) (t ε γ r : ℝ) (ord : LinearOrder (Finset (Edge n)))
      (V : ℕ → Finset (Fin n)) (W : Finset (Fin n) → ℕ → ℕ → Finset (Fin n)) (ℓ : ℕ),
      1 < t → 0 < ε → ε < 1 / 2 → 0 < γ → γ ≤ 1 → 0 < r →
      IsBoundedMatchingLaw μ t → IsSpread μ r →
      (∀ i ∈ Icc 1 (stageCount t), 1 ≤ stageSize n t ε γ i) →
      1 ≤ ℓ → ℓ ≤ numStages t ε →
      (∀ X, ∀ ℓ' ∈ Ico 1 ℓ, flatW t ε (W X) ℓ' = V ℓ') →
      (∀ X, flatW t ε (W X) ℓ = X) →
      ∑ X ∈ powersetCard (stageSize n t ε γ (stageAt t ε ℓ).1) (univ \ (Ico 1 ℓ).biUnion V),
          lawProb μ (EvK ord (lawSupport μ) t ε (W X) ℓ) ≤
        (α₃ * stageWeight t ε ^ 2 / (r * γ ^ 2)) ^ stageFloor t ε ℓ *
          ((powersetCard (stageSize n t ε γ (stageAt t ε ℓ).1)
            (univ \ (Ico 1 ℓ).biUnion V)).card : ℝ)

/-- Lemma 5 from Eq. (3). -/
theorem chk_lemma_5_of_eq3 (h3 : Eq3Statement) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (μ : PMF (Finset (Edge n))) (ε t γ r : ℝ) (w : ℕ),
        0 < ε → ε < 1 / 2 → 1 < t → 0 < γ → γ ≤ 1 → (w : ℝ) = γ * (n : ℝ) →
        r = α * (t + Real.log (1 / ε) ^ 2) / γ ^ 2 →
        IsBoundedMatchingLaw μ t → IsSpread μ r →
        1 - ε < uniformProb (Finset.powersetCard w (Finset.univ : Finset (Fin n)))
          (fun W => ∃ z ∈ lawSupport μ, z ⊆ incident W) := by
  obtain ⟨α₃, hα₃, H3⟩ := h3
  refine ⟨600 * (256 * α₃ + 1), by positivity, ?_⟩
  intro n μ ε t γ r w hε₀ hε ht hγ₀ hγ₁ hw hr hμ hsp
  classical
  set α := 600 * (256 * α₃ + 1) with hα
  have hwn : w ≤ n := by
    have : (w : ℝ) ≤ n := by rw [hw]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact_mod_cast this
  set Ev : Finset (Fin n) → Prop := fun Y => ∃ z ∈ lawSupport μ, z ⊆ incident Y with hEv
  set P := powersetCard w (univ : Finset (Fin n)) with hP
  have hPpos : 0 < P.card := by
    rw [hP, card_powersetCard, card_univ, Fintype.card_fin]; exact Nat.choose_pos hwn
  have hunif : uniformProb P Ev = 1 - ((P.filter fun Y => ¬ Ev Y).card : ℝ) / P.card := by
    unfold uniformProb
    have := card_filter_add_card_filter_not (s := P) Ev
    have hP0 : (P.card : ℝ) ≠ 0 := by exact_mod_cast hPpos.ne'
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hP0]
    norm_cast
    convert this using 4
  -- trivial case
  by_cases h0 : (∅ : Finset (Edge n)) ∈ lawSupport μ
  · have : (P.filter fun Y => ¬ Ev Y) = ∅ := by
      apply filter_false_of_mem
      intro Y _ h; exact h ⟨∅, h0, empty_subset _⟩
    show 1 - ε < uniformProb P Ev
    rw [hunif, this]; simp; linarith
  have hne : ∀ z ∈ lawSupport μ, z.Nonempty := fun z hz =>
    nonempty_iff_ne_empty.2 (fun h => h0 (h ▸ hz))
  set T := t + Real.log (1 / ε) ^ 2 with hT
  have hT0 : 0 < T := by positivity
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrγ : r * γ ^ 2 = α * T := by rw [hr]; field_simp
  have hrn := r_le μ r hr0 hsp hne
  have hM2 := M_sq_le ht hε₀ hε
  have hM0 := M_pos ht hε₀ hε
  have hMγ : stageWeight t ε ≤ γ * n := by
    have h1 : stageWeight t ε ^ 2 ≤ (γ * n) ^ 2 := by
      calc stageWeight t ε ^ 2 ≤ 600 * T := hM2
        _ ≤ α * T := by apply mul_le_mul_of_nonneg_right _ hT0.le; rw [hα]; nlinarith
        _ = r * γ ^ 2 := hrγ.symm
        _ ≤ (n : ℝ) ^ 2 * γ ^ 2 := mul_le_mul_of_nonneg_right hrn (by positivity)
        _ = (γ * n) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ hM0.le (by positivity) two_ne_zero).1 h1
  have hS : ∀ i ∈ Icc 1 (stageCount t), 1 ≤ stageSize n t ε γ i :=
    fun i hi => S_pos ht hε₀ hε hMγ i (mem_Icc.1 hi).2
  have hx0 : 0 ≤ α₃ * stageWeight t ε ^ 2 / (r * γ ^ 2) := by positivity
  have hx : α₃ * stageWeight t ε ^ 2 / (r * γ ^ 2) ≤ 1 / 256 := by
    rw [hrγ, div_le_iff₀ (by positivity), hα]
    nlinarith [mul_le_mul_of_nonneg_left hM2 hα₃.le]
  -- the schedule
  set q := stageCount t with hq
  set J := stageReps t ε with hJdef
  set L := numStages t ε with hLdef
  have hJ : ∀ i, 1 ≤ i → 1 ≤ J i := fun i _ => J_pos ht hε₀ hε i
  have hq1 : 1 ≤ q := q_pos ht
  have hLeq : L = (blk J q).length := rfl
  set f := fst J q with hf
  set sz : ℕ → ℕ := fun k => stageSize n t ε γ (f k) with hsz
  have hsum : ∑ k ∈ range L, sz k ≤ w := by
    have h1 : ((∑ k ∈ range L, sz k : ℕ) : ℝ) =
        ∑ i ∈ Icc 1 q, (J i : ℝ) * (stageSize n t ε γ i : ℝ) := by
      push_cast
      rw [hLeq, sum_fst J (fun i => (stageSize n t ε γ i : ℝ)) q]
      apply sum_nbij' (fun i => i + 1) (fun i => i - 1)
      · intro i hi; simp at hi ⊢; omega
      · intro i hi; simp at hi ⊢; omega
      · intro i hi; simp
      · intro i hi; simp at hi ⊢; omega
      · intro i _; rfl
    have h2 := sum_JS_le (n := n) ht hε₀ hε hγ₀.le
    have : ((∑ k ∈ range L, sz k : ℕ) : ℝ) ≤ w := by rw [h1, hw]; exact h2
    exact_mod_cast this
  set F := Fam sz ([] : List (Finset (Fin n))) L with hF
  have hFpos : 0 < F.card := by
    rw [hF, card_Fam]
    apply gF_pos
    simp only [U, card_empty, zero_add, Fintype.card_fin, List.length_nil]
    exact hsum.trans hwn
  have hcmp := compare sz Ev (fun Y Y' h ⟨z, hz, hzY⟩ => ⟨z, hz, hzY.trans (incident_mono h)⟩)
    L w hsum (by simpa using hwn)
  let ord0 : LinearOrder (Finset (Edge n)) :=
    LinearOrder.lift' (Fintype.equivFin (Finset (Edge n))) (Fintype.equivFin _).injective
  -- the per-block bad events
  set δ : ℕ → ℝ := fun i => ((16 : ℝ) ^ (2 ^ (q - i)))⁻¹ with hδ
  set K : ℕ → Finset ℕ := fun i => (range L).filter fun k => f k = i with hK
  set A : ℕ → List (Finset (Fin n)) → Finset (Fin n) → Prop := fun i p X =>
    δ i < lawProb μ (EvK ord0 (lawSupport μ) t ε (Wof t ε (p ++ [X])) (p.length + 1)) with hA
  have hKcard : ∀ i ∈ Icc 1 q, (K i).card = J i := fun i hi => by
    rw [hK, hLeq]; exact count_fst J q i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2
  have hex : ∀ i, ex (K i) 0 L = (K i).card := by
    intro i
    unfold ex
    rw [card_eq_sum_ones, hK, sum_filter]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.1 hk
    by_cases h : f k = i
    · rw [if_pos (by simp [h, hk']), if_pos h]
    · rw [if_neg (by simp [h]), if_neg h]
  have hδpos : ∀ i, 0 < δ i := fun i => by positivity
  have hAi : ∀ i ∈ Icc 1 q, ∀ p : List (Finset (Fin n)), p.length ∈ K i →
      (((powersetCard (sz p.length) (univ \ U p)).filter (A i p)).card : ℝ) ≤
        δ i * (powersetCard (sz p.length) (univ \ U p)).card := by
    intro i hi p hp
    simp only [hK, mem_filter, mem_range] at hp
    obtain ⟨hpL, hfp⟩ := hp
    have hsub := H3 n μ t ε γ r ord0 (fun ℓ' => p.getD (ℓ' - 1) ∅)
      (fun X => Wof t ε (p ++ [X])) (p.length + 1)
      ht hε₀ hε hγ₀ hγ₁ hr0 hμ hsp hS (by omega) (by omega)
      (fun X ℓ' hℓ' => by
        simp only [mem_Ico] at hℓ'
        rw [stages_nodup_of t ε (stages_nodup t ε) _ ℓ' hℓ'.1 (by omega)]
        exact List.getD_append _ _ _ _ (by omega))
      (fun X => by
        rw [stages_nodup_of t ε (stages_nodup t ε) _ (p.length + 1) (by omega) (by omega)]
        simp)
    have hPP : powersetCard (stageSize n t ε γ (stageAt t ε (p.length + 1)).1)
        (univ \ (Ico 1 (p.length + 1)).biUnion fun ℓ' => p.getD (ℓ' - 1) ∅) =
        powersetCard (sz p.length) (univ \ U p) := by
      rw [U_eq, stageAt_fst]
    have hfloor : stageFloor t ε (p.length + 1) = 2 ^ (q - i) := by
      rw [stageFloor, stageAt_fst]; rw [← hfp]
    rw [hPP, hfloor] at hsub
    set Pp := powersetCard (sz p.length) (univ \ U p)
    have hm : δ i * ((Pp.filter (A i p)).card : ℝ) ≤ ∑ X ∈ Pp,
        lawProb μ (EvK ord0 (lawSupport μ) t ε (Wof t ε (p ++ [X])) (p.length + 1)) := by
      calc δ i * ((Pp.filter (A i p)).card : ℝ) = ∑ X ∈ Pp.filter (A i p), δ i := by
            rw [sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ X ∈ Pp.filter (A i p),
            lawProb μ (EvK ord0 (lawSupport μ) t ε (Wof t ε (p ++ [X])) (p.length + 1)) :=
            sum_le_sum fun X hX => ((mem_filter.1 hX).2).le
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => lawProb_nonneg _ _)
    have hxF : (α₃ * stageWeight t ε ^ 2 / (r * γ ^ 2)) ^ (2 ^ (q - i)) ≤
        ((1 : ℝ) / 256) ^ (2 ^ (q - i)) := pow_le_pow_left₀ hx0 hx _
    have hδ2 : ((1 : ℝ) / 256) ^ (2 ^ (q - i)) = δ i * δ i := by
      simp only [hδ]; rw [← mul_inv, ← mul_pow, one_div, ← inv_pow]; norm_num
    have := hm.trans (hsub.trans (mul_le_mul_of_nonneg_right hxF (Nat.cast_nonneg _)))
    rw [hδ2, mul_assoc] at this
    exact le_of_mul_le_mul_left this (hδpos i)
  have hbad_i : ∀ i ∈ Icc 1 q, ((F.filter fun l => ∀ k < L,
      ([] : List (Finset (Fin n))).length + k ∈ K i →
        A i ([] ++ l.take k) (l.getD k ∅)).card : ℝ) ≤ (ε / q) ^ 2 * F.card := by
    intro i hi
    have := chain sz (A i) (K i) (δ i) (hδpos i).le (hAi i hi) L []
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    simp only [List.length_nil]
    rw [hex, hKcard i hi]
    exact delta_pow t ε ht hε₀ hε i (mem_Icc.1 hi).2
  have hincl : F.filter (fun l => ¬ Ev (U l)) ⊆ (Icc 1 q).biUnion (fun i =>
      F.filter fun l => ∀ k < L, ([] : List (Finset (Fin n))).length + k ∈ K i →
        A i ([] ++ l.take k) (l.getD k ∅)) := by
    intro l hl
    rw [mem_filter] at hl
    rw [mem_biUnion]
    by_contra hcon
    push Not at hcon
    apply hl.2
    have hlen := (Fam_props sz L [] l hl.1).1
    apply good_cover ord0 μ t ε ht hε₀ hε hμ l hlen δ (sum_delta q)
    intro i hi
    have h1 := hcon i hi
    rw [mem_filter, not_and] at h1
    have h2 := h1 hl.1
    push Not at h2
    obtain ⟨k, hkL, hkK, hnA⟩ := h2
    simp only [hK, mem_filter, mem_range, List.length_nil, zero_add] at hkK
    refine ⟨k, hkL, hkK.2, ?_⟩
    simp only [hA, not_lt, List.nil_append] at hnA
    rw [EvK_take ord0 _ t ε (stages_nodup t ε) l k (by omega) (by omega)]
    have : (l.take k).length = k := by simp; omega
    rwa [this] at hnA
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hbadl : ((F.filter fun l => ¬ Ev (U l)).card : ℝ) ≤ q * (ε / q) ^ 2 * F.card := by
    calc ((F.filter fun l => ¬ Ev (U l)).card : ℝ)
        ≤ (((Icc 1 q).biUnion (fun i => F.filter fun l => ∀ k < L,
            ([] : List (Finset (Fin n))).length + k ∈ K i →
              A i ([] ++ l.take k) (l.getD k ∅))).card : ℝ) := by
          exact_mod_cast card_le_card hincl
      _ ≤ ∑ i ∈ Icc 1 q, ((F.filter fun l => ∀ k < L,
            ([] : List (Finset (Fin n))).length + k ∈ K i →
              A i ([] ++ l.take k) (l.getD k ∅)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ i ∈ Icc 1 q, (ε / q) ^ 2 * (F.card : ℝ) := sum_le_sum hbad_i
      _ = q * (ε / q) ^ 2 * F.card := by rw [sum_const, Nat.card_Icc]; simp; ring
  have hqe : (q : ℝ) * (ε / q) ^ 2 < ε := qe_lt q ε hq1 hε₀ hε
  have hFr : (0 : ℝ) < F.card := by exact_mod_cast hFpos
  have hPr : (0 : ℝ) < P.card := by exact_mod_cast hPpos
  have hcmpR : ((P.filter fun Y => ¬ Ev Y).card : ℝ) * F.card ≤
      ((F.filter fun l => ¬ Ev (U l)).card : ℝ) * P.card := by
    have h := (Nat.cast_le (α := ℝ)).2 hcmp
    push_cast at h
    exact h
  show 1 - ε < uniformProb P Ev
  rw [hunif]
  have : ((P.filter fun Y => ¬ Ev Y).card : ℝ) / P.card < ε := by
    rw [div_lt_iff₀ hPr]
    have h1 : ((P.filter fun Y => ¬ Ev Y).card : ℝ) * F.card < ε * P.card * F.card := by
      calc _ ≤ _ := hcmpR
        _ ≤ (q * (ε / q) ^ 2 * F.card) * P.card := mul_le_mul_of_nonneg_right hbadl hPr.le
        _ < ε * F.card * P.card := by
          apply mul_lt_mul_of_pos_right _ hPr
          exact mul_lt_mul_of_pos_right hqe hFr
        _ = ε * P.card * F.card := by ring
    exact lt_of_mul_lt_mul_right h1 hFr.le
  linarith

/-- STUB (the only remaining gap): Eq. (3) of the source, the encoding/counting argument
(Claim 10, the count of `W_ℓ ∪ V(π_ℓ(z))`, spreadness, and the probability `≥ 2^{-2^{q-i+2}}(ea)^{-a}`
of consistency with a random `(S, f)`). -/
theorem eq3 : Eq3Statement := by
  exact Dev.Eq3.eq3_main

/-- Lemma 5 (Spread Matching Lemma), p. 4, statement verbatim. -/
theorem chk_lemma_5 :
    ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (μ : PMF (Finset (Edge n))) (ε t γ r : ℝ) (w : ℕ),
        0 < ε → ε < 1 / 2 → 1 < t → 0 < γ → γ ≤ 1 → (w : ℝ) = γ * (n : ℝ) →
        r = α * (t + Real.log (1 / ε) ^ 2) / γ ^ 2 →
        IsBoundedMatchingLaw μ t → IsSpread μ r →
        1 - ε < uniformProb (Finset.powersetCard w (Finset.univ : Finset (Fin n)))
          (fun W => ∃ z ∈ lawSupport μ, z ⊆ incident W) :=
  chk_lemma_5_of_eq3 eq3

end SpreadMatchCircuit.Matching
end

theorem solution : type_of% @SpreadMatchCircuit.Matching.chk_lemma_5 := @SpreadMatchCircuit.Matching.chk_lemma_5
