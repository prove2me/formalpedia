-- Prove2me | solution 1 for PolygonalPathOrderedFirstHitPrefix
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:39:12.691767+00:00
-- url     : https://prove2.me/submissions/6f783bcc-17a5-47bc-87bd-b1c57573a775

import Mathlib
import Definitions.Def_PolygonalPath

set_option autoImplicit false

open Classical
noncomputable section

namespace P419c

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Segs (L : List E) : Set E :=
  {p | ∃ i : ℕ, ∃ hi : i + 1 < L.length, p ∈ segment ℝ L[i] L[i + 1]}

lemma segs_head (v0 v1 : E) (rest : List E) :
    segment ℝ v0 v1 ⊆ Segs (v0 :: v1 :: rest) := by
  intro p hp
  exact ⟨0, by simp, by simpa using hp⟩

lemma segs_tail (v0 : E) (L : List E) :
    Segs L ⊆ Segs (v0 :: L) := by
  rintro p ⟨i, hi, hp⟩
  exact ⟨i + 1, by simp; omega, by simpa using hp⟩

lemma firstHit (S U : Set E) (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsClosed S)
    (v0 v1 : E) (hv0 : v0 ∉ S)
    (h : ∃ t ∈ Set.Icc (0:ℝ) 1, AffineMap.lineMap v0 v1 t ∈ S) :
    ∃ (y : E) (P : Set E), y ∈ segment ℝ v0 v1 ∧ y ∈ U ∧ y ∉ S ∧
      IsConnected P ∧ v0 ∈ P ∧ y ∈ P ∧ P ⊆ segment ℝ v0 v1 ∩ Sᶜ := by
  set f : ℝ → E := fun t => AffineMap.lineMap v0 v1 t with hfdef
  have hf : Continuous f := AffineMap.lineMap_continuous
  set T : Set ℝ := Set.Icc 0 1 ∩ f ⁻¹' S with hT
  have hTc : IsCompact T := isCompact_Icc.inter_right (hS.preimage hf)
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, hts⟩ := h
    exact ⟨t, ht, hts⟩
  obtain ⟨t0, ht0T, ht0min⟩ := hTc.exists_isLeast hTne
  have ht0pos : 0 < t0 := by
    rcases lt_or_eq_of_le ht0T.1.1 with h0 | h0
    · exact h0
    · exfalso
      apply hv0
      have := ht0T.2
      rw [← h0] at this
      simpa [f] using this
  have hfU : f t0 ∈ U := hSU ht0T.2
  have hev : ∀ᶠ t in nhds t0, f t ∈ U :=
    hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hfU)
  have hev' : ∀ᶠ t in nhdsWithin t0 (Set.Iio t0), f t ∈ U :=
    nhdsWithin_le_nhds hev
  have hI : ∀ᶠ t in nhdsWithin t0 (Set.Iio t0), t ∈ Set.Ioo 0 t0 :=
    Ioo_mem_nhdsLT ht0pos
  obtain ⟨s, hsU, hs⟩ := (hev'.and hI).exists
  have hs1 : s ≤ 1 := le_trans hs.2.le ht0T.1.2
  have hseg : ∀ r ∈ Set.Icc (0:ℝ) 1, f r ∈ segment ℝ v0 v1 := by
    intro r hr
    rw [segment_eq_image_lineMap]
    exact ⟨r, hr, rfl⟩
  have hnot : ∀ r ∈ Set.Icc (0:ℝ) s, f r ∉ S := by
    intro r hr hrS
    have : t0 ≤ r := ht0min ⟨⟨hr.1, le_trans hr.2 hs1⟩, hrS⟩
    linarith [hr.2, hs.2]
  refine ⟨f s, f '' Set.Icc 0 s, hseg s ⟨hs.1.le, hs1⟩, hsU,
    hnot s ⟨hs.1.le, le_rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact (isConnected_Icc hs.1.le).image f hf.continuousOn
  · exact ⟨0, ⟨le_rfl, hs.1.le⟩, by simp [f]⟩
  · exact ⟨s, ⟨hs.1.le, le_rfl⟩, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨hseg r ⟨hr.1, le_trans hr.2 hs1⟩, hnot r hr⟩

lemma key (S U : Set E) (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsClosed S) :
    ∀ (L : List E) (v0 : E), v0 ∉ S → (v0 :: L).getLast (List.cons_ne_nil _ _) ∈ S →
      ∃ (y : E) (P : Set E), y ∈ U ∧ y ∉ S ∧
        IsConnected P ∧ v0 ∈ P ∧ y ∈ P ∧ P ⊆ Segs (v0 :: L) ∩ Sᶜ := by
  intro L
  induction L with
  | nil =>
    intro v0 hv0 hlast
    exact absurd (by simpa using hlast) hv0
  | cons v1 rest ih =>
    intro v0 hv0 hlast
    by_cases h : ∃ t ∈ Set.Icc (0:ℝ) 1, AffineMap.lineMap v0 v1 t ∈ S
    · obtain ⟨y, P, -, hyU, hyS, hP, hv0P, hyP, hPsub⟩ := firstHit S U hU hSU hS v0 v1 hv0 h
      refine ⟨y, P, hyU, hyS, hP, hv0P, hyP, ?_⟩
      intro p hp
      exact ⟨segs_head v0 v1 rest (hPsub hp).1, (hPsub hp).2⟩
    · push Not at h
      have hsegS : ∀ p ∈ segment ℝ v0 v1, p ∉ S := by
        intro p hp
        rw [segment_eq_image_lineMap] at hp
        obtain ⟨t, ht, rfl⟩ := hp
        exact h t ht
      have hv1 : v1 ∉ S := hsegS v1 (right_mem_segment ℝ v0 v1)
      have hlast' : (v1 :: rest).getLast (List.cons_ne_nil _ _) ∈ S := by
        rwa [List.getLast_cons] at hlast
      obtain ⟨y, P, hyU, hyS, hP, hv1P, hyP, hPsub⟩ := ih v1 hv1 hlast'
      refine ⟨y, segment ℝ v0 v1 ∪ P, hyU, hyS, ?_, Or.inl (left_mem_segment ℝ v0 v1),
        Or.inr hyP, ?_⟩
      · exact IsConnected.union ⟨v1, right_mem_segment ℝ v0 v1, hv1P⟩
          ((convex_segment v0 v1).isConnected ⟨v0, left_mem_segment ℝ v0 v1⟩) hP
      · rintro p (hp | hp)
        · exact ⟨segs_head v0 v1 rest hp, hsegS p hp⟩
        · exact ⟨segs_tail v0 _ (hPsub hp).1, (hPsub hp).2⟩

end P419c

theorem solution
    (γ : PolygonalPath)
    (a b : EuclideanSpace ℝ (Fin 2))
    (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : IsOpen U)
    (hsegment_subset_U : segment ℝ a b ⊆ U)
    (hsource_not : γ.source ∉ segment ℝ a b)
    (htarget_mem : γ.target ∈ segment ℝ a b) :
    ∃ (y : EuclideanSpace ℝ (Fin 2)) (P : Set (EuclideanSpace ℝ (Fin 2))),
      y ∈ γ.carrier ∧ y ∈ U ∧ y ∉ segment ℝ a b ∧
        IsConnected P ∧ γ.source ∈ P ∧ y ∈ P ∧
          P ⊆ γ.carrier ∩ (segment ℝ a b)ᶜ := by
  have hSclosed : IsClosed (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  obtain ⟨vs, hvs⟩ : ∃ L, γ.vertices = γ.source :: L := by
    have h := γ.source_eq_head
    cases hv : γ.vertices with
    | nil => exact absurd hv γ.vertices_nonempty
    | cons v L =>
      rw [hv] at h
      simp at h
      exact ⟨L, by rw [h]⟩
  have hlast : (γ.source :: vs).getLast (List.cons_ne_nil _ _) ∈ segment ℝ a b := by
    have h := γ.target_eq_last
    rw [hvs, List.getLast?_eq_getLast (List.cons_ne_nil _ _)] at h
    simp only [Option.some.injEq] at h
    rw [h]
    exact htarget_mem
  obtain ⟨y, P, hyU, hyS, hP, hsP, hyP, hPsub⟩ :=
    P419c.key (segment ℝ a b) U hUopen hsegment_subset_U hSclosed vs γ.source hsource_not hlast
  have hsub : P419c.Segs (γ.source :: vs) ⊆ γ.carrier := by
    rintro p ⟨i, hi, hp⟩
    rw [γ.carrier_eq]
    right
    refine ⟨i, by rw [hvs]; exact hi, ?_⟩
    simp only [hvs]
    exact hp
  have hPsub' : P ⊆ γ.carrier ∩ (segment ℝ a b)ᶜ := by
    intro p hp
    exact ⟨hsub (hPsub hp).1, (hPsub hp).2⟩
  exact ⟨y, P, (hPsub' hyP).1, hyU, hyS, hP, hsP, hyP, hPsub'⟩
