-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P46.section_value_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:38:04.1399+00:00
-- url     : https://prove2.me/submissions/cd748ce2-49a4-4c0a-81b5-384fd9745ac9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46

noncomputable section

namespace X7P46S

open QAlgorithms.Papers.Independent.Gap48.P46

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma closed_rel (S : Set V) (hS : IsCompact S) (l : V →ₗ[ℝ] ℝ) (rel : ℝ → ℝ → Prop)
    (hrel : rel = (· = ·) ∨ rel = (· ≤ ·) ∨ rel = (· ≥ ·)) (a : ℝ) :
    IsCompact (sectionSet S l rel a) := by
  have hc : Continuous l := LinearMap.continuous_of_finiteDimensional l
  have hcl : IsClosed {x : V | rel (l x) a} := by
    rcases hrel with rfl | rfl | rfl
    · exact isClosed_eq hc continuous_const
    · exact isClosed_le hc continuous_const
    · exact isClosed_le continuous_const hc
  have : sectionSet S l rel a = S ∩ {x : V | rel (l x) a} := rfl
  rw [this]; exact hS.inter_right hcl

lemma attain (S : Set V) (hS : IsCompact S) (F : V → ℝ) (hF : ContinuousOn F S)
    (l : V →ₗ[ℝ] ℝ) (rel : ℝ → ℝ → Prop)
    (hrel : rel = (· = ·) ∨ rel = (· ≤ ·) ∨ rel = (· ≥ ·)) (a : ℝ)
    (ha : a ∈ sectionDomain S l rel) :
    MaximizesValue (sectionSet S l rel a) F (sectionValue S F l rel a) := by
  have hK := closed_rel S hS l rel hrel a
  have hsub : sectionSet S l rel a ⊆ S := fun x hx => hx.1
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn ha (hF.mono hsub)
  have hg : IsGreatest (F '' sectionSet S l rel a) (F x) :=
    ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmax hy⟩
  unfold MaximizesValue sectionValue maxValue
  rw [hg.csSup_eq]; exact hg

lemma rel_comb (l : V →ₗ[ℝ] ℝ) (rel : ℝ → ℝ → Prop)
    (hrel : rel = (· = ·) ∨ rel = (· ≤ ·) ∨ rel = (· ≥ ·)) {x y : V} {a b s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hx : rel (l x) a) (hy : rel (l y) b) :
    rel (l (s • x + t • y)) (s * a + t * b) := by
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rcases hrel with rfl | rfl | rfl
  · rw [hx, hy]
  · exact add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)
  · exact add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)

lemma concave (S : Set V) (hS : IsCompact S) (hconv : Convex ℝ S) (F : V → ℝ)
    (hF : ContinuousOn F S) (hcc : ConcaveOn ℝ S F)
    (l : V →ₗ[ℝ] ℝ) (rel : ℝ → ℝ → Prop)
    (hrel : rel = (· = ·) ∨ rel = (· ≤ ·) ∨ rel = (· ≥ ·)) :
    ConcaveOn ℝ (sectionDomain S l rel) (sectionValue S F l rel) := by
  have key : ∀ a ∈ sectionDomain S l rel, ∀ b ∈ sectionDomain S l rel, ∀ s t : ℝ,
      0 ≤ s → 0 ≤ t → s + t = 1 →
      (s * a + t * b) ∈ sectionDomain S l rel ∧
      s * sectionValue S F l rel a + t * sectionValue S F l rel b ≤
        sectionValue S F l rel (s * a + t * b) := by
    intro a ha b hb s t hs ht hst
    obtain ⟨⟨x, hx, hFx⟩, -⟩ := attain S hS F hF l rel hrel a ha
    obtain ⟨⟨y, hy, hFy⟩, -⟩ := attain S hS F hF l rel hrel b hb
    have hz : s • x + t • y ∈ sectionSet S l rel (s * a + t * b) :=
      ⟨hconv hx.1 hy.1 hs ht hst, rel_comb l rel hrel hs ht hx.2 hy.2⟩
    refine ⟨⟨_, hz⟩, ?_⟩
    have hm := attain S hS F hF l rel hrel _ ⟨_, hz⟩
    have h1 : F (s • x + t • y) ≤ sectionValue S F l rel (s * a + t * b) :=
      hm.2 ⟨_, hz, rfl⟩
    have h2 := hcc.2 hx.1 hy.1 hs ht hst
    simp only [smul_eq_mul] at h2
    rw [← hFy, ← hFx]; linarith
  refine ⟨?_, ?_⟩
  · intro a ha b hb s t hs ht hst
    have := (key a ha b hb s t hs ht hst).1
    simpa [smul_eq_mul] using this
  · intro a ha b hb s t hs ht hst
    have := (key a ha b hb s t hs ht hst).2
    simpa [smul_eq_mul] using this

lemma one_sided (S : Set V) (hS : IsCompact S) (hconv : Convex ℝ S) (F : V → ℝ)
    (hF : ContinuousOn F S) (hcc : ConcaveOn ℝ S F) (l : V →ₗ[ℝ] ℝ) (a : ℝ)
    (ha : a ∈ sectionDomain S l (· = ·)) :
    sectionValue S F l (· = ·) a = sectionValue S F l (· ≤ ·) a ∨
      sectionValue S F l (· = ·) a = sectionValue S F l (· ≥ ·) a := by
  obtain ⟨x0, hx0⟩ := ha
  have hle : a ∈ sectionDomain S l (· ≤ ·) := ⟨x0, hx0.1, le_of_eq hx0.2⟩
  have hge : a ∈ sectionDomain S l (· ≥ ·) := ⟨x0, hx0.1, ge_of_eq hx0.2⟩
  have hE := attain S hS F hF l _ (Or.inl rfl) a ⟨x0, hx0⟩
  obtain ⟨⟨x1, hx1, hF1⟩, -⟩ := attain S hS F hF l _ (Or.inr (Or.inl rfl)) a hle
  obtain ⟨⟨x2, hx2, hF2⟩, -⟩ := attain S hS F hF l _ (Or.inr (Or.inr rfl)) a hge
  set v := sectionValue S F l (· = ·) a
  -- v ≤ both one-sided values
  have hv1 : v ≤ F x1 := by
    obtain ⟨⟨z, hz, hFz⟩, -⟩ := hE
    rw [← hFz, hF1]
    exact (attain S hS F hF l _ (Or.inr (Or.inl rfl)) a hle).2 ⟨z, ⟨hz.1, le_of_eq hz.2⟩, rfl⟩
  have hv2 : v ≤ F x2 := by
    obtain ⟨⟨z, hz, hFz⟩, -⟩ := hE
    rw [← hFz, hF2]
    exact (attain S hS F hF l _ (Or.inr (Or.inr rfl)) a hge).2 ⟨z, ⟨hz.1, ge_of_eq hz.2⟩, rfl⟩
  by_contra hne
  push Not at hne
  have h1 : v < F x1 := lt_of_le_of_ne hv1 (by rw [hF1]; exact hne.1)
  have h2 : v < F x2 := lt_of_le_of_ne hv2 (by rw [hF2]; exact hne.2)
  have hup : ∀ z ∈ S, l z = a → F z ≤ v := fun z hz hza => hE.2 ⟨z, ⟨hz, hza⟩, rfl⟩
  have hl1 : l x1 < a := lt_of_le_of_ne hx1.2 (fun h => absurd (hup x1 hx1.1 h) (not_le.2 h1))
  have hl2 : a < l x2 := lt_of_le_of_ne hx2.2 (fun h => absurd (hup x2 hx2.1 h.symm) (not_le.2 h2))
  -- convex combination hitting level a
  set s := (l x2 - a) / (l x2 - l x1)
  set t := (a - l x1) / (l x2 - l x1)
  have hd : 0 < l x2 - l x1 := by linarith
  have hs : 0 ≤ s := div_nonneg (by linarith) hd.le
  have ht : 0 ≤ t := div_nonneg (by linarith) hd.le
  have hst : s + t = 1 := by
    simp only [s, t]; rw [← add_div]; field_simp; ring
  have hz : s • x1 + t • x2 ∈ S := hconv hx1.1 hx2.1 hs ht hst
  have hlz : l (s • x1 + t • x2) = a := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [s, t]; field_simp; ring
  have hcomb := hcc.2 hx1.1 hx2.1 hs ht hst
  simp only [smul_eq_mul] at hcomb
  have := hup _ hz hlz
  have : s * F x1 + t * F x2 > v := by
    have hm : v < min (F x1) (F x2) := lt_min h1 h2
    have e1 : s * min (F x1) (F x2) ≤ s * F x1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hs
    have e2 : t * min (F x1) (F x2) ≤ t * F x2 := mul_le_mul_of_nonneg_left (min_le_right _ _) ht
    have e3 : s * min (F x1) (F x2) + t * min (F x1) (F x2) = min (F x1) (F x2) := by
      rw [← add_mul, hst, one_mul]
    linarith
  linarith

end X7P46S

open QAlgorithms.Papers.Independent.Gap48.P46 in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (S : Set V) (hS : S.Nonempty) (hcompact : IsCompact S)
    (hconvex : Convex ℝ S) (F : V → ℝ) (hcontinuous : ContinuousOn F S)
    (hconcave : ConcaveOn ℝ S F) (l : V →ₗ[ℝ] ℝ) :
    ∀ alpha ∈ sectionDomain S l (· = ·),
      sectionValue S F l (· = ·) alpha = sectionValue S F l (· ≤ ·) alpha ∨
      sectionValue S F l (· = ·) alpha = sectionValue S F l (· ≥ ·) alpha :=
  fun a ha => X7P46S.one_sided S hcompact hconvex F hcontinuous hconcave l a ha
