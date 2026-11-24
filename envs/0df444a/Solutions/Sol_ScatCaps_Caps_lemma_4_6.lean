-- Prove2me | solution 1 for ScatCaps.Caps.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:10:25.306628+00:00
-- url     : https://prove2.me/submissions/45e54d62-935a-44f8-b708-8cbf95891ca8

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

open ScatCaps.Caps

theorem solution (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : 1 < t) {r : ℕ}
    (G : AddSubgroup (Fin r → K)) (hG : IsMaximalTranslationCap (KG G)) :
    IsCompleteCap (doubling (KG G)) := by
  classical
  obtain ⟨⟨hcap, _⟩, hcard⟩ := hG
  have h2 : (2 : K) = 0 := by
    have hc := FiniteField.cast_card_eq_zero K
    rw [hK] at hc
    push_cast at hc
    exact eq_zero_of_pow_eq_zero hc
  -- G contains no three collinear points a, a + v, a + μ v
  have capG : ∀ (a v : Fin r → K) (μ : K), a ∈ G → a + v ∈ G → a + μ • v ∈ G → v ≠ 0 →
      μ ≠ 0 → μ ≠ 1 → False := by
    intro a v μ ha hb hc hv hμ0 hμ1
    have d1 : a ≠ a + v := fun h => hv (by simpa using h.symm)
    have d2 : a ≠ a + μ • v := fun h => smul_ne_zero hμ0 hv (by simpa using h.symm)
    have d3 : a + v ≠ a + μ • v := by
      intro h
      have h' := add_left_cancel h
      have : (1 - μ) • v = 0 := by rw [sub_smul, one_smul, ← h', sub_self]
      rcases smul_eq_zero.mp this with h3 | h3
      · exact hμ1 (sub_eq_zero.mp h3).symm
      · exact hv h3
    apply hcap a ha (a + v) hb (a + μ • v) hc d1 d2 d3
    rw [collinear_iff_of_mem (Set.mem_insert _ _)]
    refine ⟨v, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [add_comm]⟩
    · exact ⟨μ, by simp [add_comm]⟩
  have hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro ω _
      by_cases h0 : ω = 0
      · simp [h0]
      · simp [h ω h0]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hK] at h1
    have h3 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    have h4 : 2 ^ 2 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    omega
  -- every point of K^r is (1-ω) g + ω g' with g, g' ∈ G
  have surj : ∀ ω : K, ω ≠ 0 → ω ≠ 1 → ∀ q : Fin r → K,
      ∃ g ∈ G, ∃ g' ∈ G, q = (1 - ω) • g + ω • g' := by
    intro ω h0 h1 q
    have h1' : (1 - ω) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    let f : (Fin r → K) × (Fin r → K) → (Fin r → K) := fun x => (1 - ω) • x.1 + ω • x.2
    have inj : Set.InjOn f ((G : Set (Fin r → K)) ×ˢ (G : Set (Fin r → K))) := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨a', b'⟩ ⟨ha', hb'⟩ h
      simp only [f] at h ha hb ha' hb'
      have hd : (1 - ω) • (a - a') = ω • (b' - b) := by
        rw [smul_sub, smul_sub, sub_eq_sub_iff_add_eq_add, add_comm (ω • b')]
        exact h
      by_cases hbb : b' - b = 0
      · have hb_eq : b = b' := (sub_eq_zero.mp hbb).symm
        rw [hbb, smul_zero] at hd
        rcases smul_eq_zero.mp hd with h3 | h3
        · exact absurd h3 h1'
        · rw [sub_eq_zero.mp h3, hb_eq]
      · exfalso
        have hμv : ((1 - ω)⁻¹ * ω) • (b' - b) = a - a' := by
          rw [mul_smul, ← hd, smul_smul, inv_mul_cancel₀ h1', one_smul]
        have hμ1 : (1 - ω)⁻¹ * ω ≠ 1 := by
          intro h
          have e : ω = 1 - ω := by
            calc ω = (1 - ω) * ((1 - ω)⁻¹ * ω) := by
                  rw [← mul_assoc, mul_inv_cancel₀ h1', one_mul]
              _ = 1 - ω := by rw [h, mul_one]
          have e2 : (2 : K) * ω = 1 := by linear_combination e
          rw [h2, zero_mul] at e2
          exact zero_ne_one e2
        apply capG 0 (b' - b) ((1 - ω)⁻¹ * ω) G.zero_mem
          (by rw [zero_add]; exact G.sub_mem hb' hb)
          (by rw [zero_add, hμv]; exact G.sub_mem ha ha') hbb
          (mul_ne_zero (inv_ne_zero h1') h0) hμ1
    have himg : f '' ((G : Set (Fin r → K)) ×ˢ (G : Set (Fin r → K))) = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [inj.ncard_image, Set.ncard_prod, Set.ncard_univ, Nat.card_fun, Nat.card_fin, ← hcard,
        sq]
      exact le_rfl
    have hq : q ∈ f '' ((G : Set (Fin r → K)) ×ˢ (G : Set (Fin r → K))) := by
      rw [himg]; exact Set.mem_univ q
    obtain ⟨⟨g, g'⟩, ⟨hg, hg'⟩, hfq⟩ := hq
    exact ⟨g, hg, g', hg', hfq.symm⟩
  have memD : ∀ x : Fin (r + 1) → K, x ∈ doubling (KG G) ↔
      Fin.init x ∈ G ∧ (x (Fin.last r) = 0 ∨ x (Fin.last r) = 1) := by
    intro x
    constructor
    · rintro ⟨v, hv, c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Fin.init_snoc]; exact hv
      · rw [Fin.snoc_last]; exact hc
    · rintro ⟨h1, h3⟩
      exact ⟨Fin.init x, h1, x (Fin.last r), h3, (Fin.snoc_init_self x).symm⟩
  have tri : ∀ a b c : K, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → (c = 0 ∨ c = 1) → a ≠ b →
      c = a ∨ c = b := by
    intro a b c ha hb hc hab
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp_all
  -- collinearity of A, B and A + λ (B - A)
  have colin : ∀ (A B : Fin (r + 1) → K) (l : K),
      Collinear K ({A, B, A + l • (B - A)} : Set (Fin (r + 1) → K)) := by
    intro A B l
    rw [collinear_iff_of_mem (Set.mem_insert _ _)]
    refine ⟨B - A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨l, by rw [vadd_eq_add]; exact add_comm _ _⟩
  refine ⟨?_, ?_⟩
  · -- the doubling is a cap
    intro x hx y hy z hz hxy hxz hyz hcol
    rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨a, ha⟩ := hv y (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨b, hb⟩ := hv z (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rw [vadd_eq_add] at ha hb
    have ha0 : a ≠ 0 := by rintro rfl; apply hxy; rw [ha]; simp
    have hb0 : b ≠ 0 := by rintro rfl; apply hxz; rw [hb]; simp
    have hab : a ≠ b := by rintro rfl; apply hyz; rw [ha, hb]
    have hμ0 : b / a ≠ 0 := div_ne_zero hb0 ha0
    have hμ1 : b / a ≠ 1 := fun h => hab ((div_eq_one_iff_eq ha0).mp h).symm
    have hz' : z = x + (b / a) • (y - x) := by
      rw [hb, ha, add_sub_cancel_right, smul_smul, div_mul_cancel₀ b ha0]
      exact add_comm _ _
    obtain ⟨hgx, hcx⟩ := (memD x).mp hx
    obtain ⟨hgy, hcy⟩ := (memD y).mp hy
    obtain ⟨hgz, hcz⟩ := (memD z).mp hz
    have hzg : Fin.init z = Fin.init x + (b / a) • (Fin.init y - Fin.init x) := by
      rw [hz']; rfl
    have hzc : z (Fin.last r) = x (Fin.last r) + (b / a) * (y (Fin.last r) - x (Fin.last r)) := by
      rw [hz']; simp
    by_cases hc : y (Fin.last r) = x (Fin.last r)
    · have hgne : Fin.init y - Fin.init x ≠ 0 := by
        intro h0
        apply hxy
        rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, sub_eq_zero.mp h0, hc]
      apply capG (Fin.init x) (Fin.init y - Fin.init x) (b / a) hgx (by simpa using hgy)
        (by rw [← hzg]; exact hgz) hgne hμ0 hμ1
    · have hne : y (Fin.last r) - x (Fin.last r) ≠ 0 := sub_ne_zero.mpr hc
      rcases tri _ _ _ hcx hcy hcz (Ne.symm hc) with h3 | h3
      · have : (b / a) * (y (Fin.last r) - x (Fin.last r)) = 0 := by
          linear_combination h3 - hzc
        exact hμ0 ((mul_eq_zero.mp this).resolve_right hne)
      · have : (b / a) * (y (Fin.last r) - x (Fin.last r)) =
            1 * (y (Fin.last r) - x (Fin.last r)) := by
          linear_combination h3 - hzc
        exact hμ1 (mul_right_cancel₀ hne this)
  · -- completeness
    intro P hP hcapP
    have hPsplit := (Fin.snoc_init_self P).symm
    by_cases he : P (Fin.last r) = 0 ∨ P (Fin.last r) = 1
    · obtain ⟨ω, hω0, hω1⟩ := hω
      obtain ⟨g, hg, g', hg', hp⟩ := surj ω hω0 hω1 (Fin.init P)
      set e := P (Fin.last r) with he_def
      set A : Fin (r + 1) → K := Fin.snoc (α := fun _ => K) g e with hA
      set B : Fin (r + 1) → K := Fin.snoc (α := fun _ => K) g' e with hB
      have hAD : A ∈ doubling (KG G) := ⟨g, hg, e, he, rfl⟩
      have hBD : B ∈ doubling (KG G) := ⟨g', hg', e, he, rfl⟩
      have hPeq : P = A + ω • (B - A) := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [hA, hB, he_def]
        · have hj := congrFun hp j
          simp only [Fin.init, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
          simp only [hA, hB, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
            Fin.snoc_castSucc]
          rw [hj]; ring
      have hAB : A ≠ B := by
        intro h
        apply hP
        have hgg : g = g' := by
          have := congrArg Fin.init h
          simpa [hA, hB, Fin.init_snoc] using this
        rw [(memD P)]
        refine ⟨?_, he⟩
        rw [hp, ← hgg, ← add_smul, sub_add_cancel, one_smul]
        exact hg
      apply hcapP A (Set.mem_insert_of_mem _ hAD) B (Set.mem_insert_of_mem _ hBD) P
        (Set.mem_insert _ _) hAB (fun h => hP (h ▸ hAD)) (fun h => hP (h ▸ hBD))
      rw [hPeq]
      exact colin A B ω
    · push_neg at he
      obtain ⟨g, hg, g', hg', hp⟩ := surj (P (Fin.last r)) he.1 he.2 (Fin.init P)
      set e := P (Fin.last r) with he_def
      set A : Fin (r + 1) → K := Fin.snoc (α := fun _ => K) g 0 with hA
      set B : Fin (r + 1) → K := Fin.snoc (α := fun _ => K) g' 1 with hB
      have hAD : A ∈ doubling (KG G) := ⟨g, hg, 0, Or.inl rfl, rfl⟩
      have hBD : B ∈ doubling (KG G) := ⟨g', hg', 1, Or.inr rfl, rfl⟩
      have hPeq : P = A + e • (B - A) := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [hA, hB, he_def]
        · have hj := congrFun hp j
          simp only [Fin.init, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
          simp only [hA, hB, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
            Fin.snoc_castSucc]
          rw [hj]; ring
      have hAB : A ≠ B := by
        intro h
        have := congrFun h (Fin.last r)
        simp [hA, hB] at this
      apply hcapP A (Set.mem_insert_of_mem _ hAD) B (Set.mem_insert_of_mem _ hBD) P
        (Set.mem_insert _ _) hAB (fun h => hP (h ▸ hAD)) (fun h => hP (h ▸ hBD))
      rw [hPeq]
      exact colin A B e
