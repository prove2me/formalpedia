-- Prove2me | solution 1 for OnlineStochMatching.SuggestedMatching.tightness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:56:13.134456+00:00
-- url     : https://prove2.me/submissions/d64c2b5b-b679-4f62-a944-5be2a4a86439

import Mathlib
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

open Classical

namespace OnlineStochMatching.SuggestedMatching

noncomputable def occ {Ω : Type} [Fintype Ω] (n : ℕ) (B : Finset Ω) (ω : Fin n → Ω) : ℕ :=
  (B.filter fun b => ∃ t, ω t = b).card

lemma card_miss {Ω : Type} [Fintype Ω] (n : ℕ) (b : Ω) :
    (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ω t ≠ b).card = (Fintype.card Ω - 1)^n := by
  have h1 : (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ω t ≠ b).card
      = Fintype.card {ω : Fin n → Ω // ∀ t, ω t ≠ b} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ x => x ≠ b))]
  simp [Fintype.card_pi]

lemma card_hit {Ω : Type} [Fintype Ω] (n : ℕ) (b : Ω) :
    (Finset.univ.filter fun ω : Fin n → Ω => ∃ t, ω t = b).card
      = Fintype.card Ω ^ n - (Fintype.card Ω - 1)^n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Ω)))
    (fun ω : Fin n → Ω => ∃ t, ω t = b)
  have h2 := card_miss n b
  simp only [not_exists] at h
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  have : (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ¬ ω t = b) =
     (Finset.univ.filter fun ω : Fin n → Ω => ∀ t, ω t ≠ b) := rfl
  rw [this, h2] at h
  omega

lemma sum_occ {Ω : Type} [Fintype Ω] (n : ℕ) (B : Finset Ω) :
    ∑ ω : Fin n → Ω, occ n B ω = B.card * (Fintype.card Ω ^ n - (Fintype.card Ω - 1)^n) := by
  unfold occ
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ b ∈ B, ∑ ω : Fin n → Ω, (if ∃ t, ω t = b then 1 else 0)
      = Fintype.card Ω ^ n - (Fintype.card Ω - 1)^n := by
    intro b _
    rw [← card_hit n b, Finset.card_filter]
  rw [Finset.sum_congr rfl this]
  simp


variable {A I : Type} [Fintype A] [Fintype I]

noncomputable def labB (inst : Instance A I) (label : inst.Copy → Option A) : Finset inst.Copy :=
  Finset.univ.filter fun c => (label c).isSome

lemma algorithm_eq_occ (inst : Instance A I) (label : inst.Copy → Option A)
    (hl : ∀ c d a, label c = some a → label d = some a → c = d)
    (ω : Fin inst.n → inst.Copy) :
    algorithm inst label ω = occ inst.n (labB inst label) ω := by
  unfold algorithm occ labB
  set T := (Finset.univ.filter (fun c : inst.Copy => (label c).isSome)).filter
    (fun b => ∃ t, ω t = b) with hT
  set S := Finset.univ.filter fun a : A => ∃ t, label (ω t) = some a with hS
  have h1 : T.card = (T.image label).card := by
    symm
    apply Finset.card_image_of_injOn
    intro c hc d hd hcd
    have hc' : c ∈ T := hc
    rw [hT, Finset.mem_filter, Finset.mem_filter] at hc'
    obtain ⟨⟨_, hc1⟩, _⟩ := hc'
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc1
    exact hl c d a ha (hcd ▸ ha)
  have h2 : T.image label = S.image some := by
    ext x
    simp only [hT, hS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨hc1, t, ht⟩, rfl⟩
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc1
      exact ⟨a, ⟨t, by rw [ht]; exact ha⟩, ha.symm⟩
    · rintro ⟨a, ⟨t, ht⟩, rfl⟩
      exact ⟨ω t, ⟨by rw [ht]; rfl, t, rfl⟩, ht⟩
  have key : T.card = S.card := by
    rw [h1, h2, Finset.card_image_of_injective _ (Option.some_injective A)]
  convert key.symm


lemma card_copy (inst : Instance A I) : Fintype.card inst.Copy = inst.n := by
  simp [Instance.Copy, Fintype.card_sigma, inst.n_eq]

lemma labB_card (inst : Instance A I) (M : Finset (A × I)) (label : inst.Copy → Option A)
    (hl : IsLabelling inst M label) :
    (labB inst label).card = (coveredAds M).card := by
  obtain ⟨h1, h2⟩ := hl
  have e1 : (labB inst label).card = ((labB inst label).image label).card := by
    symm
    apply Finset.card_image_of_injOn
    intro c hc d hd hcd
    have hc' : c ∈ labB inst label := hc
    unfold labB at hc'
    rw [Finset.mem_filter] at hc'
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc'.2
    exact h2 c d a ha (hcd ▸ ha)
  have e2 : (labB inst label).image label = (coveredAds M).image some := by
    ext x
    simp only [labB, coveredAds, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hc
      refine ⟨a, ⟨c.1, ?_⟩, ha.symm⟩
      rw [h1]
      exact ⟨c.2, by rw [← ha]⟩
    · rintro ⟨a, ⟨i, hi⟩, rfl⟩
      rw [h1] at hi
      obtain ⟨j, hj⟩ := hi
      exact ⟨⟨i, j⟩, by rw [hj]; rfl, hj⟩
  rw [e1, e2, Finset.card_image_of_injective _ (Option.some_injective A)]

lemma expect_occ {Ω : Type} [Fintype Ω] [Nonempty Ω] (n : ℕ) (B : Finset Ω) :
    (∑ ω : Fin n → Ω, (occ n B ω : ℝ)) / (Fintype.card (Fin n → Ω) : ℝ)
      = B.card * (1 - (1 - 1 / (Fintype.card Ω : ℝ)) ^ n) := by
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs := sum_occ n B
  have hle : (Fintype.card Ω - 1)^n ≤ Fintype.card Ω ^ n := Nat.pow_le_pow_left (Nat.sub_le _ _) n
  have : (∑ ω : Fin n → Ω, (occ n B ω : ℝ)) = ((∑ ω : Fin n → Ω, occ n B ω : ℕ) : ℝ) := by push_cast; rfl
  rw [this, hs, Fintype.card_fun, Fintype.card_fin]
  have hc : ((Fintype.card Ω - 1 : ℕ) : ℝ) = (Fintype.card Ω : ℝ) - 1 := by
    rw [Nat.cast_sub Fintype.card_pos]; simp
  push_cast [Nat.cast_sub hle, hc]
  field_simp
  rw [div_pow]
  field_simp


lemma optimum_complete (n : ℕ) (hn : 0 < n)
    (ω : Fin (completeInstance n hn).n → (completeInstance n hn).Copy) :
    optimum (completeInstance n hn) ω = n := by
  unfold optimum
  apply le_antisymm
  · apply Finset.sup_le
    intro R _
    split_ifs with h
    · obtain ⟨_, _, h3⟩ := h
      have : R.card ≤ (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.2)
        · intro p _; simp [completeInstance]
        · intro p hp q hq hpq
          have hp' : p ∈ R.filter (fun x => x.2 = p.2) := Finset.mem_filter.mpr ⟨hp, rfl⟩
          have hq' : q ∈ R.filter (fun x => x.2 = p.2) := Finset.mem_filter.mpr ⟨hq, hpq.symm⟩
          exact Finset.card_le_one.mp (h3 p.2) p hp' q hq'
      simpa [completeInstance] using this
    · exact Nat.zero_le _
  · obtain ⟨R0, hR, hc⟩ : ∃ R0 : Finset (Fin n × Fin (completeInstance n hn).n),
        IsRealizationMatching (completeInstance n hn) ω R0 ∧ R0.card = n := by
      refine ⟨Finset.univ.image (fun t : Fin n => ((t, t) : Fin n × Fin (completeInstance n hn).n)), ?_, ?_⟩
      · unfold IsRealizationMatching
        refine ⟨?_, ?_, ?_⟩
        · intro p _; simp [completeInstance]
        · intro a
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          have : t = s := h1.trans h2.symm
          subst this; rfl
        · intro t
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t1, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          have : t1 = s := h1.trans h2.symm
          subst this; rfl
      · exact (Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)).trans (by simp)
    have := Finset.le_sup (f := fun R : Finset (Fin n × Fin (completeInstance n hn).n) =>
      if IsRealizationMatching (completeInstance n hn) ω R then R.card else 0)
      (Finset.mem_univ R0)
    beta_reduce at this
    rw [if_pos hR] at this
    omega


lemma expectedAlgorithm_eq (inst : Instance A I) (M : Finset (A × I)) (label : inst.Copy → Option A)
    (hl : IsLabelling inst M label) :
    expectedAlgorithm inst label =
      (coveredAds M).card * (1 - (1 - 1 / (inst.n : ℝ)) ^ inst.n) := by
  haveI : Nonempty inst.Copy := by
    rw [← Fintype.card_pos_iff, card_copy]; exact inst.n_pos
  unfold expectedAlgorithm uniformExpectation
  have : ∀ ω : Fin inst.n → inst.Copy, (algorithm inst label ω : ℝ) = (occ inst.n (labB inst label) ω : ℝ) := by
    intro ω; rw [algorithm_eq_occ inst label hl.2 ω]
  simp only [this]
  rw [expect_occ, labB_card inst M label hl, card_copy]

lemma tightness_core (n : ℕ) (hn : 0 < n) (M : Finset (Fin n × Fin n))
    (hM : IsMaxBMatching (completeInstance n hn) M)
    (label : (completeInstance n hn).Copy → Option (Fin n))
    (hlabel : IsLabelling (completeInstance n hn) M label) :
    (∀ ω : Fin (completeInstance n hn).n → (completeInstance n hn).Copy,
      optimum (completeInstance n hn) ω = n) ∧
      expectedAlgorithm (completeInstance n hn) label =
        (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n) := by
  refine ⟨optimum_complete n hn, ?_⟩
  rw [expectedAlgorithm_eq _ M label hlabel]
  have hcov : (coveredAds M).card = n := by
    apply le_antisymm
    · calc (coveredAds M).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := by simp
    · have hid : IsBMatching (completeInstance n hn) (Finset.univ.image (fun a : Fin n => (a, a))) := by
        unfold IsBMatching
        refine ⟨?_, ?_, ?_⟩
        · intro p _; simp [completeInstance]
        · intro a
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          subst h1; subst h2; rfl
        · intro i
          simp only [completeInstance]
          apply Finset.card_le_one.mpr
          intro p hp q hq
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
          obtain ⟨⟨t, rfl⟩, h1⟩ := hp
          obtain ⟨⟨s, rfl⟩, h2⟩ := hq
          simp at h1 h2
          subst h1; subst h2; rfl
      have h1 := hM.2 _ hid
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)] at h1
      simp at h1
      have h2 : M.card ≤ (coveredAds M).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1)
        · intro p hp
          simp only [coveredAds, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          exact ⟨p.2, hp⟩
        · intro p hp q hq hpq
          have h3 := hM.1.2.1 p.1
          exact Finset.card_le_one.mp h3 p (by simpa using Finset.mem_coe.mp hp) q (by simp only [Finset.mem_filter]; exact ⟨Finset.mem_coe.mp hq, hpq.symm⟩)
      omega
  rw [hcov]
  simp [completeInstance]

end OnlineStochMatching.SuggestedMatching

open OnlineStochMatching.SuggestedMatching


theorem solution :
    ∀ (n : ℕ) (hn : 0 < n),
      let inst := completeInstance n hn
      ∀ (M : Finset (Fin n × Fin n)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option (Fin n)) (hlabel : IsLabelling inst M label),
        (∀ ω : Fin inst.n → inst.Copy, optimum inst ω = n) ∧
          expectedAlgorithm inst label =
            (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n) := by
  exact tightness_core
