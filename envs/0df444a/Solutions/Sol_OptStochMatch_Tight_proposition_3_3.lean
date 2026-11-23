-- Prove2me | solution 1 for OptStochMatch.Tight.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:44:23.940008+00:00
-- url     : https://prove2.me/submissions/7aefd58f-372e-4b9e-8e0c-b3faf883383d

import Definitions.Def_OptStochMatch_Tight_Basic

namespace AuxProp33

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

def NestedFamily {α : Type*} [PartialOrder α] (C : Finset α) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a

noncomputable def finiteChains {α : Type*} [DecidableEq α] [PartialOrder α]
    (Q : Finset α) : Finset (Finset α) := by
  classical
  exact Q.powerset.filter NestedFamily

noncomputable def chainWeight {α : Type*} (C : Finset α) : ℝ := (-1 : ℝ) ^ C.card

noncomputable def reducedChainSum {α : Type*} [DecidableEq α] [PartialOrder α]
    (Q : Finset α) : ℝ :=
  ∑ C ∈ finiteChains Q, chainWeight C

def toggleVertex {α : Type*} [DecidableEq α] (c : α) (C : Finset α) : Finset α :=
  if c ∈ C then C.erase c else insert c C

lemma mem_finiteChains {α : Type*} [DecidableEq α] [PartialOrder α] {Q C : Finset α} :
    C ∈ finiteChains Q ↔ C ⊆ Q ∧ NestedFamily C := by
  classical
  simp only [finiteChains, Finset.mem_filter, Finset.mem_powerset]

lemma nested_subset {α : Type*} [PartialOrder α] {C D : Finset α}
    (hC : NestedFamily C) (hDC : D ⊆ C) : NestedFamily D :=
  fun a ha b hb => hC a (hDC ha) b (hDC hb)

lemma nested_insert {α : Type*} [DecidableEq α] [PartialOrder α] {C : Finset α} {c : α}
    (hC : NestedFamily C) (hc : ∀ a ∈ C, a ≤ c ∨ c ≤ a) : NestedFamily (insert c C) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with rfl | haC
  · rcases Finset.mem_insert.mp hb with rfl | hbC
    · exact Or.inl le_rfl
    · exact (hc b hbC).symm
  · rcases Finset.mem_insert.mp hb with rfl | hbC
    · exact hc a haC
    · exact hC a haC b hbC

lemma toggleVertex_involution {α : Type*} [DecidableEq α] (c : α) (C : Finset α) :
    toggleVertex c (toggleVertex c C) = C := by
  by_cases hc : c ∈ C <;> simp [toggleVertex, hc, Finset.insert_erase]

lemma toggleVertex_ne {α : Type*} [DecidableEq α] (c : α) (C : Finset α) :
    toggleVertex c C ≠ C := by
  intro he
  by_cases hc : c ∈ C
  · have ht : c ∉ toggleVertex c C := by simp [toggleVertex, hc]
    exact ht (he.symm ▸ hc)
  · exact hc (he ▸ by simp [toggleVertex, hc])

lemma chainWeight_toggle {α : Type*} [DecidableEq α] (c : α) (C : Finset α) :
    chainWeight C + chainWeight (toggleVertex c C) = 0 := by
  by_cases hc : c ∈ C
  · change (-1 : ℝ) ^ C.card + (-1 : ℝ) ^ (toggleVertex c C).card = 0
    rw [toggleVertex, if_pos hc, ← Finset.card_erase_add_one hc, pow_succ]
    ring
  · change (-1 : ℝ) ^ C.card + (-1 : ℝ) ^ (toggleVertex c C).card = 0
    rw [toggleVertex, if_neg hc, Finset.card_insert_of_notMem hc, pow_succ]
    ring

lemma toggleVertex_mem_chains {α : Type*} [DecidableEq α] [PartialOrder α] {Q C : Finset α} {c : α}
    (hC : C ∈ finiteChains Q) (hcQ : c ∈ Q) (hc : ∀ a ∈ C, a ≤ c ∨ c ≤ a) :
    toggleVertex c C ∈ finiteChains Q := by
  obtain ⟨hsub, hnest⟩ := mem_finiteChains.mp hC
  refine mem_finiteChains.mpr ?_
  unfold toggleVertex
  split_ifs with hcC
  · exact ⟨(Finset.erase_subset c C).trans hsub, nested_subset hnest (Finset.erase_subset c C)⟩
  · exact ⟨Finset.insert_subset hcQ hsub, nested_insert hnest hc⟩

lemma chainWeight_sum_cancel {α : Type*} [DecidableEq α] (S : Finset (Finset α)) (c : α)
    (hS : ∀ C ∈ S, toggleVertex c C ∈ S) : ∑ C ∈ S, chainWeight C = 0 :=
  Finset.sum_involution (fun C _ => toggleVertex c C)
    (fun C _ => chainWeight_toggle c C) (fun C _ _ => toggleVertex_ne c C)
    hS (fun C _ => toggleVertex_involution c C)

lemma reducedChainSum_apex {α : Type*} [DecidableEq α] [PartialOrder α]
    (Q : Finset α) (c : α) (hcQ : c ∈ Q) (hc : ∀ a ∈ Q, a ≤ c ∨ c ≤ a) :
    reducedChainSum Q = 0 :=
  chainWeight_sum_cancel (finiteChains Q) c fun C hC =>
    toggleVertex_mem_chains hC hcQ fun a ha => hc a ((mem_finiteChains.mp hC).1 ha)

lemma finiteChains_erase {α : Type*} [DecidableEq α] [PartialOrder α] (Q : Finset α) (a : α) :
    finiteChains (Q.erase a) = (finiteChains Q).filter fun C => a ∉ C := by
  classical
  ext C
  rw [mem_finiteChains, Finset.mem_filter, mem_finiteChains]
  constructor
  · rintro ⟨hsub, hn⟩
    exact ⟨⟨fun b hb => Finset.mem_of_mem_erase (hsub hb), hn⟩,
      fun ha => (Finset.mem_erase.mp (hsub ha)).1 rfl⟩
  · rintro ⟨⟨hsub, hn⟩, ha⟩
    exact ⟨fun b hb => Finset.mem_erase.mpr ⟨fun hba => ha (hba ▸ hb), hsub hb⟩, hn⟩

lemma reducedChainSum_delete_dominated {α : Type*} [DecidableEq α] [PartialOrder α]
    (Q : Finset α) (a c : α) (hac : a ≠ c) (hcQ : c ∈ Q)
    (hdom : ∀ C ∈ finiteChains Q, a ∈ C → ∀ b ∈ C, b ≤ c ∨ c ≤ b) :
    reducedChainSum Q = reducedChainSum (Q.erase a) := by
  classical
  have hz : ∑ C ∈ (finiteChains Q).filter (fun C => a ∈ C), chainWeight C = 0 := by
    refine chainWeight_sum_cancel _ c fun C hC => ?_
    obtain ⟨hchain, haC⟩ := Finset.mem_filter.mp hC
    refine Finset.mem_filter.mpr ⟨toggleVertex_mem_chains hchain hcQ (hdom C hchain haC), ?_⟩
    unfold toggleVertex
    split_ifs <;> simp [hac, haC]
  have hs := Finset.sum_filter_add_sum_filter_not (finiteChains Q) (fun C => a ∈ C) chainWeight
  rw [hz, zero_add, ← finiteChains_erase] at hs
  exact hs.symm

lemma reducedChainSum_union_closed {ι : Type*} [DecidableEq ι]
    (Q : Finset (Finset ι)) (B : Finset ι) (hBQ : B ∈ Q)
    (hclosed : ∀ A ∈ Q, A ∪ B ∈ Q) : reducedChainSum Q = 0 := by
  classical
  induction Q using Finset.strongInduction generalizing B with
  | H Q ih =>
    by_cases hall : ∀ A ∈ Q, B ⊆ A
    · exact reducedChainSum_apex Q B hBQ fun A hA => Or.inr (hall A hA)
    · have hbad : (Q.filter fun A => ¬ B ⊆ A).Nonempty := by
        obtain ⟨A, hA, hBA⟩ : ∃ A ∈ Q, ¬ B ⊆ A := by simpa using hall
        exact ⟨A, Finset.mem_filter.mpr ⟨hA, hBA⟩⟩
      obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image (Q.filter fun A => ¬ B ⊆ A) Finset.card hbad
      obtain ⟨hAQ, hBA⟩ := Finset.mem_filter.mp hA
      have hAC : A ≠ A ∪ B := fun he => hBA (he ▸ Finset.subset_union_right)
      have hdom : ∀ C ∈ finiteChains Q, A ∈ C → ∀ U ∈ C, U ⊆ A ∪ B ∨ A ∪ B ⊆ U := by
        intro C hC hAC' U hUC
        obtain ⟨hCQ, hn⟩ := mem_finiteChains.mp hC
        rcases hn A hAC' U hUC with hAU | hUA
        · by_cases hBU : B ⊆ U
          · exact Or.inr (Finset.union_subset hAU hBU)
          · have hcard := hmax U (Finset.mem_filter.mpr ⟨hCQ hUC, hBU⟩)
            have he := Finset.eq_of_subset_of_card_le hAU hcard
            exact Or.inl (he ▸ Finset.subset_union_left)
        · exact Or.inl (hUA.trans Finset.subset_union_left)
      rw [reducedChainSum_delete_dominated Q A (A ∪ B) hAC (hclosed A hAQ) hdom]
      refine ih (Q.erase A) (Finset.erase_ssubset hAQ) B ?_ ?_
      · exact Finset.mem_erase.mpr ⟨fun he => hBA (he ▸ le_rfl), hBQ⟩
      · intro U hU
        exact Finset.mem_erase.mpr
          ⟨fun he => hBA (he ▸ Finset.subset_union_right), hclosed U (Finset.mem_of_mem_erase hU)⟩

lemma pointwise_chain_identity {m : ℕ} (d : Finset (Fin m) → ℝ)
    (hsuper : ∀ A B : Finset (Fin m), d A + d B ≤ d (A ∪ B) + d (A ∩ B))
    (hempty : d ∅ = 0) (a : ℝ) (ha : 0 ≤ a) :
    (if a < Finset.univ.sup' Finset.univ_nonempty d then (1 : ℝ) else 0) =
      ∑ k ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (k - 1) *
        ∑ c ∈ (Finset.univ.filter fun c : Fin k → Finset (Fin m) =>
            StrictMono c ∧ ∀ r, (c r).Nonempty),
          (if ∀ r, a < d (c r) then (1 : ℝ) else 0) := by
  classical
  let Q : Finset (Finset (Fin m)) := Finset.univ.filter fun A => a < d A
  have hsup_iff : a < Finset.univ.sup' Finset.univ_nonempty d ↔ Q.Nonempty := by
    rw [Finset.lt_sup'_iff]
    constructor
    · rintro ⟨A, hA, hlt⟩; exact ⟨A, Finset.mem_filter.mpr ⟨hA, hlt⟩⟩
    · rintro ⟨A, hA⟩; exact ⟨A, Finset.mem_univ A, (Finset.mem_filter.mp hA).2⟩
  have heuler : (if Q.Nonempty then (1 : ℝ) else 0) =
      ∑ C ∈ (finiteChains Q).erase ∅, -chainWeight C := by
    have he_mem : (∅ : Finset (Finset (Fin m))) ∈ finiteChains Q :=
      mem_finiteChains.mpr ⟨Finset.empty_subset _, by simp [NestedFamily]⟩
    have hs := Finset.sum_erase_add (s := finiteChains Q) chainWeight he_mem
    have hw0 : chainWeight (∅ : Finset (Finset (Fin m))) = 1 := by simp [chainWeight]
    rw [hw0] at hs
    have hsub : ∑ C ∈ (finiteChains Q).erase ∅, -chainWeight C = 1 - reducedChainSum Q := by
      rw [Finset.sum_neg_distrib]
      unfold reducedChainSum
      linarith
    rw [hsub]
    by_cases hQ : Q.Nonempty
    · rw [if_pos hQ]
      obtain ⟨B, _, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin m))) d Finset.univ_nonempty
      obtain ⟨A₀, hA₀⟩ := hQ
      have hBQ : B ∈ Q := Finset.mem_filter.mpr
        ⟨Finset.mem_univ B, ((Finset.mem_filter.mp hA₀).2).trans_le (hm A₀ (Finset.mem_univ A₀))⟩
      have hclosed : ∀ A ∈ Q, A ∪ B ∈ Q := by
        intro A hA
        have hdA : a < d A := (Finset.mem_filter.mp hA).2
        have h1 := hsuper A B
        have h2 := hm (A ∩ B) (Finset.mem_univ _)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
      rw [reducedChainSum_union_closed Q B hBQ hclosed, sub_zero]
    · rw [if_neg hQ]
      have hQ_emp : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      have hf_emp : finiteChains (∅ : Finset (Finset (Fin m))) = {∅} := by
        ext C
        rw [mem_finiteChains, Finset.mem_singleton]
        refine ⟨fun h => Finset.subset_empty.mp h.1, ?_⟩
        rintro rfl; exact ⟨Finset.empty_subset _, by simp [NestedFamily]⟩
      unfold reducedChainSum
      rw [hQ_emp, hf_emp]; simp [chainWeight]
  let Good : Finset (Finset (Finset (Fin m))) :=
    (finiteChains (Finset.univ : Finset (Finset (Fin m)))).filter fun C =>
      C.Nonempty ∧ ∀ A ∈ C, A.Nonempty
  have hgood_rewrite : ∑ C ∈ (finiteChains Q).erase ∅, -chainWeight C =
      ∑ C ∈ Good, if ∀ A ∈ C, a < d A then -chainWeight C else 0 := by
    have hQ_sub : (finiteChains Q).erase ∅ ⊆ Good := by
      intro C hC
      obtain ⟨hne, hCQ⟩ := Finset.mem_erase.mp hC
      obtain ⟨hsub, hnest⟩ := mem_finiteChains.mp hCQ
      refine Finset.mem_filter.mpr ⟨mem_finiteChains.mpr ⟨Finset.subset_univ _, hnest⟩,
        Finset.nonempty_iff_ne_empty.mpr hne, fun A hAC => ?_⟩
      by_contra hAemp
      have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAemp
      have hdA : a < d A := (Finset.mem_filter.mp (hsub hAC)).2
      rw [hAe, hempty] at hdA
      linarith
    trans ∑ C ∈ (finiteChains Q).erase ∅, if ∀ A ∈ C, a < d A then -chainWeight C else 0
    · refine Finset.sum_congr rfl fun C hC => ?_
      have hsub := (mem_finiteChains.mp (Finset.mem_erase.mp hC).2).1
      rw [if_pos fun A hAC => (Finset.mem_filter.mp (hsub hAC)).2]
    · refine Finset.sum_subset hQ_sub fun C hCG hnot => ?_
      rw [if_neg]; intro hall
      apply hnot
      obtain ⟨hC_all, hC_ne, _⟩ := Finset.mem_filter.mp hCG
      exact Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp hC_ne,
        mem_finiteChains.mpr ⟨fun A hAC => Finset.mem_filter.mpr ⟨Finset.mem_univ A, hall A hAC⟩,
          (mem_finiteChains.mp hC_all).2⟩⟩
  have hcard_inj : ∀ C ∈ Good, Set.InjOn Finset.card (C : Set (Finset (Fin m))) := by
    intro C hC A hA B hB hcard
    have hnest := (mem_finiteChains.mp (Finset.mem_filter.mp hC).1).2
    rcases hnest A hA B hB with hAB | hBA
    · exact Finset.eq_of_subset_of_card_le hAB (le_of_eq hcard.symm)
    · exact (Finset.eq_of_subset_of_card_le hBA (le_of_eq hcard)).symm
  have hcard_Icc : ∀ C ∈ Good, C.card ∈ Finset.Icc 1 m := by
    intro C hC
    obtain ⟨_, hC_ne, hA_ne⟩ := Finset.mem_filter.mp hC
    have himg : C.image Finset.card ⊆ Finset.Icc 1 m := by
      intro n hn
      obtain ⟨A, hAC, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr ⟨Finset.Nonempty.card_pos (hA_ne A hAC),
        (Finset.card_le_univ A).trans (by simp)⟩
    have hceq : (C.image Finset.card).card = C.card := Finset.card_image_of_injOn (hcard_inj C hC)
    have hle : C.card ≤ m := by
      have := Finset.card_le_card himg
      rw [hceq, Nat.card_Icc] at this
      omega
    exact Finset.mem_Icc.mpr ⟨Finset.Nonempty.card_pos hC_ne, hle⟩
  have hite_sup : (if a < Finset.univ.sup' Finset.univ_nonempty d then (1 : ℝ) else 0) =
      if Q.Nonempty then 1 else 0 := if_congr hsup_iff rfl rfl
  rw [hite_sup, heuler, hgood_rewrite,
    ← Finset.sum_fiberwise_of_maps_to hcard_Icc]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hsign : (-1 : ℝ) ^ (k - 1) = -((-1 : ℝ) ^ k) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hk_eq, pow_succ]
    ring
  rw [Finset.mul_sum]
  let ChainsK := Good.filter fun C => C.card = k
  let MapsK := Finset.univ.filter fun c : Fin k → Finset (Fin m) =>
    StrictMono c ∧ ∀ r, (c r).Nonempty
  refine Finset.sum_bij'
    (fun (C : Finset (Finset (Fin m))) (_ : C ∈ ChainsK) =>
      if h : C ∈ ChainsK then
        let hCG := (Finset.mem_filter.mp h).1
        let hCk := (Finset.mem_filter.mp h).2
        let hcards : (C.image Finset.card).card = k := by
          rw [Finset.card_image_of_injOn (hcard_inj C hCG), hCk]
        let o := (C.image Finset.card).orderEmbOfFin hcards
        fun r : Fin k => Classical.choose (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
      else fun _ => ∅)
    (fun (c : Fin k → Finset (Fin m)) (_ : c ∈ MapsK) => Finset.univ.image c)
    ?_ ?_ ?_ ?_ ?_
  · intro C hC
    rw [dif_pos hC]
    have hCG := (Finset.mem_filter.mp hC).1
    have hCk := (Finset.mem_filter.mp hC).2
    have hnest := (mem_finiteChains.mp (Finset.mem_filter.mp hCG).1).2
    have hAne := (Finset.mem_filter.mp hCG).2.2
    have hcards : (C.image Finset.card).card = k := by
      rw [Finset.card_image_of_injOn (hcard_inj C hCG), hCk]
    let f : Fin k → Finset (Fin m) := fun r =>
      Classical.choose (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
    have hf_spec : ∀ r, f r ∈ C ∧ (f r).card = (C.image Finset.card).orderEmbOfFin hcards r :=
      fun r => Classical.choose_spec (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, fun r => hAne (f r) (hf_spec r).1⟩
    intro r₁ r₂ hr
    have hlt_card : (f r₁).card < (f r₂).card := by
      rw [(hf_spec r₁).2, (hf_spec r₂).2]
      exact ((C.image Finset.card).orderEmbOfFin hcards).strictMono hr
    rcases hnest (f r₁) (hf_spec r₁).1 (f r₂) (hf_spec r₂).1 with h12 | h21
    · exact lt_of_le_of_ne h12 fun heq => (ne_of_lt hlt_card) (congrArg Finset.card heq)
    · exact absurd (Finset.card_le_card h21) (not_le_of_gt hlt_card)
  · intro c hc
    obtain ⟨_, hsm, hne⟩ := Finset.mem_filter.mp hc
    have h0 : 0 < k := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_finiteChains.mpr ⟨Finset.subset_univ _, ?_⟩,
      ⟨c ⟨0, h0⟩, Finset.mem_image.mpr ⟨⟨0, h0⟩, Finset.mem_univ _, rfl⟩⟩, ?_⟩,
      by rw [Finset.card_image_of_injective _ hsm.injective, Finset.card_fin]⟩
    · intro A hA B hB
      obtain ⟨r₁, _, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨r₂, _, rfl⟩ := Finset.mem_image.mp hB
      rcases le_total r₁ r₂ with h12 | h21
      · exact Or.inl (hsm.monotone h12)
      · exact Or.inr (hsm.monotone h21)
    · intro A hA
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hA
      exact hne r
  · intro C hC
    rw [dif_pos hC]
    have hCG := (Finset.mem_filter.mp hC).1
    have hCk := (Finset.mem_filter.mp hC).2
    have hnest := (mem_finiteChains.mp (Finset.mem_filter.mp hCG).1).2
    have hcards : (C.image Finset.card).card = k := by
      rw [Finset.card_image_of_injOn (hcard_inj C hCG), hCk]
    let f : Fin k → Finset (Fin m) := fun r =>
      Classical.choose (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
    have hf_spec : ∀ r, f r ∈ C ∧ (f r).card = (C.image Finset.card).orderEmbOfFin hcards r :=
      fun r => Classical.choose_spec (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
    have hsub : Finset.univ.image f ⊆ C := by
      intro A hA
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hA
      exact (hf_spec r).1
    have hfinj : Function.Injective f := by
      intro r₁ r₂ heq
      have hce := congrArg Finset.card heq
      rw [(hf_spec r₁).2, (hf_spec r₂).2] at hce
      exact ((C.image Finset.card).orderEmbOfFin hcards).injective hce
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_fin, hCk]
  · intro c hc
    obtain ⟨_, hsm, hne⟩ := Finset.mem_filter.mp hc
    let C := Finset.univ.image c
    have hC : C ∈ ChainsK := by
      have h0 : 0 < k := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_finiteChains.mpr ⟨Finset.subset_univ _, ?_⟩,
        ⟨c ⟨0, h0⟩, Finset.mem_image.mpr ⟨⟨0, h0⟩, Finset.mem_univ _, rfl⟩⟩, ?_⟩,
        by rw [Finset.card_image_of_injective _ hsm.injective, Finset.card_fin]⟩
      · intro A hA B hB
        obtain ⟨r₁, _, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨r₂, _, rfl⟩ := Finset.mem_image.mp hB
        rcases le_total r₁ r₂ with h12 | h21
        · exact Or.inl (hsm.monotone h12)
        · exact Or.inr (hsm.monotone h21)
      · intro A hA
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hA
        exact hne r
    rw [dif_pos hC]
    have hCG := (Finset.mem_filter.mp hC).1
    have hCk := (Finset.mem_filter.mp hC).2
    have hcards : (C.image Finset.card).card = k := by
      rw [Finset.card_image_of_injOn (hcard_inj C hCG), hCk]
    have hc_card_sm : StrictMono (fun r => (c r).card) := fun r₁ r₂ hr => Finset.card_lt_card (hsm hr)
    have ho_eq : ∀ r, (C.image Finset.card).orderEmbOfFin hcards r = (c r).card := by
      have huniq := Finset.orderEmbOfFin_unique hcards
        (fun r => Finset.mem_image.mpr ⟨c r, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, rfl⟩)
        hc_card_sm
      intro r; rw [← huniq]
    funext r
    have hspec := Classical.choose_spec (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
    exact hcard_inj C hCG hspec.1 (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
      (hspec.2.trans (ho_eq r))
  · intro C hC
    rw [dif_pos hC]
    have hCG := (Finset.mem_filter.mp hC).1
    have hCk := (Finset.mem_filter.mp hC).2
    have hcards : (C.image Finset.card).card = k := by
      rw [Finset.card_image_of_injOn (hcard_inj C hCG), hCk]
    let f : Fin k → Finset (Fin m) := fun r =>
      Classical.choose (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
    have hf_spec : ∀ r, f r ∈ C ∧ (f r).card = (C.image Finset.card).orderEmbOfFin hcards r :=
      fun r => Classical.choose_spec (Finset.mem_image.mp (Finset.orderEmbOfFin_mem _ hcards r))
    have hfinj : Function.Injective f := by
      intro r₁ r₂ heq
      have hce := congrArg Finset.card heq
      rw [(hf_spec r₁).2, (hf_spec r₂).2] at hce
      exact ((C.image Finset.card).orderEmbOfFin hcards).injective hce
    have himg : Finset.univ.image f = C := by
      refine Finset.eq_of_subset_of_card_le (fun A hA => ?_) ?_
      · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hA; exact (hf_spec r).1
      · rw [Finset.card_image_of_injective _ hfinj, Finset.card_fin, hCk]
    have hiff : (∀ A ∈ C, a < d A) ↔ ∀ r, a < d (f r) := by
      rw [← himg]; simp
    have hcw : -chainWeight C = (-1 : ℝ) ^ (k - 1) := by
      unfold chainWeight
      rw [hCk, hsign]
    rw [hcw]
    by_cases h1 : ∀ A ∈ C, a < d A
    · rw [if_pos h1, if_pos (hiff.mp h1), mul_one]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mpr h2)), mul_zero]

end AuxProp33

open MeasureTheory ProbabilityTheory AuxProp33
open scoped BigOperators

theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → Finset (Fin m) → ℝ)
    (hd_meas : ∀ A : Finset (Fin m), Measurable fun ω => d ω A)
    (hsuper : ∀ᵐ ω ∂μ, ∀ A B : Finset (Fin m),
      d ω A + d ω B ≤ d ω (A ∪ B) + d ω (A ∩ B))
    (hempty : ∀ᵐ ω ∂μ, d ω ∅ = 0) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {ω | a < Finset.univ.sup' Finset.univ_nonempty (d ω)} =
      ∑ k ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (k - 1) *
        ∑ c ∈ (Finset.univ.filter fun c : Fin k → Finset (Fin m) =>
            StrictMono c ∧ ∀ r, (c r).Nonempty),
          μ.real {ω | ∀ r, a < d ω (c r)} := by
  classical
  let Emax : Set Ω := {ω | a < Finset.univ.sup' Finset.univ_nonempty (d ω)}
  have hEmax_meas : MeasurableSet Emax := by
    have heq : Emax = ⋃ A : Finset (Fin m), {ω | a < d ω A} := by
      ext ω; simp [Emax, Finset.lt_sup'_iff]
    rw [heq]
    exact MeasurableSet.iUnion fun A => measurableSet_lt measurable_const (hd_meas A)
  have hEc_meas : ∀ (k : ℕ) (c : Fin k → Finset (Fin m)), MeasurableSet {ω | ∀ r, a < d ω (c r)} := by
    intro k c
    have heq : {ω | ∀ r, a < d ω (c r)} = ⋂ r : Fin k, {ω | a < d ω (c r)} := by
      ext ω; simp
    rw [heq]
    exact MeasurableSet.iInter fun r => measurableSet_lt measurable_const (hd_meas (c r))
  have hae : Emax.indicator (fun _ => (1 : ℝ)) =ᵐ[μ]
      fun ω => ∑ k ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (k - 1) *
        ∑ c ∈ (Finset.univ.filter fun c : Fin k → Finset (Fin m) =>
            StrictMono c ∧ ∀ r, (c r).Nonempty),
          ({ω' | ∀ r, a < d ω' (c r)} : Set Ω).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hsuper, hempty] with ω hsupω hempω
    have hp := pointwise_chain_identity (d ω) hsupω hempω a ha
    have hlhs : Emax.indicator (fun _ => (1 : ℝ)) ω =
        if a < Finset.univ.sup' Finset.univ_nonempty (d ω) then (1 : ℝ) else 0 := by
      by_cases h : a < Finset.univ.sup' Finset.univ_nonempty (d ω)
      · rw [Set.indicator_of_mem (show ω ∈ Emax from h), if_pos h]
      · rw [Set.indicator_of_notMem (show ω ∉ Emax from h), if_neg h]
    rw [hlhs, hp]
    refine Finset.sum_congr rfl fun k _ => congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
    by_cases h : ∀ r, a < d ω (c r)
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω' | ∀ r, a < d ω' (c r)} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω' | ∀ r, a < d ω' (c r)} from h)]
  have hint_ind : ∀ {S : Set Ω}, MeasurableSet S →
      Integrable (S.indicator fun _ => (1 : ℝ)) μ ∧
      (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real S := by
    intro S hS
    refine ⟨(integrable_const (1 : ℝ)).indicator hS, ?_⟩
    rw [integral_indicator_const _ hS, smul_eq_mul, mul_one]
  have hi := integral_congr_ae hae
  rw [(hint_ind hEmax_meas).2] at hi
  rw [integral_finset_sum _ fun k _ => Integrable.const_mul
    (integrable_finset_sum _ fun c _ => (hint_ind (hEc_meas k c)).1) _] at hi
  rw [hi]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_finset_sum _ fun c _ => (hint_ind (hEc_meas k c)).1]
  congr 1
  exact Finset.sum_congr rfl fun c _ => (hint_ind (hEc_meas k c)).2
