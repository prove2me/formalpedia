-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.continuous_iff_completelyAdditive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:19:53.079542+00:00
-- url     : https://prove2.me/submissions/c6d38f60-fedf-4358-9148-45e7d0e875b7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_finadd {A : Type u} [CompleteBooleanAlgebra A] {I : Type*} [DecidableEq I]
    (nu : A → ℝ≥0) (hv : IsValuation nu) (x : I → A)
    (hx : ∀ i j, i ≠ j → x i ⊓ x j = ⊥) (F : Finset I) :
    ∑ i ∈ F, nu (x i) = nu (F.sup x) := by
  induction F using Finset.induction_on with
  | empty => simp [hv.1]
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.sup_insert, ih]
    have hd : x i ⊓ F.sup x = ⊥ := by
      rw [← disjoint_iff, Finset.disjoint_sup_right]
      intro j hj
      rw [disjoint_iff]
      exact hx i j (fun h => hi (h ▸ hj))
    have := hv.2 (x i) (F.sup x)
    rw [hd, hv.1, add_zero] at this
    exact this

theorem solution (A : Type u) [CompleteBooleanAlgebra A]
    (nu : A → ℝ≥0) :
    IsPositiveContinuousValuation nu ↔ IsCompletelyAdditiveValuation nu := by
  classical
  constructor
  · rintro ⟨hv, hmono, hcont⟩
    refine ⟨hv, hmono, fun I x hx => ?_⟩
    apply hasSum_of_isLUB
    let S : Set A := Set.range (fun F : Finset I => F.sup x)
    have hS : IsLUB S (iSup x) := by
      constructor
      · rintro _ ⟨F, rfl⟩
        exact Finset.sup_le (fun i _ => le_iSup x i)
      · intro u hu
        apply iSup_le
        intro i
        have := hu ⟨{i}, rfl⟩
        simpa using this
    have hdir : DirectedOn (· ≤ ·) S := by
      rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
      exact ⟨(F ∪ G).sup x, ⟨F ∪ G, rfl⟩, Finset.sup_mono Finset.subset_union_left,
        Finset.sup_mono Finset.subset_union_right⟩
    have h := hcont S (iSup x) ⟨_, ⟨∅, rfl⟩⟩ hdir hS
    have he : nu '' S = Set.range (fun F : Finset I => ∑ i ∈ F, nu (x i)) := by
      ext r
      simp only [S, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨F, rfl⟩, rfl⟩; exact ⟨F, g67c_finadd nu hv x hx F⟩
      · rintro ⟨F, rfl⟩; exact ⟨_, ⟨F, rfl⟩, (g67c_finadd nu hv x hx F).symm⟩
    rw [he] at h
    exact h
  · rintro ⟨hv, hmono, hadd⟩
    refine ⟨hv, hmono, fun s a hsne hdir hlub => ?_⟩
    refine ⟨fun _ ⟨y, hy, hye⟩ => hye ▸ hmono (hlub.1 hy), fun c hc => ?_⟩
    have hc' : ∀ d ∈ s, nu d ≤ c := fun d hd => hc ⟨d, hd, rfl⟩
    have ha : a = sSup s := hlub.unique (isLUB_sSup s)
    let P : Set A := {x | x ≠ ⊥ ∧ ∃ d ∈ s, x ≤ d}
    let 𝒮 : Set (Set A) := {T | T ⊆ P ∧ T.PairwiseDisjoint id}
    obtain ⟨T, hTm⟩ := zorn_subset 𝒮 (by
      intro C hC hchain
      refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun T hT => Set.subset_sUnion_of_mem hT⟩
      · rintro x ⟨T, hT, hx⟩; exact (hC hT).1 hx
      · rintro x ⟨T1, hT1, hx⟩ y ⟨T2, hT2, hy⟩ hxy
        rcases hchain.total hT1 hT2 with h | h
        · exact (hC hT2).2 (h hx) hy hxy
        · exact (hC hT1).2 hx (h hy) hxy)
    obtain ⟨⟨hTP, hTd⟩, hmax⟩ := hTm
    have hcover : a ≤ sSup T := by
      by_contra hne
      set r := a \ sSup T
      have hr : r ≠ ⊥ := fun h => hne (sdiff_eq_bot_iff.1 h)
      have hra : r ≤ sSup s := ha ▸ sdiff_le
      have : ∃ d ∈ s, r ⊓ d ≠ ⊥ := by
        by_contra hall
        push Not at hall
        apply hr
        rw [← inf_eq_left.2 hra, inf_sSup_eq]
        exact le_antisymm (iSup₂_le fun d hd => (hall d hd).le) bot_le
      obtain ⟨d, hd, hrd⟩ := this
      have hdisj : ∀ y ∈ T, Disjoint (r ⊓ d) y := by
        intro y hy
        exact Disjoint.mono_left inf_le_left
          (Disjoint.mono_right (le_sSup hy) disjoint_sdiff_self_left)
      have hnot : r ⊓ d ∉ T := by
        intro hmem
        exact hrd ((hdisj _ hmem).eq_bot_of_self)
      have hins : insert (r ⊓ d) T ∈ 𝒮 := by
        refine ⟨Set.insert_subset ⟨hrd, d, hd, inf_le_right⟩ hTP, ?_⟩
        refine hTd.insert (fun y hy _ => hdisj y hy)
      exact hnot (hmax hins (Set.subset_insert _ _) (Set.mem_insert _ _))
    have hsum := hadd T (fun i : T => i.val) (by
      intro i j hij
      exact disjoint_iff.1 (hTd i.2 j.2 (fun h => hij (Subtype.ext h))))
    have hsT : sSup T = ⨆ i : T, i.val := sSup_eq_iSup' T
    calc nu a ≤ nu (sSup T) := hmono hcover
      _ = nu (⨆ i : T, i.val) := by rw [hsT]
      _ ≤ c := by
        apply hasSum_le_of_sum_le hsum
        intro F
        rw [g67c_finadd nu hv (fun i : T => i.val) (fun i j hij =>
          disjoint_iff.1 (hTd i.2 j.2 (fun h => hij (Subtype.ext h)))) F]
        have hub : ∃ d ∈ s, ∀ i ∈ F, i.val ≤ d := by
          induction F using Finset.induction_on with
          | empty => obtain ⟨d, hd⟩ := hsne; exact ⟨d, hd, by simp⟩
          | insert i F hi ih =>
            obtain ⟨d, hd, hdF⟩ := ih
            obtain ⟨-, d', hd', hid'⟩ := hTP i.2
            obtain ⟨e, he, hde, hd'e⟩ := hdir d hd d' hd'
            refine ⟨e, he, fun j hj => ?_⟩
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact hid'.trans hd'e
            · exact (hdF j hj).trans hde
        obtain ⟨d, hd, hdF⟩ := hub
        exact (hmono (Finset.sup_le hdF)).trans (hc' d hd)
