-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P02.semifinitePart_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:10:41.241608+00:00
-- url     : https://prove2.me/submissions/5a147108-77a4-4c6c-8c9d-c35ab243d684

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

namespace A3SF

/-- Exhaustion: inside a finite-measure set `F`, there is a `nu`-null measurable
subset `E₀` such that every `nu`-null measurable subset of `F \ E₀` is `mu`-null. -/
theorem exhaust {X : Type u} [MeasurableSpace X] (mu nu : Measure X) (F : Set X)
    (hF : MeasurableSet F) (hFfin : mu F < ⊤) :
    ∃ E₀ : Set X, MeasurableSet E₀ ∧ E₀ ⊆ F ∧ nu E₀ = 0 ∧
      ∀ G : Set X, MeasurableSet G → G ⊆ F \ E₀ → nu G = 0 → mu G = 0 := by
  let A : Set ℝ≥0∞ := {m | ∃ E, MeasurableSet E ∧ E ⊆ F ∧ nu E = 0 ∧ mu E = m}
  have hA : A.Nonempty := ⟨0, ∅, MeasurableSet.empty, empty_subset _, by simp, by simp⟩
  have hAb : BddAbove A := ⟨⊤, fun _ _ => le_top⟩
  obtain ⟨w, -, hw, hwA⟩ := exists_seq_tendsto_sSup hA hAb
  choose E hEm hEF hEnu hEmu using hwA
  refine ⟨⋃ n, E n, MeasurableSet.iUnion hEm, iUnion_subset hEF,
    measure_iUnion_null hEnu, ?_⟩
  have hge : sSup A ≤ mu (⋃ n, E n) :=
    le_of_tendsto' hw (fun n => (hEmu n) ▸ measure_mono (subset_iUnion E n))
  intro G hG hGsub hGnu
  have hmem : mu ((⋃ n, E n) ∪ G) ∈ A :=
    ⟨_, (MeasurableSet.iUnion hEm).union hG,
      union_subset (iUnion_subset hEF) (fun x hx => (hGsub hx).1),
      measure_union_null (measure_iUnion_null hEnu) hGnu, rfl⟩
  have hle : mu ((⋃ n, E n) ∪ G) ≤ mu (⋃ n, E n) := (le_sSup hmem).trans hge
  have hdisj : Disjoint (⋃ n, E n) G :=
    Set.disjoint_left.2 (fun x hx hxG => (hGsub hxG).2 hx)
  rw [measure_union hdisj hG] at hle
  have hfin : mu (⋃ n, E n) ≠ ⊤ :=
    ne_top_of_le_ne_top hFfin.ne (measure_mono (iUnion_subset hEF))
  have hle' : mu (⋃ n, E n) + mu G ≤ mu (⋃ n, E n) + 0 := by rwa [add_zero]
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 hle') (zero_le)

theorem main {X : Type u} [MeasurableSpace X]
    (mu : Measure X) (hded : IsDedekindOn mu Set.univ) :
    ∃ S : Set X, IsSemifinitePart mu S ∧ IsSemifiniteOn mu S ∧ IsDedekindOn mu S ∧
      (∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → 0 < mu E → mu E = ⊤) ∧
      (∀ nu : Measure X, nu ≪ mu → IsRelativeSemifiniteOn mu nu Set.univ →
        HasMeasureSupport mu nu ∧ IsRelativeSemifiniteOn mu nu S ∧
          ∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → nu E = 0) := by
  obtain ⟨S, -, hSm, hSub, hSmin⟩ :=
    hded {E | MeasurableSet E ∧ 0 < mu E ∧ mu E < ⊤} (fun E hE => ⟨hE.1, subset_univ _⟩)
  -- complement subsets
  have hcomp : ∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → 0 < mu E → mu E = ⊤ := by
    intro E hE hES hpos
    by_contra hne
    have h0 := hSub E ⟨hE, hpos, lt_top_iff_ne_top.2 hne⟩
    rw [sdiff_eq_left.2 (Set.disjoint_left.2 fun x hx hxS => hES hx hxS)] at h0
    exact hpos.ne' h0
  refine ⟨S, ⟨hSm, hSub, hSmin⟩, ?_, ?_, hcomp, ?_⟩
  · -- semifinite
    intro E hE hES hpos
    by_contra hno
    push Not at hno
    have hT : ∀ F ∈ {E | MeasurableSet E ∧ 0 < mu E ∧ mu E < ⊤}, mu (F \ (S \ E)) = 0 := by
      intro F hF
      have h1 : mu (F ∩ E) = 0 := by
        by_contra h
        have := hno (F ∩ E) (hF.1.inter hE) inter_subset_right (pos_iff_ne_zero.2 h)
        exact absurd ((measure_mono inter_subset_left).trans_lt hF.2.2) (not_lt.2 this)
      refine measure_mono_null ?_ (measure_union_null (hSub F hF) h1)
      intro x ⟨hxF, hx⟩
      by_cases hxS : x ∈ S
      · right; exact ⟨hxF, by by_contra h; exact hx ⟨hxS, h⟩⟩
      · left; exact ⟨hxF, hxS⟩
    have := hSmin (S \ E) (hSm.diff hE) hT
    rw [sdiff_sdiff_right_self, Set.inter_eq_right.2 hES] at this
    exact hpos.ne' this
  · -- Dedekind on S
    intro C hC
    obtain ⟨T, -, hTm, hTsub, hTmin⟩ := hded C (fun E hE => ⟨(hC E hE).1, subset_univ _⟩)
    refine ⟨T ∩ S, inter_subset_right, hTm.inter hSm, ?_, ?_⟩
    · intro E hE
      refine measure_mono_null ?_ (hTsub E hE)
      intro x ⟨hxE, hx⟩
      exact ⟨hxE, fun hxT => hx ⟨hxT, (hC E hE).2 hxE⟩⟩
    · intro T' hT' h
      exact measure_mono_null (diff_subset_diff_left inter_subset_left) (hTmin T' hT' h)
  · intro nu hac hrel
    have hvan : ∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → nu E = 0 := by
      intro E hE hES
      by_contra hne
      obtain ⟨F, hFm, hFE, hFfin, hFpos⟩ := hrel E hE (subset_univ _) (pos_iff_ne_zero.2 hne)
      have hmuF : 0 < mu F := pos_iff_ne_zero.2 (fun h => hFpos.ne' (hac h))
      exact hFfin.ne (hcomp F hFm (hFE.trans hES) hmuF)
    refine ⟨?_, fun E hE _ hpos => hrel E hE (subset_univ _) hpos, hvan⟩
    -- measure support
    obtain ⟨T, -, hTm, hTsub, hTmin⟩ :=
      hded {E | MeasurableSet E ∧ nu E = 0} (fun E hE => ⟨hE.1, subset_univ _⟩)
    refine ⟨Tᶜ, hTm.compl, ?_, ?_⟩
    · rw [compl_compl]
      by_contra hne
      obtain ⟨F, hFm, hFT, hFfin, hFpos⟩ := hrel T hTm (subset_univ _) (pos_iff_ne_zero.2 hne)
      obtain ⟨E₀, hE₀m, hE₀F, hE₀nu, hE₀max⟩ := exhaust mu nu F hFm hFfin
      have hT'm : MeasurableSet (T \ (F \ E₀)) := hTm.diff (hFm.diff hE₀m)
      have hub : ∀ E ∈ {E | MeasurableSet E ∧ nu E = 0}, mu (E \ (T \ (F \ E₀))) = 0 := by
        intro E hE
        have h1 : mu (E ∩ (F \ E₀)) = 0 :=
          hE₀max _ (hE.1.inter (hFm.diff hE₀m)) inter_subset_right
            (measure_mono_null inter_subset_left hE.2)
        refine measure_mono_null ?_ (measure_union_null (hTsub E hE) h1)
        intro x ⟨hxE, hx⟩
        by_cases hxT : x ∈ T
        · right; exact ⟨hxE, by by_contra h; exact hx ⟨hxT, h⟩⟩
        · left; exact ⟨hxE, hxT⟩
      have h2 := hTmin _ hT'm hub
      have h3 : F \ E₀ ⊆ T \ (T \ (F \ E₀)) := fun x hx => ⟨hFT hx.1, fun h => h.2 hx⟩
      have h4 : nu (F \ E₀) = 0 := hac (measure_mono_null h3 h2)
      have h5 : nu F ≤ nu (F \ E₀) + nu E₀ := by
        calc nu F ≤ nu ((F \ E₀) ∪ E₀) := measure_mono (fun x hx => by
              by_cases h : x ∈ E₀
              · exact Or.inr h
              · exact Or.inl ⟨hx, h⟩)
          _ ≤ _ := measure_union_le _ _
      rw [h4, hE₀nu, add_zero] at h5
      exact hFpos.ne' (le_antisymm h5 (zero_le))
    · intro E hE hET hpos
      by_contra hne
      have h0 := hTsub E ⟨hE, by simpa using hne⟩
      rw [sdiff_eq_left.2 (Set.disjoint_left.2 fun x hx hxT => hET hx hxT)] at h0
      exact hpos.ne' h0

end A3SF

end QAlgorithms.Papers.Independent.Renew46.P02

end

universe u

open MeasureTheory in
theorem solution {X : Type u} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X)
    (hded : QAlgorithms.Papers.Independent.Renew46.P02.IsDedekindOn mu Set.univ) :
    ∃ S : Set X, QAlgorithms.Papers.Independent.Renew46.P02.IsSemifinitePart mu S ∧
      QAlgorithms.Papers.Independent.Renew46.P02.IsSemifiniteOn mu S ∧
      QAlgorithms.Papers.Independent.Renew46.P02.IsDedekindOn mu S ∧
      (∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → 0 < mu E → mu E = ⊤) ∧
      (∀ nu : MeasureTheory.Measure X, nu ≪ mu →
        QAlgorithms.Papers.Independent.Renew46.P02.IsRelativeSemifiniteOn mu nu Set.univ →
        QAlgorithms.Papers.Independent.Renew46.P02.HasMeasureSupport mu nu ∧
          QAlgorithms.Papers.Independent.Renew46.P02.IsRelativeSemifiniteOn mu nu S ∧
          ∀ E : Set X, MeasurableSet E → E ⊆ Sᶜ → nu E = 0) :=
  QAlgorithms.Papers.Independent.Renew46.P02.A3SF.main mu hded
