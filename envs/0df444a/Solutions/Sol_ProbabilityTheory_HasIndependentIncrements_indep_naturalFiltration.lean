-- Prove2me | solution 1 for ProbabilityTheory.HasIndependentIncrements.indep_naturalFiltration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:20:24.549982+00:00
-- url     : https://prove2.me/submissions/733d617a-fed6-4a61-8a8b-aeb9d1479cc5

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_ProbabilityTheory_increment_apply
import Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indepFun_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {ι : Type*} {Ω : Type*} {E : Type*}
section FiltrationIndependence
variable [LinearOrder ι] [MeasurableSpace Ω] [MeasurableSpace E] [AddGroup E]
private theorem indep_finset_X_increment [Zero ι] [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [BorelSpace E] [MeasurableSub₂ E] {X : ι → Ω → E} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] (h : HasIndependentIncrements X μ) (hX : ∀ i, StronglyMeasurable (X i)) (h0 : X 0 = fun _ => 0) (h0le : ∀ (i : ι), 0 ≤ i) {s t : ι} (hst : s ≤ t) (F : Finset {j : ι // j ≤ s}) : Indep (⨆ j ∈ F, MeasurableSpace.comap (X (j : ι)) ‹MeasurableSpace E›) (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›) μ := by
  haveI : MeasurableNeg E := ⟨by
    show Measurable (fun x : E => -x)
    have : (fun x : E => -x) = fun x => (0 : E) - x := by ext x; rw [zero_sub]
    rw [this]; exact measurable_const.sub measurable_id⟩
  haveI : MeasurableAdd₂ E := ⟨by
    have : (fun p : E × E => p.1 + p.2) = fun p => p.1 - (-p.2) := by
      ext ⟨a, b⟩; rw [sub_eq_add_neg, neg_neg]
    rw [this]; exact measurable_fst.sub measurable_snd.neg⟩
  by_cases hst_eq : s = t
  · have : increment X s t = fun _ => 0 := by ext ω; simp [increment_apply, hst_eq]
    rw [this, MeasurableSpace.comap_const]; exact indep_bot_right _
  have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
  by_cases hF : F = ∅
  · simp [hF]; exact indep_bot_left _
  let pts : Finset ι := F.image Subtype.val ∪ {0, s, t}
  have hpts_nonempty : pts.Nonempty := ⟨0, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self 0 _))⟩
  set n := pts.card with hn_def
  have hn_pos : 0 < n := Finset.card_pos.mpr hpts_nonempty
  let τ : Fin n → ι := pts.orderEmbOfFin rfl
  have hτ_strictMono : StrictMono τ := (pts.orderEmbOfFin rfl).strictMono
  have hτ_val : ∀ (a : ι) (ha : a ∈ pts), τ ((pts.orderIsoOfFin rfl).symm ⟨a, ha⟩) = a := by
    intro a ha; show (pts.orderEmbOfFin rfl) ((pts.orderIsoOfFin rfl).symm ⟨a, ha⟩) = a; rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have hτ_mem : ∀ i : Fin n, τ i ∈ pts := fun i => Finset.orderEmbOfFin_mem pts rfl i
  have h0_mem : (0 : ι) ∈ pts := Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self 0 _))
  have hs_mem : s ∈ pts := Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self s _))))
  have ht_mem : t ∈ pts := Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))))
  have hpts_le_t : ∀ x ∈ pts, x ≤ t := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx_left | hx_right
    · obtain ⟨⟨j, hjs⟩, _, rfl⟩ := Finset.mem_image.mp hx_left
      exact le_trans hjs hst
    · rcases Finset.mem_insert.mp hx_right with rfl | hx_right
      · exact le_trans (h0le s) hst
      · rcases Finset.mem_insert.mp hx_right with rfl | hx_right
        · exact hst
        · exact le_of_eq (Finset.mem_singleton.mp hx_right)
  have hτ_zero : τ ⟨0, hn_pos⟩ = 0 := by show pts.orderEmbOfFin rfl ⟨0, hn_pos⟩ = 0; rw [Finset.orderEmbOfFin_zero rfl hn_pos]; exact le_antisymm (Finset.min'_le pts 0 h0_mem) (h0le (pts.min' hpts_nonempty))
  have hτ_last : τ ⟨n - 1, Nat.sub_lt hn_pos Nat.one_pos⟩ = t := by show pts.orderEmbOfFin rfl ⟨n - 1, _⟩ = t; rw [Finset.orderEmbOfFin_last rfl hn_pos]; exact le_antisymm (Finset.max'_le pts hpts_nonempty _ hpts_le_t) (Finset.le_max' pts t ht_mem)
  have hn_ge2 : 2 ≤ n := by
    rw [hn_def]; apply Finset.one_lt_card.mpr; exact ⟨s, hs_mem, t, ht_mem, ne_of_lt hst_lt⟩
  have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hn_ge2))
  have hτ_mono : Monotone τ := hτ_strictMono.monotone
  have hind := h (n - 1) (τ ∘ Fin.cast hn_sub) (hτ_mono.comp (Fin.cast_strictMono hn_sub).monotone)
  have hpts_gt_s : ∀ x ∈ pts, s < x → x = t := by
    intro x hx hsx
    rcases Finset.mem_union.mp hx with hx_left | hx_right
    · obtain ⟨⟨j, hjs⟩, _, rfl⟩ := Finset.mem_image.mp hx_left
      exact absurd hsx (not_lt.mpr hjs)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx_right
      rcases hx_right with rfl | rfl | rfl
      · exact absurd hsx (not_lt.mpr (h0le _))
      · exact absurd hsx (lt_irrefl _)
      · rfl
  have hn2_lt : n - 2 < n := Nat.sub_lt hn_pos (by omega)
  have hτ_second_last : τ ⟨n - 2, hn2_lt⟩ = s := by
    set p := ((pts.orderIsoOfFin rfl).symm ⟨s, hs_mem⟩).val with hp_def
    have hp_lt : p < n := ((pts.orderIsoOfFin rfl).symm ⟨s, hs_mem⟩).isLt
    have hτp : τ ⟨p, hp_lt⟩ = s := by
      show τ ((pts.orderIsoOfFin rfl).symm ⟨s, hs_mem⟩) = s; exact hτ_val s hs_mem
    suffices p = n - 2 by
      have : (⟨p, hp_lt⟩ : Fin n) = ⟨n - 2, hn2_lt⟩ := Fin.ext this
      rw [← this]; exact hτp
    have hp_lt_last : p < n - 1 := by
      by_contra h_ge
      push Not at h_ge; have : p = n - 1 := by omega
      have : τ ⟨p, hp_lt⟩ = τ ⟨n - 1, Nat.sub_lt hn_pos Nat.one_pos⟩ := by
        congr 1; ext; exact this
      rw [hτp, hτ_last] at this; exact absurd this (ne_of_lt hst_lt)
    by_contra hp_ne
    have hp_lt2 : p < n - 2 := by omega
    have hp1_lt : p + 1 < n := by omega
    have hp1_lt_last : p + 1 < n - 1 := by omega
    have hgt : s < τ ⟨p + 1, hp1_lt⟩ := by
      rw [← hτp]; exact hτ_strictMono (show (⟨p, hp_lt⟩ : Fin n) < ⟨p + 1, hp1_lt⟩ by exact Fin.mk_lt_mk.mpr (by omega))
    have hlt : τ ⟨p + 1, hp1_lt⟩ < t := by
      rw [← hτ_last]; exact hτ_strictMono (show (⟨p + 1, hp1_lt⟩ : Fin n) < ⟨n - 1, _⟩ by exact Fin.mk_lt_mk.mpr (by omega))
    have := hpts_gt_s (τ ⟨p + 1, hp1_lt⟩) (hτ_mem ⟨p + 1, hp1_lt⟩) hgt
    exact absurd this (ne_of_lt hlt)
  let m : Fin (n - 1) → MeasurableSpace Ω := fun k => MeasurableSpace.comap (increment X (τ ⟨k.val, by omega⟩) (τ ⟨k.val + 1, by omega⟩)) ‹MeasurableSpace E›
  have hind' : iIndep m μ := hind
  have hm_le : ∀ k : Fin (n - 1), m k ≤ ‹MeasurableSpace Ω› := by intro k; exact Measurable.comap_le ((hX _).measurable.sub (hX _).measurable)
  let S : Set (Fin (n - 1)) := {k | k.val < n - 2}
  let T : Set (Fin (n - 1)) := {k | k.val = n - 2}
  have hST : Disjoint S T := by rw [Set.disjoint_iff]; intro k ⟨hkS, hkT⟩; simp only [S, T, Set.mem_setOf_eq] at hkS hkT; omega
  have hn2_lt' : n - 2 < n - 1 := by omega
  let last : Fin (n - 1) := ⟨n - 2, hn2_lt'⟩
  have hindST : Indep (⨆ k ∈ S, m k) (⨆ k ∈ T, m k) μ := indep_iSup_of_disjoint hm_le hind' hST
  have hT_eq : (⨆ k ∈ T, m k) = MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E› := by
    have : T = {last} := by ext k; simp only [T, last, Set.mem_setOf_eq, Set.mem_singleton_iff, Fin.ext_iff]
    rw [this, iSup_singleton]
    show MeasurableSpace.comap (increment X (τ ⟨n - 2, _⟩) (τ ⟨(n - 2) + 1, _⟩)) _ = _
    have hn21 : n - 2 + 1 = n - 1 := by omega
    have hτn2plus1 : τ ⟨n - 2 + 1, by omega⟩ = t := by
      have : (⟨n - 2 + 1, (by omega : n - 2 + 1 < n)⟩ : Fin n) = ⟨n - 1, Nat.sub_lt hn_pos Nat.one_pos⟩ := by ext; exact hn21
      rw [this]; exact hτ_last
    have : increment X (τ ⟨n - 2, by omega⟩) (τ ⟨n - 2 + 1, by omega⟩) = increment X s t := by
      ext ω; simp only [increment_apply]; rw [hτ_second_last, hτn2plus1]
    rw [this]
  have hF_le_past : ⨆ j ∈ F, MeasurableSpace.comap (X (j : ι)) ‹MeasurableSpace E› ≤ ⨆ k ∈ S, m k := by
    apply iSup₂_le; intro ⟨j, hjs⟩ hjF
    have hj_pts : j ∈ pts :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨⟨j, hjs⟩, hjF, rfl⟩))
    suffices hmeas_telescope : ∀ (p : ℕ) (hp : p < n), τ ⟨p, hp⟩ ≤ s → @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E› (X (τ ⟨p, hp⟩)) by
      let p_fin := (pts.orderIsoOfFin rfl).symm ⟨j, hj_pts⟩
      have hτp : τ p_fin = j := hτ_val j hj_pts
      have hp_lt : p_fin.val < n := p_fin.isLt
      have : @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E› (X j) := by rw [← hτp]; exact hmeas_telescope p_fin.val hp_lt (by rw [hτp]; exact hjs)
      exact this.comap_le
    intro p
    induction p with
    | zero =>
      intro hp _; rw [hτ_zero, h0]; exact measurable_const
    | succ p ih =>
      intro hp hle
      have hp_lt : p < n := by omega
      have hp_in_S : p < n - 2 := by
        by_contra h_ge; push Not at h_ge; have : p + 1 = n - 1 := by omega
        have : τ ⟨p + 1, hp⟩ = t := by rw [show (⟨p + 1, hp⟩ : Fin n) = ⟨n - 1, _⟩ from Fin.ext (by omega)]; exact hτ_last
        exact absurd (this ▸ hle) (not_le.mpr hst_lt)
      have hmeas_incr : @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E› (increment X (τ ⟨p, hp_lt⟩) (τ ⟨p + 1, hp⟩)) := (@comap_measurable Ω E _ (increment X (τ ⟨p, hp_lt⟩) (τ ⟨p + 1, hp⟩))).mono (le_iSup₂ (f := fun k (_ : k ∈ S) => m k) ⟨p, by omega⟩ hp_in_S) le_rfl
      have hmeas_prev : @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E› (X (τ ⟨p, hp_lt⟩)) := ih hp_lt (le_trans (hτ_mono (Fin.mk_le_mk.mpr (by omega))) hle)
      have heq : X (τ ⟨p + 1, hp⟩) = fun ω => increment X (τ ⟨p, hp_lt⟩) (τ ⟨p + 1, hp⟩) ω + X (τ ⟨p, hp_lt⟩) ω := by
        ext ω; simp only [increment_apply]; exact (sub_add_cancel _ _).symm
      rw [heq]
      exact hmeas_incr.add hmeas_prev
  rw [← hT_eq]; exact indep_of_indep_of_le_left hindST hF_le_past
theorem solution [Zero ι] [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [BorelSpace E] [MeasurableSub₂ E] {X : ι → Ω → E} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] (h : HasIndependentIncrements X μ) (hX : ∀ i, StronglyMeasurable (X i)) (h0 : X 0 = fun _ => 0) (h0le : ∀ (i : ι), 0 ≤ i) {s t : ι} (hst : s ≤ t) : Indep (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›) ((Filtration.natural (fun i => X i) hX).seq s) μ := by
  apply Indep.symm; show Indep ((Filtration.natural (fun i => X i) hX).seq s) (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›) μ
  simp only [Filtration.natural]; rw [iSup_subtype']
  rw [iSup_eq_iSup_finset]; apply indep_iSup_of_directed_le
  · exact fun F => indep_finset_X_increment h hX h0 h0le hst F
  · intro F; exact iSup₂_le fun j _ => (hX j).measurable.comap_le
  · exact ((hX t).measurable.sub (hX s).measurable).comap_le
  · exact directed_of_isDirected_le fun F₁ F₂ h12 => biSup_mono fun j hj => Finset.mem_of_subset h12 hj
end FiltrationIndependence
