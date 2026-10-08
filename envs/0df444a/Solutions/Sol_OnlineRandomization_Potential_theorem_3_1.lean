-- Prove2me | solution 1 for OnlineRandomization.Potential.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:16:57.822979+00:00
-- url     : https://prove2.me/submissions/94911de0-7f5d-416d-a889-c905b1f1bcd4

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential



namespace OnlineRandomization.Potential

open MeasureTheory

theorem orp_answers_nil {R A : Type*} (G : DetAlg R A) : G.answers [] = [] := by
  simp [DetAlg.answers]

theorem orp_answers_snoc {R A : Type*} (G : DetAlg R A) (r : List R) (x : R) :
    G.answers (r ++ [x]) = G.answers r ++ [G (r ++ [x])] := by
  unfold DetAlg.answers
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · have : List.take (r.length + 1) (r ++ [x]) = r ++ [x] :=
      List.take_of_length_le (by simp)
    simp [this]

theorem orp_answers_length {R A : Type*} (G : DetAlg R A) (r : List R) :
    (G.answers r).length = r.length := by
  simp [DetAlg.answers]

theorem orp_meas_pt {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω] (H : RandAlg R A Ω)
    (r : List R) : ∀ l : List A, MeasurableSet {y | (H.alg y).answers r = l} := by
  induction r using List.reverseRecOn with
  | nil =>
    intro l
    simp only [orp_answers_nil]
    by_cases h : ([] : List A) = l
    · simp [h]
    · simp [h]
  | append_singleton r x ih =>
    intro l
    simp only [orp_answers_snoc]
    rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
    · subst h; simp
    · subst h
      rw [List.concat_eq_append]
      have : {y | (H.alg y).answers r ++ [H.alg y (r ++ [x])] = L ++ [b]} =
          {y | (H.alg y).answers r = L} ∩ {y | H.alg y (r ++ [x]) = b} := by
        ext y; simp
      rw [this]
      exact (ih L).inter (H.meas _ _)

theorem orp_integrable {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω] (H : RandAlg R A Ω)
    (r : List R) (h : List A → ℝ) : Integrable (fun y => h ((H.alg y).answers r)) H.μ := by
  have := H.isProb
  have hm : Measurable (fun y => h ((H.alg y).answers r)) := by
    intro s _
    have : (fun y => h ((H.alg y).answers r)) ⁻¹' s =
        ⋃ l ∈ h ⁻¹' s, {y | (H.alg y).answers r = l} := by
      ext y; simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) (fun l _ => orp_meas_pt H r l)
  have hfin := List.finite_length_eq A r.length
  refine Integrable.of_bound hm.aestronglyMeasurable (∑ l ∈ hfin.toFinset, |h l|) ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  rw [Real.norm_eq_abs]
  have hmem : (H.alg y).answers r ∈ hfin.toFinset := by
    simp [orp_answers_length]
  exact Finset.single_le_sum (f := fun l => |h l|) (fun _ _ => abs_nonneg _) hmem


theorem orp_invariant {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω) (M : DetAlg R A)
    (hM : ObeysPotentialRule Φ H M) (r : List R) :
    0 ≤ ∫ y, Φ r (M.answers r) ((H.alg y).answers r) ∂H.μ := by
  induction r using List.reverseRecOn with
  | nil => simp [orp_answers_nil, hΦ.zero]
  | append_singleton r x ih =>
    refine ih.trans ?_
    have := hM r x
    simpa only [orp_answers_snoc M r x] using this

theorem orp_comp_H {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A)
    (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω)
    (M : DetAlg R A) (hM : ObeysPotentialRule Φ H M) (r : List R) :
    M.costOn F r ≤ ∫ y, α ((H.alg y).costOn F r) ∂H.μ := by
  have := H.isProb
  have h0 := orp_invariant F α g Φ hΦ H M hM r
  have h1 : (∫ y, Φ r (M.answers r) ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, (α ((H.alg y).costOn F r) - M.costOn F r) ∂H.μ := by
    apply integral_mono (orp_integrable H r (fun l => Φ r (M.answers r) l))
      (orp_integrable H r (fun l => α (F.cost r l) - M.costOn F r))
    intro y
    exact hΦ.le_residue r _ _ (orp_answers_length _ _) (orp_answers_length _ _)
  have hi : Integrable (fun y => α ((H.alg y).costOn F r)) H.μ :=
    orp_integrable H r (fun l => α (F.cost r l))
  rw [integral_sub hi (integrable_const (M.costOn F r))] at h1
  simp at h1
  linarith

theorem orp_greedy {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω)
    (r : List R) (x : R) (a : List A) (ha : a.length = r.length) :
    ∃ a' : A, (∫ y, Φ r a ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (a ++ [a']) ((H.alg y).answers (r ++ [x])) ∂H.μ := by
  set I : A → ℝ := fun a' => ∫ y, Φ (r ++ [x]) (a ++ [a']) ((H.alg y).answers (r ++ [x])) ∂H.μ
    with hI
  obtain ⟨a0, -, ha0⟩ := Finset.exists_max_image Finset.univ I Finset.univ_nonempty
  refine ⟨a0, ?_⟩
  set p := g (r ++ [x]) a
  have hp1 : ∑ a' : A, (p a').toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a' _ => PMF.apply_ne_top p a')]
    rw [← tsum_fintype (L := SummationFilter.unconditional A), PMF.tsum_coe]; simp
  have h1 : (∫ y, Φ r a ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, ∑ a' : A, (p a').toReal * Φ (r ++ [x]) (a ++ [a']) ((H.alg y).answers (r ++ [x])) ∂H.μ := by
    apply integral_mono (orp_integrable H r (fun l => Φ r a l))
    · exact integrable_finsetSum _ (fun a' _ =>
        (orp_integrable H (r ++ [x]) (fun l => Φ (r ++ [x]) (a ++ [a']) l)).const_mul _)
    intro y
    simp only [orp_answers_snoc]
    exact hΦ.le_step r a _ ha (orp_answers_length _ _) x _
  rw [integral_finsetSum _ (fun a' _ =>
        (orp_integrable H (r ++ [x]) (fun l => Φ (r ++ [x]) (a ++ [a']) l)).const_mul _)] at h1
  simp only [integral_const_mul] at h1
  refine h1.trans ?_
  calc ∑ a' : A, (p a').toReal * I a' ≤ ∑ a' : A, (p a').toReal * I a0 :=
        Finset.sum_le_sum (fun a' _ => mul_le_mul_of_nonneg_left (ha0 a' (Finset.mem_univ _))
          ENNReal.toReal_nonneg)
    _ = I a0 := by rw [← Finset.sum_mul, hp1, one_mul]


noncomputable def orpG {R A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) (r : List R) (x : R) (a : List A) :
    A := by
  classical
  exact if h : ∃ a' : A, (∫ y, Φ r a ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (a ++ [a']) ((H.alg y).answers (r ++ [x])) ∂H.μ then h.choose
    else Classical.arbitrary A

theorem orpG_spec {R A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) (r : List R) (x : R) (a : List A)
    (h : ∃ a' : A, (∫ y, Φ r a ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (a ++ [a']) ((H.alg y).answers (r ++ [x])) ∂H.μ) :
    (∫ y, Φ r a ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (a ++ [orpG Φ H r x a]) ((H.alg y).answers (r ++ [x])) ∂H.μ := by
  unfold orpG
  rw [dif_pos h]
  exact h.choose_spec

noncomputable def orpS {R A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) : List R → List A
  | [] => []
  | x :: rr => orpS Φ H rr ++ [orpG Φ H rr.reverse x (orpS Φ H rr)]

theorem orpS_length {R A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) (l : List R) :
    (orpS Φ H l).length = l.length := by
  induction l with
  | nil => simp [orpS]
  | cons x rr ih => simp [orpS, ih]

noncomputable def orpM {R A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) : DetAlg R A := fun l =>
  match l.reverse with
  | [] => Classical.arbitrary A
  | x :: rr => orpG Φ H rr.reverse x (orpS Φ H rr)

theorem orpM_snoc {R A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) (r : List R) (x : R) :
    orpM Φ H (r ++ [x]) = orpG Φ H r x (orpS Φ H r.reverse) := by
  simp [orpM]

theorem orpM_answers {R A Ω : Type*} [Nonempty A] [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) (r : List R) :
    (orpM Φ H).answers r = orpS Φ H r.reverse := by
  induction r using List.reverseRecOn with
  | nil => simp [orp_answers_nil, orpS]
  | append_singleton r x ih =>
    rw [orp_answers_snoc, ih, orpM_snoc]
    simp [orpS]

theorem orp_main {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α β : ℝ → ℝ) (hα : IsLinear α) (hα_mono : Monotone α)
    (hβ : IsLinear β) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω) (hH : IsCompetitiveObl F β H) :
    (∃ M : DetAlg R A, ObeysPotentialRule Φ H M) ∧
      ∀ M : DetAlg R A, ObeysPotentialRule Φ H M → IsCompetitive F (α ∘ β) M := by
  refine ⟨⟨orpM Φ H, ?_⟩, ?_⟩
  · intro r x
    rw [orpM_answers, orpM_snoc]
    apply orpG_spec
    exact orp_greedy F α g Φ hΦ H r x _ (by simp [orpS_length])
  · intro M hM r
    have := H.isProb
    have h1 := orp_comp_H F α g Φ hΦ H M hM r
    obtain ⟨c, d, hcd⟩ := hα
    have hi : Integrable (fun y => (H.alg y).costOn F r) H.μ :=
      orp_integrable H r (fun l => F.cost r l)
    have h2 : (∫ y, α ((H.alg y).costOn F r) ∂H.μ) = α (∫ y, (H.alg y).costOn F r ∂H.μ) := by
      simp only [hcd]
      rw [integral_add (hi.const_mul c) (integrable_const d), integral_const_mul]
      simp
    rw [h2] at h1
    exact h1.trans (hα_mono (hH r))

end OnlineRandomization.Potential

open OnlineRandomization.Potential


theorem solution {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α β : ℝ → ℝ) (hα : IsLinear α) (hα_mono : Monotone α)
    (hβ : IsLinear β) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω) (hH : IsCompetitiveObl F β H) :
    (∃ M : DetAlg R A, ObeysPotentialRule Φ H M) ∧
      ∀ M : DetAlg R A, ObeysPotentialRule Φ H M → IsCompetitive F (α ∘ β) M := by
  exact orp_main F α β hα hα_mono hβ g Φ hΦ H hH
