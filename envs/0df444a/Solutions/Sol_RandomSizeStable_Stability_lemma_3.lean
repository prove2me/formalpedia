-- Prove2me | solution 1 for RandomSizeStable.Stability.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:23.472996+00:00
-- url     : https://prove2.me/submissions/4ff1b3a4-1764-4c87-b1b1-f13f88d44fad

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks
import Definitions.Def_RandomSizeStable_Stability_Stability

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability

namespace RandomSizeStable.Dev.Common

theorem leftRank_bounds {V C : Type} [Fintype C] (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    0 ≤ leftRank E P v c ∧ 0 ≤ P c ∧ leftRank E P v c + P c ≤ 1 := by
  classical
  have := E.isStrictTotalOrder v
  refine ⟨Finset.sum_nonneg (fun b _ => hP.1 b), hP.1 c, ?_⟩
  unfold leftRank
  have hc : c ∉ Finset.univ.filter (fun b => E.prefers v c b) := by
    simp [irrefl_of (E.prefers v) c]
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := P) (Finset.subset_univ (insert c (Finset.univ.filter (fun b => E.prefers v c b))))
    (fun b _ _ => hP.1 b)
  rw [Finset.sum_insert hc, hP.2] at h
  linarith

end RandomSizeStable.Dev.Common
end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common

set_option linter.unusedSectionVars false

namespace RandomSizeStable.Dev.L3

theorem G (f : ℝ → ℝ) (hm : Measurable f) (K T : ℝ) (hb : ∀ t, |f t| ≤ K)
    (hz : ∀ t, T < t → f t = 0) : IntegrableOn f (Set.Ioi 0) := by
  have h1 : IntegrableOn f (Set.Ioc 0 T) :=
    Measure.integrableOn_of_bounded (M := K) (by simp) hm.aestronglyMeasurable
      (ae_of_all _ (fun t => by rw [Real.norm_eq_abs]; exact hb t))
  have h2 : IntegrableOn f (Set.Ioi T) :=
    (integrableOn_zero (μ := volume) (s := Set.Ioi T)).congr_fun
      (fun t ht => (hz t ht).symm) measurableSet_Ioi
  refine (h1.union h2).mono_set ?_
  intro t ht
  by_cases h : t ≤ T
  · exact Or.inl ⟨ht, h⟩
  · exact Or.inr (not_le.mp h)

section
variable {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]

theorem lc_nonneg (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (v : V) (H : Set C) :
    0 ≤ lowerCut E P v H := by
  unfold lowerCut
  exact Finset.sum_nonneg (fun c _ => by split_ifs; exact hP.1 c; exact le_refl 0)

theorem lc_le_one (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (v : V) (H : Set C) :
    lowerCut E P v H ≤ 1 := by
  unfold lowerCut
  calc _ ≤ ∑ c, P c := Finset.sum_le_sum (fun c _ => by split_ifs; exact le_rfl; exact hP.1 c)
    _ = 1 := hP.2

theorem lc_mono (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (v : V) {H H' : Set C}
    (h : H' ⊆ H) : lowerCut E P v H' ≤ lowerCut E P v H := by
  unfold lowerCut
  refine Finset.sum_le_sum (fun c _ => ?_)
  by_cases h1 : ∀ j, j ∉ H' → E.prefers v j c
  · have h2 : ∀ j, j ∉ H → E.prefers v j c := fun j hj => h1 j (fun hh => hj (h hh))
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1]
    split_ifs
    · exact hP.1 c
    · exact le_rfl

theorem uc_mono (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (v : V) {H H' : Set C}
    (h : H' ⊆ H) : upperCut E P v H' ≤ upperCut E P v H := by
  unfold upperCut
  refine Finset.sup'_mono_fun (fun c _ => ?_)
  obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v c P hP
  by_cases h3 : c ∈ H' ∧ 0 < P c
  · rw [if_pos h3, if_pos ⟨h h3.1, h3.2⟩]
  · rw [if_neg h3]
    split_ifs
    · linarith
    · exact le_rfl

theorem marked_anti (d : V ⊕ C → V ⊕ C → ℝ) (o : C) {s t : ℝ} (h : s ≤ t) :
    marked d o t ⊆ marked d o s := by
  intro c hc
  exact lt_of_le_of_lt h hc

theorem vanish (E : Election V C) (P : C → ℝ) (v : V) (d : V ⊕ C → V ⊕ C → ℝ) (o : C) (T : ℝ)
    (hT : ∀ c, d (Sum.inr o) (Sum.inr c) ≤ T) (t : ℝ) (ht : T < t) :
    lowerCut E P v (marked d o t) = 0 ∧ upperCut E P v (marked d o t) ≤ 0 := by
  have hsto := E.isStrictTotalOrder v
  have hnm : ∀ c, c ∉ marked d o t := fun c hc => by
    have : t < d (Sum.inr o) (Sum.inr c) := hc
    linarith [hT c]
  constructor
  · unfold lowerCut
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [if_neg]
    intro h
    exact irrefl_of (E.prefers v) c (h c (hnm c))
  · unfold upperCut
    refine Finset.sup'_le _ _ (fun c _ => ?_)
    rw [if_neg (fun h => hnm c h.1)]

theorem int1 (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (v : V)
    (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d) (o : C) :
    IntegrableOn (fun t => lowerCut E P v (marked d o t)) (Set.Ioi 0) := by
  have hanti : Antitone (fun t => lowerCut E P v (marked d o t)) :=
    fun s t hst => lc_mono E P hP v (marked_anti d o hst)
  refine G _ hanti.measurable 1 (∑ c, d (Sum.inr o) (Sum.inr c)) (fun t => ?_) (fun t ht => ?_)
  · rw [abs_of_nonneg (lc_nonneg E P hP v _)]; exact lc_le_one E P hP v _
  · exact (vanish E P v d o _ (fun c => Finset.single_le_sum (f := fun c => d (Sum.inr o) (Sum.inr c))
      (fun i _ => hd.nonneg _ _) (Finset.mem_univ c)) t ht).1

theorem cutB_meas (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (v : V)
    (d : V ⊕ C → V ⊕ C → ℝ) (o : C) (q : ℝ) :
    MeasurableSet {t : ℝ | lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)} := by
  have hanti : Antitone (fun t => lowerCut E P v (marked d o t)) :=
    fun s t hst => lc_mono E P hP v (marked_anti d o hst)
  have hanti2 : Antitone (fun t => upperCut E P v (marked d o t)) :=
    fun s t hst => uc_mono E P hP v (marked_anti d o hst)
  exact (measurableSet_le hanti.measurable measurable_const).inter
    (measurableSet_lt measurable_const hanti2.measurable)

theorem int2 (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (v : V)
    (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d) (o : C) (q : ℝ) (hq : 0 ≤ q) :
    IntegrableOn (fun t : ℝ =>
      (if lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)
        then 1 else 0 : ℝ)) (Set.Ioi 0) := by
  refine G _ (Measurable.ite (cutB_meas E P hP v d o q) measurable_const measurable_const) 1
    (∑ c, d (Sum.inr o) (Sum.inr c)) (fun t => ?_) (fun t ht => ?_)
  · split_ifs <;> simp
  · have := (vanish E P v d o _ (fun c => Finset.single_le_sum
      (f := fun c => d (Sum.inr o) (Sum.inr c))
      (fun i _ => hd.nonneg _ _) (Finset.mem_univ c)) t ht).2
    rw [if_neg]
    intro h
    linarith [h.2]

theorem pw1 (E : Election V C) (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d)
    (hc : Consistent E d) (o : C) (v : V) (c : C) (t : ℝ)
    (hlt : t < d (Sum.inl v) (Sum.inr c) - d (Sum.inl v) (Sum.inr o)) :
    ∀ j, j ∉ marked d o t → E.prefers v j c := by
  have hsto := E.isStrictTotalOrder v
  intro j hj
  by_contra hn
  have hj' : d (Sum.inr o) (Sum.inr j) ≤ t := not_lt.mp hj
  have h1 : d (Sum.inl v) (Sum.inr c) ≤ d (Sum.inl v) (Sum.inr j) := by
    rcases trichotomous_of (E.prefers v) c j with h | h | h
    · exact hc v c j h
    · rw [h]
    · exact absurd h hn
  have h2 := hd.triangle (Sum.inl v) (Sum.inr o) (Sum.inr j)
  linarith

theorem ineq1 (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (d : V ⊕ C → V ⊕ C → ℝ)
    (hd : IsPseudometric d) (hc : Consistent E d) (o : C) (v : V) :
    (∑ c, P c * d (Sum.inl v) (Sum.inr c)) - d (Sum.inl v) (Sum.inr o) ≤
      ∫ t in Set.Ioi (0 : ℝ), lowerCut E P v (marked d o t) := by
  set y : C → ℝ := fun c => d (Sum.inl v) (Sum.inr c) - d (Sum.inl v) (Sum.inr o) with hy
  set g : C → ℝ → ℝ := fun c => (Set.Iio (y c)).indicator (fun _ => (1 : ℝ)) with hg
  have e1 : (∑ c, P c * d (Sum.inl v) (Sum.inr c)) - d (Sum.inl v) (Sum.inr o) = ∑ c, P c * y c := by
    simp only [hy, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2]
    ring
  have hgi : ∀ c, IntegrableOn (g c) (Set.Ioi 0) := by
    intro c
    refine G _ (measurable_const.indicator measurableSet_Iio) 1 (y c) (fun t => ?_) (fun t ht => ?_)
    · simp only [hg]; by_cases h : t ∈ Set.Iio (y c) <;> simp [h]
    · simp only [hg]; rw [Set.indicator_of_notMem]; simpa using ht.le
  have hgint : ∀ c, ∫ t in Set.Ioi (0 : ℝ), g c t = max (y c) 0 := by
    intro c
    simp only [hg]
    rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio, setIntegral_const, smul_eq_mul,
      mul_one, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal', sub_zero]
  have hsum : ∫ t in Set.Ioi (0 : ℝ), ∑ c, P c * g c t = ∑ c, P c * max (y c) 0 := by
    rw [integral_finsetSum _ (fun c _ => (hgi c).const_mul (P c))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [integral_const_mul, hgint]
  have hle : ∫ t in Set.Ioi (0 : ℝ), ∑ c, P c * g c t ≤
      ∫ t in Set.Ioi (0 : ℝ), lowerCut E P v (marked d o t) := by
    refine setIntegral_mono_on (integrable_finsetSum _ (fun c _ => (hgi c).const_mul (P c)))
      (int1 E P hP v d hd o) measurableSet_Ioi (fun t ht => ?_)
    unfold lowerCut
    refine Finset.sum_le_sum (fun c _ => ?_)
    by_cases hlt : t < y c
    · have hcond := pw1 E d hd hc o v c t hlt
      rw [if_pos hcond]
      simp [hg, hlt]
    · have : g c t = 0 := by simp [hg, hlt]
      rw [this, mul_zero]
      split_ifs
      · exact hP.1 c
      · exact le_rfl
  calc _ = ∑ c, P c * y c := e1
    _ ≤ ∑ c, P c * max (y c) 0 :=
        Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hP.1 c))
    _ = _ := hsum.symm
    _ ≤ _ := hle

theorem pair (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (d : V ⊕ C → V ⊕ C → ℝ)
    (hd : IsPseudometric d) (hc : Consistent E d) (o : C) (v : V) (q : ℝ) (hq0 : 0 ≤ q)
    (t s : ℝ) (hts : t < s)
    (hL : lowerCut E P v (marked d o t) ≤ q) (hU : q < upperCut E P v (marked d o s)) :
    s - t ≤ 2 * d (Sum.inl v) (Sum.inr o) := by
  classical
  have hsto := E.isStrictTotalOrder v
  unfold upperCut at hU
  obtain ⟨c, _, hcq⟩ := (Finset.lt_sup'_iff _).1 hU
  have hcm : c ∈ marked d o s ∧ 0 < P c := by
    by_contra h
    rw [if_neg h] at hcq
    linarith
  rw [if_pos hcm] at hcq
  have hxc : s < d (Sum.inr o) (Sum.inr c) := hcm.1
  have key : ∃ j, d (Sum.inr o) (Sum.inr j) ≤ t ∧ ¬ E.prefers v j c := by
    by_contra hno
    push_neg at hno
    unfold lowerCut at hL
    have hcF : c ∉ Finset.univ.filter (fun b => E.prefers v c b) := by
      simp [irrefl_of (E.prefers v) c]
    have h1 : ∑ b ∈ insert c (Finset.univ.filter (fun b => E.prefers v c b)), P b ≤
        ∑ b, (if ∀ j, j ∉ marked d o t → E.prefers v j b then P b else 0) := by
      calc ∑ b ∈ insert c (Finset.univ.filter (fun b => E.prefers v c b)), P b
          = ∑ b ∈ insert c (Finset.univ.filter (fun b => E.prefers v c b)),
              (if ∀ j, j ∉ marked d o t → E.prefers v j b then P b else 0) := by
            refine Finset.sum_congr rfl (fun b hb => ?_)
            rw [if_pos]
            intro j hj
            have hj' : d (Sum.inr o) (Sum.inr j) ≤ t := not_lt.mp hj
            have hjc := hno j hj'
            rcases Finset.mem_insert.1 hb with h | h
            · rw [h]; exact hjc
            · have h' : E.prefers v c b := by simpa using h
              exact trans_of (E.prefers v) hjc h'
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun b _ _ => by split_ifs; exact hP.1 b; exact le_rfl)
    rw [Finset.sum_insert hcF] at h1
    unfold leftRank at hcq
    linarith
  obtain ⟨j, hjt, hjn⟩ := key
  have hjc : j ≠ c := by
    intro h; subst h; linarith
  have hpref : E.prefers v c j := by
    rcases trichotomous_of (E.prefers v) c j with h | h | h
    · exact h
    · exact absurd h.symm hjc
    · exact absurd h hjn
  have h1 := hc v c j hpref
  have h2 := hd.triangle (Sum.inr o) (Sum.inl v) (Sum.inr c)
  have h3 := hd.triangle (Sum.inl v) (Sum.inr o) (Sum.inr j)
  have h4 := hd.symm (Sum.inr o) (Sum.inl v)
  linarith

theorem ineq2 (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (d : V ⊕ C → V ⊕ C → ℝ)
    (hd : IsPseudometric d) (hc : Consistent E d) (o : C) (v : V) (q : ℝ) (hq0 : 0 ≤ q) :
    (∫ t in Set.Ioi (0 : ℝ),
      (if lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)
        then 1 else 0 : ℝ)) ≤ 2 * d (Sum.inl v) (Sum.inr o) := by
  set B := {t : ℝ | lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)} with hB
  have hBm : MeasurableSet B := cutB_meas E P hP v d o q
  have hδ : 0 ≤ d (Sum.inl v) (Sum.inr o) := hd.nonneg _ _
  have hf : (fun t : ℝ => (if lowerCut E P v (marked d o t) ≤ q ∧
      q < upperCut E P v (marked d o t) then 1 else 0 : ℝ)) = B.indicator (fun _ => (1 : ℝ)) := by
    ext t; simp [Set.indicator, hB]
  rw [hf, setIntegral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hpair : ∀ x ∈ Set.Ioi (0 : ℝ) ∩ B, ∀ y ∈ Set.Ioi (0 : ℝ) ∩ B,
      |x - y| ≤ 2 * d (Sum.inl v) (Sum.inr o) := by
    intro x hx y hy
    rw [abs_le]
    constructor
    · rcases lt_or_ge x y with h | h
      · linarith [pair E P hP d hd hc o v q hq0 x y h hx.2.1 hy.2.2]
      · linarith
    · rcases lt_or_ge y x with h | h
      · linarith [pair E P hP d hd hc o v q hq0 y x h hy.2.1 hx.2.2]
      · linarith
  have hdiam : volume (Set.Ioi (0 : ℝ) ∩ B) ≤ ENNReal.ofReal (2 * d (Sum.inl v) (Sum.inr o)) := by
    refine (Real.volume_le_diam _).trans ?_
    refine Metric.ediam_le (fun x hx y hy => ?_)
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (hpair x hx y hy)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdiam
  rwa [ENNReal.toReal_ofReal (by linarith)] at this

end

end RandomSizeStable.Dev.L3

namespace RandomSizeStable

open RandomSizeStable.Stability in
theorem chk_lemma_3 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C)
    (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d) (hc : Consistent E d)
    (o : C) (ho : ∀ c, candCost d o ≤ candCost d c) (v : V)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (fun t => lowerCut E P v (marked d o t)) (Set.Ioi 0) ∧
    IntegrableOn (fun t : ℝ =>
      (if lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)
        then 1 else 0 : ℝ)) (Set.Ioi 0) ∧
    (∑ c, P c * d (Sum.inl v) (Sum.inr c)) - d (Sum.inl v) (Sum.inr o) ≤
      ∫ t in Set.Ioi (0 : ℝ), lowerCut E P v (marked d o t) ∧
    (∫ t in Set.Ioi (0 : ℝ),
      (if lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)
        then 1 else 0 : ℝ)) ≤ 2 * d (Sum.inl v) (Sum.inr o) :=
  ⟨RandomSizeStable.Dev.L3.int1 E P hP v d hd o,
   RandomSizeStable.Dev.L3.int2 E P hP v d hd o q hq.1,
   RandomSizeStable.Dev.L3.ineq1 E P hP d hd hc o v,
   RandomSizeStable.Dev.L3.ineq2 E P hP d hd hc o v q hq.1⟩

end RandomSizeStable
end

theorem solution : type_of% @RandomSizeStable.chk_lemma_3 := @RandomSizeStable.chk_lemma_3
