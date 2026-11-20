-- Prove2me | solution 1 for RandomSizeStable.Stability.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:23.045191+00:00
-- url     : https://prove2.me/submissions/69ed5162-4e1e-40d3-b743-b5a550c13cc3

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Dev.L4

open RandomSizeStable.Stability

theorem summ (D : PMF ℕ+) : Summable (fun k : ℕ+ => (D k).toReal) :=
  ENNReal.summable_toReal (by rw [D.tsum_coe]; exact ENNReal.one_ne_top)

theorem pgf_cont (D : PMF ℕ+) : ContinuousOn (pgf D) (Set.Icc 0 1) := by
  unfold pgf
  refine continuousOn_tsum (u := fun k : ℕ+ => (D k).toReal) (fun k => by fun_prop) (summ D) ?_
  intro k x hx
  have h0 : 0 ≤ x := hx.1
  have h1 : x ≤ 1 := hx.2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg (pow_nonneg h0 _)]
  have := pow_le_one₀ (n := (k : ℕ)) h0 h1
  nlinarith [ENNReal.toReal_nonneg (a := D k)]

theorem pgf_mono (D : PMF ℕ+) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    pgf D x ≤ pgf D y := by
  unfold pgf
  have hs : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → Summable (fun k : ℕ+ => (D k).toReal * z ^ (k : ℕ)) := by
    intro z hz0 hz1
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hz0 _))
      (fun k => ?_) (summ D)
    have := pow_le_one₀ (n := (k : ℕ)) hz0 hz1
    nlinarith [ENNReal.toReal_nonneg (a := D k)]
  refine Summable.tsum_le_tsum (fun k => ?_) (hs x hx (hxy.trans hy)) (hs y (hx.trans hxy) hy)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) ENNReal.toReal_nonneg

theorem pgf_integrableOn (D : PMF ℕ+) : IntegrableOn (pgf D) (Set.Icc 0 1) :=
  (pgf_cont D).integrableOn_Icc

theorem main (D : PMF ℕ+) (a p A : ℝ)
    (ha : 0 ≤ a) (hap : a ≤ p) (hpA : p ≤ A) (hA : A ≤ 1)
    (S : Set ℝ) (hS : NullMeasurableSet S volume) (hsub : S ⊆ Set.Icc 0 A)
    (hlen : volume S = ENNReal.ofReal p) (hcontains : Set.Ioo 0 a ⊆ S) :
    (∫ u in S, (pgf D u - benchmark D)) ≤
      primitive D a + primitive D A - primitive D (a + A - p) - p * benchmark D := by
  set g := pgf D with hg
  set x0 := a + A - p with hx0
  have hx0a : a ≤ x0 := by linarith
  have hx0A : x0 ≤ A := by linarith
  have hI : ∀ s : Set ℝ, s ⊆ Set.Icc 0 1 → IntegrableOn g s := fun s hs =>
    (pgf_integrableOn D).mono_set hs
  have hSI : S ⊆ Set.Icc 0 1 := hsub.trans (Set.Icc_subset_Icc_right hA)
  set S' := S \ Set.Ioo 0 a with hS'
  have hS'm : NullMeasurableSet S' volume := hS.diff measurableSet_Ioo.nullMeasurableSet
  have hSU : S = Set.Ioo 0 a ∪ S' := by
    rw [hS']; exact (Set.union_sdiff_cancel hcontains).symm
  have hdis : Disjoint (Set.Ioo (0:ℝ) a) S' := Set.disjoint_sdiff_right
  have hvolS' : volume S' = ENNReal.ofReal (p - a) := by
    have h1 : volume S = volume (Set.Ioo (0:ℝ) a) + volume S' := by
      conv_lhs => rw [hSU]
      exact measure_union₀ hS'm hdis.aedisjoint
    rw [hlen, Real.volume_Ioo, sub_zero] at h1
    have h2 : ENNReal.ofReal p = ENNReal.ofReal a + ENNReal.ofReal (p - a) := by
      rw [← ENNReal.ofReal_add ha (by linarith)]; congr 1; ring
    rw [h2] at h1
    exact ((ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp h1).symm
  set T := Set.Icc x0 A with hT
  have hvolT : volume T = ENNReal.ofReal (p - a) := by
    rw [hT, Real.volume_Icc]; congr 1; rw [hx0]; ring
  have hS'sub : S' ⊆ Set.Icc 0 1 := (Set.sdiff_subset).trans hSI
  have hTsub : T ⊆ Set.Icc 0 1 :=
    Set.Icc_subset_Icc (by linarith) hA
  set M := g x0 with hM
  -- bathtub
  have hbath : ∫ u in S', (g u - M) ≤ ∫ u in T, (g u - M) := by
    have hi1 : IntegrableOn (fun u => g u - M) S' := (hI _ hS'sub).sub (integrableOn_const (by
      rw [hvolS']; exact ENNReal.ofReal_ne_top))
    have hi2 : IntegrableOn (fun u => g u - M) T := (hI _ hTsub).sub (integrableOn_const (by
      rw [hvolT]; exact ENNReal.ofReal_ne_top))
    rw [← integral_indicator₀ hS'm, ← integral_indicator measurableSet_Icc]
    refine integral_mono (hi1.integrable_indicator₀ hS'm) (hi2.integrable_indicator measurableSet_Icc) ?_
    intro x
    by_cases hxS : x ∈ S'
    · have hx : x ∈ Set.Icc 0 A := hsub hxS.1
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxT]
      · have hlt : x < x0 := by
          by_contra hh; exact hxT ⟨not_lt.mp hh, hx.2⟩
        have := pgf_mono D hx.1 hlt.le (hx0A.trans hA)
        rw [Set.indicator_of_mem hxS, Set.indicator_of_notMem hxT]
        simp only [← hg, ← hM] at this ⊢
        linarith
    · by_cases hxT : x ∈ T
      · have := pgf_mono D (by linarith [hxT.1]) hxT.1 (hxT.2.trans hA)
        rw [Set.indicator_of_notMem hxS, Set.indicator_of_mem hxT]
        simp only [← hg, ← hM] at this ⊢
        linarith
      · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxT]
  have hSconst : ∫ u in S', M = M * (p - a) := by
    rw [setIntegral_const, measureReal_def, hvolS', ENNReal.toReal_ofReal (by linarith)]
    simp [mul_comm]
  have hTconst : ∫ u in T, M = M * (p - a) := by
    rw [setIntegral_const, measureReal_def, hvolT, ENNReal.toReal_ofReal (by linarith)]
    simp [mul_comm]
  have hS'g : IntegrableOn g S' := hI _ hS'sub
  have hTg : IntegrableOn g T := hI _ hTsub
  have hcS : IntegrableOn (fun _ : ℝ => M) S' := integrableOn_const (by
      rw [hvolS']; exact ENNReal.ofReal_ne_top)
  have hcT : IntegrableOn (fun _ : ℝ => M) T := integrableOn_const (by
      rw [hvolT]; exact ENNReal.ofReal_ne_top)
  rw [integral_sub hS'g hcS, integral_sub hTg hcT, hSconst, hTconst] at hbath
  have hSg : ∫ u in S', g u ≤ ∫ u in T, g u := by linarith
  -- split S
  have hIoo : IntegrableOn g (Set.Ioo 0 a) :=
    hI _ (fun x hx => ⟨hx.1.le, by linarith [hx.2, hsub (hcontains hx) |>.2]⟩)
  have hvS : (volume S).toReal = p := by rw [hlen, ENNReal.toReal_ofReal (by linarith)]
  have hSg2 : ∫ u in S, (g u - benchmark D) = (∫ u in S, g u) - p * benchmark D := by
    rw [integral_sub ((hI _ hSI)) (integrableOn_const (by rw [hlen]; exact ENNReal.ofReal_ne_top)),
      setIntegral_const, measureReal_def, hvS]
    simp
  rw [hSg2]
  have hsplit : ∫ u in S, g u = (∫ u in Set.Ioo 0 a, g u) + ∫ u in S', g u := by
    conv_lhs => rw [hSU]
    exact setIntegral_union₀ hdis.aedisjoint hS'm hIoo hS'g
  have hprim1 : ∫ u in Set.Ioo 0 a, g u = primitive D a := by
    unfold primitive
    rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo]
  have hprim2 : ∫ u in T, g u = primitive D A - primitive D x0 := by
    unfold primitive
    have hc := pgf_cont D
    have h0x0 : 0 ≤ x0 := ha.trans hx0a
    have hii : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → IntervalIntegrable g volume 0 v := by
      intro v hv0 hv
      refine (hc.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hv0]
      exact Set.Icc_subset_Icc le_rfl hv
    rw [intervalIntegral.integral_interval_sub_left (hii A (ha.trans (hap.trans hpA)) hA) (hii x0 h0x0 (hx0A.trans hA)),
      intervalIntegral.integral_of_le hx0A, hT, integral_Icc_eq_integral_Ioc]
  rw [hsplit, hprim1]
  linarith

end RandomSizeStable.Dev.L4

namespace RandomSizeStable

open RandomSizeStable.Stability in
theorem chk_lemma_4 (D : PMF ℕ+) (a p A : ℝ)
    (ha : 0 ≤ a) (hap : a ≤ p) (hpA : p ≤ A) (hA : A ≤ 1)
    (S : Set ℝ) (hS : NullMeasurableSet S volume) (hsub : S ⊆ Set.Icc 0 A)
    (hlen : volume S = ENNReal.ofReal p) (hcontains : Set.Ioo 0 a ⊆ S) :
    (∫ u in S, (pgf D u - benchmark D)) ≤
      primitive D a + primitive D A - primitive D (a + A - p) - p * benchmark D :=
  RandomSizeStable.Dev.L4.main D a p A ha hap hpA hA S hS hsub hlen hcontains

end RandomSizeStable
end

theorem solution : type_of% @RandomSizeStable.chk_lemma_4 := @RandomSizeStable.chk_lemma_4
