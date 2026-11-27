-- Prove2me | solution 1 for ProcessingNetworks.FluidEquations.relaxed_policy_fluid_equation_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:40:42.654838+00:00
-- url     : https://prove2.me/submissions/659df9c2-80ce-44f5-b7ae-13444dd26930

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_SatisfiesAssumption76

namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

lemma relaxed_uoc_at {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ} (h : UOCConverges f g)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin d) : Tendsto (fun n => f n t i) atTop (nhds (g t i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h t ht ε hε
  exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n hn t ⟨ht, le_rfl⟩ i⟩

theorem relaxed_policy_fluid_equation_corrected
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (sd : SPNData I I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep sd E v φ)
    (h : (Fin I → ℝ) → (Fin I → ℝ))
    (h719 : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → ∀ k, ∑ i, sd.A k i * h z i ≤ sd.b k)
    (h76 : SatisfiesAssumption76 h)
    (hnonneg : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → ∀ i, 0 ≤ h z i)
    (hZmeas : ∀ (x : Xstate) (ω : Ω), Measurable fun u => fam.Zx x u ω)
    (hpolicy : ∀ (x : Xstate) (ω : Ω) (t : ℝ), 0 ≤ t →
      fam.T x t ω = fun i => ∫ u in Set.Ioc (0 : ℝ) t, h (fun l => (fam.Zx x u ω l : ℝ)) i)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (i : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < Zh t i) :
    HasDerivAt (fun s => Th s i) (h (Zh t) i) t := by
  obtain ⟨-, -, -, hZc, ω, x, hs, -, -, hT, hZ⟩ := hfl
  set s : ℕ → ℝ := fun n => Mrep.size (x n) with hs_def
  have hspos : ∀ᶠ n in atTop, 0 < s n := hs.eventually_gt_atTop 0
  -- bounds on h
  have hB : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → h z i ≤ ∑ k, sd.b k := by
    intro z hz0
    obtain ⟨k, hk⟩ := sd.A_col_nonzero i
    have h2 : sd.A k i * h z i ≤ ∑ i', sd.A k i' * h z i' :=
      Finset.single_le_sum (f := fun i' => sd.A k i' * h z i')
        (fun i' _ => mul_nonneg (by rcases sd.A_binary k i' with h' | h' <;> simp [h'])
          (hnonneg z hz0 i')) (Finset.mem_univ i)
    have h3 := h719 z hz0 k
    have h4 : sd.b k ≤ ∑ k, sd.b k :=
      Finset.single_le_sum (fun k _ => (sd.b_pos k).le) (Finset.mem_univ k)
    rw [hk, one_mul] at h2
    linarith
  set B : ℝ := ∑ k, sd.b k with hB_def
  -- nonnegativity of Ẑ
  have hZnn : ∀ r, 0 ≤ r → ∀ l, 0 ≤ Zh r l := by
    intro r hr l
    apply ge_of_tendsto (relaxed_uoc_at hZ r hr l)
    filter_upwards [hspos] with n hn
    exact mul_nonneg (inv_nonneg.mpr hn.le) (Nat.cast_nonneg _)
  -- positivity window
  have hev : ∀ᶠ r in nhds t, 0 < Zh r i :=
    ((continuous_apply i).comp hZc).continuousAt.eventually (lt_mem_nhds hz)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set a := t - min ε t / 2 with ha_def
  set c := t + min ε t / 2 with hc_def
  have hmin : 0 < min ε t := lt_min hε ht
  have ha0 : 0 < a := by have := min_le_right ε t; rw [ha_def]; linarith
  have hat : a < t := by rw [ha_def]; linarith
  have htc : t < c := by rw [hc_def]; linarith
  have hwin : ∀ r, a < r → r < c → 0 < Zh r i := by
    intro r h1 h2
    apply hball
    rw [Real.dist_eq, abs_lt]
    have := min_le_left ε t
    constructor <;> linarith
  set g : ℝ → ℝ := fun r => h (Zh r) i with hg_def
  have hgc : ∀ r, a < r → r < c → ContinuousAt g r := by
    intro r h1 h2
    exact (h76.1 i (Zh r) (hZnn r (by linarith)) (hwin r h1 h2)).comp hZc.continuousAt
  -- measurability of the raw integrand
  have hfmeas : ∀ n, Measurable fun w => h (fun l => (fam.Zx (x n) w ω l : ℝ)) i := by
    intro n
    have : Measurable fun z : Fin I → ℕ => h (fun l => (z l : ℝ)) i := measurable_of_countable _
    exact this.comp (hZmeas (x n) ω)
  have hfbd : ∀ n w, ‖h (fun l => (fam.Zx (x n) w ω l : ℝ)) i‖ ≤ B := by
    intro n w
    have h0 : ∀ j, (0 : ℝ) ≤ (fam.Zx (x n) w ω j : ℝ) := fun j => Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _ h0 i)]
    exact hB _ h0
  have hfint : ∀ n (p q : ℝ), IntervalIntegrable
      (fun w => h (fun l => (fam.Zx (x n) w ω l : ℝ)) i) volume p q := by
    intro n p q
    exact (intervalIntegrable_const (c := B)).mono_fun' (hfmeas n).aestronglyMeasurable
      (Eventually.of_forall (hfbd n))
  -- the key increment identity
  have hclaim : ∀ u1 u2, a < u1 → u1 ≤ u2 → u2 < c → Th u2 i - Th u1 i = ∫ r in u1..u2, g r := by
    intro u1 u2 h1 h12 h2
    have hu1 : 0 ≤ u1 := by linarith
    have hu2 : 0 ≤ u2 := by linarith
    set Fn : ℕ → ℝ → ℝ := fun n r => h (fun l => (s n)⁻¹ * (fam.Zx (x n) (s n * r) ω l : ℝ)) i
      with hFn
    have hFn_eq : ∀ n, 0 < s n → ∀ r,
        Fn n r = h (fun l => (fam.Zx (x n) (s n * r) ω l : ℝ)) i := by
      intro n hn r
      simp only [hFn]
      have := h76.2 (s n)⁻¹ (fun l => (fam.Zx (x n) (s n * r) ω l : ℝ)) (inv_pos.mpr hn)
        (fun j => Nat.cast_nonneg _)
      rw [← this]
      rfl
    have hseq : ∀ n, 0 < s n →
        (s n)⁻¹ * fam.T (x n) (s n * u2) ω i - (s n)⁻¹ * fam.T (x n) (s n * u1) ω i =
          ∫ r in u1..u2, Fn n r := by
      intro n hn
      have e1 := congrFun (hpolicy (x n) ω (s n * u2) (by positivity)) i
      have e2 := congrFun (hpolicy (x n) ω (s n * u1) (by positivity)) i
      rw [e1, e2, ← intervalIntegral.integral_of_le (by positivity),
        ← intervalIntegral.integral_of_le (by positivity), ← mul_sub,
        intervalIntegral.integral_interval_sub_left (hfint n _ _) (hfint n _ _)]
      rw [intervalIntegral.integral_congr (g := fun r =>
        h (fun l => (fam.Zx (x n) (s n * r) ω l : ℝ)) i) (fun r _ => hFn_eq n hn r)]
      rw [intervalIntegral.integral_comp_mul_left
        (fun w => h (fun l => (fam.Zx (x n) w ω l : ℝ)) i) hn.ne', smul_eq_mul]
    have hlimT : Tendsto (fun n => (s n)⁻¹ * fam.T (x n) (s n * u2) ω i -
        (s n)⁻¹ * fam.T (x n) (s n * u1) ω i) atTop (nhds (Th u2 i - Th u1 i)) :=
      (relaxed_uoc_at hT u2 hu2 i).sub (relaxed_uoc_at hT u1 hu1 i)
    have hlimI : Tendsto (fun n => ∫ r in u1..u2, Fn n r) atTop (nhds (∫ r in u1..u2, g r)) := by
      apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
      · filter_upwards [hspos] with n hn
        have hm : Measurable fun r => h (fun l => (fam.Zx (x n) (s n * r) ω l : ℝ)) i :=
          (hfmeas n).comp (measurable_const_mul (s n))
        refine (hm.aestronglyMeasurable).congr (Eventually.of_forall fun r => ?_)
        exact (hFn_eq n hn r).symm
      · filter_upwards [hspos] with n hn
        refine Eventually.of_forall fun r _ => ?_
        rw [hFn_eq n hn r]
        exact hfbd n _
      · exact intervalIntegrable_const
      · refine Eventually.of_forall fun r hr => ?_
        rw [Set.uIoc_of_le h12] at hr
        have hr1 : a < r := by linarith [hr.1]
        have hr2 : r < c := by linarith [hr.2]
        have hconv : Tendsto (fun n => fun l => (s n)⁻¹ * (fam.Zx (x n) (s n * r) ω l : ℝ))
            atTop (nhds (Zh r)) :=
          tendsto_pi_nhds.mpr (fun l => relaxed_uoc_at hZ r (by linarith) l)
        exact ((h76.1 i (Zh r) (hZnn r (by linarith)) (hwin r hr1 hr2)).tendsto).comp hconv
    apply tendsto_nhds_unique hlimT
    apply hlimI.congr'
    filter_upwards [hspos] with n hn
    exact (hseq n hn).symm
  -- FTC
  have hmeasF : StronglyMeasurableAtFilter g (nhds t) volume := by
    have hco : ContinuousOn g (Set.Ioo a c) := fun r hr => (hgc r hr.1 hr.2).continuousWithinAt
    exact hco.stronglyMeasurableAtFilter isOpen_Ioo t ⟨hat, htc⟩
  have hderiv : HasDerivAt (fun u => ∫ r in t..u, g r) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl) hmeasF (hgc t hat htc)
  have hderiv2 := hderiv.const_add (Th t i)
  apply hderiv2.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hat htc] with u hu
  rcases le_total t u with htu | hut
  · have := hclaim t u hat htu hu.2
    linarith
  · have := hclaim u t hu.1 hut htc
    rw [intervalIntegral.integral_symm]
    linarith

end ProcessingNetworks.FluidEquations

open ProcessingNetworks.FluidEquations
open MeasureTheory Filter ProcessingNetworks.Stability

theorem solution
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (sd : SPNData I I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep sd E v φ)
    (h : (Fin I → ℝ) → (Fin I → ℝ))
    (h719 : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → ∀ k, ∑ i, sd.A k i * h z i ≤ sd.b k)
    (h76 : SatisfiesAssumption76 h)
    (hnonneg : ∀ z : Fin I → ℝ, (∀ j, 0 ≤ z j) → ∀ i, 0 ≤ h z i)
    (hZmeas : ∀ (x : Xstate) (ω : Ω), Measurable fun u => fam.Zx x u ω)
    (hpolicy : ∀ (x : Xstate) (ω : Ω) (t : ℝ), 0 ≤ t →
      fam.T x t ω = fun i => ∫ u in Set.Ioc (0 : ℝ) t, h (fun l => (fam.Zx x u ω l : ℝ)) i)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (i : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < Zh t i) :
    HasDerivAt (fun s => Th s i) (h (Zh t) i) t :=
  relaxed_policy_fluid_equation_corrected sd fam h h719 h76 hnonneg hZmeas hpolicy Dh Fh Th Zh hfl i t ht hz
