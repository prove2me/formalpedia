-- Prove2me | solution 1 for PowerOfDUniversality.Diffusion.theorem_2_4_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:49:25.220254+00:00
-- url     : https://prove2.me/submissions/6f8a71bd-f1dd-4423-b1af-47baef79c11e

import Mathlib
import Definitions.Def_PowerOfDUniversality_Diffusion_Limit

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open PowerOfDUniversality.Diffusion

namespace PoDUniqAux

open BellWilliams2001.ThresholdPolicy

lemma cadlag_bdd (f : ℝ → ℝ) (hf : IsCadlag f) (t : ℝ) :
    ∃ K, ∀ s ∈ Icc 0 t, |f s| ≤ K := by
  refine (isCompact_Icc (a := (0:ℝ)) (b := t)).induction_on
    (p := fun S => ∃ K, ∀ s ∈ S, |f s| ≤ K) ⟨0, by simp⟩ ?_ ?_ ?_
  · intro S T hST ⟨K, hK⟩
    exact ⟨K, fun s hs => hK s (hST hs)⟩
  · intro S T ⟨K, hK⟩ ⟨K', hK'⟩
    refine ⟨max K K', fun s hs => ?_⟩
    rcases hs with hs | hs
    · exact (hK s hs).trans (le_max_left _ _)
    · exact (hK' s hs).trans (le_max_right _ _)
  · intro x hx
    have hR : ∀ᶠ y in 𝓝[≥] x, |f y| < |f x| + 1 := by
      have := ((hf.1 x hx.1).abs)
      exact this.eventually (gt_mem_nhds (by linarith))
    rcases eq_or_lt_of_le hx.1 with h0 | hpos
    · subst h0
      refine ⟨{y | |f y| < |f 0| + 1}, ?_, ⟨|f 0| + 1, fun s hs => le_of_lt hs⟩⟩
      exact nhdsWithin_mono _ (fun y hy => hy.1) hR
    · obtain ⟨l, hl⟩ := hf.2 x hpos
      have hL : ∀ᶠ y in 𝓝[<] x, |f y| < |l| + 1 :=
        (hl.abs).eventually (gt_mem_nhds (by linarith))
      refine ⟨{y | |f y| < max (|f x| + 1) (|l| + 1)}, ?_, ⟨_, fun s hs => le_of_lt hs⟩⟩
      apply mem_nhdsWithin_of_mem_nhds
      rw [← nhdsLT_sup_nhdsGE, Filter.mem_sup]
      exact ⟨hL.mono fun y hy => lt_max_of_lt_right hy, hR.mono fun y hy => lt_max_of_lt_left hy⟩

lemma cadlag_meas (f : ℝ → ℝ) (hf : IsCadlag f) : Measurable (fun s => f (max s 0)) := by
  set g : ℕ → ℝ → ℝ := fun n s => f ((⌈max s 0 * (n + 1)⌉₊ : ℝ) / (n + 1)) with hg
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    have h1 : Measurable (fun s : ℝ => ⌈max s 0 * ((n:ℝ) + 1)⌉₊) :=
      ((measurable_id.max measurable_const).mul_const _).nat_ceil
    exact (measurable_from_nat (f := fun m : ℕ => f ((m : ℝ) / (n + 1)))).comp h1
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.2 fun s => ?_)
  set y := max s 0
  have hy : 0 ≤ y := le_max_right _ _
  have hc : Tendsto (fun n : ℕ => (⌈y * (n + 1)⌉₊ : ℝ) / (n + 1)) atTop (𝓝[≥] y) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hup : ∀ n : ℕ, (⌈y * (n + 1)⌉₊ : ℝ) / (n + 1) ≤ y + 1 / (n + 1) := by
        intro n
        have hn : (0:ℝ) < n + 1 := by positivity
        rw [div_le_iff₀ hn]
        have := Nat.ceil_lt_add_one (mul_nonneg hy hn.le)
        have : y * (n+1) + 1 = (y + 1 / (n + 1)) * (n + 1) := by field_simp
        linarith
      have hlow : ∀ n : ℕ, y ≤ (⌈y * (n + 1)⌉₊ : ℝ) / (n + 1) := by
        intro n
        have hn : (0:ℝ) < n + 1 := by positivity
        rw [le_div_iff₀ hn]
        exact Nat.le_ceil _
      have ht : Tendsto (fun n : ℕ => y + 1 / ((n:ℝ) + 1)) atTop (𝓝 y) := by
        simpa using (tendsto_const_nhds (x := y)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht hlow hup
    · exact Eventually.of_forall fun n => by
        have hn : (0:ℝ) < n + 1 := by positivity
        show y ≤ _
        rw [le_div_iff₀ hn]
        exact Nat.le_ceil _
  exact (hf.1 y hy).tendsto.comp hc

lemma cadlag_int (f : ℝ → ℝ) (hf : IsCadlag f) (t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable f volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  obtain ⟨K, hK⟩ := cadlag_bdd f hf t
  have hI : IntegrableOn (fun s => f (max s 0)) (Ioc 0 t) volume := by
    refine Measure.integrableOn_of_bounded (M := K) (by simp) (cadlag_meas f hf).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs, max_eq_left hs.1.le]; exact hK s ⟨hs.1.le, hs.2⟩
  refine hI.congr_fun (fun s hs => ?_) measurableSet_Ioc
  simp [max_eq_left hs.1.le]


lemma stieltjes_eq (U : ℝ → ℝ) (hU : Monotone (fun r => U (max r 0)))
    (hUr : ∀ r, 0 ≤ r → ContinuousWithinAt U (Ici r) r) (r : ℝ) (hr : 0 ≤ r) :
    hU.stieltjesFunction r = U r := by
  rw [Monotone.stieltjesFunction_eq]
  have h1 : Tendsto U (𝓝[>] r) (𝓝 (U r)) := (hUr r hr).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h2 : Tendsto (fun r => U (max r 0)) (𝓝[>] r) (𝓝 (U r)) := by
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [max_eq_left (hr.trans (le_of_lt hy))]
  exact rightLim_eq_of_tendsto h2

lemma skorokhod (z z' U U' : ℝ → ℝ) (t B : ℝ)
    (hU : Monotone (fun r => U (max r 0)))
    (hUr : ∀ r, 0 ≤ r → ContinuousWithinAt U (Ici r) r)
    (hmeas : hU.stieltjesFunction.measure {r | 0 ≤ r ∧ z r < 0} = 0)
    (hU' : Monotone (fun r => U' (max r 0)))
    (hz' : ∀ r, 0 ≤ r → z' r ≤ 0)
    (hA : ∀ r ∈ Icc 0 t, z r - z' r ≤ B - (U r - U' r))
    (h0 : U 0 - U' 0 ≤ B) :
    ∀ s ∈ Icc 0 t, U s - U' s ≤ B := by
  intro s hs
  by_contra hlt
  push_neg at hlt
  set m := (B + (U s - U' s)) / 2 with hm
  have hBm : B < m := by linarith
  have hmV : m < U s - U' s := by linarith
  set S := {r | r ∈ Icc 0 s ∧ U r - U' r ≤ m} with hS
  have h0S : (0:ℝ) ∈ S := ⟨⟨le_rfl, hs.1⟩, by linarith⟩
  have hSb : BddAbove S := ⟨s, fun r hr => hr.1.2⟩
  set τ := sSup S with hτ
  have hτs : τ ≤ s := csSup_le ⟨0, h0S⟩ fun r hr => hr.1.2
  have hτ0 : 0 ≤ τ := le_csSup hSb h0S
  set F := hU.stieltjesFunction
  have hF : ∀ r, 0 ≤ r → F r = U r := stieltjes_eq U hU hUr
  have hU'mono : ∀ a b, 0 ≤ a → a ≤ b → U' a ≤ U' b := by
    intro a b ha hab
    have := hU' hab
    simpa [max_eq_left ha, max_eq_left (ha.trans hab)] using this
  -- points not in S within [0,s] have z < 0
  have hneg : ∀ r, r ∈ Icc 0 s → r ∉ S → 0 ≤ r ∧ z r < 0 := by
    intro r hr hrS
    have hV : m < U r - U' r := by
      by_contra h; push_neg at h; exact hrS ⟨hr, h⟩
    have := hA r ⟨hr.1, hr.2.trans hs.2⟩
    have := hz' r hr.1
    exact ⟨hr.1, by linarith⟩
  have hK : ∀ r, τ < r → r ≤ s → 0 ≤ r ∧ z r < 0 := by
    intro r hτr hrs
    refine hneg r ⟨hτ0.trans hτr.le, hrs⟩ fun hrS => ?_
    exact absurd (le_csSup hSb hrS) (not_le.2 hτr)
  by_cases hτS : τ ∈ S
  · have hsub : Ioc τ s ⊆ {r | 0 ≤ r ∧ z r < 0} := fun r hr => hK r hr.1 hr.2
    have hz : F.measure (Ioc τ s) = 0 := measure_mono_null hsub hmeas
    rw [StieltjesFunction.measure_Ioc, ENNReal.ofReal_eq_zero, hF s hs.1, hF τ hτ0] at hz
    have := hU'mono τ s hτ0 hτs
    have := hτS.2
    linarith
  · have hsub : Icc τ s ⊆ {r | 0 ≤ r ∧ z r < 0} := by
      intro r hr
      rcases eq_or_lt_of_le hr.1 with h | h
      · subst h; exact hneg _ ⟨hτ0, hτs⟩ hτS
      · exact hK r h hr.2
    have hz : F.measure (Icc τ s) = 0 := measure_mono_null hsub hmeas
    rw [StieltjesFunction.measure_Icc, ENNReal.ofReal_eq_zero, hF s hs.1] at hz
    have hlim := F.mono.tendsto_leftLim τ
    have : U s - U' s ≤ m := by
      refine le_of_forall_pos_lt_add fun η hη => ?_
      have hev : ∀ᶠ r in 𝓝[<] τ, Function.leftLim F τ - η < F r :=
        hlim.eventually (lt_mem_nhds (by linarith))
      obtain ⟨l, hl, hlsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
      obtain ⟨r, hrS, hlr⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hl
      have hrτ : r ≤ τ := le_csSup hSb hrS
      have hrτ' : r < τ := lt_of_le_of_ne hrτ (fun h => hτS (h ▸ hrS))
      have h1 := hlsub ⟨hlr, hrτ'⟩
      simp only [mem_setOf_eq] at h1
      rw [hF r hrS.1.1] at h1
      have := hU'mono r s hrS.1.1 hrS.1.2
      have := hrS.2
      linarith
    linarith

lemma gronwall0 (φ : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hφ0 : ∀ t, 0 ≤ t → 0 ≤ φ t)
    (hint : ∀ t, 0 ≤ t → IntervalIntegrable φ volume 0 t)
    (hbd : ∀ T, ∃ K, ∀ s ∈ Icc 0 T, φ s ≤ K)
    (h : ∀ t, 0 ≤ t → φ t ≤ C * ∫ s in (0:ℝ)..t, φ s) : ∀ t, 0 ≤ t → φ t = 0 := by
  intro t ht
  obtain ⟨K, hK⟩ := hbd t
  have hind : ∀ n : ℕ, ∀ s ∈ Icc 0 t, φ s ≤ K * ((C * s) ^ n / n.factorial) := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hK s hs
    | succ n ih =>
      intro s hs
      have hle : ∫ r in (0:ℝ)..s, φ r ≤ ∫ r in (0:ℝ)..s, K * ((C * r) ^ n / n.factorial) := by
        apply intervalIntegral.integral_mono_on hs.1 (hint s hs.1)
        · exact (by fun_prop : Continuous fun r : ℝ => K * ((C * r) ^ n / n.factorial)).intervalIntegrable _ _
        · intro r hr; exact ih r ⟨hr.1, hr.2.trans hs.2⟩
      have hcomp : ∫ r in (0:ℝ)..s, K * ((C * r) ^ n / n.factorial)
          = K * C ^ n / n.factorial * (s ^ (n+1) / (n+1)) := by
        have : (fun r : ℝ => K * ((C * r) ^ n / n.factorial)) = fun r => (K * C ^ n / n.factorial) * r ^ n := by
          funext r; rw [mul_pow]; ring
        rw [this, intervalIntegral.integral_const_mul, integral_pow]
        simp
      calc φ s ≤ C * ∫ r in (0:ℝ)..s, φ r := h s hs.1
        _ ≤ C * (K * C ^ n / n.factorial * (s ^ (n+1) / (n+1))) := by
          rw [← hcomp]; exact mul_le_mul_of_nonneg_left hle hC
        _ = K * ((C * s) ^ (n+1) / (n+1).factorial) := by
          rw [Nat.factorial_succ, mul_pow]; push_cast; field_simp; ring
  have hlim : Tendsto (fun n : ℕ => K * ((C * t) ^ n / n.factorial)) atTop (𝓝 (K * 0)) :=
    tendsto_const_nhds.mul (FloorSemiring.tendsto_pow_div_factorial_atTop (C * t))
  rw [mul_zero] at hlim
  have : φ t ≤ 0 := ge_of_tendsto' hlim fun n => hind n t ⟨ht, le_rfl⟩
  exact le_antisymm this (hφ0 t ht)

end PoDUniqAux

open PoDUniqAux in
theorem solution (β : ℝ) (hβ : 0 < β) (k : ℕ) (hk : 2 ≤ k) (w : ℝ → ℝ)
    (x : Fin k → ℝ) (Q Q' : ℝ → ℕ → ℝ) (U U' : ℝ → ℝ)
    (h : Solves24 β k w x Q U) (h' : Solves24 β k w x Q' U') :
    ∀ t : ℝ, 0 ≤ t → Q t = Q' t ∧ U t = U' t := by
  obtain ⟨h0, hinit, hcad, hUcad, -, ⟨hUm, hmeas⟩, hle, e1, e2, e3⟩ := h
  obtain ⟨h0', hinit', hcad', hUcad', -, ⟨hUm', hmeas'⟩, hle', e1', e2', e3'⟩ := h'
  -- integrability of every coordinate
  have hQint : ∀ (R : ℝ → ℕ → ℝ), (∀ t : ℝ, 0 ≤ t → R t 0 = 0 ∧ ∀ i : ℕ, k + 1 ≤ i → R t i = 0) →
      (∀ i : ℕ, 1 ≤ i → i ≤ k → BellWilliams2001.ThresholdPolicy.IsCadlag (fun t => R t i)) →
      ∀ i t, 0 ≤ t → IntervalIntegrable (fun s => R s i) volume 0 t := by
    intro R hR0 hRc i t ht
    by_cases hi : 1 ≤ i ∧ i ≤ k
    · exact cadlag_int _ (hRc i hi.1 hi.2) t ht
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
      refine (integrableOn_zero (μ := volume) (s := Ioc 0 t)).congr_fun (fun s hs => ?_) measurableSet_Ioc
      rcases Nat.eq_zero_or_pos i with h0i | hpos
      · subst h0i; exact ((hR0 s hs.1.le).1).symm
      · exact ((hR0 s hs.1.le).2 i (by omega)).symm
  have hQi := hQint Q h0 hcad
  have hQi' := hQint Q' h0' hcad'
  set D : ℕ → ℝ → ℝ := fun i s => Q s i - Q' s i with hD
  set φ : ℝ → ℝ := fun s => ∑ i ∈ Finset.Icc 1 k, |D i s| with hφ
  have hDint : ∀ i t, 0 ≤ t → IntervalIntegrable (D i) volume 0 t :=
    fun i t ht => (hQi i t ht).sub (hQi' i t ht)
  have hφint : ∀ t, 0 ≤ t → IntervalIntegrable φ volume 0 t := by
    intro t ht
    have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := t) (Finset.Icc 1 k)
      (f := fun i s => |D i s|) (fun i _ => (hDint i t ht).abs)
    have e : φ = ∑ i ∈ Finset.Icc 1 k, fun s => |D i s| := by
      funext s; simp [hφ, Finset.sum_apply]
    rw [e]; exact this
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hDφ : ∀ i, 1 ≤ i → ∀ s, 0 ≤ s → |D i s| ≤ φ s := by
    intro i hi s hs
    by_cases hik : i ≤ k
    · exact Finset.single_le_sum (f := fun i => |D i s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.2 ⟨hi, hik⟩)
    · have : D i s = 0 := by
        simp only [hD, (h0 s hs).2 i (by omega), (h0' s hs).2 i (by omega), sub_self]
      rw [this, abs_zero]; exact hφ0 s
  set J : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, φ s with hJ
  have hJmono : ∀ r t, 0 ≤ r → r ≤ t → J r ≤ J t := by
    intro r t hr hrt
    exact intervalIntegral.integral_mono_interval le_rfl hr hrt
      (Eventually.of_forall fun s => hφ0 s) (hφint t (hr.trans hrt))
  have hJ0 : ∀ t, 0 ≤ t → 0 ≤ J t := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s _ => hφ0 s
  -- bound on integrals of differences
  have hintbd : ∀ (g : ℝ → ℝ) (t : ℝ), 0 ≤ t → IntervalIntegrable g volume 0 t →
      (∀ s, 0 ≤ s → |g s| ≤ 2 * φ s) → |∫ s in (0:ℝ)..t, g s| ≤ 2 * J t := by
    intro g t ht hg hgb
    calc |∫ s in (0:ℝ)..t, g s| ≤ ∫ s in (0:ℝ)..t, |g s| :=
          intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in (0:ℝ)..t, 2 * φ s :=
          intervalIntegral.integral_mono_on ht hg.abs ((hφint t ht).const_mul 2)
            fun s hs => hgb s hs.1
      _ = 2 * J t := by rw [intervalIntegral.integral_const_mul]
  have hpair : ∀ i j, 1 ≤ i → 1 ≤ j → ∀ s, 0 ≤ s → |D i s| + |D j s| ≤ 2 * φ s := by
    intro i j hi hj s hs
    have := hDφ i hi s hs; have := hDφ j hj s hs; linarith
  -- initial values agree
  have hQ0 : ∀ i, 1 ≤ i → i ≤ k → Q 0 i = Q' 0 i := by
    intro i hi hik
    have a := hinit ⟨i - 1, by omega⟩
    have b := hinit' ⟨i - 1, by omega⟩
    simp only [Nat.sub_add_cancel hi] at a b
    rw [a, b]
  have hU0 : U 0 = U' 0 := by
    have a := e1 0 le_rfl
    have b := e1' 0 le_rfl
    simp only [intervalIntegral.integral_same, mul_zero, sub_zero, add_zero] at a b
    linarith
  -- the three relations
  have rel1 : ∀ t, 0 ≤ t → D 1 t = (∫ s in (0:ℝ)..t, (-D 1 s + D 2 s)) - (U t - U' t) := by
    intro t ht
    have a := e1 t ht
    have b := e1' t ht
    have hi : (∫ s in (0:ℝ)..t, (-Q s 1 + Q s 2)) - (∫ s in (0:ℝ)..t, (-Q' s 1 + Q' s 2))
        = ∫ s in (0:ℝ)..t, (-D 1 s + D 2 s) := by
      rw [← intervalIntegral.integral_sub (f := fun s => -Q s 1 + Q s 2) (g := fun s => -Q' s 1 + Q' s 2) ((hQi 1 t ht).neg.add (hQi 2 t ht))
        ((hQi' 1 t ht).neg.add (hQi' 2 t ht))]
      congr 1; funext s; simp only [hD]; ring
    have := hQ0 1 le_rfl (by omega)
    simp only [hD]; rw [← hi]; linarith
  have rel2 : ∀ t, 0 ≤ t → D 2 t = (U t - U' t) - ∫ s in (0:ℝ)..t, (D 2 s - D 3 s) := by
    intro t ht
    have a := e2 t ht
    have b := e2' t ht
    have hi : (∫ s in (0:ℝ)..t, (Q s 2 - Q s 3)) - (∫ s in (0:ℝ)..t, (Q' s 2 - Q' s 3))
        = ∫ s in (0:ℝ)..t, (D 2 s - D 3 s) := by
      rw [← intervalIntegral.integral_sub (f := fun s => Q s 2 - Q s 3) (g := fun s => Q' s 2 - Q' s 3) ((hQi 2 t ht).sub (hQi 3 t ht))
        ((hQi' 2 t ht).sub (hQi' 3 t ht))]
      congr 1; funext s; simp only [hD]; ring
    have := hQ0 2 (by omega) hk
    simp only [hD]; rw [← hi]; linarith
  have rel3 : ∀ i, 3 ≤ i → i ≤ k → ∀ t, 0 ≤ t →
      D i t = -∫ s in (0:ℝ)..t, (D i s - D (i+1) s) := by
    intro i hi hik t ht
    have a := e3 i hi hik t ht
    have b := e3' i hi hik t ht
    have hi' : (∫ s in (0:ℝ)..t, (Q s i - Q s (i+1))) - (∫ s in (0:ℝ)..t, (Q' s i - Q' s (i+1)))
        = ∫ s in (0:ℝ)..t, (D i s - D (i+1) s) := by
      rw [← intervalIntegral.integral_sub (f := fun s => Q s i - Q s (i+1)) (g := fun s => Q' s i - Q' s (i+1)) ((hQi i t ht).sub (hQi (i+1) t ht))
        ((hQi' i t ht).sub (hQi' (i+1) t ht))]
      congr 1; funext s; simp only [hD]; ring
    have := hQ0 i (by omega) hik
    simp only [hD]; rw [← hi']; linarith
  -- bound on A
  have hAbd : ∀ t, 0 ≤ t → |∫ s in (0:ℝ)..t, (-D 1 s + D 2 s)| ≤ 2 * J t := by
    intro t ht
    refine hintbd _ t ht ((hDint 1 t ht).neg.add (hDint 2 t ht)) fun s hs => ?_
    have := hpair 1 2 le_rfl (by norm_num) s hs
    calc |-D 1 s + D 2 s| ≤ |-D 1 s| + |D 2 s| := abs_add_le _ _
      _ = |D 1 s| + |D 2 s| := by rw [abs_neg]
      _ ≤ _ := this
  -- Skorokhod bound on V
  have hVbd : ∀ t, 0 ≤ t → |U t - U' t| ≤ 2 * J t := by
    intro T hT
    have hA : ∀ r, 0 ≤ r → r ≤ T → |∫ s in (0:ℝ)..r, (-D 1 s + D 2 s)| ≤ 2 * J T :=
      fun r hr hrT => (hAbd r hr).trans (by linarith [hJmono r T hr hrT])
    have hB : 0 ≤ 2 * J T := by linarith [hJ0 T hT]
    have s1 := skorokhod (fun r => Q r 1) (fun r => Q' r 1) U U' T (2 * J T) hUm hUcad.1 hmeas hUm'
      (fun r hr => hle' r hr) (fun r hr => by
        have := rel1 r hr.1; have := hA r hr.1 hr.2
        have := le_abs_self (∫ s in (0:ℝ)..r, (-D 1 s + D 2 s))
        simp only [hD] at *; linarith) (by rw [hU0]; linarith) T ⟨hT, le_rfl⟩
    have s2 := skorokhod (fun r => Q' r 1) (fun r => Q r 1) U' U T (2 * J T) hUm' hUcad'.1 hmeas' hUm
      (fun r hr => hle r hr) (fun r hr => by
        have := rel1 r hr.1; have := hA r hr.1 hr.2
        have := neg_abs_le (∫ s in (0:ℝ)..r, (-D 1 s + D 2 s))
        simp only [hD] at *; linarith) (by rw [hU0]; linarith) T ⟨hT, le_rfl⟩
    rw [abs_le]; constructor <;> linarith
  -- pointwise bound on each D i
  have hDbd : ∀ i ∈ Finset.Icc 1 k, ∀ t, 0 ≤ t → |D i t| ≤ 4 * J t := by
    intro i hi t ht
    rw [Finset.mem_Icc] at hi
    have hV := hVbd t ht
    rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with h1 | h2 | h3
    · subst h1
      rw [rel1 t ht]
      have := hAbd t ht
      calc _ ≤ |∫ s in (0:ℝ)..t, (-D 1 s + D 2 s)| + |U t - U' t| := abs_sub _ _
        _ ≤ _ := by linarith
    · subst h2
      rw [rel2 t ht]
      have := hintbd (fun s => D 2 s - D 3 s) t ht ((hDint 2 t ht).sub (hDint 3 t ht))
        fun s hs => (abs_sub _ _).trans (hpair 2 3 (by norm_num) (by norm_num) s hs)
      calc _ ≤ |U t - U' t| + |∫ s in (0:ℝ)..t, (D 2 s - D 3 s)| := abs_sub _ _
        _ ≤ _ := by linarith
    · rw [rel3 i h3 hi.2 t ht, abs_neg]
      have := hintbd (fun s => D i s - D (i+1) s) t ht ((hDint i t ht).sub (hDint (i+1) t ht))
        fun s hs => (abs_sub _ _).trans (hpair i (i+1) (by omega) (by omega) s hs)
      linarith [hJ0 t ht]
  have hφbd : ∀ t, 0 ≤ t → φ t ≤ (4 * k) * J t := by
    intro t ht
    calc φ t ≤ ∑ i ∈ Finset.Icc 1 k, 4 * J t := Finset.sum_le_sum fun i hi => hDbd i hi t ht
      _ = (4 * k) * J t := by rw [Finset.sum_const, Nat.card_Icc]; simp; ring
  have hbd : ∀ T, ∃ K, ∀ s ∈ Icc 0 T, φ s ≤ K := by
    intro T
    have : ∀ i, ∃ K, ∀ s ∈ Icc 0 T, |D i s| ≤ K := by
      intro i
      by_cases hi : 1 ≤ i ∧ i ≤ k
      · obtain ⟨K1, hK1⟩ := cadlag_bdd _ (hcad i hi.1 hi.2) T
        obtain ⟨K2, hK2⟩ := cadlag_bdd _ (hcad' i hi.1 hi.2) T
        exact ⟨K1 + K2, fun s hs => (abs_sub _ _).trans (add_le_add (hK1 s hs) (hK2 s hs))⟩
      · refine ⟨0, fun s hs => ?_⟩
        rcases Nat.eq_zero_or_pos i with h0i | hpos
        · subst h0i; simp [hD, (h0 s hs.1).1, (h0' s hs.1).1]
        · simp [hD, (h0 s hs.1).2 i (by omega), (h0' s hs.1).2 i (by omega)]
    choose K hK using this
    exact ⟨∑ i ∈ Finset.Icc 1 k, K i, fun s hs => Finset.sum_le_sum fun i _ => hK i s hs⟩
  have hφz := gronwall0 φ (4 * k) (by positivity) (fun t _ => hφ0 t) hφint hbd hφbd
  have hJz : ∀ t, 0 ≤ t → J t = 0 := by
    intro t ht
    simp only [hJ]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun s hs => by
      rw [uIcc_of_le ht] at hs; exact hφz s hs.1)]
    simp
  intro t ht
  constructor
  · funext i
    by_cases hi : 1 ≤ i ∧ i ≤ k
    · have := hDφ i hi.1 t ht
      rw [hφz t ht] at this
      have : D i t = 0 := abs_nonpos_iff.1 this
      simp only [hD] at this; linarith
    · rcases Nat.eq_zero_or_pos i with h0i | hpos
      · subst h0i; rw [(h0 t ht).1, (h0' t ht).1]
      · rw [(h0 t ht).2 i (by omega), (h0' t ht).2 i (by omega)]
  · have := hVbd t ht
    rw [hJz t ht, mul_zero] at this
    linarith [abs_nonpos_iff.1 this]
