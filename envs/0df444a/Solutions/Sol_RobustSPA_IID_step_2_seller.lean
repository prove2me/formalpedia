-- Prove2me | solution 1 for RobustSPA.IID.step_2_seller
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:47:26.883021+00:00
-- url     : https://prove2.me/submissions/d12339e7-2e90-471a-96b0-50ac70b3f37c

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting
import Theorems.Thm_RobustSPA_IID_SPA_isDSIC
import Theorems.Thm_RobustSPA_IID_proposition_A_3_phi

open MeasureTheory RobustSPA.IID
open scoped Classical

namespace RAffS2

/-- If `F` has increments squeezed by a monotone `f`, then `∫ f = F b - F a`. -/
theorem integral_eq_of_squeeze {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Set.Icc a b))
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (t - s) * f s ≤ F t - F s ∧ F t - F s ≤ (t - s) * f t) :
    ∫ x in a..b, f x = F b - F a := by
  set E := |(∫ x in a..b, f x) - (F b - F a)| with hE
  have hfab : f a ≤ f b := hf ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  set C := (b - a) * (f b - f a) with hC
  have key : ∀ N : ℕ, 0 < N → E ≤ C / N := by
    intro N hN
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    set δ := (b - a) / N with hδ
    have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hNpos.le
    let x : ℕ → ℝ := fun j => a + j * δ
    have hxN : x N = b := by
      simp only [x, hδ]; field_simp; ring
    have hx0 : x 0 = a := by simp [x]
    have hxmem : ∀ j, j ≤ N → x j ∈ Set.Icc a b := by
      intro j hj
      refine ⟨by simp only [x]; nlinarith [hδ0], ?_⟩
      have : (j:ℝ) * δ ≤ N * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ0
      have h2 : (N:ℝ) * δ = b - a := by simp only [hδ]; field_simp
      simp only [x]; linarith
    have hxsucc : ∀ j, x (j + 1) = x j + δ := by intro j; simp only [x]; push_cast; ring
    have hint : ∀ j < N, IntervalIntegrable f volume (x j) (x (j + 1)) := by
      intro j hj
      apply MonotoneOn.intervalIntegrable
      rw [Set.uIcc_of_le (by rw [hxsucc]; linarith)]
      exact hf.mono (Set.Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j+1) hj).2)
    have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
    rw [hx0, hxN] at hsum
    have htel : ∑ j ∈ Finset.range N, (F (x (j + 1)) - F (x j)) = F b - F a := by
      rw [Finset.sum_range_sub (fun j => F (x j)), hxN, hx0]
    have htelf : ∑ j ∈ Finset.range N, (f (x (j + 1)) - f (x j)) = f b - f a := by
      rw [Finset.sum_range_sub (fun j => f (x j)), hxN, hx0]
    have hpiece : ∀ j ∈ Finset.range N,
        |(∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j))|
          ≤ δ * (f (x (j + 1)) - f (x j)) := by
      intro j hj
      have hj' : j < N := Finset.mem_range.1 hj
      have hle : x j ≤ x (j + 1) := by rw [hxsucc]; linarith
      have hmj := hxmem j hj'.le
      have hmj1 := hxmem (j + 1) hj'
      have hlo : ∫ y in x j..x (j + 1), f (x j) ≤ ∫ y in x j..x (j + 1), f y :=
        intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint j hj')
          (fun y hy => hf hmj ⟨hmj.1.trans hy.1, hy.2.trans hmj1.2⟩ hy.1)
      have hhi : ∫ y in x j..x (j + 1), f y ≤ ∫ y in x j..x (j + 1), f (x (j + 1)) :=
        intervalIntegral.integral_mono_on hle (hint j hj') intervalIntegrable_const
          (fun y hy => hf ⟨hmj.1.trans hy.1, hy.2.trans hmj1.2⟩ hmj1 hy.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
      have hd : x (j + 1) - x j = δ := by rw [hxsucc]; ring
      rw [hd] at hlo hhi
      obtain ⟨h1, h2⟩ := h (x j) (x (j + 1)) hmj.1 hle hmj1.2
      rw [hd] at h1 h2
      rw [abs_le]; constructor <;> nlinarith
    have : (∫ x in a..b, f x) - (F b - F a)
        = ∑ j ∈ Finset.range N, ((∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j))) := by
      rw [Finset.sum_sub_distrib, hsum, htel]
    rw [hE, this]
    calc |∑ j ∈ Finset.range N, ((∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j)))|
        ≤ ∑ j ∈ Finset.range N, |(∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, δ * (f (x (j + 1)) - f (x j)) := Finset.sum_le_sum hpiece
      _ = C / N := by rw [← Finset.mul_sum, htelf, hδ, hC]; ring
  have hC0 : 0 ≤ C := mul_nonneg (by linarith) (by linarith)
  have hE0 : E = 0 := by
    by_contra hne
    have hEpos : 0 < E := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (C / E)
    have hNpos : (0:ℝ) < N := lt_of_le_of_lt (div_nonneg hC0 hEpos.le) hN
    have h1 := key N (by exact_mod_cast hNpos)
    rw [le_div_iff₀ hNpos] at h1
    rw [div_lt_iff₀ hEpos] at hN
    linarith
  have := abs_eq_zero.1 hE0
  linarith

/-- antitone version -/
theorem integral_eq_of_squeeze_anti {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Set.Icc a b))
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (t - s) * f t ≤ F t - F s ∧ F t - F s ≤ (t - s) * f s) :
    ∫ x in a..b, f x = F b - F a := by
  have := integral_eq_of_squeeze (f := fun x => -f x) (F := fun x => -F x) hab
    (fun x hx y hy hxy => neg_le_neg (hf hx hy hxy))
    (fun s t h1 h2 h3 => by
      obtain ⟨k1, k2⟩ := h s t h1 h2 h3
      constructor <;> nlinarith)
  rw [intervalIntegral.integral_neg] at this
  linarith


/-- quantile transform of the isorevenue law: `T(u) = 1 / max(1, u/r)` -/
noncomputable def Tm (r u : ℝ) : ℝ := (max 1 (u / r))⁻¹

section T
variable {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
include hr0

lemma meas_Tm : Measurable (Tm r) := by unfold Tm; fun_prop

lemma Tm_pos (u : ℝ) : 0 < Tm r u := by
  unfold Tm; exact inv_pos.2 (lt_of_lt_of_le one_pos (le_max_left _ _))

lemma Tm_le_one (u : ℝ) : Tm r u ≤ 1 := by
  unfold Tm; exact inv_le_one_of_one_le₀ (le_max_left _ _)

include hr1 in
lemma Tm_ge (u : ℝ) (hu : u ≤ 1) : r ≤ Tm r u := by
  unfold Tm
  rw [le_inv_comm₀ hr0 (lt_of_lt_of_le one_pos (le_max_left _ _))]
  apply max_le ((one_le_inv₀ hr0).mpr hr1.le)
  rw [div_eq_mul_inv]
  calc u * r⁻¹ ≤ 1 * r⁻¹ := mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr hr0.le)
    _ = r⁻¹ := one_mul _

lemma Tm_mem (u : ℝ) : Tm r u ∈ Set.Icc (0 : ℝ) 1 := ⟨(Tm_pos hr0 u).le, Tm_le_one hr0 u⟩

lemma Tm_small (u : ℝ) (hu : u ≤ r) : Tm r u = 1 := by
  unfold Tm
  have : u / r ≤ 1 := by rw [div_le_one hr0]; exact hu
  rw [max_eq_left this, inv_one]

lemma Tm_big (u : ℝ) (hu : r ≤ u) : Tm r u = r / u := by
  unfold Tm
  have hu0 : 0 < u := lt_of_lt_of_le hr0 hu
  have : 1 ≤ u / r := by rw [le_div_iff₀ hr0]; linarith
  rw [max_eq_right this, inv_div]

lemma Tm_anti : AntitoneOn (Tm r) (Set.Icc 0 1) := by
  intro x _ y _ hxy
  unfold Tm
  apply inv_anti₀ (lt_of_lt_of_le one_pos (le_max_left _ _))
  exact max_le_max (le_refl _) (div_le_div_of_nonneg_right hxy hr0.le)

include hr1 in
lemma G_eq (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF r t) :
    G = (volume.restrict (Set.Icc (0 : ℝ) 1)).map (Tm r) := by
  apply Measure.ext_of_Iic
  intro a
  have h1 : G (Set.Iic a) = ENNReal.ofReal (isoCDF r a) := by
    rw [← hG a, cdfOf, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [h1, Measure.map_apply (meas_Tm hr0) measurableSet_Iic, Measure.restrict_apply
    ((meas_Tm hr0) measurableSet_Iic)]
  unfold isoCDF
  by_cases ha1 : 1 ≤ a
  · rw [if_neg (by linarith), if_neg (by linarith)]
    have : Tm r ⁻¹' Set.Iic a ∩ Set.Icc 0 1 = Set.Icc 0 1 := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
      exact ⟨fun h => h.2, fun h => ⟨(Tm_le_one hr0 u).trans ha1, h⟩⟩
    rw [this, Real.volume_Icc]; simp
  push_neg at ha1
  by_cases hae : a < r
  · rw [if_pos hae, ENNReal.ofReal_zero]
    have : Tm r ⁻¹' Set.Iic a ∩ Set.Icc 0 1 = ∅ := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h hu
      have := Tm_ge hr0 hr1 u hu.2; linarith
    rw [this, measure_empty]
  · push_neg at hae
    rw [if_neg (not_lt.2 hae), if_pos ha1]
    have ha0 : 0 < a := lt_of_lt_of_le hr0 hae
    set θ := r / a with hθ
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one ha0]; exact hae
    have hθ0 : 0 ≤ θ := div_nonneg hr0.le ha0.le
    have : Tm r ⁻¹' Set.Iic a ∩ Set.Icc 0 1 = Set.Icc θ 1 := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h, hu0, hu1⟩
        refine ⟨?_, hu1⟩
        by_contra hlt
        push_neg at hlt
        by_cases hue : u ≤ r
        · rw [Tm_small hr0 u hue] at h; linarith
        · push_neg at hue
          rw [Tm_big hr0 u hue.le, div_le_iff₀ (lt_trans hr0 hue)] at h
          rw [hθ, lt_div_iff₀ ha0] at hlt
          linarith
      · rintro ⟨h1, h2⟩
        have hue : r ≤ u := by
          have : r ≤ θ := by
            rw [hθ, le_div_iff₀ ha0]; nlinarith
          linarith
        refine ⟨?_, hθ0.trans h1, h2⟩
        rw [Tm_big hr0 u hue, div_le_iff₀ (lt_of_lt_of_le hr0 hue)]
        rw [hθ, div_le_iff₀ ha0] at h1
        linarith
    rw [this, Real.volume_Icc]

include hr1 in
/-- Single-buyer revenue identity under the isorevenue law. -/
theorem single_buyer (X P : ℝ → ℝ)
    (hIC : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1, t * X s - P s ≤ t * X t - P t) :
    ∫ u in Set.Icc (0:ℝ) 1, P (Tm r u) = r * X 1 - (∫ t in (0:ℝ)..r, X t) + P 0 := by
  have hc0 : 0 < r := hr0
  have hXmono : MonotoneOn X (Set.Icc 0 1) := by
    intro s hs t ht hst
    have h1 := hIC t ht s hs
    have h2 := hIC s hs t ht
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hst with h | h
    · subst h; exact lt_irrefl _ hcon
    · nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hcon)]
  have hPmono : MonotoneOn P (Set.Icc 0 1) := by
    intro s hs t ht hst
    have h2 := hIC s hs t ht
    have := hXmono hs ht hst
    nlinarith [mul_nonneg hs.1 (sub_nonneg.2 this)]
  have hPT : AntitoneOn (fun u => P (Tm r u)) (Set.Icc 0 1) := by
    intro x hx y hy hxy
    exact hPmono (Tm_mem hr0 y) (Tm_mem hr0 x) (Tm_anti hr0 hx hy hxy)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hint1 : IntervalIntegrable (fun u => P (Tm r u)) volume 0 r :=
    AntitoneOn.intervalIntegrable (hPT.mono (by
      rw [Set.uIcc_of_le hc0.le]; exact Set.Icc_subset_Icc (le_refl _) hr1.le))
  have hint2 : IntervalIntegrable (fun u => P (Tm r u)) volume r 1 :=
    AntitoneOn.intervalIntegrable (hPT.mono (by
      rw [Set.uIcc_of_le hr1.le]; exact Set.Icc_subset_Icc hc0.le (le_refl _)))
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hA : ∫ u in (0:ℝ)..r, P (Tm r u) = r * P 1 := by
    rw [intervalIntegral.integral_congr (g := fun _ => P 1)]
    · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    · intro u hu
      rw [Set.uIcc_of_le hc0.le] at hu
      simp only [Tm_small hr0 u hu.2]
  set U : ℝ → ℝ := fun t => t * X t - P t with hU
  have hB : ∫ u in r..1, P (Tm r u) =
      (fun u => -(u * U (r / u))) 1 - (fun u => -(u * U (r / u))) r := by
    rw [intervalIntegral.integral_congr (g := fun u => P (r / u))]
    · refine integral_eq_of_squeeze_anti (f := fun x => P (r / x))
        (F := fun u => -(u * U (r / u))) hr1.le ?_ ?_
      · intro x hx y hy hxy
        have hx0 : 0 < x := lt_of_lt_of_le hc0 hx.1
        have hy0 : 0 < y := lt_of_lt_of_le hc0 hy.1
        apply hPmono
        · exact ⟨div_nonneg hc0.le hy0.le, by rw [div_le_one hy0]; exact hy.1⟩
        · exact ⟨div_nonneg hc0.le hx0.le, by rw [div_le_one hx0]; exact hx.1⟩
        · exact div_le_div_of_nonneg_left hc0.le hx0 hxy
      · intro s t hs hst ht
        have hs0 : 0 < s := lt_of_lt_of_le hc0 hs
        have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
        have m1 : r / s ∈ Set.Icc (0:ℝ) 1 :=
          ⟨div_nonneg hc0.le hs0.le, by rw [div_le_one hs0]; exact hs⟩
        have m2 : r / t ∈ Set.Icc (0:ℝ) 1 :=
          ⟨div_nonneg hc0.le ht0.le, by rw [div_le_one ht0]; exact hs.trans hst⟩
        have k1 := mul_le_mul_of_nonneg_left (hIC (r / s) m1 (r / t) m2) hs0.le
        have k2 := mul_le_mul_of_nonneg_left (hIC (r / t) m2 (r / s) m1) ht0.le
        have e1 : s * (r / s) = r := mul_div_cancel₀ r hs0.ne'
        have e2 : t * (r / t) = r := mul_div_cancel₀ r ht0.ne'
        have f1 : s * (r / s * X (r / t)) = r * X (r / t) := by rw [← mul_assoc, e1]
        have f2 : s * (r / s * X (r / s)) = r * X (r / s) := by rw [← mul_assoc, e1]
        have f3 : t * (r / t * X (r / s)) = r * X (r / s) := by rw [← mul_assoc, e2]
        have f4 : t * (r / t * X (r / t)) = r * X (r / t) := by rw [← mul_assoc, e2]
        simp only [hU]
        constructor
        · nlinarith
        · nlinarith
    · intro u hu
      rw [Set.uIcc_of_le hr1.le] at hu
      simp only [Tm_big hr0 u hu.1]
  have hC : ∫ t in (0:ℝ)..r, X t = U r - U 0 := by
    apply integral_eq_of_squeeze hc0.le
    · exact hXmono.mono (Set.Icc_subset_Icc (le_refl _) hr1.le)
    · intro s t hs hst ht
      have m1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs, by linarith⟩
      have m2 : t ∈ Set.Icc (0:ℝ) 1 := ⟨hs.trans hst, by linarith⟩
      have k1 := hIC t m2 s m1
      have k2 := hIC s m1 t m2
      simp only [hU]
      constructor <;> nlinarith
  rw [hA, hB]
  have hC' := hC
  simp only [hU] at hC' ⊢
  rw [div_self hc0.ne', div_one]
  rw [hC']
  ring

end T

end RAffS2

namespace RAffS2

variable {k : ℕ}

lemma insertNth_mem_cube (i : Fin (k + 1)) (t : ℝ) (w : Fin k → ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ cube k) : (Fin.insertNth i t w : Fin (k + 1) → ℝ) ∈ cube (k + 1) := by
  intro j _
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simpa using ht
  · simpa using hw l (Set.mem_univ _)

lemma cube_meas (n : ℕ) : MeasurableSet (cube n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- splitting `Gⁿ⁺¹` at coordinate `i` -/
lemma integral_split (G : Measure ℝ) [IsProbabilityMeasure G] (i : Fin (k + 1))
    (f : (Fin (k + 1) → ℝ) → ℝ) (hf : Integrable f (Measure.pi fun _ => G)) :
    ∫ v, f v ∂(Measure.pi fun _ => G) =
      ∫ w, ∫ t, f (Fin.insertNth i t w) ∂G ∂(Measure.pi fun _ : Fin k => G) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i with he
  have hmp : MeasurePreserving e (Measure.pi fun _ => G) (G.prod (Measure.pi fun _ : Fin k => G)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => G) i
  have hmps := hmp.symm e
  rw [← hmps.integral_comp e.symm.measurableEmbedding f]
  have hint : Integrable (fun z => f (e.symm z)) (G.prod (Measure.pi fun _ : Fin k => G)) :=
    (hmps.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  rw [integral_prod_symm _ hint]
  rfl

/-- the per-buyer identity from the envelope argument -/
lemma buyer_identity {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF r t) (M : Mechanism (k + 1)) (hM : M.IsDSIC) (i : Fin (k + 1))
    (w : Fin k → ℝ) (hw : w ∈ cube k) :
    ∫ t, M.p i (Fin.insertNth i t w) ∂G =
      r * M.x i (Fin.insertNth i 1 w) - (∫ t in (0 : ℝ)..r, M.x i (Fin.insertNth i t w)) +
        M.p i (Fin.insertNth i 0 w) := by
  have hmI : Measurable (fun t : ℝ => (Fin.insertNth i t w : Fin (k + 1) → ℝ)) := by
    have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm.measurable
    exact this.comp (measurable_id.prodMk measurable_const)
  have hPm : Measurable (fun t : ℝ => M.p i (Fin.insertNth i t w)) := (hM.meas_p i).comp hmI
  rw [G_eq hr0 hr1 G hG, integral_map (f := fun t : ℝ => M.p i (Fin.insertNth i t w))
    (meas_Tm hr0).aemeasurable hPm.aestronglyMeasurable]
  refine single_buyer hr0 hr1 (fun t => M.x i (Fin.insertNth i t w))
    (fun t => M.p i (Fin.insertNth i t w)) ?_
  intro t ht s hs
  have hv := insertNth_mem_cube i t w ht hw
  have := hM.ic _ hv i s hs
  simp only [Fin.update_insertNth, Fin.insertNth_apply_same] at this
  exact this

lemma integrable_of_cube {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cube n)ᶜ = 0) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ v ∈ cube n, |f v| ≤ C) : Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  have hae : ∀ᵐ v ∂μ, v ∈ cube n := by
    rw [ae_iff]; simpa [Set.compl_def] using hμ
  filter_upwards [hae] with v hv
  rw [Real.norm_eq_abs]; exact hC v hv

end RAffS2

namespace RAffS2

variable {k : ℕ}

lemma split_integrable (G : Measure ℝ) [IsProbabilityMeasure G] (i : Fin (k + 1))
    (f : (Fin (k + 1) → ℝ) → ℝ) (hf : Integrable f (Measure.pi fun _ => G)) :
    Integrable (fun w => ∫ t, f (Fin.insertNth i t w) ∂G) (Measure.pi fun _ : Fin k => G) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i with he
  have hmp : MeasurePreserving e (Measure.pi fun _ => G) (G.prod (Measure.pi fun _ : Fin k => G)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => G) i
  have hmps := hmp.symm e
  have hint : Integrable (fun z => f (e.symm z)) (G.prod (Measure.pi fun _ : Fin k => G)) :=
    (hmps.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  exact hint.integral_prod_right

lemma isWinner_unique {n : ℕ} {v : Fin n → ℝ} {i j : Fin n} (hi : isWinner v i) (hj : isWinner v j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.2 i h; have := hi.1 j; linarith
  · exact h
  · have := hi.2 j h; have := hj.1 i; linarith

lemma exists_winner {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) : ∃ i, isWinner v i := by
  obtain ⟨i1, _, hi1⟩ := Finset.exists_max_image Finset.univ v ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let S := Finset.univ.filter (fun i => ∀ j, v j ≤ v i)
  have hS : S.Nonempty := ⟨i1, by simp [S]; exact fun j => hi1 j (Finset.mem_univ _)⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have := S.min'_mem hS
    simp only [S, Finset.mem_filter] at this
    exact this.2
  · intro j hj
    by_contra hcon
    push_neg at hcon
    have hmem := S.min'_mem hS
    simp only [S, Finset.mem_filter] at hmem
    have hjS : j ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k; exact (hmem.2 k).trans hcon
    exact absurd (S.min'_le j hjS) (not_le.2 hj)

lemma meas_top {n : ℕ} : Measurable (fun v : Fin n → ℝ => top v) := by
  unfold top
  exact Measurable.iSup (fun i => measurable_pi_apply i)

/-- `G{1} = r` -/
lemma G_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF r t) : G.real {1} = r := by
  rw [G_eq hr0 hr1 G hG, Measure.real, Measure.map_apply (meas_Tm hr0) (measurableSet_singleton 1),
    Measure.restrict_apply ((meas_Tm hr0) (measurableSet_singleton 1))]
  have : Tm r ⁻¹' {1} ∩ Set.Icc 0 1 = Set.Icc 0 r := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Icc]
    constructor
    · rintro ⟨h, hu0, hu1⟩
      refine ⟨hu0, ?_⟩
      by_contra hlt
      push_neg at hlt
      rw [Tm_big hr0 u hlt.le, div_eq_one_iff_eq (by linarith)] at h
      linarith
    · rintro ⟨hu0, hur⟩
      exact ⟨Tm_small hr0 u hur, hu0, by linarith⟩
  rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), sub_zero]

lemma G_supp {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF r t) : G (Set.Icc 0 1)ᶜ = 0 := by
  rw [G_eq hr0 hr1 G hG, Measure.map_apply (meas_Tm hr0) measurableSet_Icc.compl,
    Measure.restrict_apply ((meas_Tm hr0) measurableSet_Icc.compl)]
  apply measure_mono_null _ measure_empty
  intro u ⟨h1, _⟩
  exact absurd (Tm_mem hr0 u) h1

lemma pi_cube_null (G : Measure ℝ) [IsProbabilityMeasure G] (hG : G (Set.Icc 0 1)ᶜ = 0) (n : ℕ) :
    (Measure.pi fun _ : Fin n => G) (cube n)ᶜ = 0 := by
  have hIcc : G (Set.Icc 0 1) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).mp hG
  unfold cube
  rw [prob_compl_eq_zero_iff (MeasurableSet.univ_pi fun _ => measurableSet_Icc), Measure.pi_pi]
  simp [hIcc]

/-- per-buyer bound: `E[p_i] ≤ E[1(v_i = 1) x_i]`, with equality when `x_i(t, ·) = 0` for `t ≤ r`
and `p_i(0, ·) = 0`. -/
lemma buyer_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF r t) (M : Mechanism (k + 1)) (hM : M.IsDSIC) (i : Fin (k + 1)) :
    ∫ v, M.p i v ∂(Measure.pi fun _ => G) ≤
      ∫ v, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v) v ∂(Measure.pi fun _ => G) ∧
    ((∀ v ∈ cube (k + 1), v i ≤ r → M.x i v = 0) → (∀ v ∈ cube (k + 1), v i = 0 → M.p i v = 0) →
      ∫ v, M.p i v ∂(Measure.pi fun _ => G) =
      ∫ v, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v) v ∂(Measure.pi fun _ => G)) := by
  have hsupp := G_supp hr0 hr1 G hG
  have hnull := pi_cube_null G hsupp (k + 1)
  have hnullk := pi_cube_null G hsupp k
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin (k + 1) => G) := inferInstance
  obtain ⟨B, hB⟩ := hM.p_bdd
  have hpi : Integrable (fun v => M.p i v) (Measure.pi fun _ => G) :=
    integrable_of_cube _ hnull _ (hM.meas_p i) B (fun v hv => hB v hv i)
  have hfm : Measurable (fun v : Fin (k + 1) → ℝ =>
      {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v) v) :=
    (hM.meas_x i).indicator (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
  have hfi : Integrable (fun v => {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v) v)
      (Measure.pi fun _ => G) := by
    refine integrable_of_cube _ hnull _ hfm 1 (fun v hv => ?_)
    have := hM.x_mem v hv i
    by_cases h : v ∈ {v : Fin (k + 1) → ℝ | v i = 1}
    · rw [Set.indicator_of_mem h, abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [Set.indicator_of_notMem h]; norm_num
  have haew : ∀ᵐ w ∂(Measure.pi fun _ : Fin k => G), w ∈ cube k := by
    rw [ae_iff]; simpa [Set.compl_def] using hnullk
  have hG1 := G_one hr0 hr1 G hG
  -- inner integral of the indicator
  have hinner : ∀ w : Fin k → ℝ, ∫ t, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v)
      (Fin.insertNth i t w) ∂G = r * M.x i (Fin.insertNth i 1 w) := by
    intro w
    have : (fun t => {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v)
        (Fin.insertNth i t w)) = ({1} : Set ℝ).indicator (fun t => M.x i (Fin.insertNth i t w)) := by
      funext t
      simp [Set.indicator_apply]
    rw [this, integral_indicator (measurableSet_singleton 1), integral_singleton, hG1, smul_eq_mul]
  rw [integral_split G i _ hpi, integral_split G i _ hfi]
  simp_rw [hinner]
  have hXnn : ∀ w ∈ cube k, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.x i (Fin.insertNth i t w) := fun w hw t ht =>
    (hM.x_mem _ (insertNth_mem_cube i t w ht hw) i).1
  have hP0 : ∀ w ∈ cube k, M.p i (Fin.insertNth i 0 w) ≤ 0 := by
    intro w hw
    have := hM.ir _ (insertNth_mem_cube i 0 w ⟨le_rfl, zero_le_one⟩ hw) i
    simp only [Fin.insertNth_apply_same, zero_mul, zero_sub] at this
    linarith
  have hint2 : Integrable (fun w => r * M.x i (Fin.insertNth i 1 w)) (Measure.pi fun _ : Fin k => G) := by
    have := split_integrable G i _ hfi
    simp_rw [hinner] at this
    exact this
  constructor
  · apply integral_mono_ae (split_integrable G i _ hpi) hint2
    filter_upwards [haew] with w hw
    rw [buyer_identity hr0 hr1 G hG M hM i w hw]
    have hX : 0 ≤ ∫ t in (0 : ℝ)..r, M.x i (Fin.insertNth i t w) :=
      intervalIntegral.integral_nonneg hr0.le fun t ht => hXnn w hw t ⟨ht.1, by linarith [ht.2]⟩
    linarith [hP0 w hw]
  · intro hx0 hp0
    apply integral_congr_ae
    filter_upwards [haew] with w hw
    rw [buyer_identity hr0 hr1 G hG M hM i w hw]
    have hX : ∫ t in (0 : ℝ)..r, M.x i (Fin.insertNth i t w) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
      · simp
      · rw [Set.uIcc_of_le hr0.le] at ht
        exact hx0 _ (insertNth_mem_cube i t w ⟨ht.1, by linarith [ht.2]⟩ hw) (by simpa using ht.2)
    have hP : M.p i (Fin.insertNth i 0 w) = 0 :=
      hp0 _ (insertNth_mem_cube i 0 w ⟨le_rfl, zero_le_one⟩ hw) (by simp)
    rw [hX, hP]; ring

end RAffS2

open RAffS2 in
theorem solution (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / n))
    (hroot : rEq n r = 0) (ρ G : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiStar n r t) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    ∀ m : Mechanism n, m.IsDSIC →
      regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) ≤
        regret m (Measure.pi fun _ : Fin n => (G : Measure ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hr0 := hr.1
  have hnR : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hr1 : r < 1 := by
    have h1 : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith [hr.2]
  intro M hM
  set μ : Measure (Fin (k + 1) → ℝ) := Measure.pi fun _ => (G : Measure ℝ) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hsupp := G_supp hr0 hr1 (G : Measure ℝ) hG
  have hnull : μ (cube (k + 1))ᶜ = 0 := pi_cube_null (G : Measure ℝ) hsupp (k + 1)
  have hae : ∀ᵐ v ∂μ, v ∈ cube (k + 1) := by
    rw [ae_iff]; simpa [Set.compl_def] using hnull
  set S : Mechanism (k + 1) := SPA (ρ : Measure ℝ) with hSdef
  have hS : S.IsDSIC := SPA_isDSIC (k + 1) ρ
  have hΦ1 : ((ρ : Measure ℝ) (Set.Iic 1)).toReal = 1 := by
    show cdfOf ρ 1 = 1
    rw [hρ 1]; exact (proposition_A_3_phi (k + 1) hn r hr hroot).2.2.2
  have hΦr : ∀ t ≤ r, ((ρ : Measure ℝ) (Set.Iic t)).toReal = 0 := by
    intro t ht
    show cdfOf ρ t = 0
    rw [hρ t]; simp [PhiStar, ht]
  -- the event that some value is `1`
  set E : Set (Fin (k + 1) → ℝ) := {v | ∃ i, v i = 1} with hE
  have hEm : MeasurableSet E := by
    have : E = ⋃ i, {v : Fin (k + 1) → ℝ | v i = 1} := by ext v; simp [hE]
    rw [this]
    exact MeasurableSet.iUnion fun i => measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hEval : μ.real E = 1 - (1 - r) ^ (k + 1) := by
    have hEc : Eᶜ = Set.univ.pi (fun _ : Fin (k + 1) => ({1} : Set ℝ)ᶜ) := by
      ext v; simp [hE]
    have hG1 := G_one hr0 hr1 (G : Measure ℝ) hG
    have h1 : μ.real Eᶜ = (1 - r) ^ (k + 1) := by
      rw [hEc, Measure.real, hμ, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ENNReal.toReal_pow, prob_compl_eq_one_sub (measurableSet_singleton 1),
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
      rw [Measure.real] at hG1
      rw [hG1]
    have h2 := measureReal_add_measureReal_compl (μ := μ) hEm
    rw [probReal_univ] at h2
    linarith
  -- integrability
  have htop : Integrable (fun v => top v) μ := by
    refine integrable_of_cube μ hnull _ meas_top 1 (fun v hv => ?_)
    haveI : Nonempty (Fin (k + 1)) := ⟨0⟩
    have h1 : top v ≤ 1 := ciSup_le fun i => (hv i (Set.mem_univ _)).2
    have h0 : 0 ≤ top v :=
      le_trans (hv 0 (Set.mem_univ _)).1 (le_ciSup (Finite.bddAbove_range v) 0)
    rw [abs_le]; constructor <;> linarith
  have hpint : ∀ (N : Mechanism (k + 1)), N.IsDSIC → ∀ i, Integrable (fun v => N.p i v) μ := by
    intro N hN i
    obtain ⟨B, hB⟩ := hN.p_bdd
    exact integrable_of_cube μ hnull _ (hN.meas_p i) B (fun v hv => hB v hv i)
  have hfint : ∀ (N : Mechanism (k + 1)), N.IsDSIC → ∀ i, Integrable
      (fun v => {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => N.x i v) v) μ := by
    intro N hN i
    have hfm : Measurable (fun v : Fin (k + 1) → ℝ =>
        {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => N.x i v) v) :=
      (hN.meas_x i).indicator (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
    refine integrable_of_cube μ hnull _ hfm 1 (fun v hv => ?_)
    have := hN.x_mem v hv i
    by_cases h : v ∈ {v : Fin (k + 1) → ℝ | v i = 1}
    · rw [Set.indicator_of_mem h, abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [Set.indicator_of_notMem h]; norm_num
  have hEint : Integrable (E.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hEm
  have hEint' : ∫ v, E.indicator (fun _ => (1 : ℝ)) v ∂μ = 1 - (1 - r) ^ (k + 1) := by
    rw [integral_indicator_const _ hEm, smul_eq_mul, mul_one, hEval]
  -- revenue of `M`
  have hrevM : ∫ v, ∑ i, M.p i v ∂μ ≤ 1 - (1 - r) ^ (k + 1) := by
    rw [integral_finset_sum _ (fun i _ => hpint M hM i)]
    calc ∑ i, ∫ v, M.p i v ∂μ
        ≤ ∑ i, ∫ v, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v) v ∂μ :=
          Finset.sum_le_sum fun i _ => (buyer_le hr0 hr1 (G : Measure ℝ) hG M hM i).1
      _ = ∫ v, ∑ i, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v) v ∂μ :=
          (integral_finset_sum _ (fun i _ => hfint M hM i)).symm
      _ ≤ ∫ v, E.indicator (fun _ => (1 : ℝ)) v ∂μ := by
          apply integral_mono_ae (integrable_finset_sum _ (fun i _ => hfint M hM i)) hEint
          filter_upwards [hae] with v hv
          by_cases hvE : v ∈ E
          · rw [Set.indicator_of_mem hvE]
            calc ∑ i, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => M.x i v) v
                ≤ ∑ i, M.x i v := Finset.sum_le_sum fun i _ => by
                  by_cases h : v ∈ {v : Fin (k + 1) → ℝ | v i = 1}
                  · rw [Set.indicator_of_mem h]
                  · rw [Set.indicator_of_notMem h]; exact (hM.x_mem v hv i).1
              _ ≤ 1 := hM.ac v hv
          · rw [Set.indicator_of_notMem hvE]
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro i _
            apply Set.indicator_of_notMem
            intro h; exact hvE ⟨i, h⟩
      _ = 1 - (1 - r) ^ (k + 1) := hEint'
  -- revenue of the SPA
  have hrevS : ∫ v, ∑ i, S.p i v ∂μ = 1 - (1 - r) ^ (k + 1) := by
    rw [integral_finset_sum _ (fun i _ => hpint S hS i)]
    have hx0 : ∀ i, ∀ v ∈ cube (k + 1), v i ≤ r → S.x i v = 0 := by
      intro i v _ hvr
      show (if isWinner v i then ((ρ : Measure ℝ) (Set.Iic (v i))).toReal else 0) = 0
      split_ifs
      · exact hΦr _ hvr
      · rfl
    have hp0 : ∀ i, ∀ v ∈ cube (k + 1), v i = 0 → S.p i v = 0 := by
      intro i v _ hv0
      show (if isWinner v i then
        ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂(ρ : Measure ℝ) else 0) = 0
      split_ifs
      · rw [hv0, integral_indicator measurableSet_Iic]
        apply setIntegral_measure_zero
        have := hΦr 0 hr0.le
        rcases (ENNReal.toReal_eq_zero_iff _).mp this with h | h
        · exact h
        · exact absurd h (measure_ne_top _ _)
      · rfl
    calc ∑ i, ∫ v, S.p i v ∂μ
        = ∑ i, ∫ v, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => S.x i v) v ∂μ :=
          Finset.sum_congr rfl fun i _ =>
            (buyer_le hr0 hr1 (G : Measure ℝ) hG S hS i).2 (hx0 i) (hp0 i)
      _ = ∫ v, ∑ i, {v : Fin (k + 1) → ℝ | v i = 1}.indicator (fun v => S.x i v) v ∂μ :=
          (integral_finset_sum _ (fun i _ => hfint S hS i)).symm
      _ = ∫ v, E.indicator (fun _ => (1 : ℝ)) v ∂μ := by
          apply integral_congr_ae
          filter_upwards [hae] with v hv
          by_cases hvE : v ∈ E
          · rw [Set.indicator_of_mem hvE]
            obtain ⟨j, hj⟩ := hvE
            obtain ⟨w, hw⟩ := exists_winner (Nat.succ_pos k) v
            have hvw : v w = 1 := le_antisymm (hv w (Set.mem_univ _)).2 (hj ▸ hw.1 j)
            rw [Finset.sum_eq_single w]
            · have hmem : v ∈ {v : Fin (k + 1) → ℝ | v w = 1} := hvw
              rw [Set.indicator_of_mem hmem]
              show (if isWinner v w then ((ρ : Measure ℝ) (Set.Iic (v w))).toReal else 0) = 1
              rw [if_pos hw, hvw, hΦ1]
            · intro i _ hiw
              have : S.x i v = 0 := by
                show (if isWinner v i then ((ρ : Measure ℝ) (Set.Iic (v i))).toReal else 0) = 0
                rw [if_neg (fun h => hiw (isWinner_unique h hw))]
              by_cases h : v ∈ {v : Fin (k + 1) → ℝ | v i = 1}
              · rw [Set.indicator_of_mem h, this]
              · rw [Set.indicator_of_notMem h]
            · intro h; exact absurd (Finset.mem_univ w) h
          · rw [Set.indicator_of_notMem hvE]
            apply Finset.sum_eq_zero
            intro i _
            apply Set.indicator_of_notMem
            intro h; exact hvE ⟨i, h⟩
      _ = 1 - (1 - r) ^ (k + 1) := hEint'
  -- conclude
  unfold regret
  rw [integral_sub htop (integrable_finset_sum _ (fun i _ => hpint S hS i)),
    integral_sub htop (integrable_finset_sum _ (fun i _ => hpint M hM i)), hrevS]
  linarith
