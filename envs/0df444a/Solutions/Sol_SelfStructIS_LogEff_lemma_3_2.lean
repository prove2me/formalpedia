-- Prove2me | solution 1 for SelfStructIS.LogEff.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:44:11.981604+00:00
-- url     : https://prove2.me/submissions/c8631a72-34bd-41ef-8df1-49de50db4dce

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SSIS32

open SelfStructIS.LogEff

set_option linter.unusedSectionVars false

variable {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (i : Fin d)

lemma meas_lt (s : ℝ) : MeasurableSet {y : Fin d → ℝ | s < y i} :=
  measurableSet_lt measurable_const (measurable_pi_apply i)

lemma surv_nonneg (s : ℝ) : 0 ≤ survival μ i s := ENNReal.toReal_nonneg

lemma surv_le_one (s : ℝ) : survival μ i s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma surv_anti {s s' : ℝ} (h : s ≤ s') : survival μ i s' ≤ survival μ i s :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun y (hy : s' < y i) => (lt_of_le_of_lt h hy : s < y i))

lemma hazard_nonneg (s : ℝ) : 0 ≤ hazard μ i s := by
  unfold hazard
  have := Real.log_nonpos (surv_nonneg μ i s) (surv_le_one μ i s)
  linarith

lemma surv_pos (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) (s : ℝ) : 0 < survival μ i s := by
  rcases (surv_nonneg μ i s).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    have h1 := hX (max X s) (le_max_left _ _)
    have h2 : survival μ i (max X s) = 0 :=
      le_antisymm (h ▸ surv_anti μ i (le_max_right X s)) (surv_nonneg μ i _)
    unfold hazard at h1
    rw [h2, Real.log_zero] at h1
    simp at h1

lemma hazard_mono (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) : Monotone (hazard μ i) := by
  intro s s' h
  unfold hazard
  have := Real.log_le_log (surv_pos μ i hev s') (surv_anti μ i h)
  linarith

lemma surv_eq_exp (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) (s : ℝ) :
    survival μ i s = Real.exp (-hazard μ i s) := by
  unfold hazard; rw [neg_neg, Real.exp_log (surv_pos μ i hev s)]

lemma hazard_tendsto {a : ℝ} (ha : 0 < a) (hrv : HeavyTailNV.Tail.IsRegularlyVarying (hazard μ i) a) :
    Tendsto (hazard μ i) atTop atTop := by
  have hmono := hazard_mono μ i hrv.1
  have h2 : (1 : ℝ) < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
  set c : ℝ := (1 + (2 : ℝ) ^ a) / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hc2 : c < (2 : ℝ) ^ a := by rw [hc]; linarith
  have hev2 : ∀ᶠ x in atTop, c < hazard μ i (2 * x) / hazard μ i x :=
    (hrv.2 2 (by norm_num)).eventually (lt_mem_nhds hc2)
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hev2.and (hrv.1.and (eventually_ge_atTop 1)))
  have hX1 : 1 ≤ X := (hX X le_rfl).2.2
  have hpow : ∀ n : ℕ, c ^ n * hazard μ i X ≤ hazard μ i (2 ^ n * X) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hge : X ≤ 2 ^ n * X := le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
      obtain ⟨h1, h2', -⟩ := hX (2 ^ n * X) hge
      rw [lt_div_iff₀ h2'] at h1
      calc c ^ (n + 1) * hazard μ i X = c * (c ^ n * hazard μ i X) := by ring
        _ ≤ c * hazard μ i (2 ^ n * X) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ hazard μ i (2 * (2 ^ n * X)) := h1.le
        _ = hazard μ i (2 ^ (n + 1) * X) := by ring_nf
  have hHX : 0 < hazard μ i X := (hX X le_rfl).2.1
  rw [tendsto_atTop_atTop]
  intro b
  have htend : Tendsto (fun n : ℕ => c ^ n * hazard μ i X) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hc1).atTop_mul_const hHX
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 htend b).exists
  exact ⟨2 ^ n * X, fun y hy => le_trans hn (le_trans (hpow n) (hmono hy))⟩


lemma marg (hcont : Continuous (hazard μ i)) {a : ℝ} (ha : 0 < a)
    (hrv : HeavyTailNV.Tail.IsRegularlyVarying (hazard μ i) a) (s : ℝ) (hs : 0 < s) :
    μ {x | s < hazard μ i (x i)} = ENNReal.ofReal (Real.exp (-s)) := by
  have hev := hrv.1
  have hmono := hazard_mono μ i hev
  have htend := hazard_tendsto μ i ha hrv
  have hm : Monotone (fun n : ℕ => {y : Fin d → ℝ | -(n : ℝ) < y i}) := by
    intro m n hmn y (hy : -(m : ℝ) < y i)
    show -(n : ℝ) < y i
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hU : Tendsto (fun n : ℕ => μ {y : Fin d → ℝ | -(n : ℝ) < y i}) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) hm
    have hun : (⋃ n : ℕ, {y : Fin d → ℝ | -(n : ℝ) < y i}) = Set.univ := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (-y i)
      exact ⟨n, by linarith⟩
    rw [hun, measure_univ] at h
    exact h
  have hlt : ENNReal.ofReal (Real.exp (-s)) < 1 := by
    rw [ENNReal.ofReal_lt_one]; exact Real.exp_lt_one_iff.2 (by linarith)
  obtain ⟨n, hn⟩ := (hU.eventually (lt_mem_nhds hlt)).exists
  have hx1 : hazard μ i (-(n : ℝ)) < s := by
    have h1 : Real.exp (-s) < survival μ i (-(n : ℝ)) :=
      (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le (measure_ne_top _ _)).1 hn
    have h2 : -s < Real.log (survival μ i (-(n : ℝ))) :=
      (Real.lt_log_iff_exp_lt (surv_pos μ i hev _)).2 h1
    unfold hazard; linarith
  set S := {x : ℝ | hazard μ i x ≤ s} with hS
  have hne : S.Nonempty := ⟨-(n : ℝ), hx1.le⟩
  obtain ⟨X, hX⟩ := (tendsto_atTop.1 htend (s + 1)).exists_forall_of_atTop
  have hbdd : BddAbove S := by
    refine ⟨X, fun x (hx : hazard μ i x ≤ s) => ?_⟩
    by_contra h
    push Not at h
    have := hX x h.le
    linarith
  have hclosed : IsClosed S := isClosed_le hcont continuous_const
  have hbS : sSup S ∈ S := hclosed.csSup_mem hne hbdd
  set b := sSup S with hb
  have hbS' : hazard μ i b ≤ s := hbS
  have hbeq : hazard μ i b = s := by
    apply le_antisymm hbS'
    have hseq : Tendsto (fun k : ℕ => b + 1 / ((k : ℝ) + 1)) atTop (𝓝 b) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add b
      simpa using this
    have hlim := (hcont.tendsto b).comp hseq
    refine ge_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    show s ≤ hazard μ i (b + 1 / ((k : ℝ) + 1))
    by_contra h
    push Not at h
    have : b + 1 / ((k : ℝ) + 1) ≤ b := le_csSup hbdd h.le
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hset : {x : Fin d → ℝ | s < hazard μ i (x i)} = {y : Fin d → ℝ | b < y i} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      have := hmono h'
      linarith
    · intro h
      by_contra h'
      push Not at h'
      have : x i ≤ b := le_csSup hbdd h'
      linarith
  rw [hset]
  have : μ {y : Fin d → ℝ | b < y i} = ENNReal.ofReal (survival μ i b) := by
    unfold survival; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [this, surv_eq_exp μ i hev, hbeq]

end SSIS32

namespace SSIS32

open SelfStructIS.LogEff

lemma glue {d : ℕ} (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (w : ℕ → Fin d → ℝ) (a : Fin d → ℝ)
    (hw : Tendsto w atTop (𝓝 a)) :
    ∃ ys : ℕ → Fin d → ℝ, (∀ k, ys (ψ k) = w k) ∧ (∀ n, ys n = a ∨ ∃ k, ys n = w k) ∧
      Tendsto ys atTop (𝓝 a) := by
  classical
  refine ⟨fun n => if h : ∃ k, ψ k = n then w (Classical.choose h) else a, ?_, ?_, ?_⟩
  · intro k
    have h : ∃ k', ψ k' = ψ k := ⟨k, rfl⟩
    simp only [dif_pos h]
    rw [hψ.injective (Classical.choose_spec h)]
  · intro n
    by_cases h : ∃ k, ψ k = n
    · right; exact ⟨Classical.choose h, by simp only [dif_pos h]⟩
    · left; simp only [dif_neg h]
  · rw [Metric.tendsto_atTop] at hw ⊢
    intro ε hε
    obtain ⟨K, hK⟩ := hw ε hε
    refine ⟨ψ K, fun n hn => ?_⟩
    by_cases h : ∃ k, ψ k = n
    · simp only [dif_pos h]
      have hk := Classical.choose_spec h
      apply hK
      by_contra hlt
      push Not at hlt
      have := hψ hlt
      omega
    · simp only [dif_neg h, dist_self]; exact hε

lemma U1 {d : ℕ} (p φ I : (Fin d → ℝ) → ℝ) (h13 : Conv13 p φ I) (y : Fin d → ℝ)
    (hy0 : ∀ j, 0 ≤ y j) (hy : y ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ s : Fin d → ℝ, (∀ j, 0 ≤ s j ∧ s j ≤ 1) →
      φ ((n : ℝ) • y + s) < n * (I y + ε) ∧ 0 < p ((n : ℝ) • y + s) ∧
        -(ε * n) < Real.log (p ((n : ℝ) • y + s)) := by
  by_contra h
  rw [not_eventually] at h
  obtain ⟨ψ, hψ, hP⟩ := extraction_of_frequently_atTop (h.and_eventually (eventually_ge_atTop 1))
  have hP' : ∀ k, ∃ s : Fin d → ℝ, (∀ j, 0 ≤ s j ∧ s j ≤ 1) ∧
      ¬ (φ ((ψ k : ℝ) • y + s) < ψ k * (I y + ε) ∧ 0 < p ((ψ k : ℝ) • y + s) ∧
        -(ε * ψ k) < Real.log (p ((ψ k : ℝ) • y + s))) := by
    intro k
    have := (hP k).1
    push Not at this
    obtain ⟨s, hs, hbad⟩ := this
    exact ⟨s, hs, fun ⟨h1, h2, h3⟩ => (not_lt.2 (hbad h1 h2)) h3⟩
  choose s hs hbad using hP'
  have hψ1 : ∀ k, (1 : ℝ) ≤ ψ k := fun k => by exact_mod_cast (hP k).2
  set w : ℕ → Fin d → ℝ := fun k => y + ((ψ k : ℝ)⁻¹) • s k with hwdef
  have hw : Tendsto w atTop (𝓝 y) := by
    have hinv : Tendsto (fun k => ((ψ k : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop)
    have h0 : Tendsto (fun k => ((ψ k : ℝ)⁻¹) • s k) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) hinv
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by linarith [hψ1 k]))]
      have : ‖s k‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
        rw [Real.norm_of_nonneg (hs k j).1]; exact (hs k j).2
      calc ((ψ k : ℝ))⁻¹ * ‖s k‖ ≤ ((ψ k : ℝ))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 (by linarith [hψ1 k]))
        _ = _ := mul_one _
    simpa using h0.const_add y
  obtain ⟨ys, hys1, hys2, hys3⟩ := glue ψ hψ w y hw
  have hys0 : ∀ n j, 0 ≤ ys n j := by
    intro n j
    rcases hys2 n with h | ⟨k, h⟩
    · rw [h]; exact hy0 j
    · rw [h]
      simp only [hwdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hy0 j) (mul_nonneg (inv_nonneg.2 (by linarith [hψ1 k])) (hs k j).1)
  obtain ⟨h1, h2, h3⟩ := h13 ys y hys0 hys3 hy
  have hkey : ∀ k, (ψ k : ℝ) • ys (ψ k) = (ψ k : ℝ) • y + s k := by
    intro k
    rw [hys1 k]
    simp only [hwdef, smul_add]
    rw [smul_inv_smul₀ (by linarith [hψ1 k] : (ψ k : ℝ) ≠ 0)]
  have e1 := (h1.comp hψ.tendsto_atTop).eventually (gt_mem_nhds (show I y < I y + ε by linarith))
  have e2 := hψ.tendsto_atTop.eventually h2
  have h3' := h3 1 one_pos
  have e3 := (h3'.comp hψ.tendsto_atTop).eventually (lt_mem_nhds (show -ε < 0 by linarith))
  obtain ⟨k, hk1, hk2, hk3⟩ := (e1.and (e2.and e3)).exists
  simp only [Function.comp, hkey, Real.rpow_one] at hk1 hk2 hk3
  apply hbad k
  have hpos : (0 : ℝ) < ψ k := by linarith [hψ1 k]
  refine ⟨?_, hk2, ?_⟩
  · rwa [div_lt_iff₀ hpos, mul_comm] at hk1
  · rw [lt_div_iff₀ hpos] at hk3; linarith

end SSIS32

namespace SSIS32

open SelfStructIS.LogEff

lemma lower {d : ℕ} (ν : Measure (Fin d → ℝ)) (p φ I : (Fin d → ℝ) → ℝ)
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (p y * Real.exp (-φ y))))
    (h13 : Conv13 p φ I) (i : Fin d)
    (hmarg : ∀ s : ℝ, 0 < s → ν {z | s < z i} = ENNReal.ofReal (Real.exp (-s)))
    (y : Fin d → ℝ) (hy0 : ∀ j, 0 ≤ y j) (hyi : 0 < y i) : y i ≤ I y := by
  by_contra hlt
  push Not at hlt
  have hy : y ≠ 0 := fun h => by rw [h] at hyi; simp at hyi
  set ε := (y i - I y) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (2 * ε) + 1 / y i)
  obtain ⟨n, hn, hnM⟩ := ((U1 p φ I h13 y hy0 hy ε hε).and (eventually_ge_atTop M)).exists
  have hnM' : (M : ℝ) ≤ n := by exact_mod_cast hnM
  have h2ε : 0 < 2 * ε := by linarith
  have hn1 : 1 / (2 * ε) < n := by
    have : 0 < 1 / y i := by positivity
    linarith
  have hn2 : 1 / y i < n := by
    have : 0 < 1 / (2 * ε) := by positivity
    linarith
  have hnpos : (0 : ℝ) < n := lt_trans (by positivity) hn2
  have hnyi : 1 < n * y i := by rwa [div_lt_iff₀ hyi] at hn2
  set B := Set.Icc ((n : ℝ) • y) ((n : ℝ) • y + 1) with hB
  set c := Real.exp (-(ε * n)) * Real.exp (-(n * (I y + ε))) with hc
  have hfB : ∀ z ∈ B, ENNReal.ofReal c ≤ ENNReal.ofReal (p z * Real.exp (-φ z)) := by
    intro z hz
    have hs : ∀ j, 0 ≤ (z - (n : ℝ) • y) j ∧ (z - (n : ℝ) • y) j ≤ 1 := by
      intro j
      have h1 := hz.1 j
      have h2 := hz.2 j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply] at h1 h2 ⊢
      constructor <;> linarith
    obtain ⟨h1, h2, h3⟩ := hn (z - (n : ℝ) • y) hs
    rw [add_sub_cancel] at h1 h2 h3
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul _ _ (Real.exp_pos _).le h2.le
    · rw [← Real.exp_log h2]; exact Real.exp_le_exp.2 h3.le
    · exact Real.exp_le_exp.2 (by linarith)
  have hvolB : volume B = 1 := by
    rw [hB, Real.volume_Icc_pi]
    simp
  have hνB : ENNReal.ofReal c ≤ ν B := by
    rw [hν, withDensity_apply _ measurableSet_Icc]
    calc ENNReal.ofReal c = ∫⁻ _ in B, ENNReal.ofReal c := by
          rw [setLIntegral_const, hvolB, mul_one]
      _ ≤ _ := setLIntegral_mono' measurableSet_Icc hfB
  have hsub : B ⊆ {z | (n * y i - 1) < z i} := by
    intro z hz
    have := hz.1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    show n * y i - 1 < z i
    linarith
  have hle := le_trans hνB (measure_mono hsub)
  rw [hmarg _ (by linarith), ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, hc,
    ← Real.exp_add, Real.exp_le_exp] at hle
  have : 2 * ε * n ≤ 1 := by
    have : y i - I y = 4 * ε := by rw [hεdef]; ring
    nlinarith
  rw [div_lt_iff₀ h2ε] at hn1
  linarith

end SSIS32

namespace SSIS32

open SelfStructIS.LogEff

lemma U2 {d : ℕ} (p φ I : (Fin d → ℝ) → ℝ) (h13 : Conv13 p φ I) (K : Set (Fin d → ℝ))
    (hK : IsCompact K) (hK0 : ∀ w ∈ K, (∀ j, 0 ≤ w j) ∧ w ≠ 0) (m : ℝ)
    (hm : ∀ w ∈ K, m < I w) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ w ∈ K, n * m < φ ((n : ℝ) • w) ∧ p ((n : ℝ) • w) ≤ Real.exp (ε * n) := by
  by_contra h
  rw [not_eventually] at h
  obtain ⟨ψ, hψ, hP⟩ := extraction_of_frequently_atTop (h.and_eventually (eventually_ge_atTop 1))
  have hP' : ∀ k, ∃ w ∈ K, ¬ (ψ k * m < φ ((ψ k : ℝ) • w) ∧
      p ((ψ k : ℝ) • w) ≤ Real.exp (ε * ψ k)) := by
    intro k
    have := (hP k).1
    push Not at this
    obtain ⟨w, hw, hbad⟩ := this
    exact ⟨w, hw, fun ⟨h1, h2⟩ => (not_le.2 (hbad h1)) h2⟩
  choose w hwK hbad using hP'
  have hψ1 : ∀ k, (1 : ℝ) ≤ ψ k := fun k => by exact_mod_cast (hP k).2
  obtain ⟨a, haK, χ, hχ, hconv⟩ := hK.tendsto_subseq hwK
  obtain ⟨ys, hys1, hys2, hys3⟩ := glue (ψ ∘ χ) (hψ.comp hχ) (w ∘ χ) a hconv
  have hys0 : ∀ n j, 0 ≤ ys n j := by
    intro n j
    rcases hys2 n with h | ⟨k, h⟩
    · rw [h]; exact (hK0 a haK).1 j
    · rw [h]; exact (hK0 _ (hwK _)).1 j
  obtain ⟨h1, h2, h3⟩ := h13 ys a hys0 hys3 (hK0 a haK).2
  have hst := (hψ.comp hχ).tendsto_atTop
  have e1 := (h1.comp hst).eventually (lt_mem_nhds (hm a haK))
  have e2 := hst.eventually h2
  have e3 := ((h3 1 one_pos).comp hst).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk1, hk2, hk3⟩ := (e1.and (e2.and e3)).exists
  have hys1' : ys (ψ (χ k)) = w (χ k) := hys1 k
  simp only [Function.comp, hys1', Real.rpow_one] at hk1 hk2 hk3
  apply hbad (χ k)
  have hpos : (0 : ℝ) < ψ (χ k) := by linarith [hψ1 (χ k)]
  refine ⟨?_, ?_⟩
  · rwa [lt_div_iff₀ hpos, mul_comm] at hk1
  · rw [div_lt_iff₀ hpos] at hk3
    rw [← Real.exp_log hk2]
    exact Real.exp_le_exp.2 hk3.le

lemma upper {d : ℕ} (ν : Measure (Fin d → ℝ)) (p φ I : (Fin d → ℝ) → ℝ)
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (p y * Real.exp (-φ y))))
    (h13 : Conv13 p φ I)
    (hmarg : ∀ (j : Fin d) (s : ℝ), 0 < s → ν {z | s < z j} = ENNReal.ofReal (Real.exp (-s)))
    (hneg : ∀ j : Fin d, ν {z | z j < 0} = 0) (i : Fin d)
    (c : ℝ) (hc : 0 ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Fin d → ℝ, (∀ j, 0 ≤ y j) ∧ c < y i ∧ I y < c + ε := by
  by_contra h
  push Not at h
  set c' := c + ε / 4 with hc'
  set R := c + ε + 1 with hR
  set m := c + ε / 2 with hmdef
  have hc'pos : 0 < c' := by rw [hc']; linarith
  have hRpos : 0 < R := by rw [hR]; linarith
  set K := Set.Icc (0 : Fin d → ℝ) (fun _ => R) ∩ {w | c' ≤ w i} with hKdef
  have hKc : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_apply i))
  have hK0 : ∀ w ∈ K, (∀ j, 0 ≤ w j) ∧ w ≠ 0 := by
    intro w hw
    refine ⟨fun j => hw.1.1 j, fun h0 => ?_⟩
    have := hw.2
    rw [h0] at this
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at this
    linarith
  have hm : ∀ w ∈ K, m < I w := by
    intro w hw
    have := h w (fun j => hw.1.1 j) (by have := hw.2; simp only [Set.mem_setOf_eq] at this; linarith)
    rw [hmdef]; linarith
  have hε8 : 0 < ε / 8 := by linarith
  have hU := U2 p φ I h13 K hKc hK0 m hm (ε / 8) hε8
  -- the error term tends to zero
  have hT1 : Tendsto (fun n : ℕ => ((n : ℝ) * R) ^ d * Real.exp (-(ε / 8 * n))) atTop (𝓝 0) := by
    have hg := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d
    have hlin : Tendsto (fun n : ℕ => ε / 8 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε8
    have := (hg.comp hlin).const_mul ((R / (ε / 8)) ^ d)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    simp only [Function.comp]
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  have hT2 : Tendsto (fun n : ℕ => (d : ℝ) * Real.exp (-((R - c') * n))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun n : ℕ => (R - c') * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by rw [hR, hc']; linarith)
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).const_mul (d : ℝ)
    rw [mul_zero] at this
    exact this
  have hT := hT1.add hT2
  rw [add_zero] at hT
  obtain ⟨n, hn, hn1, hnT⟩ :=
    (hU.and ((eventually_ge_atTop 1).and (hT.eventually (gt_mem_nhds one_pos)))).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set Bn := Set.Icc (0 : Fin d → ℝ) (fun _ => n * R) ∩ {z | n * c' ≤ z i} with hBn
  have hBnm : MeasurableSet Bn :=
    measurableSet_Icc.inter (measurableSet_le measurable_const (measurable_pi_apply i))
  set C := Real.exp (ε / 8 * n) * Real.exp (-(n * m)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hfB : ∀ z ∈ Bn, ENNReal.ofReal (p z * Real.exp (-φ z)) ≤ ENNReal.ofReal C := by
    intro z hz
    have hwK : (n : ℝ)⁻¹ • z ∈ K := by
      refine ⟨⟨fun j => ?_, fun j => ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact mul_nonneg (inv_nonneg.2 hnpos.le) (hz.1.1 j)
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [inv_mul_le_iff₀ hnpos]; exact hz.1.2 j
      · simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
        rw [le_inv_mul_iff₀ hnpos]; exact hz.2
    obtain ⟨h1, h2⟩ := hn _ hwK
    rw [smul_inv_smul₀ hnpos.ne'] at h1 h2
    apply ENNReal.ofReal_le_ofReal
    by_cases hp : p z ≤ 0
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hp (Real.exp_pos _).le) hC0
    · push Not at hp
      exact mul_le_mul h2 (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
  have hvol : volume Bn ≤ ENNReal.ofReal ((n : ℝ) * R) ^ d := by
    calc volume Bn ≤ volume (Set.Icc (0 : Fin d → ℝ) (fun _ => n * R)) :=
          measure_mono Set.inter_subset_left
      _ = _ := by rw [Real.volume_Icc_pi]; simp
  have hνB : ν Bn ≤ ENNReal.ofReal (C * ((n : ℝ) * R) ^ d) := by
    rw [hν, withDensity_apply _ hBnm]
    calc ∫⁻ z in Bn, ENNReal.ofReal (p z * Real.exp (-φ z))
        ≤ ∫⁻ _ in Bn, ENNReal.ofReal C := setLIntegral_mono' hBnm hfB
      _ = ENNReal.ofReal C * volume Bn := by rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((n : ℝ) * R) ^ d := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hC0]
  have hcover : {z : Fin d → ℝ | n * c' < z i} ⊆
      Bn ∪ ((⋃ j, {z : Fin d → ℝ | n * R < z j}) ∪ ⋃ j, {z : Fin d → ℝ | z j < 0}) := by
    intro z hz
    by_cases hA : ∃ j, z j < 0
    · obtain ⟨j, hj⟩ := hA
      exact Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, hj⟩))
    by_cases hB : ∃ j, n * R < z j
    · obtain ⟨j, hj⟩ := hB
      exact Or.inr (Or.inl (Set.mem_iUnion.2 ⟨j, hj⟩))
    push Not at hA hB
    exact Or.inl ⟨⟨fun j => hA j, fun j => hB j⟩, le_of_lt (show (n : ℝ) * c' < z i from hz)⟩
  have hmain : ENNReal.ofReal (Real.exp (-(n * c'))) ≤
      ENNReal.ofReal (C * ((n : ℝ) * R) ^ d) + (d : ENNReal) * ENNReal.ofReal (Real.exp (-(n * R))) := by
    rw [← hmarg i _ (by positivity)]
    calc ν {z | n * c' < z i}
        ≤ ν (Bn ∪ ((⋃ j, {z : Fin d → ℝ | n * R < z j}) ∪ ⋃ j, {z : Fin d → ℝ | z j < 0})) :=
          measure_mono hcover
      _ ≤ ν Bn + (ν (⋃ j, {z : Fin d → ℝ | n * R < z j}) + ν (⋃ j, {z : Fin d → ℝ | z j < 0})) :=
          le_trans (measure_union_le _ _) (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ ENNReal.ofReal (C * ((n : ℝ) * R) ^ d) +
            ((d : ENNReal) * ENNReal.ofReal (Real.exp (-(n * R))) + 0) := by
          gcongr
          · calc ν (⋃ j, {z : Fin d → ℝ | n * R < z j})
                ≤ ∑ j, ν {z : Fin d → ℝ | n * R < z j} := measure_iUnion_fintype_le _ _
              _ = ∑ _j : Fin d, ENNReal.ofReal (Real.exp (-(n * R))) := by
                  refine Finset.sum_congr rfl fun j _ => hmarg j _ (by positivity)
              _ = _ := by simp
          · exact le_of_eq (measure_iUnion_null hneg)
      _ = _ := by rw [add_zero]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  -- divide by exp(-n c')
  have hE : Real.exp (-(n * c')) * (((n : ℝ) * R) ^ d * Real.exp (-(ε / 8 * n)) +
      (d : ℝ) * Real.exp (-((R - c') * n))) = C * ((n : ℝ) * R) ^ d + d * Real.exp (-(n * R)) := by
    rw [hC, mul_add]
    congr 1
    · rw [show Real.exp (ε / 8 * n) * Real.exp (-(n * m)) =
          Real.exp (-(n * c')) * Real.exp (-(ε / 8 * n)) by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hmdef, hc']; ring]
      ring
    · rw [mul_left_comm, ← Real.exp_add]
      congr 2; ring
  rw [← hE] at hmain
  have hpos := Real.exp_pos (-(n * c'))
  have : Real.exp (-(n * c')) * 1 ≤ Real.exp (-(n * c')) * (((n : ℝ) * R) ^ d *
      Real.exp (-(ε / 8 * n)) + (d : ℝ) * Real.exp (-((R - c') * n))) := by linarith
  have := le_of_mul_le_mul_left this hpos
  linarith

end SSIS32

namespace SSIS32

open SelfStructIS.LogEff

lemma homog {d : ℕ} (p φ I : (Fin d → ℝ) → ℝ) (h13 : Conv13 p φ I) (s : ℝ) (hs : 0 < s)
    (y : Fin d → ℝ) (hy0 : ∀ j, 0 ≤ y j) (hy : y ≠ 0) : I (s • y) = s * I y := by
  set N : ℕ → ℕ := fun m => ⌈(m : ℝ) / s⌉₊ with hN
  have hNge : ∀ m : ℕ, (m : ℝ) / s ≤ N m := fun m => Nat.le_ceil _
  have hNlt : ∀ m : ℕ, (N m : ℝ) < m / s + 1 := fun m => Nat.ceil_lt_add_one (by positivity)
  set r : ℕ → ℝ := fun m => (N m : ℝ) * s / m with hr
  have hr_t : Tendsto r atTop (𝓝 1) := by
    have hup : Tendsto (fun m : ℕ => 1 + s / (m : ℝ)) atTop (𝓝 1) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat s).const_add 1
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with m hm
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      simp only [hr]
      rw [le_div_iff₀ hm', one_mul]
      have := hNge m
      rw [div_le_iff₀ hs] at this
      linarith
    · filter_upwards [eventually_ge_atTop 1] with m hm
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      simp only [hr]
      rw [div_le_iff₀ hm', add_mul, one_mul, div_mul_cancel₀ _ hm'.ne']
      have := hNlt m
      have h2 : (N m : ℝ) * s < (m / s + 1) * s := mul_lt_mul_of_pos_right this hs
      rw [add_mul, div_mul_cancel₀ _ hs.ne', one_mul] at h2
      linarith
  set z : ℕ → Fin d → ℝ := fun m => r m • y with hz
  have hz_t : Tendsto z atTop (𝓝 y) := by
    have := hr_t.smul_const y
    simpa using this
  have hz0 : ∀ m j, 0 ≤ z m j := by
    intro m j
    simp only [hz, hr, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hy0 j)
  have h1 := (h13 z y hz0 hz_t hy).1
  have hsy0 : ∀ j, 0 ≤ (s • y) j := fun j => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs.le (hy0 j)
  have hsy : s • y ≠ 0 := smul_ne_zero hs.ne' hy
  have h2 := (h13 (fun _ => s • y) (s • y) (fun _ => hsy0) tendsto_const_nhds hsy).1
  have hNt : Tendsto N atTop atTop := by
    have hR : Tendsto (fun m : ℕ => (N m : ℝ)) atTop atTop :=
      tendsto_atTop_mono hNge (tendsto_natCast_atTop_atTop.atTop_div_const hs)
    exact tendsto_natCast_atTop_iff.1 hR
  have h2' := h2.comp hNt
  have hratio : Tendsto (fun m : ℕ => (N m : ℝ) / m) atTop (𝓝 (1 / s)) := by
    have := hr_t.div_const s
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [hr]
    field_simp
  have hprod := h2'.mul hratio
  have hlim : Tendsto (fun m : ℕ => φ ((m : ℝ) • z m) / m) atTop (𝓝 (I (s • y) * (1 / s))) := by
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hNpos : (0 : ℝ) < N m := lt_of_lt_of_le (by positivity) (hNge m)
    have heq : (m : ℝ) • z m = (N m : ℝ) • (s • y) := by
      simp only [hz, hr, smul_smul]
      congr 1
      field_simp
    simp only [Function.comp, heq]
    field_simp
  have := tendsto_nhds_unique h1 hlim
  rw [this]
  field_simp

lemma cont {d : ℕ} (p φ I : (Fin d → ℝ) → ℝ) (h13 : Conv13 p φ I) :
    ContinuousOn I {y | (∀ i, 0 ≤ y i) ∧ y ≠ 0} := by
  intro y hyS
  show Tendsto I _ _
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  have hx1 : Tendsto x atTop (𝓝 y) := (tendsto_nhdsWithin_iff.1 hx).1
  have hx2 := (tendsto_nhdsWithin_iff.1 hx).2
  rw [Metric.tendsto_atTop]
  by_contra h
  push Not at h
  obtain ⟨ε, hε, hbad⟩ := h
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (I (x n)) (I y) := by
    rw [frequently_atTop]; intro N; obtain ⟨n, hn, h⟩ := hbad N; exact ⟨n, hn, h⟩
  obtain ⟨κ, hκ, hP⟩ := extraction_of_frequently_atTop (hfreq.and_eventually hx2)
  have hev : ∀ j, ∀ᶠ n : ℕ in atTop,
      dist (φ ((n : ℝ) • x (κ j)) / n) (I (x (κ j))) < ε / 2 := by
    intro j
    have := (h13 (fun _ => x (κ j)) (x (κ j)) (fun _ => (hP j).2.1) tendsto_const_nhds
      (hP j).2.2).1
    exact (Metric.tendsto_nhds.1 this) (ε / 2) (by linarith)
  obtain ⟨ν', hν', hQ⟩ := extraction_forall_of_eventually hev
  obtain ⟨ys, hys1, hys2, hys3⟩ := glue ν' hν' (x ∘ κ) y (hx1.comp hκ.tendsto_atTop)
  have hys0 : ∀ n j, 0 ≤ ys n j := by
    intro n j
    rcases hys2 n with h | ⟨k, h⟩
    · rw [h]; exact hyS.1 j
    · rw [h]; exact (hP k).2.1 j
  have hlim := ((h13 ys y hys0 hys3 hyS.2).1).comp hν'.tendsto_atTop
  obtain ⟨j, hj⟩ := ((Metric.tendsto_nhds.1 hlim) (ε / 2) (by linarith)).exists
  have hys1' : ys (ν' j) = x (κ j) := hys1 j
  simp only [Function.comp, hys1'] at hj
  have h1 := hQ j
  have h2 := (hP j).1
  have := dist_triangle (I (x (κ j))) (φ ((ν' j : ℝ) • x (κ j)) / ν' j) (I y)
  rw [dist_comm] at h1
  linarith

end SSIS32

open SelfStructIS.LogEff in
theorem solution (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (p φ I : (Fin d → ℝ) → ℝ) (h32 : Assumption32 μ p φ I) :
    (ContinuousOn I {y | (∀ i, 0 ≤ y i) ∧ y ≠ 0} ∧
        Tendsto I (𝓝[{y | (∀ i, 0 ≤ y i) ∧ y ≠ 0}] 0) (𝓝 0) ∧
        ∀ y : Fin d → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 → 0 < I y) ∧
      (∀ (s : ℝ) (y : Fin d → ℝ), 0 < s → (∀ i, 0 ≤ y i) → y ≠ 0 → I (s • y) = s * I y) ∧
      (∀ (c : ℝ) (i : Fin d), 0 ≤ c →
        sInf (I '' {y : Fin d → ℝ | (∀ j, 0 ≤ y j) ∧ c < y i}) = c) := by
  obtain ⟨hν, hI, h13⟩ := h32
  set ν := μ.map (hazardVec μ) with hνdef
  have hmeas : Measurable (hazardVec μ) :=
    measurable_pi_lambda _ (fun j => (h31 j).2.1.measurable.comp (measurable_pi_apply j))
  have hmarg : ∀ (j : Fin d) (s : ℝ), 0 < s → ν {z | s < z j} = ENNReal.ofReal (Real.exp (-s)) := by
    intro j s hs
    rw [hνdef, Measure.map_apply hmeas (SSIS32.meas_lt j s)]
    exact SSIS32.marg μ j (h31 j).2.1 (h31 j).1 (h31 j).2.2.2 s hs
  have hneg : ∀ j : Fin d, ν {z | z j < 0} = 0 := by
    intro j
    rw [hνdef, Measure.map_apply hmeas (measurableSet_lt (measurable_pi_apply j) measurable_const)]
    have : hazardVec μ ⁻¹' {z : Fin d → ℝ | z j < 0} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact SSIS32.hazard_nonneg μ j (x j)
    rw [this, measure_empty]
  have hlow : ∀ (i : Fin d) (y : Fin d → ℝ), (∀ j, 0 ≤ y j) → 0 < y i → y i ≤ I y :=
    fun i y hy0 hyi => SSIS32.lower ν p φ I hν h13 i (hmarg i) y hy0 hyi
  have hcont := SSIS32.cont p φ I h13
  have hhom := fun s y hs hy0 hy => SSIS32.homog p φ I h13 s hs y hy0 hy
  refine ⟨⟨hcont, ?_, ?_⟩, fun s y hs hy0 hy => hhom s y hs hy0 hy, ?_⟩
  · -- limit at the origin
    set U := {w : Fin d → ℝ | (∀ j, 0 ≤ w j) ∧ ‖w‖ = 1} with hU
    have hUS : U ⊆ {y | (∀ i, 0 ≤ y i) ∧ y ≠ 0} := by
      intro w hw
      refine ⟨hw.1, fun h0 => ?_⟩
      have := hw.2
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hUc : IsCompact U := by
      apply Metric.isCompact_of_isClosed_isBounded
      · have : U = (⋂ j, {w : Fin d → ℝ | 0 ≤ w j}) ∩ {w | ‖w‖ = 1} := by
          ext w; simp [hU]
        rw [this]
        exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
          (isClosed_eq continuous_norm continuous_const)
      · refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := 1)).subset ?_
        intro w hw
        rw [Metric.mem_closedBall, dist_zero_right, hw.2]
    obtain ⟨B, hB⟩ := hUc.exists_bound_of_continuousOn (hcont.mono hUS)
    have hbound : ∀ y ∈ {y : Fin d → ℝ | (∀ i, 0 ≤ y i) ∧ y ≠ 0}, ‖I y‖ ≤ B * ‖y‖ := by
      intro y hy
      have hn : 0 < ‖y‖ := norm_pos_iff.2 hy.2
      set w := ‖y‖⁻¹ • y with hw
      have hw0 : ∀ j, 0 ≤ w j := fun j => by
        simp only [hw, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hn.le) (hy.1 j)
      have hwU : w ∈ U := ⟨hw0, by rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn.le),
        inv_mul_cancel₀ hn.ne']⟩
      have hyw : y = ‖y‖ • w := by rw [hw, smul_inv_smul₀ hn.ne']
      have := hhom ‖y‖ w hn hw0 (hUS hwU).2
      rw [← hyw] at this
      rw [this, norm_mul, Real.norm_of_nonneg hn.le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB w hwU) hn.le
    have hlim : Tendsto (fun y : Fin d → ℝ => B * ‖y‖)
        (𝓝[{y | (∀ i, 0 ≤ y i) ∧ y ≠ 0}] 0) (𝓝 0) := by
      have : Tendsto (fun y : Fin d → ℝ => B * ‖y‖) (𝓝 0) (𝓝 (B * ‖(0 : Fin d → ℝ)‖)) :=
        (continuous_const.mul continuous_norm).tendsto 0
      rw [norm_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm' (eventually_nhdsWithin_of_forall hbound) hlim
  · -- positivity
    intro y hy0 hy
    have : ∃ i, 0 < y i := by
      by_contra h
      push Not at h
      exact hy (funext fun i => le_antisymm (h i) (hy0 i))
    obtain ⟨i, hi⟩ := this
    exact lt_of_lt_of_le hi (hlow i y hy0 hi)
  · -- infimum
    intro c i hc
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨I (fun _ => c + 1), _, ⟨fun _ => by linarith, by simp⟩, rfl⟩
    · rintro a ⟨y, ⟨hy0, hyi⟩, rfl⟩
      exact le_trans hyi.le (hlow i y hy0 (lt_of_le_of_lt hc hyi))
    · intro w hw
      obtain ⟨y, hy0, hyi, hIy⟩ := SSIS32.upper ν p φ I hν h13 hmarg hneg i c hc (w - c) (by linarith)
      exact ⟨I y, ⟨y, ⟨hy0, hyi⟩, rfl⟩, by linarith⟩
