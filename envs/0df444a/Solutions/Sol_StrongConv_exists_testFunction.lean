-- Prove2me | solution 1 for StrongConv.exists_testFunction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:00:45.542748+00:00
-- url     : https://prove2.me/submissions/c342c5c7-a64d-4d04-90f7-c1382d6e74a3

import Definitions.Def_StrongConv
import Mathlib

section
section
open MeasureTheory

namespace StrongConvS4.L410

/-- smooth -/
abbrev Sm (f : ℝ → ℝ) : Prop := ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f

/-- moving average -/
noncomputable def Tm (a : ℝ) (G : ℝ → ℝ) (x : ℝ) : ℝ := (∫ t in (x - a)..x, G t) / a

/-- difference quotient -/
noncomputable def Dm (a : ℝ) (G : ℝ → ℝ) (x : ℝ) : ℝ := (G x - G (x - a)) / a

noncomputable def PP (G : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, G t

lemma Tm_eq (a : ℝ) (G : ℝ → ℝ) (hG : Continuous G) :
    Tm a G = fun x => (PP G x - PP G (x - a)) / a := by
  funext x
  unfold Tm PP
  rw [← intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable 0 x)
    (hG.intervalIntegrable 0 (x - a))]

lemma PP_hasDerivAt (G : ℝ → ℝ) (hG : Continuous G) (x : ℝ) : HasDerivAt (PP G) (G x) x :=
  (hG.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma PP_sm (G : ℝ → ℝ) (hG : Sm G) : Sm (PP G) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun x => (PP_hasDerivAt G hG.continuous x).differentiableAt, ?_⟩
  have : deriv (PP G) = G := funext fun x => (PP_hasDerivAt G hG.continuous x).deriv
  rw [this]; exact hG

lemma Tm_hasDerivAt (a : ℝ) (ha : 0 < a) (G : ℝ → ℝ) (hG : Continuous G) (x : ℝ) :
    HasDerivAt (Tm a G) (Dm a G x) x := by
  rw [Tm_eq a G hG]
  have h1 := PP_hasDerivAt G hG x
  have h2 := (PP_hasDerivAt G hG (x - a)).comp_sub_const x a
  have := (h1.sub h2).div_const a
  simpa [Dm] using this

lemma Tm_sm (a : ℝ) (G : ℝ → ℝ) (hG : Sm G) : Sm (Tm a G) := by
  rw [Tm_eq a G hG.continuous]
  have h := PP_sm G hG
  exact (h.sub (h.comp (contDiff_id.sub contDiff_const))).div_const a

lemma Dm_sm (a : ℝ) (X : ℝ → ℝ) (hX : Sm X) : Sm (Dm a X) := by
  unfold Dm
  exact (hX.sub (hX.comp (contDiff_id.sub contDiff_const))).div_const a

lemma deriv_Tm (a : ℝ) (ha : 0 < a) (G : ℝ → ℝ) (hG : Continuous G) :
    deriv (Tm a G) = Dm a G := funext fun x => (Tm_hasDerivAt a ha G hG x).deriv

lemma Dm_iter_sm (a : ℝ) (n : ℕ) (X : ℝ → ℝ) (hX : Sm X) : Sm ((Dm a)^[n] X) := by
  induction n with
  | zero => simpa using hX
  | succ n ih => rw [Function.iterate_succ_apply']; exact Dm_sm a _ ih

lemma Tm_iter_sm (a : ℝ) (n : ℕ) (X : ℝ → ℝ) (hX : Sm X) : Sm ((Tm a)^[n] X) := by
  induction n with
  | zero => simpa using hX
  | succ n ih => rw [Function.iterate_succ_apply']; exact Tm_sm a _ ih

lemma iteratedDeriv_Dm (a : ℝ) (X : ℝ → ℝ) (hX : Sm X) (k : ℕ) :
    iteratedDeriv k (Dm a X) = Dm a (iteratedDeriv k X) := by
  have hc : ∀ y, ContDiffAt ℝ k X y := fun y =>
    (hX.of_le (by exact_mod_cast le_top)).contDiffAt
  have hs : Dm a X = fun x => a⁻¹ * (X x - X (x - a)) := by
    funext x; simp [Dm, div_eq_inv_mul]
  funext x
  rw [hs, iteratedDeriv_const_mul_field, iteratedDeriv_fun_sub (hc x)
    ((hc (x - a)).comp x (contDiffAt_id.sub contDiffAt_const) |>.congr_of_eventuallyEq
      (by exact Filter.Eventually.of_forall fun _ => rfl)), iteratedDeriv_comp_sub_const]
  simp [Dm, div_eq_inv_mul]

lemma deriv_Dm_iter (a : ℝ) (n : ℕ) (X : ℝ → ℝ) (hX : Sm X) :
    deriv ((Dm a)^[n] X) = (Dm a)^[n] (deriv X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← iteratedDeriv_one,
      iteratedDeriv_Dm a _ (Dm_iter_sm a n X hX), iteratedDeriv_one, ih]

lemma iteratedDeriv_Tm_iter (a : ℝ) (ha : 0 < a) (G : ℝ → ℝ) (hG : Sm G) (j : ℕ) :
    ∀ i : ℕ, iteratedDeriv j ((Tm a)^[i + j] G) = (Dm a)^[j] ((Tm a)^[i] G) := by
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    rw [iteratedDeriv_succ', show i + (j + 1) = (i + j) + 1 by ring,
      Function.iterate_succ_apply', deriv_Tm a ha _ (Tm_iter_sm a _ G hG).continuous,
      iteratedDeriv_Dm a _ (Tm_iter_sm a _ G hG), ih, Function.iterate_succ_apply' (Dm a)]


lemma Tm_const_on (a : ℝ) (ha : 0 < a) (G : ℝ → ℝ) (x c : ℝ)
    (h : ∀ t, x - a ≤ t → t ≤ x → G t = c) : Tm a G x = c := by
  unfold Tm
  have : ∫ t in (x - a)..x, G t = ∫ t in (x - a)..x, c := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact h t ht.1 ht.2
  rw [this]
  simp
  field_simp

lemma Tm_mem (a : ℝ) (ha : 0 < a) (G : ℝ → ℝ) (hG : Continuous G)
    (h : ∀ t, G t ∈ Set.Icc (0:ℝ) 1) (x : ℝ) : Tm a G x ∈ Set.Icc (0:ℝ) 1 := by
  unfold Tm
  have hle : x - a ≤ x := by linarith
  have i1 : 0 ≤ ∫ t in (x - a)..x, G t :=
    intervalIntegral.integral_nonneg hle fun t _ => (h t).1
  have i2 : ∫ t in (x - a)..x, G t ≤ ∫ t in (x - a)..x, (1:ℝ) :=
    intervalIntegral.integral_mono_on hle (hG.intervalIntegrable _ _) (by simp)
      fun t _ => (h t).2
  simp at i2
  constructor
  · positivity
  · rw [div_le_one ha]; linarith

lemma Tm_iter_props (a : ℝ) (ha : 0 < a) (H0 : ℝ → ℝ) (c : ℝ) (hs : Sm H0)
    (hm : ∀ x, H0 x ∈ Set.Icc (0:ℝ) 1) (h0 : ∀ x, x ≤ 0 → H0 x = 0)
    (h1 : ∀ x, c ≤ x → H0 x = 1) (i : ℕ) :
    Sm ((Tm a)^[i] H0) ∧ (∀ x, (Tm a)^[i] H0 x ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ x, x ≤ 0 → (Tm a)^[i] H0 x = 0) ∧ (∀ x, c + i * a ≤ x → (Tm a)^[i] H0 x = 1) := by
  induction i with
  | zero => exact ⟨by simpa using hs, by simpa using hm, by simpa using h0, by simpa using h1⟩
  | succ i ih =>
    obtain ⟨ihs, ihm, ih0, ih1⟩ := ih
    simp only [Function.iterate_succ_apply']
    refine ⟨Tm_sm a _ ihs, Tm_mem a ha _ ihs.continuous ihm, ?_, ?_⟩
    · intro x hx
      exact Tm_const_on a ha _ x 0 fun t _ ht => ih0 t (by linarith)
    · intro x hx
      refine Tm_const_on a ha _ x 1 fun t ht _ => ih1 t ?_
      push_cast at hx; linarith

lemma eLpNorm_Dm_le (a : ℝ) (ha : 0 < a) (G : ℝ → ℝ) (hG : Continuous G) (p : ENNReal) (hp : 1 ≤ p) :
    eLpNorm (Dm a G) p volume ≤ ENNReal.ofReal (2 / a) * eLpNorm G p volume := by
  have h1 : Dm a G = a⁻¹ • (G - fun x => G (x - a)) := by
    funext x; simp [Dm, div_eq_inv_mul]
  have hc : Continuous fun x => G (x - a) := hG.comp (continuous_id.sub continuous_const)
  have h2 : eLpNorm (fun x => G (x - a)) p volume = eLpNorm G p volume :=
    eLpNorm_comp_measurePreserving (g := G) hG.aestronglyMeasurable
      (measurePreserving_sub_right volume a)
  rw [h1]
  refine (eLpNorm_const_smul_le).trans ?_
  have h3 := eLpNorm_sub_le (μ := volume) hG.aestronglyMeasurable
    hc.aestronglyMeasurable hp
  rw [h2] at h3
  calc ‖a⁻¹‖ₑ * eLpNorm (G - fun x => G (x - a)) p volume
      ≤ ‖a⁻¹‖ₑ * (eLpNorm G p volume + eLpNorm G p volume) := by gcongr
    _ = ENNReal.ofReal (2 / a) * eLpNorm G p volume := by
      have : ‖a⁻¹‖ₑ = ENNReal.ofReal a⁻¹ := by
        rw [Real.enorm_eq_ofReal (by positivity)]
      rw [this, ← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

lemma eLpNorm_Dm_iter_le (a : ℝ) (ha : 0 < a) (G : ℝ → ℝ) (hG : Sm G) (p : ENNReal)
    (hp : 1 ≤ p) (n : ℕ) :
    eLpNorm ((Dm a)^[n] G) p volume ≤ ENNReal.ofReal (2 / a) ^ n * eLpNorm G p volume := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc eLpNorm (Dm a ((Dm a)^[n] G)) p volume
        ≤ ENNReal.ofReal (2 / a) * eLpNorm ((Dm a)^[n] G) p volume :=
          eLpNorm_Dm_le a ha _ (Dm_iter_sm a n G hG).continuous p hp
      _ ≤ ENNReal.ofReal (2 / a) * (ENNReal.ofReal (2 / a) ^ n * eLpNorm G p volume) := by gcongr
      _ = _ := by rw [pow_succ]; ring


lemma Phi_sm : Sm Real.smoothTransition := Real.smoothTransition.contDiff

lemma deriv_Phi_zero (y : ℝ) (hy : y ∉ Set.Icc (0:ℝ) 1) : deriv Real.smoothTransition y = 0 := by
  rcases not_and_or.1 hy with h | h
  · replace h := not_le.1 h
    have : Real.smoothTransition =ᶠ[nhds y] fun _ => 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds h)
        fun z hz => Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
    rw [this.deriv_eq]; simp
  · replace h := not_le.1 h
    have : Real.smoothTransition =ᶠ[nhds y] fun _ => 1 :=
      Filter.eventually_of_mem (Ioi_mem_nhds h)
        fun z hz => Real.smoothTransition.one_of_one_le (le_of_lt hz)
    rw [this.deriv_eq]; simp

lemma exists_Phi_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |deriv Real.smoothTransition y| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.1 Phi_sm).2.continuous
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := deriv Real.smoothTransition)
    (s := Set.Icc (0:ℝ) 1) hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (0:ℝ) 1
  · exact (hM y hy).trans (le_max_left _ _)
  · rw [deriv_Phi_zero y hy]; simp

noncomputable def H0 (s : ℝ) (x : ℝ) : ℝ := Real.smoothTransition (x / s)

lemma H0_sm (s : ℝ) : Sm (H0 s) := Phi_sm.comp (contDiff_id.div_const s)

lemma deriv_H0 (s : ℝ) (x : ℝ) : deriv (H0 s) x = deriv Real.smoothTransition (x / s) * s⁻¹ := by
  have h1 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (x / s)) (x / s) :=
    ((Phi_sm.differentiable (by simp)) (x / s)).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => x / s) s⁻¹ x := by
    simpa [div_eq_inv_mul] using (hasDerivAt_id x).const_mul s⁻¹
  exact (h1.comp x h2).deriv

lemma eLpNorm_deriv_H0 (M : ℝ) (hM : ∀ y, |deriv Real.smoothTransition y| ≤ M) (s : ℝ) (hs : 0 < s)
    (β : ℝ) (hβ : 1 < β) :
    eLpNorm (deriv (H0 s)) (ENNReal.ofReal β) volume ≤
      ENNReal.ofReal (M * s⁻¹) * ENNReal.ofReal s ^ β⁻¹ := by
  have hind : deriv (H0 s) = (Set.Icc 0 s).indicator (deriv (H0 s)) := by
    funext x
    by_cases hx : x ∈ Set.Icc 0 s
    · simp [hx]
    · rw [Set.indicator_of_notMem hx, deriv_H0, deriv_Phi_zero, zero_mul]
      intro hy
      apply hx
      exact ⟨by have := hy.1; rwa [le_div_iff₀ hs, zero_mul] at this,
        by have := hy.2; rwa [div_le_one hs] at this⟩
  rw [hind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
  have hb : ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) s)), ‖deriv (H0 s) x‖ ≤ M * s⁻¹ :=
    Filter.Eventually.of_forall fun x => by
      rw [deriv_H0, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hs)]
      exact mul_le_mul_of_nonneg_right (hM _) (inv_pos.2 hs).le
  refine (eLpNorm_le_of_ae_bound hb).trans ?_
  rw [mul_comm]
  gcongr
  simp [Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith)]


lemma exists_h (M : ℝ) (hM : ∀ y, |deriv Real.smoothTransition y| ≤ M) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ h : ℝ → ℝ, Sm h ∧ (∀ x, h x ∈ Set.Icc (0:ℝ) 1) ∧ (∀ x, x ≤ 0 → h x = 0) ∧
      (∀ x, δ ≤ x → h x = 1) ∧ ∀ β : ℝ, 1 < β →
        eLpNorm (iteratedDeriv (m + 1) h) (ENNReal.ofReal β) volume ≤
          ENNReal.ofReal ((4 * m / δ) ^ m * (M * (δ / 2)⁻¹ * (δ / 2) ^ β⁻¹)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  set a : ℝ := δ / (2 * m) with ha_def
  have ha : 0 < a := by positivity
  set s : ℝ := δ / 2 with hs_def
  have hs : 0 < s := by positivity
  have hH0m : ∀ x, H0 s x ∈ Set.Icc (0:ℝ) 1 := fun x =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hH00 : ∀ x, x ≤ 0 → H0 s x = 0 := fun x hx =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hs.le)
  have hH01 : ∀ x, s ≤ x → H0 s x = 1 := fun x hx =>
    Real.smoothTransition.one_of_one_le ((one_le_div hs).2 hx)
  obtain ⟨p1, p2, p3, p4⟩ := Tm_iter_props a ha (H0 s) s (H0_sm s) hH0m hH00 hH01 m
  have hcm : s + m * a = δ := by
    rw [hs_def, ha_def]; field_simp; ring
  refine ⟨(Tm a)^[m] (H0 s), p1, p2, p3, fun x hx => p4 x (by rw [hcm]; exact hx), ?_⟩
  intro β hβ
  have hid := iteratedDeriv_Tm_iter a ha (H0 s) (H0_sm s) m 0
  simp only [zero_add, Function.iterate_zero, id] at hid
  rw [iteratedDeriv_succ, hid, deriv_Dm_iter a m _ (H0_sm s)]
  have hdsm : Sm (deriv (H0 s)) := (contDiff_infty_iff_deriv.1 (H0_sm s)).2
  have hp : (1 : ENNReal) ≤ ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hβ.le
  refine (eLpNorm_Dm_iter_le a ha _ hdsm _ hp m).trans ?_
  have h2a : 2 / a = 4 * m / δ := by rw [ha_def]; field_simp; ring
  rw [h2a]
  have hn := eLpNorm_deriv_H0 M hM s hs β hβ
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc ENNReal.ofReal (4 * m / δ) ^ m * eLpNorm (deriv (H0 s)) (ENNReal.ofReal β) volume
      ≤ ENNReal.ofReal (4 * m / δ) ^ m * (ENNReal.ofReal (M * s⁻¹) * ENNReal.ofReal s ^ β⁻¹) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_rpow_of_nonneg hs.le (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]


lemma term_le (p : ℝ → ℝ) (hp : Continuous p) (A : ℝ → ℝ) (hA : Continuous A)
    (hAm : MeasurePreserving A volume volume) (q : ENNReal) (S : Set ℝ) :
    eLpNorm (fun θ => |p (A θ)|) q (volume.restrict S) ≤ eLpNorm p q volume := by
  calc eLpNorm (fun θ => |p (A θ)|) q (volume.restrict S)
      ≤ eLpNorm (fun θ => |p (A θ)|) q volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (p ∘ A) q volume := by
        rw [← eLpNorm_norm (f := p ∘ A)]; simp [Function.comp]
    _ = eLpNorm p q volume := eLpNorm_comp_measurePreserving hp.aestronglyMeasurable hAm

lemma circle_norm (h : ℝ → ℝ) (hh : Sm h) (c1 c2 : ℝ) (f : ℝ → ℝ) (n : ℕ) (q : ENNReal)
    (hq : 1 ≤ q)
    (hf1 : ∀ θ ∈ Set.Ioo 0 Real.pi, f =ᶠ[nhds θ] fun θ => h (c1 - θ) + h (θ - c2))
    (hf2 : ∀ θ ∈ Set.Ioo Real.pi (2 * Real.pi),
      f =ᶠ[nhds θ] fun θ => h (θ - (2 * Real.pi - c1)) + h ((2 * Real.pi - c2) - θ)) :
    eLpNorm (iteratedDeriv n f) q (volume.restrict (Set.Icc 0 (2 * Real.pi))) ≤
      4 * eLpNorm (iteratedDeriv n h) q volume := by
  set p := iteratedDeriv n h with hp_def
  have hpc : Continuous p := hh.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  have hcd : ∀ y, ContDiffAt ℝ n h y := fun y =>
    (hh.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcd1 : ∀ θ, ContDiffAt ℝ n (fun θ => h (c1 - θ)) θ := fun θ =>
    (hcd _).comp θ (contDiffAt_const.sub contDiffAt_id)
  have hcd2 : ∀ θ c, ContDiffAt ℝ n (fun θ => h (θ - c)) θ := fun θ c =>
    (hcd _).comp θ (contDiffAt_id.sub contDiffAt_const)
  have hcd3 : ∀ θ c, ContDiffAt ℝ n (fun θ => h (c - θ)) θ := fun θ c =>
    (hcd _).comp θ (contDiffAt_const.sub contDiffAt_id)
  have key1 : ∀ c θ, |iteratedDeriv n (fun θ => h (c - θ)) θ| = |p (c - θ)| := by
    intro c θ
    rw [iteratedDeriv_comp_const_sub]
    simp [abs_pow, hp_def]
  have key2 : ∀ c θ, iteratedDeriv n (fun θ => h (θ - c)) θ = p (θ - c) := by
    intro c θ
    rw [iteratedDeriv_comp_sub_const]
  set G : ℝ → ℝ := fun θ => |p (c1 - θ)| + |p (θ - c2)| + |p (θ - (2 * Real.pi - c1))| +
    |p ((2 * Real.pi - c2) - θ)| with hG
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (2 * Real.pi))),
      ‖iteratedDeriv n f θ‖ ≤ G θ := by
    have hnull : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi, 2 * Real.pi} : Set ℝ) :=
      (Set.toFinite _).countable.ae_notMem volume
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hnull] with θ hθ hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    obtain ⟨hn0, hnpi, hn2⟩ := hne
    have hpi := Real.pi_pos
    have n1 : 0 ≤ |p (c1 - θ)| := abs_nonneg _
    have n2 : 0 ≤ |p (θ - c2)| := abs_nonneg _
    have n3 : 0 ≤ |p (θ - (2 * Real.pi - c1))| := abs_nonneg _
    have n4 : 0 ≤ |p ((2 * Real.pi - c2) - θ)| := abs_nonneg _
    rw [Real.norm_eq_abs]
    rcases lt_trichotomy θ Real.pi with hlt | heq | hgt
    · have hmem : θ ∈ Set.Ioo 0 Real.pi := ⟨lt_of_le_of_ne hθ.1 (Ne.symm hn0), hlt⟩
      rw [(hf1 θ hmem).iteratedDeriv_eq n,
        iteratedDeriv_fun_add (hcd1 θ) (hcd2 θ c2), key2]
      calc |iteratedDeriv n (fun θ => h (c1 - θ)) θ + p (θ - c2)|
          ≤ |iteratedDeriv n (fun θ => h (c1 - θ)) θ| + |p (θ - c2)| := abs_add_le _ _
        _ = |p (c1 - θ)| + |p (θ - c2)| := by rw [key1]
        _ ≤ G θ := by simp only [hG]; linarith
    · exact absurd heq hnpi
    · have hmem : θ ∈ Set.Ioo Real.pi (2 * Real.pi) :=
        ⟨hgt, lt_of_le_of_ne hθ.2 hn2⟩
      rw [(hf2 θ hmem).iteratedDeriv_eq n,
        iteratedDeriv_fun_add (hcd2 θ _) (hcd3 θ _), key2]
      calc |p (θ - (2 * Real.pi - c1)) + iteratedDeriv n (fun θ => h (2 * Real.pi - c2 - θ)) θ|
          ≤ |p (θ - (2 * Real.pi - c1))| +
            |iteratedDeriv n (fun θ => h (2 * Real.pi - c2 - θ)) θ| := abs_add_le _ _
        _ = |p (θ - (2 * Real.pi - c1))| + |p (2 * Real.pi - c2 - θ)| := by rw [key1]
        _ ≤ G θ := by simp only [hG]; linarith
  refine (eLpNorm_mono_ae_real hae).trans ?_
  have m1 := term_le p hpc (fun θ => c1 - θ) (continuous_const.sub continuous_id)
    (Measure.measurePreserving_sub_left volume c1) q (Set.Icc 0 (2 * Real.pi))
  have m2 := term_le p hpc (fun θ => θ - c2) (continuous_id.sub continuous_const)
    (measurePreserving_sub_right volume c2) q (Set.Icc 0 (2 * Real.pi))
  have m3 := term_le p hpc (fun θ => θ - (2 * Real.pi - c1)) (continuous_id.sub continuous_const)
    (measurePreserving_sub_right volume _) q (Set.Icc 0 (2 * Real.pi))
  have m4 := term_le p hpc (fun θ => (2 * Real.pi - c2) - θ) (continuous_const.sub continuous_id)
    (Measure.measurePreserving_sub_left volume _) q (Set.Icc 0 (2 * Real.pi))
  have c1' : Continuous fun θ => |p (c1 - θ)| := (hpc.comp (continuous_const.sub continuous_id)).abs
  have c2' : Continuous fun θ => |p (θ - c2)| := (hpc.comp (continuous_id.sub continuous_const)).abs
  have c3' : Continuous fun θ => |p (θ - (2 * Real.pi - c1))| :=
    (hpc.comp (continuous_id.sub continuous_const)).abs
  have c4' : Continuous fun θ => |p ((2 * Real.pi - c2) - θ)| :=
    (hpc.comp (continuous_const.sub continuous_id)).abs
  have s1 := eLpNorm_add_le (μ := volume.restrict (Set.Icc 0 (2 * Real.pi)))
    c1'.aestronglyMeasurable c2'.aestronglyMeasurable hq
  have s2 := eLpNorm_add_le (μ := volume.restrict (Set.Icc 0 (2 * Real.pi)))
    (c1'.add c2').aestronglyMeasurable c3'.aestronglyMeasurable hq
  have s3 := eLpNorm_add_le (μ := volume.restrict (Set.Icc 0 (2 * Real.pi)))
    ((c1'.add c2').add c3').aestronglyMeasurable c4'.aestronglyMeasurable hq
  have tot := s3.trans (add_le_add (s2.trans (add_le_add (s1.trans (add_le_add m1 m2)) m3)) m4)
  refine tot.trans (le_of_eq ?_)
  ring


open Real in
/-- the test function built from `h` -/
noncomputable def chi (h : ℝ → ℝ) (K φ0 : ℝ) (x : ℝ) : ℝ :=
  if |x| < K then h (arcsin (x / K) - φ0) + h (-arcsin (x / K) - φ0) else 1

structure HSpec (h : ℝ → ℝ) (δ : ℝ) : Prop where
  sm : Sm h
  mem : ∀ x, h x ∈ Set.Icc (0:ℝ) 1
  zero : ∀ x, x ≤ 0 → h x = 0
  one : ∀ x, δ ≤ x → h x = 1

open Real in
lemma chi_zero (h : ℝ → ℝ) (δ K t0 t1 : ℝ) (hH : HSpec h δ) (hK : 0 < K) (ht0 : 0 < t0)
    (ht01 : t0 < t1) (ht1 : t1 < K) (hδ : δ = arcsin (t1 / K) - arcsin (t0 / K)) (x : ℝ)
    (hx : |x| ≤ t0) : chi h K (arcsin (t0 / K)) x = 0 := by
  have hxK : |x| < K := by linarith
  unfold chi
  rw [if_pos hxK]
  have h1 : arcsin (x / K) ≤ arcsin (t0 / K) := by
    apply arcsin_le_arcsin
    rw [div_le_div_iff_of_pos_right hK]; exact (le_abs_self x).trans hx
  have h2 : arcsin (t0 / K) ≥ -arcsin (x / K) := by
    rw [← arcsin_neg]
    apply arcsin_le_arcsin
    rw [← neg_div, div_le_div_iff_of_pos_right hK]; exact (neg_le_abs x).trans hx
  rw [hH.zero _ (by linarith), hH.zero _ (by linarith)]; simp

open Real in
lemma chi_one (h : ℝ → ℝ) (δ K t0 t1 : ℝ) (hH : HSpec h δ) (hK : 0 < K) (ht0 : 0 < t0)
    (ht01 : t0 < t1) (ht1 : t1 < K) (hδ : δ = arcsin (t1 / K) - arcsin (t0 / K)) (x : ℝ)
    (hx : t1 ≤ |x|) : chi h K (arcsin (t0 / K)) x = 1 := by
  unfold chi
  have p0 : 0 ≤ arcsin (t0 / K) := arcsin_nonneg.2 (by positivity)
  have p1 : 0 ≤ arcsin (t1 / K) := arcsin_nonneg.2 (by have : 0 < t1 := by linarith
                                                       positivity)
  split_ifs with hxK
  · rcases le_abs'.1 hx with hneg | hpos
    · have h1 : arcsin (x / K) ≤ -arcsin (t1 / K) := by
        rw [← arcsin_neg]
        apply arcsin_le_arcsin
        rw [← neg_div, div_le_div_iff_of_pos_right hK]; exact hneg
      rw [hH.zero _ (by linarith), hH.one _ (by linarith)]; simp
    · have h1 : arcsin (t1 / K) ≤ arcsin (x / K) := by
        apply arcsin_le_arcsin
        rw [div_le_div_iff_of_pos_right hK]; exact hpos
      rw [hH.one _ (by linarith), hH.zero _ (by linarith)]; simp
  · rfl

open Real in
lemma chi_mem (h : ℝ → ℝ) (δ K φ0 : ℝ) (hH : HSpec h δ) (hφ : 0 ≤ φ0) (x : ℝ) :
    chi h K φ0 x ∈ Set.Icc (0:ℝ) 1 := by
  unfold chi
  split_ifs with hxK
  · set s := arcsin (x / K)
    by_cases hs : 0 ≤ s
    · rw [hH.zero (-s - φ0) (by linarith), add_zero]; exact hH.mem _
    · rw [hH.zero (s - φ0) (by linarith), zero_add]; exact hH.mem _
  · exact ⟨zero_le_one, le_rfl⟩

open Real in
lemma chi_sm (h : ℝ → ℝ) (δ K t0 t1 : ℝ) (hH : HSpec h δ) (hK : 0 < K) (ht0 : 0 < t0)
    (ht01 : t0 < t1) (ht1 : t1 < K) (hδ : δ = arcsin (t1 / K) - arcsin (t0 / K)) :
    Sm (chi h K (arcsin (t0 / K))) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hxK : |x| < K
  · have hne1 : x / K ≠ 1 := by
      intro h1; rw [div_eq_one_iff_eq hK.ne'] at h1; rw [h1] at hxK
      exact lt_irrefl _ (lt_of_le_of_lt (le_abs_self _) hxK)
    have hne2 : x / K ≠ -1 := by
      intro h1; rw [div_eq_iff hK.ne'] at h1; rw [h1] at hxK
      simp [abs_of_pos hK] at hxK
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arcsin (x / K) :=
      Real.contDiffAt_arcsin hne2 hne1
    have hasin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => arcsin (y / K)) x :=
      ContDiffAt.comp (g := Real.arcsin) (f := fun y : ℝ => y / K) x h1
        (contDiffAt_id.div_const K)
    have hform : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ℝ => h (arcsin (y / K) - arcsin (t0 / K)) +
          h (-arcsin (y / K) - arcsin (t0 / K))) x := by
      have hhc : ∀ z, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h z := fun z => hH.sm.contDiffAt
      exact ((hhc _).comp x (hasin.sub contDiffAt_const)).add
        ((hhc _).comp x (hasin.neg.sub contDiffAt_const))
    refine hform.congr_of_eventuallyEq ?_
    have : {y : ℝ | |y| < K} ∈ nhds x :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hxK
    exact Filter.eventually_of_mem this fun y hy => by
      have hy' : |y| < K := hy
      simp only [chi]; rw [if_pos hy']
  · have : {y : ℝ | t1 < |y|} ∈ nhds x :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds
        (show t1 < |x| by linarith [not_lt.1 hxK])
    refine (contDiffAt_const (c := (1:ℝ))).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem this fun y hy =>
      chi_one h δ K t0 t1 hH hK ht0 ht01 ht1 hδ y (le_of_lt hy)

open Real in
lemma chi_cos (h : ℝ → ℝ) (K φ0 : ℝ) (hK : 0 < K) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 π) :
    chi h K φ0 (K * cos θ) = h ((π / 2 - φ0) - θ) + h (θ - (π / 2 + φ0)) := by
  have hs := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsq := sin_sq_add_cos_sq θ
  have hlt : |K * cos θ| < K := by
    rw [abs_mul, abs_of_pos hK]
    have : |cos θ| < 1 := abs_lt.2 ⟨by nlinarith, by nlinarith⟩
    nlinarith
  unfold chi
  rw [if_pos hlt, mul_div_cancel_left₀ _ hK.ne', arcsin_eq_pi_div_two_sub_arccos,
    arccos_cos hθ.1.le hθ.2.le]
  congr 2 <;> ring

open Real in
lemma chi_cos' (h : ℝ → ℝ) (K φ0 : ℝ) (hK : 0 < K) (θ : ℝ) (hθ : θ ∈ Set.Ioo π (2 * π)) :
    chi h K φ0 (K * cos θ) =
      h (θ - (2 * π - (π / 2 - φ0))) + h ((2 * π - (π / 2 + φ0)) - θ) := by
  have hc : cos θ = cos (2 * π - θ) := by rw [cos_two_pi_sub]
  rw [hc, chi_cos h K φ0 hK (2 * π - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩]
  congr 2 <;> ring


lemma final_ineq (M : ℝ) (hM : 0 ≤ M) (m : ℕ) (hm : 1 ≤ m) (δ K ε β : ℝ) (hδ : 0 < δ)
    (hε : 0 < ε) (hεK : ε < K) (hδ2 : ε / (2 * K) ≤ δ) (hβ : 1 < β) :
    4 * ((4 * m / δ) ^ m * (M * (δ / 2)⁻¹ * (δ / 2) ^ β⁻¹)) ≤
      ((8 * max 1 (16 * M)) * m) ^ m * (K / ε) ^ ((m : ℝ) + (1 - 1 / β)) := by
  have hK : 0 < K := hε.trans hεK
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hs : 0 < δ / 2 := by positivity
  set r := K / ε with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, le_div_iff₀ hε]; linarith
  have hr0 : 0 < r := by linarith
  set t := 1 - 1 / β with ht_def
  have hβi : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  have hβi0 : 0 < β⁻¹ := inv_pos.2 (by linarith)
  have ht0 : 0 ≤ t := by rw [ht_def]; rw [one_div]; linarith
  have ht1 : t ≤ 1 := by rw [ht_def]; rw [one_div]; linarith
  have hbi : β⁻¹ = 1 - t := by rw [ht_def, one_div]; ring
  -- 1/δ ≤ 2 r
  have hδr : 1 / δ ≤ 2 * r := by
    rw [div_le_iff₀ hδ]
    have : ε / (2 * K) ≤ δ := hδ2
    rw [hr_def]
    have e : 2 * (K / ε) * δ = (2 * K) * δ / ε := by field_simp
    rw [e, le_div_iff₀ hε]
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  have h1 : (δ / 2)⁻¹ * (δ / 2) ^ β⁻¹ = (2 / δ) ^ t := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hs, hbi]
    have : (2 / δ) = (δ / 2)⁻¹ := by rw [inv_div]
    rw [this, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
    congr 1; ring
  have h2 : 2 / δ ≤ 4 * r := by
    have : 2 / δ = 2 * (1 / δ) := by ring
    rw [this]; linarith
  have h3 : (2 / δ) ^ t ≤ 4 * r ^ t := by
    calc (2 / δ) ^ t ≤ (4 * r) ^ t := Real.rpow_le_rpow (by positivity) h2 ht0
      _ = 4 ^ t * r ^ t := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ 4 * r ^ t := by
        gcongr
        calc (4:ℝ) ^ t ≤ 4 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht1
          _ = 4 := Real.rpow_one 4
  have h4 : (4 * m / δ) ^ m ≤ (8 * m * r) ^ m := by
    apply pow_le_pow_left₀ (by positivity)
    have : 4 * (m:ℝ) / δ = 4 * m * (1 / δ) := by ring
    rw [this]
    nlinarith
  set B := max 1 (16 * M) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBm : B ≤ B ^ m := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ m := pow_le_pow_right₀ hB1 hm
  have hMB : 16 * M ≤ B ^ m := (le_max_right _ _).trans hBm
  have e : M * (δ / 2)⁻¹ * (δ / 2) ^ β⁻¹ = M * ((δ / 2)⁻¹ * (δ / 2) ^ β⁻¹) := by ring
  rw [e, h1]
  have hrt : 0 ≤ r ^ t := by positivity
  have hrm : (r : ℝ) ^ ((m : ℝ) + t) = r ^ m * r ^ t := by
    rw [Real.rpow_add hr0, Real.rpow_natCast]
  rw [hrm]
  calc 4 * ((4 * m / δ) ^ m * (M * (2 / δ) ^ t))
      ≤ 4 * ((8 * m * r) ^ m * (M * (4 * r ^ t))) := by gcongr
    _ = (16 * M) * ((8 * m) ^ m * r ^ m * r ^ t) := by rw [mul_pow]; ring
    _ ≤ B ^ m * ((8 * m) ^ m * r ^ m * r ^ t) := by gcongr
    _ = _ := by rw [mul_pow, mul_pow, mul_pow]; ring

end StrongConvS4.L410

namespace StrongConv

open StrongConvS4.L410 Real in
theorem exists_testFunction_dev :
    ∃ C : ℝ, ∀ (m : ℕ) (K ρ ε : ℝ), 1 ≤ m → 0 < K → 0 < ρ → 0 < ε → ρ + ε < K →
      ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, χ x ∈ Set.Icc 0 1) ∧
        (∀ x, |x| ≤ ρ + ε / 2 → χ x = 0) ∧ (∀ x, ρ + ε ≤ |x| → χ x = 1) ∧
        ∀ β : ℝ, 1 < β →
          lpNormCircle β (iteratedDeriv (m + 1) (fun θ => χ (K * Real.cos θ))) ≤
            (C * m) ^ m * (K / ε) ^ ((m : ℝ) + 1 / conjExp β) := by
  obtain ⟨M, hM0, hM⟩ := exists_Phi_bound
  refine ⟨8 * max 1 (16 * M), fun m K ρ ε hm hK hρ hε hρε => ?_⟩
  set t0 := ρ + ε / 2 with ht0_def
  set t1 := ρ + ε with ht1_def
  have ht0 : 0 < t0 := by positivity
  have ht01 : t0 < t1 := by rw [ht0_def, ht1_def]; linarith
  have ht1K : t1 < K := hρε
  set φ0 := arcsin (t0 / K) with hφ0
  set φ1 := arcsin (t1 / K) with hφ1
  have hφ0n : 0 ≤ φ0 := arcsin_nonneg.2 (by positivity)
  have hmono : φ0 ≤ φ1 := arcsin_le_arcsin (by rw [div_le_div_iff_of_pos_right hK]; exact ht01.le)
  set δ := φ1 - φ0 with hδ_def
  have hsin1 : sin φ1 = t1 / K := sin_arcsin (by
    have : 0 < t1 / K := by have : 0 < t1 := by linarith
                            positivity
    linarith) (by rw [div_le_one hK]; exact ht1K.le)
  have hsin0 : sin φ0 = t0 / K := sin_arcsin (by
    have : 0 < t0 / K := by positivity
    linarith) (by rw [div_le_one hK]; linarith)
  have hδ2 : ε / (2 * K) ≤ δ := by
    have := abs_sin_sub_sin_le φ1 φ0
    rw [hsin1, hsin0, abs_of_nonneg (by rw [← sub_div, div_nonneg_iff]; left; exact ⟨by linarith, hK.le⟩),
      abs_of_nonneg (by linarith)] at this
    have e : t1 / K - t0 / K = ε / (2 * K) := by
      rw [ht1_def, ht0_def]; field_simp; ring
    linarith
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδ2
  obtain ⟨h, hsm, hmem, hz, hone, hbound⟩ := exists_h M hM m hm δ hδ
  have hH : HSpec h δ := ⟨hsm, hmem, hz, hone⟩
  have hδ' : δ = arcsin (t1 / K) - arcsin (t0 / K) := rfl
  refine ⟨chi h K φ0, chi_sm h δ K t0 t1 hH hK ht0 ht01 ht1K hδ', chi_mem h δ K φ0 hH hφ0n,
    fun x hx => chi_zero h δ K t0 t1 hH hK ht0 ht01 ht1K hδ' x hx,
    fun x hx => chi_one h δ K t0 t1 hH hK ht0 ht01 ht1K hδ' x hx, ?_⟩
  intro β hβ
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hβ.le
  have hcirc := circle_norm h hsm (π / 2 - φ0) (π / 2 + φ0) (fun θ => chi h K φ0 (K * cos θ))
    (m + 1) (ENNReal.ofReal β) hq
    (fun θ hθ => Filter.eventually_of_mem (Ioo_mem_nhds hθ.1 hθ.2)
      fun y hy => chi_cos h K φ0 hK y hy)
    (fun θ hθ => Filter.eventually_of_mem (Ioo_mem_nhds hθ.1 hθ.2)
      fun y hy => chi_cos' h K φ0 hK y hy)
  have hb := hbound β hβ
  have hfin : ENNReal.ofReal ((4 * m / δ) ^ m * (M * (δ / 2)⁻¹ * (δ / 2) ^ β⁻¹)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hconj : 1 / conjExp β = 1 - 1 / β := by
    unfold conjExp
    rw [one_div, inv_inv]
  rw [hconj]
  have hfin2 : 4 * ENNReal.ofReal ((4 * m / δ) ^ m * (M * (δ / 2)⁻¹ * (δ / 2) ^ β⁻¹)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hfin
  have hle : eLpNorm (iteratedDeriv (m + 1) fun θ => chi h K φ0 (K * cos θ)) (ENNReal.ofReal β)
      (volume.restrict (Set.Icc 0 (2 * π))) ≤
      4 * ENNReal.ofReal ((4 * m / δ) ^ m * (M * (δ / 2)⁻¹ * (δ / 2) ^ β⁻¹)) :=
    hcirc.trans (by gcongr)
  have hfi := final_ineq M hM0 m hm δ K ε β hδ hε (by linarith) hδ2 hβ
  unfold lpNormCircle
  refine (ENNReal.toReal_mono hfin2 hle).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    have : 0 ≤ M := hM0
    positivity)]
  simpa using hfi

end StrongConv

end
end

section
open StrongConv

theorem solution :
    ∃ C : ℝ, ∀ (m : ℕ) (K ρ ε : ℝ), 1 ≤ m → 0 < K → 0 < ρ → 0 < ε → ρ + ε < K →
      ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, χ x ∈ Set.Icc 0 1) ∧
        (∀ x, |x| ≤ ρ + ε / 2 → χ x = 0) ∧ (∀ x, ρ + ε ≤ |x| → χ x = 1) ∧
        ∀ β : ℝ, 1 < β →
          lpNormCircle β (iteratedDeriv (m + 1) (fun θ => χ (K * Real.cos θ))) ≤
            (C * m) ^ m * (K / ε) ^ ((m : ℝ) + 1 / conjExp β) := by
  apply StrongConv.exists_testFunction_dev <;> assumption

end
