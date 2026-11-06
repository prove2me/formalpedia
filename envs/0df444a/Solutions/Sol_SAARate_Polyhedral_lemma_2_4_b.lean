-- Prove2me | solution 1 for SAARate.Polyhedral.lemma_2_4_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:24:10.328213+00:00
-- url     : https://prove2.me/submissions/cda8de31-695d-4bba-8a3f-83a6dd5ec910

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

open MeasureTheory ProbabilityTheory Filter Topology ShorNonsmooth.Subdiff

open SAARate.Sharp SAARate.Polyhedral in
theorem solution {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω))
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) :
    ∀ᵐ s ∂Q, Tendsto (fun N : ℕ => ⨆ x : SAARate.Sharp.E m,
        Metric.hausdorffEDist (subdifferential Set.univ (SAARate.Sharp.saaObj h (fun j => ω j s) N) x)
          (subdifferential Set.univ (SAARate.Sharp.expectedObj P h) x)) atTop (𝓝 0) := by
  classical
  choose k a b hrep0 using hpl
  have hrep : ∀ ω x, h x ω = Finset.univ.sup' Finset.univ_nonempty
      (fun i => inner ℝ (a ω i) x + b ω i) := fun ω x => hrep0 ω x
  have hle : ∀ ω i x, inner ℝ (a ω i) x + b ω i ≤ h x ω := fun ω i x => by
    rw [hrep ω x]
    exact Finset.le_sup' (fun i => inner ℝ (a ω i) x + b ω i) (Finset.mem_univ i)
  have hex : ∀ ω x, ∃ i, h x ω = inner ℝ (a ω i) x + b ω i := fun ω x => by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => inner ℝ (a ω i) x + b ω i)
    exact ⟨i, by rw [hrep ω x, hi]⟩
  -- a uniform bound on the slopes
  set B : ℝ := ∑ ω, ∑ i, ‖a ω i‖ with hBdef
  have hB : ∀ ω i, ‖a ω i‖ ≤ B := fun ω i => by
    have h1 : ‖a ω i‖ ≤ ∑ i, ‖a ω i‖ :=
      Finset.single_le_sum (f := fun i => ‖a ω i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, ‖a ω i‖ ≤ B :=
      Finset.single_le_sum (f := fun ω => ∑ i, ‖a ω i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ ω)
    linarith
  let G : (Ω → ℝ) → E m → ℝ := fun c y => ∑ ω', c ω' * h y ω'
  -- the key approximation estimate (Moreau–Rockafellar via separation)
  have key : ∀ (z : E m) (c c' : Ω → ℝ), (∀ ω', 0 ≤ c ω') → (∀ ω', 0 ≤ c' ω') →
      ∀ v ∈ subdifferential Set.univ (G c) z, ∃ v' ∈ subdifferential Set.univ (G c') z,
        ‖v - v'‖ ≤ ∑ ω', |c ω' - c' ω'| * B := by
    intro z c c' hc hc' v hv
    let I : ∀ ω', Finset (Fin (k ω' + 1)) := fun ω' =>
      Finset.univ.filter (fun i => inner ℝ (a ω' i) z + b ω' i = h z ω')
    have hIne : ∀ ω', (I ω').Nonempty := fun ω' => by
      obtain ⟨i, hi⟩ := hex ω' z
      exact ⟨i, by simp [I, hi]⟩
    let D : ∀ _ω' : Ω, Set (E m) := fun ω' =>
      convexHull ℝ ((fun i => a ω' i) '' ((I ω' : Finset _) : Set (Fin (k ω' + 1))))
    have hDsub : ∀ ω', ∀ u ∈ D ω', ∀ y, h y ω' - h z ω' ≥ inner ℝ u (y - z) := by
      intro ω'
      refine convexHull_min ?_ ?_
      · rintro _ ⟨i, hi, rfl⟩ y
        have hi' : inner ℝ (a ω' i) z + b ω' i = h z ω' := by
          simpa [I] using hi
        have := hle ω' i y
        rw [inner_sub_right]
        linarith
      · intro u1 hu1 u2 hu2 α β hα hβ hαβ y
        have e1 := hu1 y
        have e2 := hu2 y
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        have : h y ω' - h z ω' = α * (h y ω' - h z ω') + β * (h y ω' - h z ω') := by
          rw [← add_mul, hαβ, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left e1 hα, mul_le_mul_of_nonneg_left e2 hβ]
    have hDB : ∀ ω', ∀ u ∈ D ω', ‖u‖ ≤ B := by
      intro ω' u hu
      have : D ω' ⊆ Metric.closedBall 0 B := by
        refine convexHull_min ?_ (convex_closedBall 0 B)
        rintro _ ⟨i, -, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hB ω' i
      simpa [Metric.mem_closedBall, dist_zero_right] using this hu
    -- the candidate set
    let K : Set (E m) := (fun u : Ω → E m => ∑ ω', c ω' • u ω') '' (Set.univ.pi D)
    have hKc : IsClosed K := by
      have hcpt : IsCompact (Set.univ.pi D) := isCompact_univ_pi fun ω' =>
        ((Set.toFinite _).isCompact_convexHull ℝ)
      exact (hcpt.image (by fun_prop)).isClosed
    have hKv : Convex ℝ K := by
      rintro _ ⟨u1, hu1, rfl⟩ _ ⟨u2, hu2, rfl⟩ α β hα hβ hαβ
      refine ⟨fun ω' => α • u1 ω' + β • u2 ω', fun ω' _ =>
        (convex_convexHull ℝ _) (hu1 ω' (Set.mem_univ _)) (hu2 ω' (Set.mem_univ _)) hα hβ hαβ, ?_⟩
      simp only [Finset.smul_sum, smul_add, ← Finset.sum_add_distrib, smul_smul]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      rw [mul_comm α, mul_comm β]
    have hvK : v ∈ K := by
      by_contra hvK
      obtain ⟨f, u0, hf1, hf2⟩ := geometric_hahn_banach_closed_point hKv hKc hvK
      set d := (InnerProductSpace.toDual ℝ (E m)).symm f
      have hd : ∀ y, inner ℝ d y = f y := fun y => InnerProductSpace.toDual_symm_apply
      have hmax : ∀ ω', ∃ i ∈ I ω', ∀ j ∈ I ω', inner ℝ (a ω' j) d ≤ inner ℝ (a ω' i) d :=
        fun ω' => Finset.exists_max_image (I ω') (fun i => inner ℝ (a ω' i) d) (hIne ω')
      choose istar histar hmaxi using hmax
      have hloc : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ ∀ ω', h (z + t • d) ω' ≤
          h z ω' + t * inner ℝ (a ω' (istar ω')) d := by
        refine eventually_mem_nhdsWithin.and ?_
        rw [Filter.eventually_all]
        intro ω'
        have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ (Finset.univ : Finset (Fin (k ω' + 1))),
            inner ℝ (a ω' i) (z + t • d) + b ω' i ≤ h z ω' + t * inner ℝ (a ω' (istar ω')) d := by
          rw [Filter.eventually_all_finset]
          intro i _
          by_cases hiI : i ∈ I ω'
          · filter_upwards [eventually_mem_nhdsWithin] with t ht
            have ht' : (0 : ℝ) < t := ht
            have hi' : inner ℝ (a ω' i) z + b ω' i = h z ω' := by simpa [I] using hiI
            rw [inner_add_right, real_inner_smul_right]
            have := mul_le_mul_of_nonneg_left (hmaxi ω' i hiI) ht'.le
            rw [real_inner_comm d (a ω' i)] at this ⊢
            linarith
          · have hlt : inner ℝ (a ω' i) z + b ω' i < h z ω' := by
              refine lt_of_le_of_ne (hle ω' i z) fun heq => hiI ?_
              simp [I, heq]
            have hc1 : Continuous fun t : ℝ => inner ℝ (a ω' i) (z + t • d) + b ω' i := by
              fun_prop
            have hc2 : Continuous fun t : ℝ =>
                h z ω' + t * inner ℝ (a ω' (istar ω')) d := by fun_prop
            have : ∀ᶠ t in 𝓝 (0 : ℝ), inner ℝ (a ω' i) (z + t • d) + b ω' i <
                h z ω' + t * inner ℝ (a ω' (istar ω')) d := by
              apply hc1.continuousAt.eventually_lt hc2.continuousAt
              simpa using hlt
            exact nhdsWithin_le_nhds (this.mono fun t ht => ht.le)
        filter_upwards [hall] with t ht
        rw [hrep ω' (z + t • d)]
        exact Finset.sup'_le _ _ ht
      obtain ⟨t, ht0, ht⟩ := hloc.exists
      set wstar := ∑ ω', c ω' • a ω' (istar ω')
      have hwK : wstar ∈ K := ⟨fun ω' => a ω' (istar ω'), fun ω' _ =>
        subset_convexHull ℝ _ ⟨istar ω', histar ω', rfl⟩, rfl⟩
      have hsub := hv (z + t • d) (Set.mem_univ _)
      rw [add_sub_cancel_left, real_inner_smul_right] at hsub
      have hinc : G c (z + t • d) - G c z ≤ t * inner ℝ d wstar := by
        simp only [G, wstar, ← Finset.sum_sub_distrib, ← mul_sub, inner_sum,
          real_inner_smul_right, Finset.mul_sum]
        refine Finset.sum_le_sum fun ω' _ => ?_
        have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.2 (ht ω')) (hc ω')
        have e : inner ℝ (a ω' (istar ω')) d = inner ℝ d (a ω' (istar ω')) := real_inner_comm _ _
        rw [e] at this
        linarith
      have h1 : inner ℝ v d ≤ inner ℝ d wstar := by
        have : t * inner ℝ v d ≤ t * inner ℝ d wstar := by linarith
        exact le_of_mul_le_mul_left this ht0
      have h2 := hf1 wstar hwK
      rw [← hd] at h2 hf2
      have e : inner ℝ v d = inner ℝ d v := real_inner_comm _ _
      linarith
    obtain ⟨u, hu, rfl⟩ := hvK
    refine ⟨∑ ω', c' ω' • u ω', ?_, ?_⟩
    · intro y _
      simp only [G, ← Finset.sum_sub_distrib, ← mul_sub, sum_inner, real_inner_smul_left]
      exact Finset.sum_le_sum fun ω' _ =>
        mul_le_mul_of_nonneg_left (hDsub ω' (u ω') (hu ω' (Set.mem_univ _)) y) (hc' ω')
    · rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ω' _ => ?_)
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hDB ω' _ (hu ω' (Set.mem_univ _))) (abs_nonneg _)
  have hHaus : ∀ (z : E m) (c c' : Ω → ℝ), (∀ ω', 0 ≤ c ω') → (∀ ω', 0 ≤ c' ω') →
      Metric.hausdorffEDist (subdifferential Set.univ (G c) z)
        (subdifferential Set.univ (G c') z) ≤ ENNReal.ofReal (∑ ω', |c ω' - c' ω'| * B) := by
    intro z c c' hc hc'
    apply Metric.hausdorffEDist_le_of_mem_edist
    · intro v hv
      obtain ⟨v', hv', hn⟩ := key z c c' hc hc' v hv
      exact ⟨v', hv', by rw [edist_dist, dist_eq_norm]; exact ENNReal.ofReal_le_ofReal hn⟩
    · intro v hv
      obtain ⟨v', hv', hn⟩ := key z c' c hc' hc v hv
      refine ⟨v', hv', ?_⟩
      rw [edist_dist, dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal (hn.trans (le_of_eq ?_))
      exact Finset.sum_congr rfl fun ω' _ => by rw [abs_sub_comm]
  -- the two objectives
  set p : Ω → ℝ := fun ω' => P.real {ω'} with hpdef
  have hfeq : expectedObj P h = G p := by
    funext y
    simp only [expectedObj, G, hpdef]
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul]
  let cN : (ℕ → Ω) → ℕ → Ω → ℝ := fun s N ω' =>
    (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, (if s j = ω' then (1 : ℝ) else 0)
  have hsaa : ∀ s N, saaObj h s N = G (cN s N) := by
    intro s N; funext y
    simp only [saaObj, G, cN]
    have : ∑ j ∈ Finset.range N, h y (s j) =
        ∑ ω', (∑ j ∈ Finset.range N, (if s j = ω' then (1 : ℝ) else 0)) * h y ω' := by
      simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq]; simp
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω' _ => by ring
  have hcN0 : ∀ s N ω', 0 ≤ cN s N ω' := fun s N ω' =>
    mul_nonneg (inv_nonneg.2 N.cast_nonneg) (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num)
  have hp0 : ∀ ω', 0 ≤ p ω' := fun ω' => measureReal_nonneg
  -- strong law of large numbers for the empirical frequencies
  obtain ⟨hm, hind, hlaw⟩ := hω
  have hSLLN : ∀ ω0 : Ω, ∀ᵐ s ∂Q, Tendsto (fun N => cN (fun j => ω j s) N ω0) atTop (𝓝 (p ω0)) := by
    intro ω0
    let φ : Ω → ℝ := fun w => if w = ω0 then 1 else 0
    have hφ : Measurable φ := Measurable.of_discrete
    let X : ℕ → S → ℝ := fun j s => φ (ω j s)
    have hint : Integrable (X 0) Q := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) (hφ.comp (hm 0)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      simp only [X, φ]; split_ifs <;> norm_num
    have hindep : Pairwise (fun i j => X i ⟂ᵢ[Q] X j) := fun i j hij =>
      (hind.indepFun hij).comp hφ hφ
    have hident : ∀ i, IdentDistrib (X i) (X 0) Q Q := fun i =>
      (show IdentDistrib (ω i) (ω 0) Q Q from
        ⟨(hm i).aemeasurable, (hm 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩).comp hφ
    have hmean : Q[X 0] = p ω0 := by
      have : Q[X 0] = ∫ w, φ w ∂(Q.map (ω 0)) := by
        rw [integral_map (hm 0).aemeasurable hφ.aestronglyMeasurable]
      rw [this, hlaw 0, integral_fintype Integrable.of_finite]
      simp [φ, hpdef]
    filter_upwards [strong_law_ae_real X hint hindep hident] with s hs
    rw [hmean] at hs
    refine hs.congr fun N => ?_
    simp only [cN, X, φ]
    rw [div_eq_inv_mul]
  have hall : ∀ᵐ s ∂Q, ∀ ω0 : Ω, Tendsto (fun N => cN (fun j => ω j s) N ω0) atTop (𝓝 (p ω0)) :=
    ae_all_iff.2 hSLLN
  filter_upwards [hall] with s hs
  have hbound : Tendsto (fun N => ENNReal.ofReal (∑ ω', |cN (fun j => ω j s) N ω' - p ω'| * B))
      atTop (𝓝 0) := by
    have : Tendsto (fun N => ∑ ω', |cN (fun j => ω j s) N ω' - p ω'| * B) atTop
        (𝓝 (∑ ω', |p ω' - p ω'| * B)) :=
      tendsto_finset_sum _ fun ω' _ => (((hs ω').sub_const (p ω')).abs).mul_const B
    simp only [sub_self, abs_zero, zero_mul, Finset.sum_const_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => bot_le) (fun N => ?_)
  refine iSup_le fun x => ?_
  rw [hsaa, hfeq]
  exact hHaus x _ _ (hcN0 _ N) hp0
