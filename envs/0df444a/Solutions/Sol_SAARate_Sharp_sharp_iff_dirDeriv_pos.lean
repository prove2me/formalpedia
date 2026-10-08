-- Prove2me | solution 1 for SAARate.Sharp.sharp_iff_dirDeriv_pos
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:47:34.944266+00:00
-- url     : https://prove2.me/submissions/daec69f3-9c37-4d60-ad48-0a1022e2a31e

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

open SAARate.Sharp Filter Set
open scoped Topology

theorem line_convex {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x d : E m) :
    ConvexOn ℝ univ (fun t : ℝ => g (x + t • d)) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ u v hu hv huv
  have hh := hg.2 (mem_univ (x + a • d)) (mem_univ (x + b • d)) hu hv huv
  have he : u • (x + a • d) + v • (x + b • d) = x + (u * a + v * b) • d := by
    rw [smul_add, smul_add, smul_smul, smul_smul]
    calc
      u • x + (u * a) • d + (v • x + (v * b) • d) =
          (u + v) • x + (u * a + v * b) • d := by module
      _ = x + (u * a + v * b) • d := by rw [huv, one_smul]
  rw [he] at hh
  simpa only [smul_eq_mul] using hh

theorem quotient_tendsto {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x d : E m) :
    Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
      (𝓝[>] 0) (𝓝 (dirDeriv g x d)) := by
  let f : ℝ → ℝ := fun t => g (x + t • d)
  have hd := (line_convex g hg x d).hasDerivWithinAt_rightDeriv_of_mem_interior
    (x := (0 : ℝ)) (by simp)
  have hl := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp hd
  have hl' : Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
      (𝓝[>] 0) (𝓝 (derivWithin f (Ioi 0) 0)) := by
    simpa only [slope_fun_def_field, sub_zero, zero_smul, add_zero] using hl
  have he : dirDeriv g x d = derivWithin f (Ioi 0) 0 := by
    exact hl'.limUnder_eq
  rwa [he]

theorem dirDeriv_support {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x d : E m) :
    dirDeriv g x d ≤ g (x + d) - g x := by
  have hc := line_convex g hg x d
  have hd := hc.hasDerivWithinAt_rightDeriv_of_mem_interior (x := (0 : ℝ)) (by simp)
  have hb := hc.le_slope_of_hasDerivWithinAt_Ioi (mem_univ 0) (mem_univ 1) zero_lt_one hd
  have hl := quotient_tendsto g hg x d
  have hl' := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp hd
  have he : dirDeriv g x d = derivWithin (fun t : ℝ => g (x + t • d)) (Ioi 0) 0 := by
    apply tendsto_nhds_unique hl
    simpa only [slope_fun_def_field, sub_zero, zero_smul, add_zero] using hl'
  simpa [← he, slope_def_field] using hb

theorem dirDeriv_zero {m : ℕ} (g : E m → ℝ) (x : E m) : dirDeriv g x 0 = 0 := by
  unfold dirDeriv
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)).limUnder_eq

theorem dirDeriv_continuous {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x : E m) :
    Continuous (dirDeriv g x) := by
  obtain ⟨K, U, hU, hL⟩ := hg.locallyLipschitz x
  apply LipschitzWith.continuous (K := K)
  apply LipschitzWith.of_dist_le_mul
  intro d e
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun t : ℝ => x + t • d) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (ht0.smul (tendsto_const_nhds (x := d)))
  have he : Tendsto (fun t : ℝ => x + t • e) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (ht0.smul (tendsto_const_nhds (x := e)))
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      dist ((g (x + t • d) - g x) / t) ((g (x + t • e) - g x) / t) ≤
        (K : ℝ) * dist d e := by
    filter_upwards [hd.eventually hU, he.eventually hU, self_mem_nhdsWithin] with t htd hte ht
    change 0 < t at ht
    have hh := hL.dist_le_mul (x + t • d) htd (x + t • e) hte
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] at hh
    rw [Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos ht]
    apply (div_le_iff₀ ht).mpr
    simpa [Real.dist_eq, dist_eq_norm, mul_assoc, mul_comm, mul_left_comm] using hh
  exact le_of_tendsto ((quotient_tendsto g hg x d).dist (quotient_tendsto g hg x e)) hb

theorem dirDeriv_smul_pos {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g)
    (x d : E m) (a : ℝ) (ha : 0 < a) :
    dirDeriv g x (a • d) = a * dirDeriv g x d := by
  have hmul : Tendsto (fun t : ℝ => t * a) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using ht0.mul_const a
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht ha
  have hl := (quotient_tendsto g hg x d).comp hmul
  have hl' : Tendsto (fun t : ℝ => (g (x + t • (a • d)) - g x) / t)
      (𝓝[>] 0) (𝓝 (a * dirDeriv g x d)) := by
    apply (tendsto_const_nhds.mul hl).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_apply, smul_smul]
    field_simp
  exact tendsto_nhds_unique (quotient_tendsto g hg x (a • d)) hl'

theorem cone_closed {m : ℕ} (Θ : Set (E m)) (x : E m) :
    IsClosed (posTangentConeAt Θ x) := by
  change IsClosed (tangentConeAt NNReal Θ x)
  rw [tangentConeAt_eq_biInter_closure]
  exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closure

theorem cone_smul {m : ℕ} (Θ : Set (E m)) (x d : E m)
    (hd : d ∈ posTangentConeAt Θ x) (a : ℝ) (ha : 0 ≤ a) :
    a • d ∈ posTangentConeAt Θ x := by
  obtain ⟨β, l, hl, c, u, hu, hΘ, hcu⟩ := exists_fun_of_mem_tangentConeAt hd
  letI := hl
  apply mem_tangentConeAt_of_seq l (fun b => (Real.toNNReal a) * c b) u hu hΘ
  simpa only [mul_smul, NNReal.smul_def, Real.coe_toNNReal a ha] using
    (tendsto_const_nhds.smul hcu : Tendsto (fun b => a • (c b • u b)) l (𝓝 (a • d)))

theorem uniform_margin {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g)
    (Θ : Set (E m)) (x : E m)
    (hp : ∀ d ∈ posTangentConeAt Θ x, d ≠ 0 → 0 < dirDeriv g x d) :
    ∃ ε > 0, ∀ d ∈ posTangentConeAt Θ x, ε * ‖d‖ ≤ dirDeriv g x d := by
  let K := posTangentConeAt Θ x ∩ Metric.sphere (0 : E m) 1
  have hK : IsCompact K := (isCompact_sphere (0 : E m) 1).inter_left (cone_closed Θ x)
  by_cases hne : K.Nonempty
  · obtain ⟨d₀, hd₀, hmin⟩ := hK.exists_isMinOn hne (dirDeriv_continuous g hg x).continuousOn
    have hdn : ‖d₀‖ = 1 := by simpa using hd₀.2
    have hd0 : d₀ ≠ 0 := by intro h; simpa [h] using hdn
    refine ⟨dirDeriv g x d₀, hp d₀ hd₀.1 hd0, ?_⟩
    intro d hd
    by_cases hdz : d = 0
    · simp [hdz, dirDeriv_zero]
    · have hn : 0 < ‖d‖ := norm_pos_iff.mpr hdz
      have hu : ‖d‖⁻¹ • d ∈ K := by
        refine ⟨cone_smul Θ x d hd _ (inv_nonneg.mpr hn.le), ?_⟩
        simp [Metric.mem_sphere, norm_smul, abs_of_pos (inv_pos.mpr hn), hn.ne']
      have hh := hmin hu
      change dirDeriv g x d₀ ≤ dirDeriv g x (‖d‖⁻¹ • d) at hh
      rw [dirDeriv_smul_pos g hg x d _ (inv_pos.mpr hn)] at hh
      have := mul_le_mul_of_nonneg_right hh hn.le
      simpa [mul_assoc, hn.ne', mul_comm, mul_left_comm] using this
  · refine ⟨1, zero_lt_one, ?_⟩
    intro d hd
    by_cases hdz : d = 0
    · simp [hdz, dirDeriv_zero]
    · have hn : 0 < ‖d‖ := norm_pos_iff.mpr hdz
      apply False.elim
      apply hne
      refine ⟨‖d‖⁻¹ • d, cone_smul Θ x d hd _ (inv_nonneg.mpr hn.le), ?_⟩
      simp [Metric.mem_sphere, norm_smul, abs_of_pos (inv_pos.mpr hn), hn.ne']

theorem sharp_direction_bound {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g)
    (Θ : Set (E m)) (hΘ : Convex ℝ Θ) (x : E m) (hx : x ∈ Θ)
    (c : ℝ) (hc : 0 < c) (hsharp : ∀ y ∈ Θ, g y ≥ g x + c * ‖y - x‖)
    (d : E m) (hd : d ∈ posTangentConeAt Θ x) : c * ‖d‖ ≤ dirDeriv g x d := by
  have radial (u : E m) (hu : x + u ∈ Θ) : c * ‖u‖ ≤ dirDeriv g x u := by
    apply ge_of_tendsto (quotient_tendsto g hg x u)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    change 0 < t ∧ t < 1 at ht
    have hy : x + t • u ∈ Θ := by
      have := hΘ hx hu (show 0 ≤ 1 - t by linarith [ht.2]) ht.1.le (by ring : (1 - t) + t = 1)
      convert this using 1 <;> module
    have hs := hsharp (x + t • u) hy
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hs
    apply (le_div_iff₀ ht.1).mpr
    nlinarith
  obtain ⟨β, l, hl, a, u, hu, hmem, hlim⟩ := exists_fun_of_mem_tangentConeAt hd
  letI := hl
  have hb : ∀ᶠ b in l, c * ‖a b • u b‖ ≤ dirDeriv g x (a b • u b) := by
    filter_upwards [hmem] with b hb
    by_cases hz : a b = 0
    · simp [hz, dirDeriv_zero]
    · have ha : 0 < (a b : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hz)
      rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
        dirDeriv_smul_pos g hg x (u b) _ ha]
      nlinarith [mul_le_mul_of_nonneg_left (radial (u b) hb) ha.le]
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hlim.norm)
    ((dirDeriv_continuous g hg x).tendsto d |>.comp hlim) hb

theorem sharp_equivalence {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g)
    (Θ : Set (E m)) (hΘ : Convex ℝ Θ) (x : E m) (hx : x ∈ Θ) :
    (argminOn g Θ = {x} ∧ ∃ c > 0, ∀ y ∈ Θ, g y ≥ g x + c * ‖y - x‖) ↔
      ∀ d ∈ posTangentConeAt Θ x, d ≠ 0 → 0 < dirDeriv g x d := by
  constructor
  · rintro ⟨_, c, hc, hsharp⟩ d hd hdn
    exact (mul_pos hc (norm_pos_iff.mpr hdn)).trans_le
      (sharp_direction_bound g hg Θ hΘ x hx c hc hsharp d hd)
  · intro hp
    obtain ⟨c, hc, hbound⟩ := uniform_margin g hg Θ x hp
    have hsharp (y : E m) (hy : y ∈ Θ) : g y ≥ g x + c * ‖y - x‖ := by
      have hcone : y - x ∈ posTangentConeAt Θ x :=
        sub_mem_posTangentConeAt_of_openSegment_subset
          ((openSegment_subset_segment ℝ x y).trans (hΘ.segment_subset hx hy))
      have hb := hbound (y - x) hcone
      have hs := dirDeriv_support g hg x (y - x)
      rw [add_sub_cancel] at hs
      linarith
    refine ⟨?_, c, hc, hsharp⟩
    ext y
    constructor
    · intro hy
      have hle := hy.2 x hx
      have hb := hsharp y hy.1
      have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
      have he : y = x := sub_eq_zero.mp (norm_eq_zero.mp hz)
      simpa using he
    · intro hy
      have he : y = x := Set.mem_singleton_iff.mp hy
      subst y
      refine ⟨hx, ?_⟩
      intro z hz
      have hb := hsharp z hz
      have hn := mul_nonneg hc.le (norm_nonneg (z - x))
      linarith


theorem solution {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (Θ : Set (E m)) (hΘ : Convex ℝ Θ) (xbar : E m) (hx : xbar ∈ Θ) :
    (argminOn g Θ = {xbar} ∧ ∃ c > 0, ∀ x ∈ Θ, g x ≥ g xbar + c * ‖x - xbar‖) ↔
      ∀ d ∈ posTangentConeAt Θ xbar, d ≠ 0 → 0 < dirDeriv g xbar d := by
  exact sharp_equivalence g hg Θ hΘ xbar hx

#print axioms solution
