-- Prove2me | solution 1 for ReinfRegGames.Extinction.proposition_C_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:34:31.427607+00:00
-- url     : https://prove2.me/submissions/7d301569-5842-40b7-8849-adc3d673a641

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_Extinction_Bregman

namespace RGAux
open ReinfRegGames.Extinction Filter Topology

section Basic
variable {B : Type*} [Fintype B]

lemma isChoice_conj {h : (B → ℝ) → ℝ} {y x : B → ℝ} (hx : IsChoice h y x) :
    conj h y = y ⬝ᵥ x - h x := by
  unfold conj
  have : IsGreatest ((fun x => y ⬝ᵥ x - h x) '' stdSimplex ℝ B) (y ⬝ᵥ x - h x) := by
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    exact hx.2 x' hx'
  exact this.csSup_eq

lemma fenchel_eq {h : (B → ℝ) → ℝ} {p y x : B → ℝ} (hx : IsChoice h y x) :
    fenchelCoupling h p y = h p - h x - y ⬝ᵥ (p - x) := by
  unfold fenchelCoupling
  rw [isChoice_conj hx, dotProduct_sub]; ring

lemma exists_choice [Nonempty B] {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) (y : B → ℝ) :
    ∃ x, IsChoice h y x := by
  classical
  have hc : ContinuousOn (fun x => y ⬝ᵥ x - h x) (stdSimplex ℝ B) := by
    refine ContinuousOn.sub (Continuous.continuousOn ?_) hpen.1
    unfold dotProduct
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))
  obtain ⟨b⟩ := ‹Nonempty B›
  obtain ⟨x, hx, hmax⟩ := (isCompact_stdSimplex ℝ B).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ b⟩ hc
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩

lemma exists_bound {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ stdSimplex ℝ B, |h x| ≤ R := by
  obtain ⟨C, hC⟩ := (isCompact_stdSimplex ℝ B).exists_bound_of_continuousOn hpen.1
  exact ⟨max C 0, le_max_right _ _, fun x hx => by
    have := hC x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

lemma sqDist_nonneg (x x' : B → ℝ) : 0 ≤ sqDist x x' :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma sqDist_comm (x x' : B → ℝ) : sqDist x x' = sqDist x' x := by
  unfold sqDist
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma conv_ineq {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {a b : B → ℝ}
    (ha : a ∈ stdSimplex ℝ B) (hb : b ∈ stdSimplex ℝ B) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    h (l • a + (1 - l) • b) ≤ l * h a + (1 - l) * h b := by
  have h1 := hpen.2.2.2 a ha b hb l ⟨hl0, hl1⟩
  have hK := hpen.2.2.1
  have h0 : 0 ≤ 1 / 2 * K * l * (1 - l) * sqDist a b :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hl0) (by linarith)) (sqDist_nonneg _ _)
  linarith

lemma line_mem {x p : B → ℝ} (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : x + t • (p - x) ∈ stdSimplex ℝ B := by
  have := convex_stdSimplex ℝ B hx hp (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
  convert this using 1
  ext i; simp; ring

lemma quot_mono {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {x p : B → ℝ}
    (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {u t : ℝ} (hu : 0 < u) (hut : u ≤ t)
    (ht : t ≤ 1) :
    (h (x + u • (p - x)) - h x) / u ≤ (h (x + t • (p - x)) - h x) / t := by
  have ht0 : 0 < t := lt_of_lt_of_le hu hut
  have hxt := line_mem hx hp ht0.le ht
  have hut' : 0 ≤ u / t := by positivity
  have hle : u / t ≤ 1 := by rw [div_le_one ht0]; exact hut
  have key := conv_ineq hpen hx hxt (l := 1 - u / t) (by linarith) (by linarith)
  have e : (1 - u / t) • x + (1 - (1 - u / t)) • (x + t • (p - x)) = x + u • (p - x) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  rw [e] at key
  rw [div_le_div_iff₀ hu ht0]
  have e1 : t * (1 - u / t) = t - u := by field_simp
  have e2 : t * (1 - (1 - u / t)) = u := by rw [mul_sub, mul_one, e1]; ring
  have k2 := mul_le_mul_of_nonneg_left key ht0.le
  have k3 : t * ((1 - u / t) * h x + (1 - (1 - u / t)) * h (x + t • (p - x))) =
      (t * (1 - u / t)) * h x + (t * (1 - (1 - u / t))) * h (x + t • (p - x)) := by ring
  rw [k3, e1, e2] at k2
  nlinarith

lemma quot_ge {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {x p : B → ℝ}
    (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {s t : ℝ} (hs : 0 < s)
    (ha : x - s • (p - x) ∈ stdSimplex ℝ B) (ht0 : 0 < t) (ht : t ≤ 1) :
    (h x - h (x - s • (p - x))) / s ≤ (h (x + t • (p - x)) - h x) / t := by
  have hxt := line_mem hx hp ht0.le ht
  have hst : 0 < s + t := by linarith
  have key := conv_ineq hpen ha hxt (l := t / (s + t)) (by positivity)
    (by rw [div_le_one hst]; linarith)
  have e : (t / (s + t)) • (x - s • (p - x)) + (1 - t / (s + t)) • (x + t • (p - x)) = x := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  rw [e] at key
  rw [div_le_div_iff₀ hs ht0]
  have e1 : (s + t) * (t / (s + t)) = t := by field_simp
  have e2 : (s + t) * (1 - t / (s + t)) = s := by rw [mul_sub, mul_one, e1]; ring
  have k2 := mul_le_mul_of_nonneg_left key hst.le
  have k3 : (s + t) * (t / (s + t) * h (x - s • (p - x)) +
      (1 - t / (s + t)) * h (x + t • (p - x))) =
      ((s + t) * (t / (s + t))) * h (x - s • (p - x)) +
      ((s + t) * (1 - t / (s + t))) * h (x + t • (p - x)) := by ring
  rw [k3, e1, e2] at k2
  nlinarith

end Basic
end RGAux

namespace RGAux
open ReinfRegGames.Extinction Filter Topology
open scoped ContDiff

section Deriv
variable {B : Type*} [Fintype B]

lemma line_deriv {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p x : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) (hx : x ∈ stdSimplex ℝ B) (hxp : ∀ α, 0 < p α → 0 < x α) :
    ∃ d : ℝ, HasDerivAt (fun t : ℝ => h (x + t • (p - x))) d 0 ∧
      ∃ ε > 0, ∀ t : ℝ, |t| < ε → x + t • (p - x) ∈ stdSimplex ℝ B := by
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), ∀ α, 0 < x α → 0 < x α + t * (p α - x α) := by
    rw [Filter.eventually_all]
    intro α
    by_cases hα : 0 < x α
    · have hc : ContinuousAt (fun t : ℝ => x α + t * (p α - x α)) 0 := by fun_prop
      have := ContinuousAt.eventually_lt (continuousAt_const (y := (0:ℝ))) hc
        (by simpa using hα)
      exact this.mono fun t ht _ => ht
    · exact Eventually.of_forall fun t h => absurd h hα
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hpos : ∀ t : ℝ, |t| < ε → ∀ α, 0 < x α → 0 < x α + t * (p α - x α) := fun t ht =>
    hball (y := t) (by simpa [Real.dist_eq] using ht)
  have hmem : ∀ t : ℝ, |t| < ε → x + t • (p - x) ∈ stdSimplex ℝ B := by
    intro t ht
    refine ⟨fun α => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      by_cases hα : 0 < x α
      · exact (hpos t ht α hα).le
      · have h1 : x α = 0 := le_antisymm (not_lt.1 hα) (hx.1 α)
        have h2 : p α = 0 :=
          le_antisymm (not_lt.1 (fun h => hα (hxp α h))) (hp.1 α)
        rw [h1, h2]; simp
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx.2, hp.2]
      ring
  have hface : ∀ t : ℝ, |t| < ε → x + t • (p - x) ∈ faceRelInt {α | 0 < x α} := by
    intro t ht
    refine ⟨hmem t ht, fun β => ?_⟩
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    constructor
    · intro h0
      by_contra hβ
      have h1 : x β = 0 := le_antisymm (not_lt.1 hβ) (hx.1 β)
      have h2 : p β = 0 := le_antisymm (not_lt.1 (fun h => hβ (hxp β h))) (hp.1 β)
      rw [h1, h2] at h0; simp at h0
    · exact fun hβ => hpos t ht β hβ
  have hcd : ContDiffOn ℝ ∞ (fun t : ℝ => x + t • (p - x)) (Set.Ioo (-ε) ε) :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
  have hh := hpen.2.1 {α | 0 < x α} ε (fun t : ℝ => x + t • (p - x)) hcd
    (fun t ht => hface t (by rw [abs_lt]; exact ht))
  have h0 : (0:ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hda := (hh.contDiffAt (Ioo_mem_nhds h0.1 h0.2)).differentiableAt (by simp)
  exact ⟨_, hda.hasDerivAt, ε, hε, hmem⟩

lemma oneSided {h : (B → ℝ) → ℝ} {x z : B → ℝ} {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => h (x + t • z)) d 0) :
    Tendsto (fun t : ℝ => (h (x + t • z) - h x) / t) (𝓝[>] 0) (𝓝 d) := by
  have := hd.tendsto_slope_zero_right
  refine this.congr (fun t => ?_)
  simp [div_eq_inv_mul]

lemma le_of_small {a b c : ℝ} (H : ∀ t : ℝ, 0 < t → t < 1 → a - c * t ≤ b) : a ≤ b := by
  have hT : Tendsto (fun t : ℝ => a - c * t) (𝓝[>] 0) (𝓝 a) := by
    have : Tendsto (fun t : ℝ => a - c * t) (𝓝 0) (𝓝 (a - c * 0)) :=
      (by fun_prop : Continuous fun t : ℝ => a - c * t).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hT (by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht using H t ht.1 ht.2)

lemma strong_conv_line {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {x p : B → ℝ}
    (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    h (x + t • (p - x)) ≤ h x + t * (h p - h x) - 1 / 2 * K * t * (1 - t) * sqDist x p := by
  have := hpen.2.2.2 p hp x hx t ⟨ht0, ht1⟩
  have e : t • p + (1 - t) • x = x + t • (p - x) := by
    ext i; simp; ring
  rw [e, sqDist_comm p x] at this
  linarith

lemma gap_of_slope {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {x p : B → ℝ}
    (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {m : ℝ}
    (H : ∀ t : ℝ, 0 < t → t < 1 → m * t ≤ h (x + t • (p - x)) - h x) :
    m + 1 / 2 * K * sqDist x p ≤ h p - h x := by
  apply le_of_small (c := 1 / 2 * K * sqDist x p)
  intro t ht0 ht1
  have h1 := H t ht0 ht1
  have h2 := strong_conv_line hpen hx hp ht0.le ht1.le
  have h3 : t * (m + 1 / 2 * K * sqDist x p * (1 - t)) ≤ t * (h p - h x) := by nlinarith
  have := le_of_mul_le_mul_left h3 ht0
  linarith

lemma deriv_le_quot {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {x p : B → ℝ}
    (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {d : ℝ}
    (hd : Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (𝓝[>] 0) (𝓝 d))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    d ≤ (h (x + t • (p - x)) - h x) / t := by
  refine le_of_tendsto hd ?_
  filter_upwards [Ioo_mem_nhdsGT ht0] with u hu
  exact quot_mono hpen hx hp hu.1 hu.2.le ht1

lemma c2ii_core {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {x p : B → ℝ}
    (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {d : ℝ}
    (hd : Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (𝓝[>] 0) (𝓝 d)) :
    0 ≤ h p - h x - d ∧ (h p - h x - d = 0 ↔ p = x) ∧
      1 / 2 * K * sqDist x p ≤ h p - h x - d := by
  have hK := hpen.2.2.1
  have hb : d + 1 / 2 * K * sqDist x p ≤ h p - h x := by
    apply gap_of_slope hpen hx hp
    intro t ht0 ht1
    have := deriv_le_quot hpen hx hp hd ht0 ht1.le
    rwa [le_div_iff₀ ht0] at this
  have hs := sqDist_nonneg x p
  have hKs : 0 ≤ 1 / 2 * K * sqDist x p := by positivity
  refine ⟨by linarith, ⟨fun h0 => ?_, fun hpx => ?_⟩, by linarith⟩
  · have hz : sqDist x p = 0 := by
      have : 1 / 2 * K * sqDist x p ≤ 0 := by linarith
      nlinarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - p i))).1 hz
    funext i
    have := this i (Finset.mem_univ i)
    have : x i - p i = 0 := by simpa using this
    linarith
  · subst hpx
    have h0 : d = 0 := by
      have : Tendsto (fun t : ℝ => (h (p + t • (p - p)) - h p) / t) (𝓝[>] 0) (𝓝 0) := by
        simp
      exact tendsto_nhds_unique hd this
    rw [h0]; ring

lemma opt_gap {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {y x x' : B → ℝ}
    (hx : IsChoice h y x) (hx' : x' ∈ stdSimplex ℝ B) :
    1 / 2 * K * sqDist x x' ≤ (y ⬝ᵥ x - h x) - (y ⬝ᵥ x' - h x') := by
  have := gap_of_slope hpen hx.1 hx' (m := y ⬝ᵥ (x' - x)) (by
    intro t ht0 ht1
    have h1 := hx.2 _ (line_mem hx.1 hx' ht0.le ht1.le)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
    linarith)
  rw [dotProduct_sub] at this
  linarith

lemma fenchel_ge {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p y x : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) (hx : IsChoice h y x) :
    1 / 2 * K * sqDist x p ≤ fenchelCoupling h p y := by
  have := opt_gap hpen hx hp
  unfold fenchelCoupling
  rw [isChoice_conj hx]
  linarith

lemma choice_deriv {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) {y x : B → ℝ} (hx : IsChoice h y x)
    (hxp : ∀ α, 0 < p α → 0 < x α) :
    HasDerivAt (fun t : ℝ => h (x + t • (p - x))) (y ⬝ᵥ (p - x)) 0 := by
  obtain ⟨d, hd, ε, hε, hmem⟩ := line_deriv hpen hp hx.1 hxp
  have h1 : HasDerivAt (fun t : ℝ => y ⬝ᵥ (x + t • (p - x))) (y ⬝ᵥ (p - x)) 0 := by
    have : (fun t : ℝ => y ⬝ᵥ (x + t • (p - x))) = fun t => y ⬝ᵥ x + t * (y ⬝ᵥ (p - x)) := by
      funext t; rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [this]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (y ⬝ᵥ (p - x))).const_add (y ⬝ᵥ x)
  have hψ := h1.sub hd
  have hmax : IsLocalMax (fun t : ℝ => y ⬝ᵥ (x + t • (p - x)) - h (x + t • (p - x))) 0 := by
    have : ∀ᶠ t in 𝓝 (0:ℝ), |t| < ε :=
      Metric.eventually_nhds_iff.2 ⟨ε, hε, fun t ht => by simpa [Real.dist_eq] using ht⟩
    filter_upwards [this] with t ht
    have := hx.2 _ (hmem t ht)
    simpa using this
  have h2 := hmax.hasDerivAt_eq_zero hψ
  have : d = y ⬝ᵥ (p - x) := by linarith
  rw [← this]; exact hd

lemma fenchel_bdd {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ y x : B → ℝ, IsChoice h y x → (∀ α, 0 < p α → ε ≤ x α) →
      fenchelCoupling h p y ≤ M := by
  obtain ⟨R, hR0, hR⟩ := exists_bound hpen
  refine ⟨2 * R + 2 * R / ε, fun y x hx hxε => ?_⟩
  have ha : x - ε • (p - x) ∈ stdSimplex ℝ B := by
    refine ⟨fun α => ?_, ?_⟩
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hα : 0 < p α
      · have h1 := hxε α hα
        have h2 : p α ≤ 1 := (mem_Icc_of_mem_stdSimplex hp α).2
        nlinarith [mul_le_mul_of_nonneg_left h1 hε.le, mul_le_mul_of_nonneg_left h2 hε.le]
      · have h2 : p α = 0 := le_antisymm (not_lt.1 hα) (hp.1 α)
        rw [h2]; nlinarith [hx.1.1 α]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx.1.2, hp.2]
      ring
  have h1 := hx.2 _ ha
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_sub] at h1
  have h3 := hR _ ha
  have h4 := hR _ hx.1
  have h5 := hR _ hp
  have h6 : -(y ⬝ᵥ (p - x)) ≤ 2 * R / ε := by
    rw [le_div_iff₀ hε, dotProduct_sub]
    have := abs_le.1 h3
    have := abs_le.1 h4
    nlinarith
  rw [fenchel_eq hx]
  have := abs_le.1 h4
  have := abs_le.1 h5
  linarith

lemma tendsto_h {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {zs : ℕ → B → ℝ} {z : B → ℝ}
    (hz : z ∈ stdSimplex ℝ B) (hzs : ∀ᶠ j in atTop, zs j ∈ stdSimplex ℝ B)
    (hl : Tendsto zs atTop (𝓝 z)) : Tendsto (fun j => h (zs j)) atTop (𝓝 (h z)) :=
  (hpen.1 z hz).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hl, hzs⟩)

end Deriv
end RGAux

namespace RGAux
open ReinfRegGames.Extinction Filter Topology

section Small
variable {B : Type*} [Fintype B]

lemma choice_small {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) (α β : B) (hβα : β ≠ α) :
    ∀ ε > 0, ∃ M : ℝ, ∀ y x : B → ℝ, IsChoice h y x → y α - y β < -M → x α < ε := by
  classical
  intro ε hε
  obtain ⟨R, hR0, hR⟩ := exists_bound hpen
  refine ⟨2 * R / ε + 1, fun y x hx hy => ?_⟩
  by_contra hge
  push_neg at hge
  have hs : ∀ a c : B, 0 ≤ (Pi.single a (1:ℝ) : B → ℝ) c := by
    intro a c
    by_cases hc : c = a
    · subst hc; simp
    · simp [Pi.single_eq_of_ne hc]
  have hxa := hx.1.1 α
  have hmem : x + x α • (Pi.single β (1:ℝ) - Pi.single α (1:ℝ)) ∈ stdSimplex ℝ B := by
    refine ⟨fun γ => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      by_cases hγ : γ = α
      · subst hγ
        simp [Pi.single_eq_of_ne hβα.symm]
      · rw [Pi.single_eq_of_ne hγ]
        have := hs β γ
        have := hx.1.1 γ
        nlinarith
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx.1.2]
      simp
  have h1 := hx.2 _ hmem
  rw [dotProduct_add, dotProduct_smul, dotProduct_sub] at h1
  simp only [dotProduct_single, smul_eq_mul, mul_one] at h1
  have h3 := abs_le.1 (hR _ hmem)
  have h4 := abs_le.1 (hR _ hx.1)
  have hM : 0 < y β - y α := by
    have : 0 ≤ 2 * R / ε := by positivity
    linarith
  have h5 : ε * (2 * R / ε + 1) ≤ x α * (y β - y α) :=
    mul_le_mul hge (by linarith) (by positivity) hxa
  have h6 : ε * (2 * R / ε + 1) = 2 * R + ε := by field_simp
  nlinarith

end Small
end RGAux

namespace RGAux
open ReinfRegGames.Extinction Filter Topology

section C2iii
variable {B : Type*} [Fintype B]

lemma back_mem {z p : B → ℝ} (hz : z ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {s : ℝ}
    (hs : 0 ≤ s) (hpos : ∀ α, 0 < p α → 0 < z α - s * (p α - z α)) :
    z - s • (p - z) ∈ stdSimplex ℝ B := by
  refine ⟨fun α => ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hα : 0 < p α
    · exact (hpos α hα).le
    · have h2 : p α = 0 := le_antisymm (not_lt.1 hα) (hp.1 α)
      rw [h2]; nlinarith [hz.1 α]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hz.2, hp.2]
    ring

lemma lower_slope {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {x p : B → ℝ}
    (hx : x ∈ stdSimplex ℝ B) (hp : p ∈ stdSimplex ℝ B) {d : ℝ}
    (hd : Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (𝓝[>] 0) (𝓝 d))
    {s : ℝ} (hs : 0 < s) (ha : x - s • (p - x) ∈ stdSimplex ℝ B) :
    (h x - h (x - s • (p - x))) / s ≤ d := by
  refine ge_of_tendsto hd ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  exact quot_ge hpen hx hp hs ha ht.1 ht.2.le

lemma c2iii_core {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) {xs : ℕ → B → ℝ} {x : B → ℝ} {ds : ℕ → ℝ} {d : ℝ}
    (hxs : ∀ᶠ j in atTop, xs j ∈ stdSimplex ℝ B)
    (hx : x ∈ stdSimplex ℝ B) (hxp : ∀ α, 0 < p α → 0 < x α)
    (hds : ∀ᶠ j in atTop, Tendsto
      (fun t : ℝ => (h (xs j + t • (p - xs j)) - h (xs j)) / t) (𝓝[>] 0) (𝓝 (ds j)))
    (hd : Tendsto (fun t : ℝ => (h (x + t • (p - x)) - h x) / t) (𝓝[>] 0) (𝓝 d))
    (hlim : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun j => h p - h (xs j) - ds j) atTop (𝓝 (h p - h x - d)) := by
  have hh0 := tendsto_h hpen hx hxs hlim
  rw [tendsto_order]
  constructor
  · intro a ha
    have hL : Tendsto (fun t : ℝ => h p - h x - (h (x + t • (p - x)) - h x) / t) (𝓝[>] 0)
        (𝓝 (h p - h x - d)) := tendsto_const_nhds.sub hd
    obtain ⟨t, ht1, ht2⟩ := ((hL.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsGT zero_lt_one)).exists
    have hxt : x + t • (p - x) ∈ stdSimplex ℝ B := line_mem hx hp ht2.1.le ht2.2.le
    have hl2 : Tendsto (fun j => xs j + t • (p - xs j)) atTop (𝓝 (x + t • (p - x))) :=
      hlim.add (tendsto_const_nhds.smul (tendsto_const_nhds.sub hlim))
    have hh1 := tendsto_h hpen hxt
      (by filter_upwards [hxs] with j hj using line_mem hj hp ht2.1.le ht2.2.le) hl2
    have hconv : Tendsto (fun j => h p - h (xs j) -
        (h (xs j + t • (p - xs j)) - h (xs j)) / t) atTop
        (𝓝 (h p - h x - (h (x + t • (p - x)) - h x) / t)) :=
      (tendsto_const_nhds.sub hh0).sub ((hh1.sub hh0).div_const t)
    filter_upwards [hconv.eventually (lt_mem_nhds ht1), hxs, hds] with j hj hxj hdj
    have := deriv_le_quot hpen hxj hp hdj ht2.1 ht2.2.le
    linarith
  · intro a ha
    obtain ⟨d', hd', -⟩ := line_deriv hpen hp hx hxp
    have hdd' : d' = d := tendsto_nhds_unique (oneSided hd') hd
    subst hdd'
    have hleft : Tendsto (fun s : ℝ => (h x - h (x - s • (p - x))) / s) (𝓝[>] 0) (𝓝 d') := by
      have h1 := hd'.tendsto_slope_zero_left
      have hneg : Tendsto (fun s : ℝ => -s) (𝓝[>] 0) (𝓝[<] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · simpa using (continuous_neg.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact Set.mem_Iio.2 (neg_lt_zero.2 hs)
      refine (h1.comp hneg).congr (fun s => ?_)
      simp only [Function.comp, zero_add, neg_smul, zero_smul, add_zero, smul_eq_mul, inv_neg]
      rw [← sub_eq_add_neg, div_eq_inv_mul]
      ring
    have hU : Tendsto (fun s : ℝ => h p - h x - (h x - h (x - s • (p - x))) / s) (𝓝[>] 0)
        (𝓝 (h p - h x - d')) := tendsto_const_nhds.sub hleft
    have hpos0 : ∀ᶠ s in 𝓝 (0:ℝ), ∀ α, 0 < p α → 0 < x α - s * (p α - x α) := by
      rw [Filter.eventually_all]
      intro α
      by_cases hα : 0 < p α
      · have hc : ContinuousAt (fun s : ℝ => x α - s * (p α - x α)) 0 := by fun_prop
        have := ContinuousAt.eventually_lt (continuousAt_const (y := (0:ℝ))) hc
          (by simpa using hxp α hα)
        exact this.mono fun s hs _ => hs
      · exact Eventually.of_forall fun s h => absurd h hα
    obtain ⟨s, hs1, hs2, hs0⟩ := ((hU.eventually (gt_mem_nhds ha)).and
      ((hpos0.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)).exists
    have hs0' : 0 < s := hs0
    have ha_s : x - s • (p - x) ∈ stdSimplex ℝ B := back_mem hx hp hs0'.le hs2
    have hevpos : ∀ᶠ j in atTop, ∀ α, 0 < p α → 0 < xs j α - s * (p α - xs j α) := by
      rw [Filter.eventually_all]
      intro α
      by_cases hα : 0 < p α
      · have hc : Tendsto (fun j => xs j α - s * (p α - xs j α)) atTop
            (𝓝 (x α - s * (p α - x α))) :=
          (tendsto_pi_nhds.1 hlim α).sub
            (tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_pi_nhds.1 hlim α)))
        exact (hc.eventually (lt_mem_nhds (hs2 α hα))).mono fun j hj _ => hj
      · exact Eventually.of_forall fun j h => absurd h hα
    have hla : Tendsto (fun j => xs j - s • (p - xs j)) atTop (𝓝 (x - s • (p - x))) :=
      hlim.sub (tendsto_const_nhds.smul (tendsto_const_nhds.sub hlim))
    have hh2 := tendsto_h hpen ha_s
      (by filter_upwards [hxs, hevpos] with j hj hj2 using back_mem hj hp hs0'.le hj2) hla
    have hconv : Tendsto (fun j => h p - h (xs j) -
        (h (xs j) - h (xs j - s • (p - xs j))) / s) atTop
        (𝓝 (h p - h x - (h x - h (x - s • (p - x))) / s)) :=
      (tendsto_const_nhds.sub hh0).sub ((hh0.sub hh2).div_const s)
    filter_upwards [hconv.eventually (gt_mem_nhds hs1), hxs, hevpos, hds] with j hj hxj hj2 hj3
    have := lower_slope hpen hxj hp hj3 hs0' (back_mem hxj hp hs0'.le hj2)
    linarith

end C2iii
end RGAux

namespace RGAux
open ReinfRegGames.Extinction Filter Topology

section C3C4
variable {B : Type*} [Fintype B]

lemma eventually_supp {p : B → ℝ} {xs : ℕ → B → ℝ} (hlim : Tendsto xs atTop (𝓝 p)) :
    ∀ᶠ j in atTop, ∀ α, 0 < p α → 0 < xs j α := by
  rw [Filter.eventually_all]
  intro α
  by_cases hα : 0 < p α
  · exact ((tendsto_pi_nhds.1 hlim α).eventually (lt_mem_nhds hα)).mono fun j hj _ => hj
  · exact Eventually.of_forall fun j h => absurd h hα

lemma c3_converse {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) {ys xs : ℕ → B → ℝ} (hQ : ∀ j, IsChoice h (ys j) (xs j))
    (hlim : Tendsto xs atTop (𝓝 p)) :
    Tendsto (fun j => fenchelCoupling h p (ys j)) atTop (𝓝 0) := by
  have hev := eventually_supp hlim
  have hds : ∀ᶠ j in atTop, Tendsto
      (fun t : ℝ => (h (xs j + t • (p - xs j)) - h (xs j)) / t) (𝓝[>] 0)
      (𝓝 (ys j ⬝ᵥ (p - xs j))) :=
    hev.mono fun j hj => oneSided (choice_deriv hpen hp (hQ j) hj)
  have hd : Tendsto (fun t : ℝ => (h (p + t • (p - p)) - h p) / t) (𝓝[>] 0) (𝓝 0) := by
    simp
  have := c2iii_core hpen hp (xs := xs) (x := p) (ds := fun j => ys j ⬝ᵥ (p - xs j)) (d := 0)
    (Eventually.of_forall fun j => (hQ j).1) hp (fun α hα => hα) hds hd hlim
  rw [sub_self, zero_sub, neg_zero] at this
  refine this.congr (fun j => ?_)
  rw [fenchel_eq (hQ j)]

lemma tendsto_of_sqDist {p : B → ℝ} {xs : ℕ → B → ℝ}
    (hsq : Tendsto (fun j => sqDist (xs j) p) atTop (𝓝 0)) : Tendsto xs atTop (𝓝 p) := by
  refine tendsto_pi_nhds.2 fun α => ?_
  rw [tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun j => Real.sqrt (sqDist (xs j) p)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) h1
  rw [Real.dist_eq]
  apply Real.abs_le_sqrt
  unfold sqDist
  exact Finset.single_le_sum (f := fun β => (xs j β - p β) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ α)

lemma c3_forward {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) {ys xs : ℕ → B → ℝ} (hQ : ∀ j, IsChoice h (ys j) (xs j))
    (hF : Tendsto (fun j => fenchelCoupling h p (ys j)) atTop (𝓝 0)) :
    Tendsto xs atTop (𝓝 p) := by
  have hK := hpen.2.2.1
  apply tendsto_of_sqDist
  have h2 : Tendsto (fun j => 2 / K * fenchelCoupling h p (ys j)) atTop (𝓝 0) := by
    simpa using hF.const_mul (2 / K)
  refine squeeze_zero (fun j => sqDist_nonneg _ _) (fun j => ?_) h2
  have := fenchel_ge hpen hp (hQ j)
  rw [div_mul_eq_mul_div, le_div_iff₀ hK]
  nlinarith

lemma not_frequently_big {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) {ys xs : ℕ → B → ℝ} (hQ : ∀ j, IsChoice h (ys j) (xs j))
    (hF : Tendsto (fun j => fenchelCoupling h p (ys j)) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ᶠ j in atTop, ∀ α, 0 < p α → ε ≤ xs j α := by
  intro hfreq
  obtain ⟨M, hM⟩ := fenchel_bdd hpen hp hε
  obtain ⟨j, hj1, hj2⟩ := (hfreq.and_eventually (hF.eventually_gt_atTop M)).exists
  exact absurd (hM _ _ (hQ j) hj1) (not_le.2 hj2)

lemma c4_main {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) {p : B → ℝ}
    (hp : p ∈ stdSimplex ℝ B) {ys xs : ℕ → B → ℝ} (hQ : ∀ j, IsChoice h (ys j) (xs j))
    (hF : Tendsto (fun j => fenchelCoupling h p (ys j)) atTop atTop) :
    (∀ z ∈ deltaP p, ¬ MapClusterPt z atTop xs) ∧
      ∀ ε > 0, ∀ N : ℕ, ∃ j ≥ N, ∃ α, 0 < p α ∧ xs j α < ε := by
  refine ⟨fun z hz hcl => ?_, fun ε hε N => ?_⟩
  · have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ α, 0 < p α → ε < z α := by
      have : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ α, 0 < p α → ε < z α := by
        rw [Filter.eventually_all]
        intro α
        by_cases hα : 0 < p α
        · exact (gt_mem_nhds (hz.2 α hα)).mono fun ε h _ => h
        · exact Eventually.of_forall fun ε h => absurd h hα
      exact this.filter_mono nhdsWithin_le_nhds
    obtain ⟨ε, hε1, hε2⟩ := (hev.and self_mem_nhdsWithin).exists
    have hε0 : 0 < ε := hε2
    have hU : {x : B → ℝ | ∀ α, 0 < p α → ε ≤ x α} ∈ 𝓝 z := by
      have : ∀ᶠ x in 𝓝 z, ∀ α, 0 < p α → ε < x α := by
        rw [Filter.eventually_all]
        intro α
        by_cases hα : 0 < p α
        · exact (((continuous_apply α).tendsto z).eventually (lt_mem_nhds (hε1 α hα))).mono
            fun x h _ => h
        · exact Eventually.of_forall fun x h => absurd h hα
      exact this.mono fun x hx α hα => (hx α hα).le
    have hfreq := mapClusterPt_iff_frequently.1 hcl _ hU
    exact not_frequently_big hpen hp hQ hF hε0 hfreq
  · by_contra hcon
    push_neg at hcon
    have := not_frequently_big hpen hp hQ hF hε
    apply this
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop N] with j hj α hα
    exact (hcon j hj α hα)

end C3C4
end RGAux

namespace RGAux
open ReinfRegGames.Extinction Filter Topology

section C1
variable {B : Type*} [Fintype B]

lemma choice_lipschitz [Nonempty B] {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K) :
    ∃ L : ℝ, ∀ y y' x x' : B → ℝ, IsChoice h y x → IsChoice h y' x' →
      dist x x' ≤ L * dist y y' := by
  have hK := hpen.2.2.1
  refine ⟨Fintype.card B / K, fun y y' x x' hx hx' => ?_⟩
  have h1 := opt_gap hpen hx hx'.1
  have h2 := opt_gap hpen hx' hx.1
  rw [sqDist_comm x' x] at h2
  have h3 : K * sqDist x x' ≤ ∑ β, (y β - y' β) * (x β - x' β) := by
    have : ∑ β, (y β - y' β) * (x β - x' β) =
        (y ⬝ᵥ x - y ⬝ᵥ x' - (y' ⬝ᵥ x - y' ⬝ᵥ x')) := by
      simp only [dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [this]; linarith
  obtain ⟨β0, -, hβ0⟩ := Finset.exists_max_image Finset.univ (fun β => |x β - x' β|)
    Finset.univ_nonempty
  set m := |x β0 - x' β0| with hmdef
  have hm : ∀ β, |x β - x' β| ≤ m := fun β => hβ0 β (Finset.mem_univ β)
  set D := dist y y' with hDdef
  have hD : ∀ β, |y β - y' β| ≤ D := fun β => by
    have := dist_le_pi_dist y y' β
    rwa [Real.dist_eq] at this
  have hdist : dist x x' ≤ m := by
    rw [dist_pi_le_iff (abs_nonneg _)]
    intro β
    rw [Real.dist_eq]
    exact hm β
  have hsq : m ^ 2 ≤ sqDist x x' := by
    unfold sqDist
    have := Finset.single_le_sum (f := fun β => (x β - x' β) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ β0)
    simpa [hmdef, sq_abs] using this
  have hD0 : 0 ≤ D := dist_nonneg
  have hm0 : 0 ≤ m := abs_nonneg _
  have h4 : ∑ β, (y β - y' β) * (x β - x' β) ≤ Fintype.card B * (D * m) := by
    calc ∑ β, (y β - y' β) * (x β - x' β) ≤ ∑ _β : B, D * m := by
          apply Finset.sum_le_sum
          intro β _
          calc (y β - y' β) * (x β - x' β) ≤ |(y β - y' β) * (x β - x' β)| := le_abs_self _
            _ = |y β - y' β| * |x β - x' β| := abs_mul _ _
            _ ≤ D * m := mul_le_mul (hD β) (hm β) (abs_nonneg _) hD0
      _ = Fintype.card B * (D * m) := by simp
  have hcard : (0:ℝ) ≤ Fintype.card B := Nat.cast_nonneg _
  by_cases hm0' : m = 0
  · have : dist x x' ≤ 0 := hdist.trans (le_of_eq hm0')
    exact this.trans (by positivity)
  · have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm0')
    have h5 : K * m ^ 2 ≤ Fintype.card B * (D * m) := by nlinarith
    have h6 : K * m ≤ Fintype.card B * D := by
      have : m * (K * m) ≤ m * (Fintype.card B * D) := by nlinarith
      exact le_of_mul_le_mul_left this hmpos
    calc dist x x' ≤ m := hdist
      _ ≤ Fintype.card B / K * D := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hK]; linarith

lemma conj_hasFDerivAt [Nonempty B] {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K)
    {y x : B → ℝ} (hx : IsChoice h y x) :
    HasFDerivAt (conj h)
      (∑ β, x β • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : B => ℝ) β) y := by
  obtain ⟨L, hL⟩ := choice_lipschitz hpen
  have hA : ∀ v : B → ℝ, (∑ β, x β • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : B => ℝ) β) v
      = x ⬝ᵥ v := by
    intro v
    simp [dotProduct, ContinuousLinearMap.sum_apply]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hn : (0:ℝ) ≤ Fintype.card B := Nat.cast_nonneg _
  have hCpos : 0 < (Fintype.card B : ℝ) * |L| + 1 := by positivity
  have hball : ∀ᶠ v : B → ℝ in 𝓝 0, ‖v‖ < c / ((Fintype.card B : ℝ) * |L| + 1) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds (0 : B → ℝ)
        (show 0 < c / ((Fintype.card B : ℝ) * |L| + 1) by positivity))
      (fun v hv => by simpa using hv)
  filter_upwards [hball] with v hv
  obtain ⟨x', hx'⟩ := exists_choice hpen (y + v)
  have e1 := isChoice_conj hx
  have e2 := isChoice_conj hx'
  have lo : (y + v) ⬝ᵥ x - h x ≤ conj h (y + v) := by
    rw [e2]; exact hx'.2 x hx.1
  have up : conj h (y + v) - conj h y ≤ v ⬝ᵥ x' := by
    rw [e1, e2]
    have := hx.2 x' hx'.1
    rw [add_dotProduct]
    linarith
  rw [hA]
  have hE0 : 0 ≤ conj h (y + v) - conj h y - x ⬝ᵥ v := by
    rw [e1] at *
    rw [add_dotProduct, dotProduct_comm v x] at *
    linarith
  have hE1 : conj h (y + v) - conj h y - x ⬝ᵥ v ≤ v ⬝ᵥ (x' - x) := by
    rw [dotProduct_sub, dotProduct_comm x v]
    linarith
  have hdist : dist x' x ≤ |L| * ‖v‖ := by
    have := hL (y + v) y x' x hx' hx
    have e : dist (y + v) y = ‖v‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
  have hsum : v ⬝ᵥ (x' - x) ≤ Fintype.card B * (‖v‖ * (|L| * ‖v‖)) := by
    calc v ⬝ᵥ (x' - x) = ∑ β, v β * (x' β - x β) := rfl
      _ ≤ ∑ _β : B, ‖v‖ * (|L| * ‖v‖) := by
          apply Finset.sum_le_sum
          intro β _
          calc v β * (x' β - x β) ≤ |v β * (x' β - x β)| := le_abs_self _
            _ = |v β| * |x' β - x β| := abs_mul _ _
            _ ≤ ‖v‖ * (|L| * ‖v‖) := by
                apply mul_le_mul _ _ (abs_nonneg _) (norm_nonneg _)
                · simpa using norm_le_pi_norm v β
                · have := dist_le_pi_dist x' x β
                  rw [Real.dist_eq] at this
                  exact this.trans hdist
      _ = Fintype.card B * (‖v‖ * (|L| * ‖v‖)) := by simp
  rw [Real.norm_eq_abs, abs_of_nonneg hE0]
  have hv' : ‖v‖ * ((Fintype.card B : ℝ) * |L| + 1) < c := by
    rwa [lt_div_iff₀ hCpos] at hv
  have hv0 := norm_nonneg v
  have hL0 := abs_nonneg L
  have : Fintype.card B * (‖v‖ * (|L| * ‖v‖)) = ‖v‖ * ((Fintype.card B : ℝ) * |L| * ‖v‖) := by ring
  nlinarith [mul_nonneg hv0 hv0, mul_nonneg (mul_nonneg hn hL0) (mul_nonneg hv0 hv0)]

end C1

section Mono
variable {B : Type*} [Fintype B]

lemma erase_sum_eq [DecidableEq B] (y : B → ℝ) (a : B) {x : B → ℝ} (hx : x ∈ stdSimplex ℝ B) :
    ∑ μ ∈ Finset.univ.erase a, x μ * (y μ - y a) = y ⬝ᵥ x - y a := by
  rw [Finset.sum_erase _ (by simp)]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx.2, one_mul]
  simp [dotProduct, mul_comm]

lemma monotone_step_core [DecidableEq B] {h : (B → ℝ) → ℝ} {K : ℝ} (hpen : IsPenalty h K)
    (αstar : B) (y y' : B → ℝ) :
    conj h y - y αstar =
        sSup ((fun x => (∑ μ ∈ Finset.univ.erase αstar, x μ * (y μ - y αstar)) - h x) ''
          stdSimplex ℝ B) ∧
      ((∀ μ, μ ≠ αstar → y' μ - y' αstar < y μ - y αstar) →
        conj h y' - y' αstar ≤ conj h y - y αstar) := by
  haveI : Nonempty B := ⟨αstar⟩
  obtain ⟨x, hx⟩ := exists_choice hpen y
  have hconj := isChoice_conj hx
  constructor
  · symm
    have : IsGreatest ((fun x => (∑ μ ∈ Finset.univ.erase αstar, x μ * (y μ - y αstar)) - h x) ''
          stdSimplex ℝ B) (conj h y - y αstar) := by
      refine ⟨⟨x, hx.1, ?_⟩, ?_⟩
      · simp only [erase_sum_eq y αstar hx.1, hconj]; ring
      · rintro _ ⟨x', hx', rfl⟩
        simp only [erase_sum_eq y αstar hx', hconj]
        have := hx.2 x' hx'
        linarith
    exact this.csSup_eq
  · intro hlt
    obtain ⟨x', hx'⟩ := exists_choice hpen y'
    have e2 := isChoice_conj hx'
    have h1 := erase_sum_eq y' αstar hx'.1
    have h2 : ∑ μ ∈ Finset.univ.erase αstar, x' μ * (y' μ - y' αstar) ≤
        ∑ μ ∈ Finset.univ.erase αstar, x' μ * (y μ - y αstar) := by
      apply Finset.sum_le_sum
      intro μ hμ
      exact mul_le_mul_of_nonneg_left (hlt μ (Finset.ne_of_mem_erase hμ)).le (hx'.1.1 μ)
    rw [erase_sum_eq y αstar hx'.1] at h2
    have := hx.2 x' hx'.1
    rw [hconj]
    linarith

end Mono
end RGAux

open ReinfRegGames.Extinction Filter Topology in
theorem solution {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : IsPenalty h K)
    (p : B → ℝ) (hp : p ∈ stdSimplex ℝ B) (ys xs : ℕ → B → ℝ)
    (hQ : ∀ j, IsChoice h (ys j) (xs j))
    (hF : Tendsto (fun j => fenchelCoupling h p (ys j)) atTop atTop) :
    (∀ z ∈ deltaP p, ¬ MapClusterPt z atTop xs) ∧
      ∀ ε > 0, ∀ N : ℕ, ∃ j ≥ N, ∃ α, 0 < p α ∧ xs j α < ε :=
  RGAux.c4_main hpen hp hQ hF
