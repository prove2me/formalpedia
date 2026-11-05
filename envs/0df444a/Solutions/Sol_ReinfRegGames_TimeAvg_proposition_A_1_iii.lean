-- Prove2me | solution 1 for ReinfRegGames.TimeAvg.proposition_A_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:34:33.232194+00:00
-- url     : https://prove2.me/submissions/469ecdc8-4b70-4607-8506-15ebac43997e

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

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

theorem solution {B : Type*} [Fintype B] [DecidableEq B]
    (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K) (α β : B) (hαβ : β ≠ α) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ y x : B → ℝ, ReinfRegGames.Extinction.IsChoice h y x → y α - y β < -M → x α < ε :=
  RGAux.choice_small hpen α β hαβ
