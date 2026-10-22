-- Prove2me | solution 1 for QiNonsmoothEq.Attraction.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:02:15.123109+00:00
-- url     : https://prove2.me/submissions/5f8091a9-cf2d-4c1f-bac3-3ec419e2ab84

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local


namespace QiNonsmoothEq.Attraction

section g52
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma g52_hasDir_smul (F : E → G) (x h : E) (d : G) (t : ℝ) (ht : 0 < t)
    (h1 : HasDirDerivAt F x h d) : HasDirDerivAt F x (t • h) (t • d) := by
  have hm : Tendsto (fun s : ℝ => s * t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun s : ℝ => s * t) (𝓝 0) (𝓝 (0 * t)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hs ht
  have h2 := (h1.comp hm).const_smul t
  unfold HasDirDerivAt
  refine h2.congr (fun s => ?_)
  simp only [Function.comp]
  rw [smul_smul, mul_smul s t h]
  congr 1
  field_simp

lemma g52_hasDir_unique (F : E → G) (x h : E) (d : G) (h1 : HasDirDerivAt F x h d) :
    dirDeriv F x h = d := h1.limUnder_eq

lemma g52_dirDeriv_smul (F : E → G) (x h : E) (hex : ∃ d, HasDirDerivAt F x h d) (t : ℝ)
    (ht : 0 < t) : dirDeriv F x (t • h) = t • dirDeriv F x h := by
  obtain ⟨d, hd⟩ := hex
  rw [g52_hasDir_unique F x h d hd, g52_hasDir_unique F x (t • h) (t • d) (g52_hasDir_smul F x h d t ht hd)]

lemma g52_hasDir_dirDeriv (F : E → G) (x h : E) (hex : ∃ d, HasDirDerivAt F x h d) :
    HasDirDerivAt F x h (dirDeriv F x h) := by
  obtain ⟨d, hd⟩ := hex
  rw [g52_hasDir_unique F x h d hd]; exact hd

lemma g52_dirDeriv_lip (F : E → G) (hF : LocallyLipschitz F) (x : E)
    (hdd : ∀ h, ∃ d, HasDirDerivAt F x h d) :
    ∃ K : ℝ, ∀ h h' : E, ‖dirDeriv F x h - dirDeriv F x h'‖ ≤ K * ‖h - h'‖ := by
  obtain ⟨K, T, hT, hK⟩ := hF x
  refine ⟨K, fun h h' => ?_⟩
  have h1 := g52_hasDir_dirDeriv F x h (hdd h)
  have h2 := g52_hasDir_dirDeriv F x h' (hdd h')
  have h3 := (h1.sub h2).norm
  unfold HasDirDerivAt at h1 h2
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), ‖s⁻¹ • (F (x + s • h) - F x) - s⁻¹ • (F (x + s • h') - F x)‖
      ≤ K * ‖h - h'‖ := by
    have c1 : Tendsto (fun s : ℝ => x + s • h) (𝓝 0) (𝓝 x) := by
      have : Continuous (fun s : ℝ => x + s • h) := by fun_prop
      simpa using this.tendsto 0
    have c2 : Tendsto (fun s : ℝ => x + s • h') (𝓝 0) (𝓝 x) := by
      have : Continuous (fun s : ℝ => x + s • h') := by fun_prop
      simpa using this.tendsto 0
    have e1 := (c1.mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))) hT
    have e2 := (c2.mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))) hT
    filter_upwards [e1, e2, self_mem_nhdsWithin] with s hs1 hs2 hs
    have hs' : (0:ℝ) < s := hs
    have := hK.dist_le_mul _ hs1 _ hs2
    rw [dist_eq_norm, dist_eq_norm] at this
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs'.le)]
    have e : F (x + s • h) - F x - (F (x + s • h') - F x) = F (x + s • h) - F (x + s • h') := by abel
    rw [e]
    have e' : x + s • h - (x + s • h') = s • (h - h') := by rw [smul_sub]; abel
    rw [e', norm_smul, Real.norm_of_nonneg hs'.le] at this
    calc s⁻¹ * ‖F (x + s • h) - F (x + s • h')‖ ≤ s⁻¹ * (K * (s * ‖h - h'‖)) := by gcongr
      _ = K * ‖h - h'‖ := by field_simp
  exact le_of_tendsto h3 hev

end g52

lemma g52_lemma24 {n m : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) (hreg : BDRegularAt F x) :
    ∃ c : ℝ, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F x h‖ := by
  obtain ⟨hdd, hne⟩ := hreg
  obtain ⟨K, hK⟩ := g52_dirDeriv_lip F hF x hdd
  have hcont : Continuous (fun h : EuclideanSpace ℝ (Fin n) => ‖dirDeriv F x h‖) := by
    have : LipschitzWith (Real.toNNReal K) (fun h : EuclideanSpace ℝ (Fin n) => dirDeriv F x h) := by
      refine LipschitzWith.of_dist_le_mul (fun h h' => ?_)
      rw [dist_eq_norm, dist_eq_norm]
      calc _ ≤ K * ‖h - h'‖ := hK h h'
        _ ≤ _ := by
          have : ((Real.toNNReal K : NNReal) : ℝ) = max K 0 := rfl
          rw [this]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    exact continuous_norm.comp this.continuous
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 → m ≤ ‖dirDeriv F x u‖ := by
    by_cases hS : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty
    · obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hS
        hcont.continuousOn
      have hu0n : ‖u0‖ = 1 := by simpa using hu0
      have hu0ne : u0 ≠ 0 := by intro h; rw [h] at hu0n; simp at hu0n
      refine ⟨‖dirDeriv F x u0‖, norm_pos_iff.mpr (hne u0 hu0ne), fun u hu => ?_⟩
      exact hmin (by simpa using hu)
    · refine ⟨1, one_pos, fun u hu => ?_⟩
      exact absurd ⟨u, by simpa using hu⟩ hS
  obtain ⟨m, hmpos, hmu⟩ := hm
  refine ⟨m⁻¹, fun h => ?_⟩
  by_cases h0 : h = 0
  · subst h0; rw [norm_zero]; positivity
  · have hpos : 0 < ‖h‖ := norm_pos_iff.mpr h0
    set u := ‖h‖⁻¹ • h with hu
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm]; field_simp
    have hhu : h = ‖h‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    have hD : dirDeriv F x h = ‖h‖ • dirDeriv F x u := by
      conv_lhs => rw [hhu]
      exact g52_dirDeriv_smul F x u (hdd u) _ hpos
    have : m * ‖h‖ ≤ ‖dirDeriv F x h‖ := by
      rw [hD, norm_smul, norm_norm]
      nlinarith [hmu u hun]
    rw [inv_mul_eq_div, le_div_iff₀ hmpos]
    linarith

lemma g52_errbd {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 
    (xstar : EuclideanSpace ℝ (Fin n)) (hBx : QiNonsmoothEq.Local.BDiffAt F xstar) (hzero : F xstar = 0)
    (c : ℝ) (hc : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F xstar h‖) :
    ∀ δ₁ : ℝ, 0 < δ₁ → ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧
      ∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ ≤ δ → ‖y - xstar‖ ≤ 2 * c * ‖F y‖ := by
  intro δ₁ hδ₁
  by_cases hc0 : c ≤ 0
  · refine ⟨δ₁ / 2, by positivity, by linarith, fun y _ => ?_⟩
    have h1 := hc (y - xstar)
    have h2 : c * ‖dirDeriv F xstar (y - xstar)‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc0 (norm_nonneg _)
    have h3 : y - xstar = 0 := norm_le_zero_iff.mp (h1.trans h2)
    have h4 : y = xstar := sub_eq_zero.mp h3
    rw [h4, hzero]; simp
  · push_neg at hc0
    obtain ⟨_, hlim⟩ := hBx
    have hη : (0:ℝ) < 1 / (2 * c) := by positivity
    have hev := (hlim.eventually (gt_mem_nhds hη))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ρ, hρ, hball⟩ := hev
    refine ⟨min ρ δ₁ / 2, by positivity, ?_, fun y hy => ?_⟩
    · have := min_le_right ρ δ₁; linarith
    · obtain ⟨h, rfl⟩ : ∃ h, y = xstar + h := ⟨y - xstar, by abel⟩
      have hy2 : xstar + h - xstar = h := by abel
      rw [hy2] at hy ⊢
      by_cases h0 : h = 0
      · rw [h0]; simp; positivity
      · have hhn : ‖h‖ < ρ := by
          have : (0:ℝ) < min ρ δ₁ := by positivity
          linarith [min_le_left ρ δ₁]
        have h6 := hball (y := h) (by simpa using hhn) h0
        have hpos : 0 < ‖h‖ := norm_pos_iff.mpr h0
        rw [inv_mul_eq_div, div_lt_iff₀ hpos] at h6
        have h5 := h6.le
        rw [hzero, sub_zero] at h5
        have h7 : ‖dirDeriv F xstar h‖ - ‖F (xstar + h)‖ ≤ ‖F (xstar + h) - dirDeriv F xstar h‖ := by
          have := norm_sub_norm_le (dirDeriv F xstar h) (F (xstar + h))
          rwa [norm_sub_rev] at this
        have h8 : ‖dirDeriv F xstar h‖ - ‖F (xstar + h)‖ ≤ 1 / (2 * c) * ‖h‖ := h7.trans h5
        have h9 : 2 * c * (1 / (2 * c) * ‖h‖) = ‖h‖ := by field_simp
        have h10 := hc h
        nlinarith

lemma g52_trap {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xstar : EuclideanSpace ℝ (Fin n)) (hBx : QiNonsmoothEq.Local.BDiffAt F xstar) (hzero : F xstar = 0)
    (c : ℝ) (hc : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F xstar h‖)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 ≤ α k)
    (hdesc : ∀ k, ‖F (x (k + 1))‖ ≤ ‖F (x k)‖)
    (δ₁ s p : ℝ) (hδ₁ : 0 < δ₁) (hs : 0 < s) (hp : 0 < p)
    (hloc : ∀ k, ‖x k - xstar‖ ≤ δ₁ → α k ≤ s ∧ ‖d k‖ ≤ p * ‖F (x k)‖) :
    ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ k : ℕ,
      (‖x k - xstar‖ ≤ ε ∧ ‖F (x k)‖ ≤ ε / (2 * c + s * p)) →
      (‖x (k + 1) - xstar‖ ≤ ε ∧ ‖F (x (k + 1))‖ ≤ ε / (2 * c + s * p)) := by
  by_cases hc0 : c ≤ 0
  · refine ⟨δ₁ / 2, by positivity, by linarith, fun ε hε _ k ⟨_, h2⟩ => ⟨?_, (hdesc k).trans h2⟩⟩
    have h1 := hc (x (k + 1) - xstar)
    have h2 : c * ‖dirDeriv F xstar (x (k + 1) - xstar)‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc0 (norm_nonneg _)
    have h3 : x (k + 1) - xstar = 0 := norm_le_zero_iff.mp (h1.trans h2)
    rw [h3]; simpa using hε.le
  · push_neg at hc0
    obtain ⟨δ, hδ, hδ1, hb⟩ := g52_errbd F xstar hBx hzero c hc δ₁ hδ₁
    refine ⟨δ, hδ, hδ1, fun ε hε hεδ k ⟨h1, h2⟩ => ⟨?_, (hdesc k).trans h2⟩⟩
    have hq : 0 < 2 * c + s * p := by positivity
    have e1 := hb (x k) (h1.trans hεδ.le)
    obtain ⟨hαs, hdp⟩ := hloc k (h1.trans (hεδ.le.trans hδ1.le))
    have e3 : ‖F (x k)‖ * (2 * c + s * p) ≤ ε := (le_div_iff₀ hq).mp h2
    have : x (k + 1) - xstar = (x k - xstar) + α k • d k := by rw [hstep]; abel
    rw [this]
    calc ‖(x k - xstar) + α k • d k‖ ≤ ‖x k - xstar‖ + ‖α k • d k‖ := norm_add_le _ _
      _ = ‖x k - xstar‖ + α k * ‖d k‖ := by rw [norm_smul, Real.norm_of_nonneg (hα k)]
      _ ≤ 2 * c * ‖F (x k)‖ + s * (p * ‖F (x k)‖) := by
          gcongr
      _ ≤ ε := by nlinarith

lemma g52_main {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (hB : ∀ y, QiNonsmoothEq.Local.BDiffAt F y)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 ≤ α k)
    (hdesc : ∀ k, ‖F (x (k + 1))‖ ≤ ‖F (x k)‖)
    (xstar : EuclideanSpace ℝ (Fin n)) (hclu : MapClusterPt xstar atTop x)
    (hzero : F xstar = 0) (hreg : BDRegularAt F xstar)
    (δ₁ s p : ℝ) (hδ₁ : 0 < δ₁) (hs : 0 < s) (hp : 0 < p)
    (hloc : ∀ k, ‖x k - xstar‖ ≤ δ₁ → α k ≤ s ∧ ‖d k‖ ≤ p * ‖F (x k)‖) :
    Tendsto x atTop (𝓝 xstar) := by
  obtain ⟨c0, hc0⟩ := g52_lemma24 F hF xstar hreg
  set c := max c0 1 with hcdef
  have hcpos : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F xstar h‖ := fun h =>
    (hc0 h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨δ, hδ, hδ1, htrap⟩ := g52_trap F xstar (hB xstar) hzero c hc x d α hstep hα hdesc δ₁ s p
    hδ₁ hs hp hloc
  have hq : 0 < 2 * c + s * p := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε₀ := min (ε / 2) (δ / 2) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hε₀δ : ε₀ < δ := by have := min_le_right (ε / 2) (δ / 2); linarith
  have hε₀ε : ε₀ ≤ ε / 2 := min_le_left _ _
  have hFc : ContinuousAt F xstar := hF.continuous.continuousAt
  have hsmall : ∀ᶠ y in 𝓝 xstar, ‖F y‖ ≤ ε₀ / (2 * c + s * p) := by
    have h0 : Tendsto (fun y => ‖F y‖) (𝓝 xstar) (𝓝 0) := by
      have := hFc.tendsto.norm
      rwa [hzero, norm_zero] at this
    exact h0.eventually (ge_mem_nhds (by positivity))
  have hnear : ∀ᶠ y in 𝓝 xstar, ‖y - xstar‖ ≤ ε₀ := by
    have : ∀ᶠ y in 𝓝 xstar, dist y xstar < ε₀ := Metric.ball_mem_nhds xstar hε₀pos
    filter_upwards [this] with y hy
    rw [← dist_eq_norm]; exact hy.le
  have hfreq := (mapClusterPt_iff_frequently.mp hclu) _ (hsmall.and hnear)
  obtain ⟨k, hk1, hk2⟩ := hfreq.exists
  refine ⟨k, fun j hj => ?_⟩
  have key : ‖x j - xstar‖ ≤ ε₀ ∧ ‖F (x j)‖ ≤ ε₀ / (2 * c + s * p) := by
    induction j, hj using Nat.le_induction with
    | base => exact ⟨hk2, hk1⟩
    | succ j _ ih => exact htrap ε₀ hε₀pos hε₀δ j ih
  rw [dist_eq_norm]
  linarith [key.1]

end QiNonsmoothEq.Attraction

open QiNonsmoothEq.Attraction


theorem solution {n m : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) (hreg : BDRegularAt F x) :
    ∃ c : ℝ, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F x h‖ := by
  exact g52_lemma24 F hF x hreg
