-- Prove2me | solution 1 for PLIAG.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T20:29:13.514813+00:00
-- url     : https://prove2.me/submissions/526962a8-a635-4c61-8ac7-b0854bed0cec

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_IsLegendre
import Definitions.Def_PLIAG_bregman
import Definitions.Def_PLIAG_Phi
import Definitions.Def_PLIAG_optSet
import Definitions.Def_PLIAG_AssumptionB1
import Definitions.Def_PLIAG_AssumptionB2
import Definitions.Def_PLIAG_AssumptionB4
import Definitions.Def_PLIAG_Phik
import Definitions.Def_PLIAG_Delta

open Filter Topology

namespace PL41

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma slope_le {g : ℝ → ℝ} {c b : ℝ} (hg : HasDerivAt g c 0)
    (h : ∀ t ∈ Set.Ioo (0:ℝ) 1, g t - g 0 ≤ b * t) : c ≤ b := by
  have ht := hg.tendsto_slope_zero_right
  apply le_of_tendsto ht
  have : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [this] with t htt
  have := h t htt
  simp only [zero_add, smul_eq_mul]
  rw [inv_mul_le_iff₀ htt.1]; linarith

lemma line_deriv {φ : E → ℝ} {p : E} (hd : DifferentiableAt ℝ φ p) (v : E) :
    HasDerivAt (fun t : ℝ => φ (p + t • v)) (fderiv ℝ φ p v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add p
  have h2 : HasFDerivAt φ (fderiv ℝ φ p) ((fun t : ℝ => p + t • v) 0) := by
    simpa using hd.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℝ) hl

lemma combo_eq (a b : E) (t : ℝ) : (1 - t) • a + t • b = a + t • (b - a) := by
  rw [smul_sub, sub_smul, one_smul]; abel

lemma grad_ineq {S : Set E} {φ : E → ℝ} (hφ : ConvexOn ℝ S φ) {p z : E} (hp : p ∈ S)
    (hz : z ∈ S) (hd : DifferentiableAt ℝ φ p) : φ p + fderiv ℝ φ p (z - p) ≤ φ z := by
  have := slope_le (b := φ z - φ p) (line_deriv hd (z - p)) (by
    intro t ht
    have h1 := hφ.2 hp hz (show (0:ℝ) ≤ 1 - t by linarith [ht.2]) ht.1.le
      (show 1 - t + t = 1 by ring)
    rw [combo_eq] at h1; simp only [smul_eq_mul] at h1
    simp only [zero_smul, add_zero]; nlinarith)
  linarith

lemma inner_grad [CompleteSpace E] (φ : E → ℝ) (p v : E) :
    inner ℝ (gradient φ p) v = fderiv ℝ φ p v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma ereal_conv (F : E → EReal) (hbot : ∀ x, F x ≠ ⊥)
    (hc : Convex ℝ {p : E × ℝ | F p.1 ≤ (p.2 : EReal)}) :
    Convex ℝ (AubinLipschitz.effDom F) ∧
      ConvexOn ℝ (AubinLipschitz.effDom F) (fun x => (F x).toReal) := by
  have key : ∀ a ∈ AubinLipschitz.effDom F, ∀ b ∈ AubinLipschitz.effDom F, ∀ θ η : ℝ,
      0 ≤ θ → 0 ≤ η → θ + η = 1 →
      F (θ • a + η • b) ≤ ((θ * (F a).toReal + η * (F b).toReal : ℝ) : EReal) := by
    intro a ha b hb θ η hθ hη hθη
    have h1 : (a, (F a).toReal) ∈ {p : E × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      show F a ≤ ((F a).toReal : EReal); rw [EReal.coe_toReal ha (hbot a)]
    have h2 : (b, (F b).toReal) ∈ {p : E × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      show F b ≤ ((F b).toReal : EReal); rw [EReal.coe_toReal hb (hbot b)]
    have := hc h1 h2 hθ hη hθη
    simpa using this
  refine ⟨?_, ?_⟩
  · intro a ha b hb θ η hθ hη hθη
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (key a ha b hb θ η hθ hη hθη)
  · refine ⟨?_, ?_⟩
    · intro a ha b hb θ η hθ hη hθη
      exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (key a ha b hb θ η hθ hη hθη)
    · intro a ha b hb θ η hθ hη hθη
      have := EReal.toReal_le_toReal (key a ha b hb θ η hθ hη hθη) (hbot _) (EReal.coe_ne_top _)
      rw [EReal.toReal_coe] at this
      simpa using this

lemma coe_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ((∑ i ∈ s, g i : ℝ) : EReal) = ∑ i ∈ s, (g i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma sum_toReal {ι : Type*} (s : Finset ι) (g : ι → EReal) (h1 : ∀ i ∈ s, g i ≠ ⊤)
    (h2 : ∀ i ∈ s, g i ≠ ⊥) : ∑ i ∈ s, g i = ((∑ i ∈ s, (g i).toReal : ℝ) : EReal) := by
  rw [coe_sum]; exact Finset.sum_congr rfl (fun i hi => (EReal.coe_toReal (h1 i hi) (h2 i hi)).symm)

lemma sum_ne_bot {ι : Type*} (s : Finset ι) (g : ι → EReal) (h2 : ∀ i ∈ s, g i ≠ ⊥) :
    ∑ i ∈ s, g i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal.add_ne_bot_iff.2 ⟨h2 a (Finset.mem_insert_self _ _),
      ih (fun i hi => h2 i (Finset.mem_insert_of_mem hi))⟩

lemma ne_top_left {a b : EReal} (h : a + b ≠ ⊤) (hb : b ≠ ⊥) : a ≠ ⊤ := by
  rintro rfl; exact h (EReal.top_add_of_ne_bot hb)

lemma ne_top_right {a b : EReal} (h : a + b ≠ ⊤) (ha : a ≠ ⊥) : b ≠ ⊤ := by
  rintro rfl; exact h (EReal.add_top_of_ne_bot ha)

/-- Essential smoothness forces a point with a uniform linear lower bound on increments toward an
interior point to be interior. -/
lemma interior_of_min {d : ℕ} (W : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (hDc : Convex ℝ D) (hW : ConvexOn ℝ D W)
    (dW : DifferentiableOn ℝ W (interior D))
    (hess : ∀ (u : ℕ → EuclideanSpace ℝ (Fin d)) (xb : EuclideanSpace ℝ (Fin d)),
      xb ∈ frontier D → (∀ k, u k ∈ interior D) → Tendsto u atTop (𝓝 xb) →
        Tendsto (fun k => ‖gradient W (u k)‖) atTop atTop)
    (xb u : EuclideanSpace ℝ (Fin d)) (hxb : xb ∈ closure D) (hxbD : xb ∈ D)
    (hu : u ∈ interior D) (K : ℝ)
    (hK : ∀ t ∈ Set.Ioo (0:ℝ) 1, W xb - K * t ≤ W ((1 - t) • xb + t • u)) :
    xb ∈ interior D := by
  by_contra hni
  have hfr : xb ∈ frontier D := ⟨hxb, hni⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u hu
  have hδpos : 0 < ε / 2 := by positivity
  have hcb : Metric.closedBall u (ε / 2) ⊆ interior D :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨M, hM⟩ := (isCompact_closedBall u (ε / 2)).exists_bound_of_continuousOn
    (dW.continuousOn.mono hcb)
  have hbound : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      ε / 2 * ‖gradient W ((1 - t) • xb + t • u)‖ ≤ M - W xb + 2 * |K| := by
    intro t ht
    have hyint : (1 - t) • xb + t • u ∈ interior D :=
      hDc.combo_closure_interior_mem_interior hxb hu (by linarith [ht.2]) ht.1 (by ring)
    set y := (1 - t) • xb + t • u with hy
    have hyd : DifferentiableAt ℝ W y := dW.differentiableAt (isOpen_interior.mem_nhds hyint)
    set v := gradient W y with hv
    have g1 := grad_ineq hW (interior_subset hyint) hxbD hyd
    rw [← inner_grad] at g1
    have e1 : xb - y = t • (xb - u) := by rw [hy]; module
    rw [e1, inner_smul_right] at g1
    have hKt := hK t ht
    have hi1 : inner ℝ v (xb - u) ≤ K := by
      by_contra hc; rw [not_le] at hc
      have : t * K < t * inner ℝ v (xb - u) := mul_lt_mul_of_pos_left hc ht.1
      linarith
    set e := ‖v‖⁻¹ • v with he
    have hve : inner ℝ v e = ‖v‖ := by
      rw [he, inner_smul_right, real_inner_self_eq_norm_sq]
      rcases eq_or_ne ‖v‖ 0 with h0 | h0
      · rw [h0]; simp
      · field_simp
    have hen : ‖e‖ ≤ 1 := by
      rw [he, norm_smul, norm_inv, norm_norm]
      rcases eq_or_ne ‖v‖ 0 with h0 | h0
      · rw [h0]; simp
      · rw [inv_mul_cancel₀ h0]
    have hzb : u + (ε / 2) • e ∈ Metric.closedBall u (ε / 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδpos.le]
      nlinarith
    have g2 := grad_ineq hW (interior_subset hyint) (interior_subset (hcb hzb)) hyd
    rw [← inner_grad] at g2
    have e2 : u + (ε / 2) • e - y = (1 - t) • (u - xb) + (ε / 2) • e := by rw [hy]; module
    rw [e2, inner_add_right, inner_smul_right, inner_smul_right, hve] at g2
    have hMz := hM _ hzb
    rw [Real.norm_eq_abs] at hMz
    have hWz := (le_abs_self (W (u + (ε / 2) • e))).trans hMz
    have hneg : inner ℝ v (u - xb) = - inner ℝ v (xb - u) := by
      rw [← inner_neg_right, neg_sub]
    rw [hneg] at g2
    have a1 : K * t ≤ |K| := by
      have := abs_nonneg K
      nlinarith [le_abs_self K, neg_abs_le K, ht.1, ht.2]
    have a2 : (1 - t) * inner ℝ v (xb - u) ≤ |K| := by
      have h1t : 0 < 1 - t := by linarith [ht.2]
      have : (1 - t) * inner ℝ v (xb - u) ≤ (1 - t) * K := mul_le_mul_of_nonneg_left hi1 h1t.le
      nlinarith [le_abs_self K, abs_nonneg K, ht.1]
    nlinarith
  set tn : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 1) / 2 with htn_def
  have htn : ∀ n, tn n ∈ Set.Ioo (0:ℝ) 1 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    refine ⟨by positivity, ?_⟩
    simp only [htn_def]; linarith
  have hlim : Tendsto tn atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (2:ℝ)
    rw [zero_div] at this
    exact this
  have hun : Tendsto (fun n => (1 - tn n) • xb + tn n • u) atTop (𝓝 xb) := by
    have := (((tendsto_const_nhds (x := (1:ℝ))).sub hlim).smul
      (tendsto_const_nhds (x := xb))).add (hlim.smul (tendsto_const_nhds (x := u)))
    simpa using this
  have hint : ∀ n, (1 - tn n) • xb + tn n • u ∈ interior D := fun n =>
    hDc.combo_closure_interior_mem_interior hxb hu (by linarith [(htn n).2]) (htn n).1 (by ring)
  have ht := hess _ xb hfr hint hun
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop ((M - W xb + 2 * |K|) / (ε / 2))).exists
  have := hbound (tn n) (htn n)
  rw [div_lt_iff₀ hδpos] at hn
  linarith

lemma sub_coe_ne_bot {b : EReal} (hb : b ≠ ⊥) (c : ℝ) : b - (c : EReal) ≠ ⊥ := by
  induction b using EReal.rec with
  | bot => exact absurd rfl hb
  | coe r => rw [← EReal.coe_sub]; exact EReal.coe_ne_bot _
  | top => rw [EReal.top_sub_coe]; exact top_ne_bot

lemma sub_coe_ne_top {b : EReal} {c : ℝ} (h : b - (c : EReal) ≠ ⊤) : b ≠ ⊤ := by
  rintro rfl; exact h (EReal.top_sub_coe c)

lemma mul_ne_bot_pos {a : ℝ} (ha : 0 < a) {b : EReal} (hb : b ≠ ⊥) : (a : EReal) * b ≠ ⊥ := by
  induction b using EReal.rec with
  | bot => exact absurd rfl hb
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  | top => rw [EReal.coe_mul_top_of_pos ha]; exact top_ne_bot

lemma mul_ne_top_pos {a : ℝ} (ha : 0 < a) {b : EReal} (h : (a : EReal) * b ≠ ⊤) : b ≠ ⊤ := by
  rintro rfl; exact h (EReal.coe_mul_top_of_pos ha)

/-- Real Bregman distance. -/
noncomputable def Dr {d : ℕ} (W : EuclideanSpace ℝ (Fin d) → ℝ)
    (y p : EuclideanSpace ℝ (Fin d)) : ℝ :=
  W y - (W p + inner ℝ (gradient W p) (y - p))

end PL41

open PLIAG in
theorem solution {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (Lc : Fin N → ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ)
    (α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ)
    (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hXne : (optSet w f h).Nonempty) (hXc : IsCompact (optSet w f h))
    (hJ : ∀ k, (J k).Nonempty) (hA0 : ∀ k n, τd k n ≤ τ)
    (hB1 : AssumptionB1 w f Lc) (hB2 : AssumptionB2 w h)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hB4 : 0 < τ → AssumptionB4 w ℓ)
    (hα : 0 < α)
    (hx : ∀ j ≤ k, x j ∈ interior (AubinLipschitz.effDom w))
    (hxk : x (k + 1) ∈ closure (AubinLipschitz.effDom w))
    (hmin : ∀ y ∈ closure (AubinLipschitz.effDom w),
      Phik w f h J τd α x k (x (k + 1)) ≤ Phik w f h J τd α x k y) :
    ∀ z ∈ AubinLipschitz.effDom w, Phi f h (x (k + 1)) ≤
      Phi f h z + ((1 / α : ℝ) : EReal) * bregman w z (x k)
        - ((1 / α : ℝ) : EReal) * bregman w z (x (k + 1))
        - ((1 / α : ℝ) : EReal) * bregman w (x (k + 1)) (x k)
        + Delta w Lc J ℓ τ x k := by
  intro z hz
  classical
  obtain ⟨hwc, -, hwd, hwess, -⟩ := hw
  have hwbot : ∀ y, w y ≠ ⊥ := hwc.1
  obtain ⟨hDc, hWc⟩ := PL41.ereal_conv w hwbot hwc.2.2.2
  obtain ⟨hHdc, hHc⟩ := PL41.ereal_conv h hh.1 hh.2.2.2
  have hfbot : ∀ n y, f n y ≠ ⊥ := fun n => (hB1 n).1.1
  have hFc : ∀ n, ConvexOn ℝ (AubinLipschitz.effDom (f n)) (fun y => (f n y).toReal) :=
    fun n => (PL41.ereal_conv (f n) (hfbot n) (hB1 n).1.2.2.2).2
  have hdomf : ∀ n, AubinLipschitz.effDom w ⊆ AubinLipschitz.effDom (f n) := fun n => (hB1 n).2.1
  have hfd : ∀ n, DifferentiableOn ℝ (fun y => (f n y).toReal)
      (interior (AubinLipschitz.effDom w)) := fun n => (hB1 n).2.2.1
  have hGc : ∀ n, ConvexOn ℝ (interior (AubinLipschitz.effDom w))
      (fun y => Lc n * (w y).toReal - (f n y).toReal) := fun n => (hB1 n).2.2.2.2
  have hLpos : ∀ n, 0 < Lc n := fun n => (hB1 n).2.2.2.1
  have hapos : 0 < 1 / α := by positivity
  have hαa : α * (1 / α) = 1 := by field_simp
  -- real forms
  have hbr : ∀ y p, y ∈ AubinLipschitz.effDom w →
      bregman w y p = ((PL41.Dr (fun y => (w y).toReal) y p : ℝ) : EReal) := by
    intro y p hy
    simp only [bregman, PL41.Dr]
    rw [← EReal.coe_toReal hy (hwbot y), ← EReal.coe_sub, EReal.toReal_coe]
  have hdiff : ∀ p ∈ interior (AubinLipschitz.effDom w),
      DifferentiableAt ℝ (fun y => (w y).toReal) p := fun p hp =>
    hwd.differentiableAt (isOpen_interior.mem_nhds hp)
  have hDr0 : ∀ y ∈ AubinLipschitz.effDom w, ∀ p ∈ interior (AubinLipschitz.effDom w),
      0 ≤ PL41.Dr (fun y => (w y).toReal) y p := by
    intro y hy p hp
    have := PL41.grad_ineq hWc (interior_subset hp) hy (hdiff p hp)
    simp only [PL41.Dr]; rw [PL41.inner_grad]; linarith
  set g := ∑ j ∈ J k, gradient (fun z => (f j z).toReal) (x (k - τd k j)) with hg
  set P : EuclideanSpace ℝ (Fin d) → ℝ := fun y => (h y).toReal +
    ∑ i ∈ (J k)ᶜ, (f i y).toReal + inner ℝ g y +
    1 / α * PL41.Dr (fun y => (w y).toReal) y (x k) with hP
  have hPk : ∀ y ∈ AubinLipschitz.effDom w, h y ≠ ⊤ →
      Phik w f h J τd α x k y = ((P y : ℝ) : EReal) := by
    intro y hy hhy
    simp only [Phik, hP]
    rw [hbr y (x k) hy, PL41.sum_toReal _ _ (fun i _ => hdomf i hy) (fun i _ => hfbot i y),
      ← EReal.coe_toReal hhy (hh.1 y), ← hg]
    norm_cast
  obtain ⟨u, huh, huint⟩ := hB2.1
  have huD : u ∈ AubinLipschitz.effDom w := interior_subset huint
  -- finiteness of x (k+1)
  have hfin : w (x (k + 1)) ≠ ⊤ ∧ h (x (k + 1)) ≠ ⊤ := by
    have hle := hmin u (subset_closure huD)
    rw [hPk u huD huh] at hle
    have hne := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
    simp only [Phik] at hne
    have hbrbot : bregman w (x (k + 1)) (x k) ≠ ⊥ := by
      simp only [bregman]; exact PL41.sub_coe_ne_bot (hwbot _) _
    have hsb := PL41.sum_ne_bot ((J k)ᶜ) (fun i => f i (x (k + 1))) (fun i _ => hfbot i _)
    have h1 := PL41.ne_top_left hne (PL41.mul_ne_bot_pos hapos hbrbot)
    have h2 := PL41.ne_top_right hne (EReal.add_ne_bot_iff.2 ⟨EReal.add_ne_bot_iff.2
      ⟨hh.1 _, hsb⟩, EReal.coe_ne_bot _⟩)
    have h3 := PL41.mul_ne_top_pos hapos h2
    simp only [bregman] at h3
    exact ⟨PL41.sub_coe_ne_top h3, PL41.ne_top_left (PL41.ne_top_left h1 (EReal.coe_ne_bot _)) hsb⟩
  have hxbD : x (k + 1) ∈ AubinLipschitz.effDom w := hfin.1
  -- convexity of P - (1/α) W
  have hQ : ∀ p1 ∈ AubinLipschitz.effDom w, h p1 ≠ ⊤ → ∀ p2 ∈ AubinLipschitz.effDom w, h p2 ≠ ⊤ →
      ∀ t ∈ Set.Ioo (0:ℝ) 1, (1 - t) • p1 + t • p2 ∈ AubinLipschitz.effDom w ∧
        h ((1 - t) • p1 + t • p2) ≠ ⊤ ∧
        P ((1 - t) • p1 + t • p2) - 1 / α * (w ((1 - t) • p1 + t • p2)).toReal ≤
          (1 - t) * (P p1 - 1 / α * (w p1).toReal) + t * (P p2 - 1 / α * (w p2).toReal) := by
    intro p1 hp1 hh1 p2 hp2 hh2 t ht
    have ht0 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
    have hsum : 1 - t + t = 1 := by ring
    refine ⟨hDc hp1 hp2 ht0 ht.1.le hsum, hHdc hh1 hh2 ht0 ht.1.le hsum, ?_⟩
    set c := (1 - t) • p1 + t • p2 with hc
    have hH := hHc.2 hh1 hh2 ht0 ht.1.le hsum
    have hF : ∑ i ∈ (J k)ᶜ, (f i c).toReal ≤
        (1 - t) * ∑ i ∈ (J k)ᶜ, (f i p1).toReal + t * ∑ i ∈ (J k)ᶜ, (f i p2).toReal := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => by
        simpa using (hFc i).2 (hdomf i hp1) (hdomf i hp2) ht0 ht.1.le hsum
    have hg1 : inner ℝ g c = (1 - t) * inner ℝ g p1 + t * inner ℝ g p2 := by
      rw [hc, inner_add_right, inner_smul_right, inner_smul_right]
    have hg2 : inner ℝ (gradient (fun y => (w y).toReal) (x k)) (c - x k) =
        (1 - t) * inner ℝ (gradient (fun y => (w y).toReal) (x k)) (p1 - x k) +
        t * inner ℝ (gradient (fun y => (w y).toReal) (x k)) (p2 - x k) := by
      have : c - x k = (1 - t) • (p1 - x k) + t • (p2 - x k) := by rw [hc]; module
      rw [this, inner_add_right, inner_smul_right, inner_smul_right]
    simp only [hP, PL41.Dr, smul_eq_mul] at hH ⊢
    have := congrArg (fun r => 1 / α * r) hg2
    nlinarith
  -- increment bound from minimality
  have hinc : ∀ b ∈ AubinLipschitz.effDom w, h b ≠ ⊤ → ∀ t ∈ Set.Ioo (0:ℝ) 1,
      (w (x (k + 1))).toReal - α * ((P b - 1 / α * (w b).toReal) -
        (P (x (k + 1)) - 1 / α * (w (x (k + 1))).toReal)) * t ≤
        (w ((1 - t) • x (k + 1) + t • b)).toReal := by
    intro b hb hhb t ht
    obtain ⟨hcD, hch, hcv⟩ := hQ _ hxbD hfin.2 b hb hhb t ht
    have hle := hmin _ (subset_closure hcD)
    rw [hPk _ hxbD hfin.2, hPk _ hcD hch, EReal.coe_le_coe_iff] at hle
    set Wc := (w ((1 - t) • x (k + 1) + t • b)).toReal
    set Δ := (P b - 1 / α * (w b).toReal) - (P (x (k + 1)) - 1 / α * (w (x (k + 1))).toReal)
    have key : 1 / α * (w (x (k + 1))).toReal - t * Δ ≤ 1 / α * Wc := by
      simp only [Δ]; nlinarith
    have := mul_le_mul_of_nonneg_left key hα.le
    have e1 : α * (1 / α * Wc) = Wc := by rw [← mul_assoc, hαa, one_mul]
    have e2 : α * (1 / α * (w (x (k + 1))).toReal - t * Δ) =
        (w (x (k + 1))).toReal - α * Δ * t := by rw [mul_sub, ← mul_assoc, hαa, one_mul]; ring
    rw [e1, e2] at this; exact this
  have hxbint : x (k + 1) ∈ interior (AubinLipschitz.effDom w) :=
    PL41.interior_of_min _ _ hDc hWc hwd hwess _ u hxk hxbD huint _ (hinc u huD huh)
  have hxall : ∀ i ≤ k + 1, x i ∈ interior (AubinLipschitz.effDom w) := by
    intro i hi
    rcases Nat.lt_or_ge i (k + 1) with h' | h'
    · exact hx i (by omega)
    · rw [show i = k + 1 by omega]; exact hxbint
  set S := ∑ i ∈ Finset.Icc (k - τ) k,
    PL41.Dr (fun y => (w y).toReal) (x (i + 1)) (x i) with hS
  have hSterm : ∀ i ∈ Finset.Icc (k - τ) k,
      0 ≤ PL41.Dr (fun y => (w y).toReal) (x (i + 1)) (x i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact hDr0 _ (interior_subset (hxall _ (by omega))) _ (hxall _ (by omega))
  have hS0 : 0 ≤ S := Finset.sum_nonneg hSterm
  have hℓτ : 1 ≤ ℓ (τ + 1) := hℓ1 ▸ hℓm (by omega)
  -- delayed term bound (B4)
  have hdel : ∀ j ∈ J k, PL41.Dr (fun y => (w y).toReal) (x (k + 1)) (x (k - τd k j)) ≤
      ℓ (τ + 1) * S := by
    intro j _
    have hτj := hA0 k j
    set m := k - τd k j with hm
    by_cases hmk : m = k
    · rw [hmk]
      have : PL41.Dr (fun y => (w y).toReal) (x (k + 1)) (x k) ≤ S :=
        Finset.single_le_sum (f := fun i => PL41.Dr (fun y => (w y).toReal) (x (i + 1)) (x i))
          hSterm (by rw [Finset.mem_Icc]; omega)
      nlinarith
    have hτpos : 0 < τ := by omega
    have hv : ∀ i, x (min (i - 1) (k + 1)) ∈ interior (AubinLipschitz.effDom w) :=
      fun i => hxall _ (min_le_right _ _)
    have hb4 := hB4 hτpos (fun i => x (min (i - 1) (k + 1))) hv (m + 1) (k + 2)
      (by omega) (by omega)
    rw [show min (k + 2 - 1) (k + 1) = k + 1 by omega,
      show min (m + 1 - 1) (k + 1) = m by omega, show k + 2 - (m + 1) = k + 1 - m by omega] at hb4
    have hre : ∑ i ∈ Finset.Ico (m + 1) (k + 2),
        bregman w (x (min (i + 1 - 1) (k + 1))) (x (min (i - 1) (k + 1))) =
        ∑ i ∈ Finset.Ico m (k + 1), bregman w (x (i + 1)) (x i) := by
      rw [show k + 2 = (k + 1) + 1 by ring, ← Finset.sum_Ico_add']
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [show min (i + 1 + 1 - 1) (k + 1) = i + 1 by omega,
        show min (i + 1 - 1) (k + 1) = i by omega]
    rw [hre, hbr _ _ hxbD,
      Finset.sum_congr rfl (fun i hi => hbr _ _ (interior_subset (hxall (i + 1)
        (by rw [Finset.mem_Ico] at hi; omega)))), ← PL41.coe_sum, ← EReal.coe_mul,
      EReal.coe_le_coe_iff] at hb4
    set T := ∑ i ∈ Finset.Ico m (k + 1), PL41.Dr (fun y => (w y).toReal) (x (i + 1)) (x i)
    have hTS : T ≤ S := Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => by rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc]; omega)
      (fun i hi _ => hSterm i hi)
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun i hi =>
      hSterm i (by rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc]; omega)
    have hl1 : ℓ (k + 1 - m) ≤ ℓ (τ + 1) := hℓm (by omega)
    have hl0 : 1 ≤ ℓ (k + 1 - m) := hℓ1 ▸ hℓm (by omega)
    calc _ ≤ ℓ (k + 1 - m) * T := hb4
      _ ≤ ℓ (τ + 1) * T := mul_le_mul_of_nonneg_right hl1 hT0
      _ ≤ ℓ (τ + 1) * S := mul_le_mul_of_nonneg_left hTS (by linarith)
  have hLmax : ∑ j ∈ J k, Lc j ≤ Lmax Lc J := by
    unfold Lmax
    refine le_ciSup (f := fun k => ∑ j ∈ J k, Lc j) ⟨∑ j, Lc j, ?_⟩ k
    rintro _ ⟨m, rfl⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => (hLpos i).le)
  have hdelsum : ∑ j ∈ J k, Lc j *
      PL41.Dr (fun y => (w y).toReal) (x (k + 1)) (x (k - τd k j)) ≤ Lmax Lc J * ℓ (τ + 1) * S := by
    calc _ ≤ ∑ j ∈ J k, Lc j * (ℓ (τ + 1) * S) :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hdel j hj) (hLpos j).le
      _ = (∑ j ∈ J k, Lc j) * (ℓ (τ + 1) * S) := by rw [Finset.sum_mul]
      _ ≤ Lmax Lc J * (ℓ (τ + 1) * S) :=
          mul_le_mul_of_nonneg_right hLmax (mul_nonneg (by linarith) hS0)
      _ = _ := by ring
  -- descent for the delayed components
  have hdesc : ∀ j ∈ J k, (f j (x (k + 1))).toReal - (f j z).toReal ≤
      inner ℝ (gradient (fun z => (f j z).toReal) (x (k - τd k j))) (x (k + 1) - z) +
      Lc j * PL41.Dr (fun y => (w y).toReal) (x (k + 1)) (x (k - τd k j)) := by
    intro j _
    have hp := hx (k - τd k j) (Nat.sub_le _ _)
    set p := x (k - τd k j)
    have hdF : DifferentiableAt ℝ (fun y => (f j y).toReal) p :=
      (hfd j).differentiableAt (isOpen_interior.mem_nhds hp)
    have hdW := hdiff p hp
    have a1 := PL41.grad_ineq (hFc j) (hdomf j (interior_subset hp)) (hdomf j hz) hdF
    have a2 := PL41.grad_ineq (hGc j) hp hxbint ((hdW.const_mul (Lc j)).sub hdF)
    have hG : fderiv ℝ (fun y => Lc j * (w y).toReal - (f j y).toReal) p =
        Lc j • fderiv ℝ (fun y => (w y).toReal) p - fderiv ℝ (fun y => (f j y).toReal) p :=
      ((hdW.hasFDerivAt.const_mul (Lc j)).sub hdF.hasFDerivAt).fderiv
    rw [hG] at a2
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at a2
    simp only [PL41.Dr]
    rw [PL41.inner_grad, PL41.inner_grad,
      show x (k + 1) - z = (x (k + 1) - p) - (z - p) by abel, map_sub]
    nlinarith
  have hsumJ : ∑ j ∈ J k, (f j (x (k + 1))).toReal - ∑ j ∈ J k, (f j z).toReal ≤
      inner ℝ g (x (k + 1) - z) + Lmax Lc J * ℓ (τ + 1) * S := by
    have : ∑ j ∈ J k, (f j (x (k + 1))).toReal - ∑ j ∈ J k, (f j z).toReal ≤
        inner ℝ g (x (k + 1) - z) + ∑ j ∈ J k, Lc j *
          PL41.Dr (fun y => (w y).toReal) (x (k + 1)) (x (k - τd k j)) := by
      rw [← Finset.sum_sub_distrib, hg, sum_inner, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hdesc
    linarith
  have hDelta : Delta w Lc J ℓ τ x k = ((Lmax Lc J * ℓ (τ + 1) * S : ℝ) : EReal) := by
    unfold Delta
    rw [Finset.sum_congr rfl (fun i hi => hbr _ _ (interior_subset (hxall (i + 1)
      (by rw [Finset.mem_Icc] at hi; omega)))), ← PL41.coe_sum, ← EReal.coe_mul]
  have hPhi : ∀ y ∈ AubinLipschitz.effDom w, h y ≠ ⊤ →
      Phi f h y = ((∑ n, (f n y).toReal + (h y).toReal : ℝ) : EReal) := by
    intro y hy hhy
    unfold Phi
    rw [PL41.sum_toReal _ _ (fun i _ => hdomf i hy) (fun i _ => hfbot i y),
      ← EReal.coe_toReal hhy (hh.1 y), EReal.coe_add, EReal.toReal_coe]
  rw [hbr z (x k) hz, hbr z (x (k + 1)) hz, hbr (x (k + 1)) (x k) hxbD, hDelta,
    hPhi _ hxbD hfin.2]
  by_cases hhz : h z = ⊤
  · have : Phi f h z = ⊤ := by
      unfold Phi; rw [hhz]
      exact EReal.add_top_of_ne_bot (PL41.sum_ne_bot _ _ (fun i _ => hfbot i z))
    rw [this, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, EReal.top_add_coe,
      EReal.top_sub_coe, EReal.top_sub_coe, EReal.top_add_coe]
    exact le_top
  rw [hPhi z hz hhz]
  -- three-point inequality
  have htp : P (x (k + 1)) + 1 / α * PL41.Dr (fun y => (w y).toReal) z (x (k + 1)) ≤ P z := by
    have hdW := hdiff _ hxbint
    have := PL41.slope_le (b := α * ((P z - 1 / α * (w z).toReal) -
        (P (x (k + 1)) - 1 / α * (w (x (k + 1))).toReal)))
      (PL41.line_deriv hdW (z - x (k + 1))).neg (by
        intro t ht
        have := hinc z hz hhz t ht
        rw [PL41.combo_eq] at this
        show -(w (x (k + 1) + t • (z - x (k + 1)))).toReal -
          -(w (x (k + 1) + (0:ℝ) • (z - x (k + 1)))).toReal ≤ _
        rw [zero_smul, add_zero]
        linarith)
    have hm := mul_le_mul_of_nonneg_left this hapos.le
    rw [← mul_assoc, mul_comm (1 / α) α, hαa, one_mul] at hm
    simp only [PL41.Dr]
    rw [PL41.inner_grad]
    linarith
  have hsplit : ∀ y, ∑ n, (f n y).toReal =
      ∑ n ∈ J k, (f n y).toReal + ∑ n ∈ (J k)ᶜ, (f n y).toReal := fun y =>
    (Finset.sum_add_sum_compl (J k) _).symm
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
    ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
  simp only [hP] at htp
  rw [hsplit, hsplit]
  rw [inner_sub_right] at hsumJ
  linarith
