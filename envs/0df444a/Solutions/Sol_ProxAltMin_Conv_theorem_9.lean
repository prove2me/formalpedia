-- Prove2me | solution 1 for ProxAltMin.Conv.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T09:12:01.278274+00:00
-- url     : https://prove2.me/submissions/14a13067-fd44-4897-b9a3-a9fe34dccd1d

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ProxAltMin_Conv_Setting

set_option autoImplicit false

open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL ProxAltMin.Conv
open scoped InnerProductSpace

namespace P8324


theorem two_le (D0 D1 M X : ℝ) (hD0 : 0 ≤ D0) (_hD1 : 0 ≤ D1) (hMX : 0 ≤ M * X)
    (h : D1 ^ 2 ≤ M * X * D0) : 2 * D1 ≤ D0 + M * X := by
  by_contra hc
  push Not at hc
  nlinarith [sq_nonneg (D0 - M * X)]

theorem capture {X : Type*} [NormedAddCommGroup X] (w : ℕ → X) (ℓ : ℕ → ℝ)
    (ζ a b η ρ : ℝ) (φ : ℝ → ℝ) (zb : X)
    (ha : 0 < a) (hb : 0 < b) (hφ : IsDesingularizer η φ)
    (hdesc : ∀ k, ℓ (k + 1) + a * ‖w (k + 1) - w k‖ ^ 2 ≤ ℓ k)
    (hgt : ∀ k, ζ < ℓ k)
    (hkl : ∀ k, ‖w (k + 1) - zb‖ < ρ → ℓ (k + 1) < ζ + η →
      1 ≤ deriv φ (ℓ (k + 1) - ζ) * (b * ‖w (k + 1) - w k‖))
    (N : ℕ) (hN1 : ‖w (N + 1) - zb‖ + ‖w (N + 1) - w N‖ + (b / a) * φ (ℓ (N + 1) - ζ) < ρ)
    (hN2 : ℓ (N + 1) < ζ + η) :
    Summable (fun k => ‖w (k + 1) - w k‖) := by
  obtain ⟨-, hconc, hnonneg, -, hC1, hpos⟩ := hφ
  set D : ℕ → ℝ := fun k => ‖w (k + 1) - w k‖ with hD
  set M : ℝ := b / a with hM
  set Φ : ℕ → ℝ := fun k => φ (ℓ k - ζ) with hΦ
  have hM0 : 0 < M := div_pos hb ha
  have hD0 : ∀ k, 0 ≤ D k := fun k => norm_nonneg _
  have hanti : Antitone ℓ := antitone_nat_of_succ_le (fun k => by
    have := hdesc k; have : 0 ≤ a * ‖w (k + 1) - w k‖ ^ 2 := by positivity
    linarith)
  -- one step
  have step : ∀ k, ‖w (k + 1) - zb‖ < ρ → ℓ (k + 1) < ζ + η →
      2 * D (k + 1) ≤ D k + M * (Φ (k + 1) - Φ (k + 2)) := by
    intro k hw hl
    set s := ℓ (k + 1) - ζ with hs
    set t := ℓ (k + 2) - ζ with ht
    have hs0 : 0 < s := by have := hgt (k + 1); linarith
    have hsη : s < η := by linarith
    have ht0 : 0 < t := by have := hgt (k + 2); linarith
    have hts : a * D (k + 1) ^ 2 ≤ s - t := by
      have := hdesc (k + 1); simp only [hD]; linarith
    have h1 : 1 ≤ deriv φ s * (b * D k) := hkl k hw hl
    have hdpos : 0 < deriv φ s := hpos s ⟨hs0, hsη⟩
    have h2 : deriv φ s * (s - t) ≤ φ s - φ t := by
      rcases eq_or_lt_of_le (show t ≤ s by nlinarith [sq_nonneg (D (k + 1))]) with heq | hlt
      · rw [heq]; simp
      · have hdiff : DifferentiableAt ℝ φ s :=
          ((hC1.contDiffAt (Ioo_mem_nhds hs0 hsη)).differentiableAt one_ne_zero)
        have := hconc.deriv_le_slope ⟨ht0.le, by linarith⟩ ⟨hs0.le, hsη⟩ hlt hdiff
        rw [slope_def_field] at this
        rwa [le_div_iff₀ (by linarith)] at this
    have hst : 0 ≤ s - t := le_trans (by positivity) hts
    have hX : 0 ≤ φ s - φ t := le_trans (mul_nonneg hdpos.le hst) h2
    have h3 : a * D (k + 1) ^ 2 * deriv φ s ≤ φ s - φ t := by nlinarith
    have h4 : a * D (k + 1) ^ 2 ≤ (φ s - φ t) * (b * D k) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ a * D (k + 1) ^ 2)
      nlinarith [hD0 k]
    have h5 : D (k + 1) ^ 2 ≤ M * (φ s - φ t) * D k := by
      rw [hM, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ha]; nlinarith
    have := two_le (D k) (D (k + 1)) M (φ s - φ t) (hD0 k) (hD0 (k + 1)) (by positivity) h5
    simpa [hΦ, hs, ht] using this
  have hΦnn : ∀ k, ℓ k < ζ + η → 0 ≤ Φ k := fun k hk =>
    hnonneg _ ⟨by have := hgt k; linarith, by linarith⟩
  -- telescoping
  have tele : ∀ j, (∀ i < j, ‖w (N + 1 + i) - zb‖ < ρ) →
      (∑ i ∈ Finset.range j, D (N + 1 + i)) + D (N + j) + M * Φ (N + 1 + j) ≤ D N + M * Φ (N + 1) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hg
      have hprev := ih (fun i hi => hg i (by omega))
      have hl : ℓ (N + j + 1) < ζ + η := lt_of_le_of_lt (hanti (by omega)) hN2
      have hs := step (N + j) (by have := hg j (by omega); rwa [show N + j + 1 = N + 1 + j by omega]) hl
      rw [Finset.sum_range_succ]
      have e1 : N + 1 + j = N + j + 1 := by omega
      have e2 : N + (j + 1) = N + j + 1 := by omega
      have e3 : N + 1 + (j + 1) = N + j + 2 := by omega
      rw [e1, e2, e3]; rw [e1] at hprev
      linarith
  have pos : ∀ j, (∀ i < j, ‖w (N + 1 + i) - zb‖ < ρ) →
      ‖w (N + 1 + j) - zb‖ ≤ ‖w (N + 1) - zb‖ + (D N + M * Φ (N + 1)) := by
    intro j hg
    have ht := tele j hg
    have hl : ℓ (N + 1 + j) < ζ + η := lt_of_le_of_lt (hanti (by omega)) hN2
    have h0 := hΦnn _ hl
    have hsum : ‖w (N + 1 + j) - w (N + 1)‖ ≤ ∑ i ∈ Finset.range j, D (N + 1 + i) := by
      have := dist_le_range_sum_dist (fun i => w (N + 1 + i)) j
      simp only [dist_eq_norm, add_zero] at this
      rw [norm_sub_rev]
      refine this.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      simp only [hD]; rw [norm_sub_rev]; congr 2
    have := norm_sub_le_norm_sub_add_norm_sub (w (N + 1 + j)) (w (N + 1)) zb
    nlinarith [hD0 (N + j)]
  have allg : ∀ j, ∀ i ≤ j, ‖w (N + 1 + i) - zb‖ < ρ := by
    have hΦ1 := hΦnn (N + 1) hN2
    intro j
    induction j with
    | zero => intro i hi; rw [Nat.le_zero.mp hi]; simp only [add_zero]
              have := hD0 N; nlinarith
    | succ j ih =>
      intro i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact ih i (by omega)
      · have hij : i = j + 1 := by omega
        subst hij
        have := pos (j + 1) (fun i hi => ih i (by omega))
        linarith
  have hbound : ∀ j, ∑ i ∈ Finset.range j, D (i + (N + 1)) ≤ D N + M * Φ (N + 1) := by
    intro j
    have ht := tele j (fun i _ => allg i i le_rfl)
    have hl : ℓ (N + 1 + j) < ζ + η := lt_of_le_of_lt (hanti (by omega)) hN2
    have h0 := hΦnn _ hl
    have : ∑ i ∈ Finset.range j, D (i + (N + 1)) = ∑ i ∈ Finset.range j, D (N + 1 + i) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    rw [this]; nlinarith [hD0 (N + j)]
  have hs : Summable (fun i => D (i + (N + 1))) :=
    summable_of_sum_range_le (fun i => hD0 _) hbound
  exact (summable_nat_add_iff (N + 1)).mp hs



theorem pt_fst {n m : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) :
    (pt u v).fst = u := rfl
theorem pt_snd {n m : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) :
    (pt u v).snd = v := rfl
theorem pt_eta {n m : ℕ} (w : Z n m) : pt w.fst w.snd = w := rfl
theorem pt_sub {n m : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin m)) :
    pt u v - pt u' v' = pt (u - u') (v - v') := rfl
theorem inner_pt {n m : ℕ} (G : Z n m) (c : EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin m)) : ⟪G, pt c d⟫_ℝ = ⟪G.fst, c⟫_ℝ + ⟪G.snd, d⟫_ℝ := rfl
theorem norm_pt_sq {n m : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) :
    ‖pt u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
theorem norm_pt_le {n m : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) :
    ‖pt u v‖ ≤ ‖u‖ + ‖v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), norm_pt_sq]
  nlinarith [norm_nonneg u, norm_nonneg v]
theorem norm_fst_le_pt {n m : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) :
    ‖u‖ ≤ ‖pt u v‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [norm_pt_sq]; nlinarith [sq_nonneg ‖v‖])
theorem norm_snd_le_pt {n m : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) :
    ‖v‖ ≤ ‖pt u v‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [norm_pt_sq]; nlinarith [sq_nonneg ‖u‖])
theorem norm_pt_u0 {n m : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    ‖pt u (0 : EuclideanSpace ℝ (Fin m))‖ = ‖u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_pt_sq]; simp
theorem norm_pt_0v {n m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    ‖pt (0 : EuclideanSpace ℝ (Fin n)) v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_pt_sq]; simp

theorem deriv_est {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Q : X → ℝ) (p : X) (hQ : DifferentiableAt ℝ Q p) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 p, |Q q - Q p - ⟪gradient Q p, q - p⟫_ℝ| ≤ ε * ‖q - p‖ := by
  have h := hQ.hasGradientAt.hasFDerivAt.isLittleO
  filter_upwards [h.def hε] with q hq
  simpa [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs] using hq

theorem L_real {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hfb : ∀ u, f u ≠ ⊥) (hgb : ∀ v, g v ≠ ⊥)
    (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) (hf : f u ≠ ⊤) (hg : g v ≠ ⊤) :
    L f Q g (pt u v) = (((f u).toReal + Q (pt u v) + (g v).toReal : ℝ) : EReal) := by
  show f u + (Q (pt u v) : EReal) + g v = _
  rw [← EReal.coe_toReal hf (hfb u), ← EReal.coe_toReal hg (hgb v)]
  simp only [EReal.toReal_coe]
  push_cast; ring_nf

theorem L_top {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hfb : ∀ u, f u ≠ ⊥) (hgb : ∀ v, g v ≠ ⊥)
    (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m)) (h : f u = ⊤ ∨ g v = ⊤) :
    L f Q g (pt u v) = ⊤ := by
  show f u + (Q (pt u v) : EReal) + g v = ⊤
  rcases h with h | h
  · rw [h, EReal.top_add_coe, EReal.top_add_of_ne_bot (hgb v)]
  · rw [h, EReal.add_top_of_ne_bot]
    intro hb
    rcases EReal.add_eq_bot_iff.mp hb with h' | h'
    · exact hfb u h'
    · exact EReal.coe_ne_bot _ h'

theorem regsub {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hfb : ∀ u, f u ≠ ⊥) (hgb : ∀ v, g v ≠ ⊥)
    (hQd : Differentiable ℝ Q) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (x0 x1 : EuclideanSpace ℝ (Fin n)) (y0 y1 : EuclideanSpace ℝ (Fin m))
    (hf1 : f x1 ≠ ⊤) (hg1 : g y1 ≠ ⊤)
    (hX : ∀ u, f u ≠ ⊤ → (f x1).toReal + Q (pt x1 y0) + ‖x1 - x0‖ ^ 2 / (2 * lam) ≤
      (f u).toReal + Q (pt u y0) + ‖u - x0‖ ^ 2 / (2 * lam))
    (hY : ∀ v, g v ≠ ⊤ → (g y1).toReal + Q (pt x1 y1) + ‖y1 - y0‖ ^ 2 / (2 * mu) ≤
      (g v).toReal + Q (pt x1 v) + ‖v - y0‖ ^ 2 / (2 * mu)) :
    IsRegularSubgrad (L f Q g) (pt x1 y1)
      (pt (gradX Q (pt x1 y1) - gradX Q (pt x1 y0) - (1 / lam) • (x1 - x0))
        (-((1 / mu) • (y1 - y0)))) := by
  refine ⟨by rw [L_real f Q g hfb hgb _ _ hf1 hg1]; exact EReal.coe_ne_top _, ?_⟩
  intro ε hε
  set p1 := pt x1 y0
  set p2 := pt x1 y1
  have e4 : 0 < ε / 4 := by positivity
  obtain ⟨δ1, hδ1, H1⟩ := Metric.eventually_nhds_iff.mp (deriv_est Q p1 (hQd p1) _ e4)
  obtain ⟨δ2, hδ2, H2⟩ := Metric.eventually_nhds_iff.mp (deriv_est Q p2 (hQd p2) _ e4)
  have hδ3 : 0 < ε * lam / 4 := by positivity
  have hδ4 : 0 < ε * mu / 4 := by positivity
  refine Metric.eventually_nhds_iff.mpr ⟨min (min δ1 δ2) (min (ε * lam / 4) (ε * mu / 4)),
    by positivity, fun w hw => ?_⟩
  rw [dist_eq_norm] at hw
  simp only [lt_min_iff] at hw
  obtain ⟨⟨hw1, hw2⟩, hw3, hw4⟩ := hw
  set u := w.fst
  set v := w.snd
  have hwe : w = pt u v := rfl
  set h1 := u - x1
  set h2 := v - y1
  have hwp : w - p2 = pt h1 h2 := by rw [hwe]; rfl
  rw [hwp] at hw1 hw2 hw3 hw4
  have nh1 : ‖h1‖ ≤ ‖pt h1 h2‖ := norm_fst_le_pt _ _
  have nh2 : ‖h2‖ ≤ ‖pt h1 h2‖ := norm_snd_le_pt _ _
  by_cases hfin : f u ≠ ⊤ ∧ g v ≠ ⊤
  swap
  · have : L f Q g w = ⊤ := L_top f Q g hfb hgb u v (by tauto)
    rw [this]; exact le_top
  obtain ⟨hfu, hgv⟩ := hfin
  have Lw : L f Q g w = (((f u).toReal + Q w + (g v).toReal : ℝ) : EReal) :=
    L_real f Q g hfb hgb u v hfu hgv
  rw [Lw, L_real f Q g hfb hgb _ _ hf1 hg1, ← EReal.coe_add, EReal.coe_le_coe_iff]
  -- Q estimates
  have q1 : pt u y0 - p1 = pt h1 0 := by simp [p1, pt_sub, h1]
  have q2 : pt x1 v - p2 = pt 0 h2 := by simp [p2, pt_sub, h2]
  have E1 := H1 (y := pt u y0) (by rw [dist_eq_norm, q1, norm_pt_u0]; linarith)
  have E2 := H2 (y := pt x1 v) (by rw [dist_eq_norm, q2, norm_pt_0v]; linarith)
  have E3 := H2 (y := w) (by rw [dist_eq_norm, hwp]; exact hw2)
  rw [q1, norm_pt_u0, inner_pt] at E1
  rw [q2, norm_pt_0v, inner_pt] at E2
  rw [hwp, inner_pt] at E3
  rw [abs_le] at E1 E2 E3
  have X := hX u hfu
  have Y := hY v hgv
  -- quadratic expansions
  have qx : ‖u - x0‖ ^ 2 / (2 * lam) =
      ‖x1 - x0‖ ^ 2 / (2 * lam) + (1 / lam) * ⟪x1 - x0, h1⟫_ℝ + ‖h1‖ ^ 2 / (2 * lam) := by
    have : u - x0 = (x1 - x0) + h1 := by simp [h1]
    rw [this, norm_add_sq_real]; field_simp
  have qy : ‖v - y0‖ ^ 2 / (2 * mu) =
      ‖y1 - y0‖ ^ 2 / (2 * mu) + (1 / mu) * ⟪y1 - y0, h2⟫_ℝ + ‖h2‖ ^ 2 / (2 * mu) := by
    have : v - y0 = (y1 - y0) + h2 := by simp [h2]
    rw [this, norm_add_sq_real]; field_simp
  have rx : ‖h1‖ ^ 2 / (2 * lam) ≤ ε / 8 * ‖h1‖ := by
    rw [div_le_iff₀ (by positivity)]
    have : ‖h1‖ ≤ ε * lam / 4 := by linarith
    nlinarith [norm_nonneg h1]
  have ry : ‖h2‖ ^ 2 / (2 * mu) ≤ ε / 8 * ‖h2‖ := by
    rw [div_le_iff₀ (by positivity)]
    have : ‖h2‖ ≤ ε * mu / 4 := by linarith
    nlinarith [norm_nonneg h2]
  have hin : ⟪pt (gradX Q p2 - gradX Q p1 - (1 / lam) • (x1 - x0)) (-((1 / mu) • (y1 - y0))),
      pt h1 h2⟫_ℝ = ⟪gradX Q p2, h1⟫_ℝ - ⟪gradX Q p1, h1⟫_ℝ - (1 / lam) * ⟪x1 - x0, h1⟫_ℝ
        - (1 / mu) * ⟪y1 - y0, h2⟫_ℝ := by
    rw [inner_pt, pt_fst, pt_snd, inner_sub_left, inner_sub_left, inner_neg_left,
      real_inner_smul_left, real_inner_smul_left]; ring
  rw [hwp, hin]
  have hq0 : Q (pt x1 y1) = Q p2 := rfl
  rw [hq0]
  have gx1 : (gradient Q p1).fst = gradX Q p1 := rfl
  have gx2 : (gradient Q p2).fst = gradX Q p2 := rfl
  have gy2 : (gradient Q p2).snd = gradY Q p2 := rfl
  simp only [gx1, gx2, gy2, inner_zero_right, add_zero, zero_add] at E1 E2 E3
  rw [qx] at X
  rw [qy] at Y
  have m1 := mul_le_mul_of_nonneg_left nh1 hε.le
  have m2 := mul_le_mul_of_nonneg_left nh2 hε.le
  linarith [E1.2, E2.2, E3.1]


theorem ne_top_of_le {a b : EReal} {r s : ℝ} (h : a + (r : EReal) ≤ b + (s : EReal))
    (hb : b ≠ ⊤) : a ≠ ⊤ := by
  intro ha
  rw [ha, EReal.top_add_coe] at h
  have : b + (s : EReal) ≠ ⊤ := by
    induction b using EReal.rec with
    | bot => simp
    | coe b => rw [← EReal.coe_add]; exact EReal.coe_ne_top _
    | top => exact absurd rfl hb
  exact this (top_le_iff.mp h)

theorem reg_mem_lim {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x v : X) (h : IsRegularSubgrad f x v) : v ∈ LimitingSubdiff f x :=
  ⟨h.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds,
    fun _ => h⟩

theorem tendsto_pt {n m : ℕ} {X : ℕ → EuclideanSpace ℝ (Fin n)} {Y : ℕ → EuclideanSpace ℝ (Fin m)}
    {a : EuclideanSpace ℝ (Fin n)} {b : EuclideanSpace ℝ (Fin m)}
    (hX : Tendsto X atTop (𝓝 a)) (hY : Tendsto Y atTop (𝓝 b)) :
    Tendsto (fun j => pt (X j) (Y j)) atTop (𝓝 (pt a b)) :=
  ((WithLp.prod_continuous_toLp 2 _ _).tendsto _).comp (hX.prodMk_nhds hY)

theorem dist_aux {n m : ℕ} (x' : EuclideanSpace ℝ (Fin n)) (y y' : EuclideanSpace ℝ (Fin m))
    (zb : Z n m) : ‖pt x' y - zb‖ ≤ ‖pt x' y' - zb‖ + ‖y' - y‖ := by
  have := norm_sub_le_norm_sub_add_norm_sub (pt x' y) (pt x' y') zb
  rw [pt_sub, sub_self, norm_pt_0v, norm_sub_rev y y'] at this
  linarith

theorem fin_all {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hfb : ∀ u, f u ≠ ⊥) (hgb : ∀ v, g v ≠ ⊥)
    (lam mu : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsPAMRun f Q g lam mu x y) (hf0 : f (x 0) ≠ ⊤) (hg0 : g (y 0) ≠ ⊤) :
    ∀ k, f (x k) ≠ ⊤ ∧ g (y k) ≠ ⊤ := by
  intro k
  induction k with
  | zero => exact ⟨hf0, hg0⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := hrun k
    have A : L f Q g (pt (x (k + 1)) (y k)) ≠ ⊤ := by
      refine ne_top_of_le (h1 (x k)) ?_
      rw [L_real f Q g hfb hgb _ _ ih.1 ih.2]; exact EReal.coe_ne_top _
    have hf1 : f (x (k + 1)) ≠ ⊤ := fun hc => A (L_top f Q g hfb hgb _ _ (Or.inl hc))
    have B : L f Q g (pt (x (k + 1)) (y (k + 1))) ≠ ⊤ := ne_top_of_le (h2 (y k)) A
    exact ⟨hf1, fun hc => B (L_top f Q g hfb hgb _ _ (Or.inr hc))⟩

theorem hX_real {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hfb : ∀ u, f u ≠ ⊥) (hgb : ∀ v, g v ≠ ⊥)
    (lam mu : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsPAMRun f Q g lam mu x y) (hfin : ∀ k, f (x k) ≠ ⊤ ∧ g (y k) ≠ ⊤)
    (k : ℕ) (u : EuclideanSpace ℝ (Fin n)) (hu : f u ≠ ⊤) :
    (f (x (k + 1))).toReal + Q (pt (x (k + 1)) (y k)) + ‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) ≤
      (f u).toReal + Q (pt u (y k)) + ‖u - x k‖ ^ 2 / (2 * lam k) := by
  have A := (hrun k).1 u
  rw [L_real f Q g hfb hgb _ _ (hfin (k + 1)).1 (hfin k).2, L_real f Q g hfb hgb _ _ hu (hfin k).2,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at A
  linarith

theorem hY_real {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (hfb : ∀ u, f u ≠ ⊥) (hgb : ∀ v, g v ≠ ⊥)
    (lam mu : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsPAMRun f Q g lam mu x y) (hfin : ∀ k, f (x k) ≠ ⊤ ∧ g (y k) ≠ ⊤)
    (k : ℕ) (v : EuclideanSpace ℝ (Fin m)) (hv : g v ≠ ⊤) :
    (g (y (k + 1))).toReal + Q (pt (x (k + 1)) (y (k + 1))) + ‖y (k + 1) - y k‖ ^ 2 / (2 * mu k) ≤
      (g v).toReal + Q (pt (x (k + 1)) v) + ‖v - y k‖ ^ 2 / (2 * mu k) := by
  have A := (hrun k).2 v
  rw [L_real f Q g hfb hgb _ _ (hfin (k + 1)).1 (hfin (k + 1)).2,
    L_real f Q g hfb hgb _ _ (hfin (k + 1)).1 hv,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at A
  linarith

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem core {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp c : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hc : ∀ z, (c : EReal) ≤ L f Q g z)
    (hrm : 0 < rm) (hsteps : ∀ k, lam k ∈ Set.Ioo rm rp ∧ mu k ∈ Set.Ioo rm rp)
    (hKL : ∀ z : Z n m, (LimitingSubdiff (L f Q g) z).Nonempty → HasKLProperty (L f Q g) z)
    (hrun : IsPAMRun f Q g lam mu x y) (hf0 : f (x 0) ≠ ⊤) (hg0 : g (y 0) ≠ ⊤) :
    Tendsto (fun k => ‖pt (x k) (y k)‖) atTop atTop ∨
      (Summable (fun k => ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖) ∧
        ∃ zlim : Z n m, (0 : Z n m) ∈ LimitingSubdiff (L f Q g) zlim ∧
          Tendsto (fun k => pt (x k) (y k)) atTop (𝓝 zlim)) := by
  have hfb : ∀ u, f u ≠ ⊥ := hH.f_proper.1
  have hgb : ∀ v, g v ≠ ⊥ := hH.g_proper.1
  have hQd : Differentiable ℝ Q := hH.Q_C1.differentiable one_ne_zero
  have : ContinuousSMul ℝ (Z n m) := IsBoundedSMul.continuousSMul
  have hQc : Continuous Q := hQd.continuous
  have hfin := fin_all f Q g hfb hgb lam mu x y hrun hf0 hg0
  have hX := hX_real f Q g hfb hgb lam mu x y hrun hfin
  have hY := hY_real f Q g hfb hgb lam mu x y hrun hfin
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ → ℝ, ∀ k,
      ℓ k = (f (x k)).toReal + Q (pt (x k) (y k)) + (g (y k)).toReal := ⟨_, fun _ => rfl⟩
  have hLz : ∀ k, L f Q g (pt (x k) (y k)) = (ℓ k : EReal) := fun k => by
    rw [hℓ]; exact L_real f Q g hfb hgb _ _ (hfin k).1 (hfin k).2
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ k,
      D k = ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖ := ⟨_, fun _ => rfl⟩
  have hD0 : ∀ k, 0 ≤ D k := fun k => by rw [hD]; exact norm_nonneg _
  have hDx : ∀ k, ‖x (k + 1) - x k‖ ≤ D k := fun k => by
    rw [hD, pt_sub]; exact norm_fst_le_pt _ _
  have hDy : ∀ k, ‖y (k + 1) - y k‖ ≤ D k := fun k => by
    rw [hD, pt_sub]; exact norm_snd_le_pt _ _
  have hDsq : ∀ k, D k ^ 2 = ‖x (k + 1) - x k‖ ^ 2 + ‖y (k + 1) - y k‖ ^ 2 := fun k => by
    rw [hD, pt_sub]; exact norm_pt_sq _ _
  have hrp : 0 < rp := hrm.trans ((hsteps 0).1.1.trans (hsteps 0).1.2)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (2 * rp) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hdesc : ∀ k, ℓ (k + 1) + a * D k ^ 2 ≤ ℓ k := by
    intro k
    have h1 := hX k (x k) (hfin k).1
    have h2 := hY k (y k) (hfin k).2
    have hl := hsteps k
    have e1 : a * ‖x (k + 1) - x k‖ ^ 2 ≤ ‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) := by
      rw [ha, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hl.1.1]) (by linarith [hl.1.2])
    have e2 : a * ‖y (k + 1) - y k‖ ^ 2 ≤ ‖y (k + 1) - y k‖ ^ 2 / (2 * mu k) := by
      rw [ha, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hl.2.1]) (by linarith [hl.2.2])
    have z1 : ‖x k - x k‖ ^ 2 / (2 * lam k) = 0 := by simp
    have z2 : ‖y k - y k‖ ^ 2 / (2 * mu k) = 0 := by simp
    rw [hDsq, hℓ, hℓ]
    nlinarith
  have hlow : ∀ k, c ≤ ℓ k := fun k => by
    have := hc (pt (x k) (y k)); rw [hLz k] at this; exact_mod_cast this
  have hanti : Antitone ℓ := antitone_nat_of_succ_le fun k => by
    have := hdesc k; have : 0 ≤ a * D k ^ 2 := by positivity
    linarith
  have hbdd : BddBelow (Set.range ℓ) := ⟨c, by rintro _ ⟨k, rfl⟩; exact hlow k⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = ⨅ k, ℓ k := ⟨_, rfl⟩
  have hℓζ : Tendsto ℓ atTop (𝓝 ζ) := by rw [hζ]; exact tendsto_atTop_ciInf hanti hbdd
  have hζle : ∀ k, ζ ≤ ℓ k := fun k => by rw [hζ]; exact ciInf_le hbdd k
  have hℓ1 : Tendsto (fun k => ℓ (k + 1)) atTop (𝓝 ζ) := hℓζ.comp (tendsto_add_atTop_nat 1)
  have hDt : Tendsto D atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (ℓ k - ℓ (k + 1)) / a) atTop (𝓝 0) := by
      simpa using (hℓζ.sub hℓ1).div_const a
    have h2 : Tendsto (fun k => Real.sqrt ((ℓ k - ℓ (k + 1)) / a)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this; exact this
    refine squeeze_zero hD0 (fun k => ?_) h2
    rw [← Real.sqrt_sq (hD0 k)]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ ha0]; nlinarith [hdesc k]
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ, Dm = Real.sqrt ((ℓ 0 - c) / a) := ⟨_, rfl⟩
  have hDmax : ∀ k, D k ≤ Dm := by
    intro k; rw [hDm, ← Real.sqrt_sq (hD0 k)]; apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ ha0]; nlinarith [hdesc k, hanti (Nat.zero_le k), hlow (k + 1)]
  have hDm0 : 0 ≤ Dm := le_trans (hD0 0) (hDmax 0)
  -- the subgradient vectors
  obtain ⟨V, hV⟩ : ∃ V : ℕ → Z n m, ∀ k, V k =
      pt (gradX Q (pt (x (k + 1)) (y (k + 1))) - gradX Q (pt (x (k + 1)) (y k)) -
        (1 / lam k) • (x (k + 1) - x k)) (-((1 / mu k) • (y (k + 1) - y k))) := ⟨_, fun _ => rfl⟩
  have hVreg : ∀ k, IsRegularSubgrad (L f Q g) (pt (x (k + 1)) (y (k + 1))) (V k) := fun k => by
    rw [hV]
    exact regsub f Q g hfb hgb hQd (lam k) (mu k) (hrm.trans (hsteps k).1.1)
      (hrm.trans (hsteps k).2.1) (x k) (x (k + 1)) (y k) (y (k + 1)) (hfin (k + 1)).1
      (hfin (k + 1)).2 (hX k) (hY k)
  have hVbd : ∀ (B : Set (Z n m)) (C : NNReal), LipschitzOnWith C (gradient Q) B → ∀ k,
      pt (x (k + 1)) (y (k + 1)) ∈ B → pt (x (k + 1)) (y k) ∈ B →
        ‖V k‖ ≤ ((C : ℝ) + 2 / rm) * D k := by
    intro B C hC k h1 h2
    rw [hV]
    have hl := hsteps k
    have hg : ‖gradX Q (pt (x (k + 1)) (y (k + 1))) - gradX Q (pt (x (k + 1)) (y k))‖ ≤
        C * D k := by
      have e : gradX Q (pt (x (k + 1)) (y (k + 1))) - gradX Q (pt (x (k + 1)) (y k)) =
          (gradient Q (pt (x (k + 1)) (y (k + 1))) - gradient Q (pt (x (k + 1)) (y k))).fst := rfl
      rw [e]
      have := hC.dist_le_mul _ h1 _ h2
      rw [dist_eq_norm, dist_eq_norm, pt_sub, sub_self, norm_pt_0v] at this
      calc _ ≤ ‖gradient Q (pt (x (k + 1)) (y (k + 1))) - gradient Q (pt (x (k + 1)) (y k))‖ := by
              conv_rhs => rw [← pt_eta (gradient Q _ - gradient Q _)]
              exact norm_fst_le_pt _ _
        _ ≤ C * ‖y (k + 1) - y k‖ := this
        _ ≤ C * D k := mul_le_mul_of_nonneg_left (hDy k) C.2
    have hlam : 0 < lam k := hrm.trans hl.1.1
    have hmu : 0 < mu k := hrm.trans hl.2.1
    have h3 : ‖(1 / lam k) • (x (k + 1) - x k)‖ ≤ 1 / rm * D k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlam)]
      exact mul_le_mul (one_div_le_one_div_of_le hrm hl.1.1.le) (hDx k) (norm_nonneg _)
        (by positivity)
    have h4 : ‖-((1 / mu k) • (y (k + 1) - y k))‖ ≤ 1 / rm * D k := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hmu)]
      exact mul_le_mul (one_div_le_one_div_of_le hrm hl.2.1.le) (hDy k) (norm_nonneg _)
        (by positivity)
    calc _ ≤ _ := norm_pt_le _ _
      _ ≤ (C * D k + 1 / rm * D k) + 1 / rm * D k :=
          add_le_add ((norm_sub_le _ _).trans (add_le_add hg h3)) h4
      _ = _ := by ring
  -- dichotomy
  by_cases hT : Tendsto (fun k => ‖pt (x k) (y k)‖) atTop atTop
  · exact Or.inl hT
  right
  rw [tendsto_atTop] at hT
  push Not at hT
  obtain ⟨R, hR⟩ := hT
  have hR1 : ∃ᶠ k in atTop, pt (x (k + 1)) (y (k + 1)) ∈ Metric.closedBall (0 : Z n m) R := by
    rw [frequently_atTop] at hR ⊢
    intro a0
    obtain ⟨b0, hb0, hb⟩ := hR (a0 + 1)
    refine ⟨b0 - 1, by omega, ?_⟩
    rw [show b0 - 1 + 1 = b0 by omega, Metric.mem_closedBall, dist_zero_right]; exact hb.le
  obtain ⟨zb, -, ψ, hψ, hψt0⟩ := tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hR1
  have hψt : Tendsto (fun j => pt (x (ψ j + 1)) (y (ψ j + 1))) atTop (𝓝 zb) := hψt0
  have hψi : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hψ1 : Tendsto (fun j => ψ j + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hψi
  have hz0 : Tendsto (fun j => pt (x (ψ j)) (y (ψ j))) atTop (𝓝 zb) := by
    have hd : Tendsto (fun j => D (ψ j)) atTop (𝓝 0) := hDt.comp hψi
    have hψn := tendsto_iff_norm_sub_tendsto_zero.mp hψt
    have hg : Tendsto (fun j => ‖pt (x (ψ j + 1)) (y (ψ j + 1)) - zb‖ + D (ψ j)) atTop (𝓝 0) := by
      simpa using hψn.add hd
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hg
    show ‖pt (x (ψ j)) (y (ψ j)) - zb‖ ≤ ‖pt (x (ψ j + 1)) (y (ψ j + 1)) - zb‖ + D (ψ j)
    have := norm_sub_le_norm_sub_add_norm_sub (pt (x (ψ j)) (y (ψ j)))
      (pt (x (ψ j + 1)) (y (ψ j + 1))) zb
    rw [norm_sub_rev (pt (x (ψ j)) (y (ψ j))) (pt (x (ψ j + 1)) (y (ψ j + 1)))] at this
    have e := hD (ψ j)
    linarith
  have hx1 : Tendsto (fun j => x (ψ j + 1)) atTop (𝓝 zb.fst) :=
    ((WithLp.continuous_fst 2 _ _).tendsto zb).comp hψt
  have hy1 : Tendsto (fun j => y (ψ j + 1)) atTop (𝓝 zb.snd) :=
    ((WithLp.continuous_snd 2 _ _).tendsto zb).comp hψt
  have hx0 : Tendsto (fun j => x (ψ j)) atTop (𝓝 zb.fst) :=
    ((WithLp.continuous_fst 2 _ _).tendsto zb).comp hz0
  have hy0 : Tendsto (fun j => y (ψ j)) atTop (𝓝 zb.snd) :=
    ((WithLp.continuous_snd 2 _ _).tendsto zb).comp hz0
  have hQt : Tendsto (fun j => Q (pt (x (ψ j + 1)) (y (ψ j + 1)))) atTop (𝓝 (Q zb)) :=
    (hQc.tendsto zb).comp hψt
  have hℓψ : ∀ j, ℓ (ψ j + 1) ≤ ℓ 0 := fun j => hanti (Nat.zero_le _)
  have lowF : ∃ r0 : ℝ, ∀ᶠ j in atTop, r0 < (f (x (ψ j + 1))).toReal := by
    obtain ⟨r0, -, hr0⟩ := EReal.lt_iff_exists_real_btwn.mp (bot_lt_iff_ne_bot.mpr (hfb zb.fst))
    refine ⟨r0, (hx1.eventually (hH.f_lsc zb.fst _ hr0)).mono
      fun j (hj : (r0 : EReal) < f (x (ψ j + 1))) => ?_⟩
    rw [← EReal.coe_toReal (hfin _).1 (hfb _)] at hj; exact_mod_cast hj
  have lowG : ∃ r0 : ℝ, ∀ᶠ j in atTop, r0 < (g (y (ψ j + 1))).toReal := by
    obtain ⟨r0, -, hr0⟩ := EReal.lt_iff_exists_real_btwn.mp (bot_lt_iff_ne_bot.mpr (hgb zb.snd))
    refine ⟨r0, (hy1.eventually (hH.g_lsc zb.snd _ hr0)).mono
      fun j (hj : (r0 : EReal) < g (y (ψ j + 1))) => ?_⟩
    rw [← EReal.coe_toReal (hfin _).2 (hgb _)] at hj; exact_mod_cast hj
  have hQe : ∀ᶠ j in atTop, Q zb - 1 < Q (pt (x (ψ j + 1)) (y (ψ j + 1))) :=
    hQt.eventually (lt_mem_nhds (by linarith))
  have hfxb : f zb.fst ≠ ⊤ := by
    intro htop
    obtain ⟨r0, hr0⟩ := lowG
    have hF : ∀ᶠ j in atTop, ((ℓ 0 - (Q zb - 1) - r0 : ℝ) : EReal) < f (x (ψ j + 1)) :=
      hx1.eventually (hH.f_lsc zb.fst _
        (show ((ℓ 0 - (Q zb - 1) - r0 : ℝ) : EReal) < f zb.fst by rw [htop]; exact EReal.coe_lt_top _))
    obtain ⟨j, hj1, hj2, hj3⟩ := (hr0.and (hQe.and hF)).exists
    rw [← EReal.coe_toReal (hfin _).1 (hfb _), EReal.coe_lt_coe_iff] at hj3
    have := hℓψ j; rw [hℓ] at this; linarith
  have hgyb : g zb.snd ≠ ⊤ := by
    intro htop
    obtain ⟨r0, hr0⟩ := lowF
    have hG : ∀ᶠ j in atTop, ((ℓ 0 - (Q zb - 1) - r0 : ℝ) : EReal) < g (y (ψ j + 1)) :=
      hy1.eventually (hH.g_lsc zb.snd _
        (show ((ℓ 0 - (Q zb - 1) - r0 : ℝ) : EReal) < g zb.snd by rw [htop]; exact EReal.coe_lt_top _))
    obtain ⟨j, hj1, hj2, hj3⟩ := (hr0.and (hQe.and hG)).exists
    rw [← EReal.coe_toReal (hfin _).2 (hgb _), EReal.coe_lt_coe_iff] at hj3
    have := hℓψ j; rw [hℓ] at this; linarith
  have hFt : Tendsto (fun j => (f (x (ψ j + 1))).toReal) atTop (𝓝 (f zb.fst).toReal) := by
    rw [tendsto_order]; constructor
    · intro a' ha'
      have : (a' : EReal) < f zb.fst := by
        rw [← EReal.coe_toReal hfxb (hfb _)]; exact_mod_cast ha'
      exact (hx1.eventually (hH.f_lsc zb.fst _ this)).mono
        fun j (hj : (a' : EReal) < f (x (ψ j + 1))) => by
        rw [← EReal.coe_toReal (hfin _).1 (hfb _)] at hj; exact_mod_cast hj
    · intro a' ha'
      have t1 : Tendsto (fun j => Q (pt zb.fst (y (ψ j)))) atTop (𝓝 (Q zb)) :=
        (hQc.tendsto _).comp (tendsto_pt tendsto_const_nhds hy0)
      have t2 : Tendsto (fun j => Q (pt (x (ψ j + 1)) (y (ψ j)))) atTop (𝓝 (Q zb)) :=
        (hQc.tendsto _).comp (tendsto_pt hx1 hy0)
      have t3 : Tendsto (fun j => ‖zb.fst - x (ψ j)‖ ^ 2 / (2 * rm)) atTop
          (𝓝 (‖zb.fst - zb.fst‖ ^ 2 / (2 * rm))) :=
        (((tendsto_const_nhds.sub hx0).norm).pow 2).div_const _
      have hU := ((tendsto_const_nhds (x := (f zb.fst).toReal)).add t1 |>.sub t2).add t3
      have hlim : (f zb.fst).toReal + Q zb - Q zb + ‖zb.fst - zb.fst‖ ^ 2 / (2 * rm) < a' := by
        simpa using ha'
      filter_upwards [hU.eventually (gt_mem_nhds hlim)] with j hj
      have h1 := hX (ψ j) zb.fst hfxb
      have hl := hsteps (ψ j)
      have hlam : 0 < lam (ψ j) := hrm.trans hl.1.1
      have e : ‖zb.fst - x (ψ j)‖ ^ 2 / (2 * lam (ψ j)) ≤ ‖zb.fst - x (ψ j)‖ ^ 2 / (2 * rm) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hl.1.1])
      have e2 : 0 ≤ ‖x (ψ j + 1) - x (ψ j)‖ ^ 2 / (2 * lam (ψ j)) := by positivity
      linarith
  have hGt : Tendsto (fun j => (g (y (ψ j + 1))).toReal) atTop (𝓝 (g zb.snd).toReal) := by
    rw [tendsto_order]; constructor
    · intro a' ha'
      have : (a' : EReal) < g zb.snd := by
        rw [← EReal.coe_toReal hgyb (hgb _)]; exact_mod_cast ha'
      exact (hy1.eventually (hH.g_lsc zb.snd _ this)).mono
        fun j (hj : (a' : EReal) < g (y (ψ j + 1))) => by
        rw [← EReal.coe_toReal (hfin _).2 (hgb _)] at hj; exact_mod_cast hj
    · intro a' ha'
      have t1 : Tendsto (fun j => Q (pt (x (ψ j + 1)) zb.snd)) atTop (𝓝 (Q zb)) :=
        (hQc.tendsto _).comp (tendsto_pt hx1 tendsto_const_nhds)
      have t3 : Tendsto (fun j => ‖zb.snd - y (ψ j)‖ ^ 2 / (2 * rm)) atTop
          (𝓝 (‖zb.snd - zb.snd‖ ^ 2 / (2 * rm))) :=
        (((tendsto_const_nhds.sub hy0).norm).pow 2).div_const _
      have hU := ((tendsto_const_nhds (x := (g zb.snd).toReal)).add t1 |>.sub hQt).add t3
      have hlim : (g zb.snd).toReal + Q zb - Q zb + ‖zb.snd - zb.snd‖ ^ 2 / (2 * rm) < a' := by
        simpa using ha'
      filter_upwards [hU.eventually (gt_mem_nhds hlim)] with j hj
      have h1 := hY (ψ j) zb.snd hgyb
      have hl := hsteps (ψ j)
      have hmu : 0 < mu (ψ j) := hrm.trans hl.2.1
      have e : ‖zb.snd - y (ψ j)‖ ^ 2 / (2 * mu (ψ j)) ≤ ‖zb.snd - y (ψ j)‖ ^ 2 / (2 * rm) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hl.2.1])
      have e2 : 0 ≤ ‖y (ψ j + 1) - y (ψ j)‖ ^ 2 / (2 * mu (ψ j)) := by positivity
      linarith
  have hℓψt : Tendsto (fun j => ℓ (ψ j + 1)) atTop (𝓝 ζ) := hℓζ.comp hψ1
  have hζv : ζ = (f zb.fst).toReal + Q zb + (g zb.snd).toReal := by
    have h2 : Tendsto (fun j => ℓ (ψ j + 1)) atTop
        (𝓝 ((f zb.fst).toReal + Q zb + (g zb.snd).toReal)) := by
      simp only [hℓ]; exact (hFt.add hQt).add hGt
    exact tendsto_nhds_unique hℓψt h2
  have hLzb : L f Q g zb = (ζ : EReal) := by
    rw [hζv]; exact L_real f Q g hfb hgb zb.fst zb.snd hfxb hgyb
  -- criticality of the cluster point
  obtain ⟨C1, hC1⟩ := hH.gradQ_lipschitz_on_bounded (Metric.closedBall zb (1 + Dm))
    Metric.isBounded_closedBall
  have hcrit : (0 : Z n m) ∈ LimitingSubdiff (L f Q g) zb := by
    refine ⟨by rw [hLzb]; exact EReal.coe_ne_top _, fun j => pt (x (ψ j + 1)) (y (ψ j + 1)),
      fun j => V (ψ j), hψt, ?_, ?_, fun j => hVreg (ψ j)⟩
    · rw [hLzb]; simp only [hLz]
      exact (continuous_coe_real_ereal.tendsto _).comp hℓψt
    · rw [tendsto_iff_norm_sub_tendsto_zero]; simp only [sub_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by simpa using (hDt.comp hψi).const_mul ((C1 : ℝ) + 2 / rm))
      filter_upwards [hψt.eventually (Metric.closedBall_mem_nhds zb one_pos)] with j hj
      apply hVbd _ C1 hC1 (ψ j)
      · exact Metric.closedBall_subset_closedBall (by linarith) hj
      · rw [dist_eq_norm] at hj
        rw [Metric.mem_closedBall, dist_eq_norm]
        have := dist_aux (x (ψ j + 1)) (y (ψ j)) (y (ψ j + 1)) zb
        linarith [hDy (ψ j), hDmax (ψ j)]
  -- KL at the cluster point
  obtain ⟨η, hη, Vn, hVn, φ, hφ, hKLi⟩ := hKL zb ⟨0, hcrit⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hVn
  obtain ⟨C, hC⟩ := hH.gradQ_lipschitz_on_bounded (Metric.closedBall zb (ρ + Dm))
    Metric.isBounded_closedBall
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (C : ℝ) + 2 / rm := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  have hsum : Summable D := by
    by_cases hex : ∃ k0, ℓ k0 = ζ
    · obtain ⟨k0, hk0⟩ := hex
      have hz : ∀ k, D (k + k0) = 0 := by
        intro k
        have h1 := hdesc (k + k0)
        have h2 : ℓ (k + k0) ≤ ℓ k0 := hanti (by omega)
        have h3 := hζle (k + k0 + 1)
        have h4 : D (k + k0) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (D (k + k0))])
          (sq_nonneg _)
        exact pow_eq_zero_iff two_ne_zero |>.mp h4
      exact (summable_nat_add_iff k0).mp (by simp only [hz]; exact summable_zero)
    · push Not at hex
      have hgt : ∀ k, ζ < ℓ k := fun k => lt_of_le_of_ne (hζle k) (Ne.symm (hex k))
      have hkl : ∀ k, ‖pt (x (k + 1)) (y (k + 1)) - zb‖ < ρ → ℓ (k + 1) < ζ + η →
          1 ≤ deriv φ (ℓ (k + 1) - ζ) * (b * ‖pt (x (k + 1)) (y (k + 1)) - pt (x k) (y k)‖) := by
        intro k h1 h2
        have hmem : pt (x (k + 1)) (y (k + 1)) ∈ Vn :=
          hball (by rw [Metric.mem_ball, dist_eq_norm]; exact h1)
        have h3 := hgt (k + 1)
        have := hKLi _ hmem (by rw [hLzb, hLz]; exact_mod_cast h3)
          (by rw [hLzb, hLz]; exact_mod_cast h2) (V k) (reg_mem_lim _ _ _ (hVreg k))
        rw [hLz, hLzb, ← EReal.coe_sub, EReal.toReal_coe] at this
        have hVk := hVbd _ C hC k
          (Metric.closedBall_subset_closedBall (ε₁ := ρ) (by linarith)
            (by rw [Metric.mem_closedBall, dist_eq_norm]; exact h1.le))
          (by
            rw [Metric.mem_closedBall, dist_eq_norm]
            have := dist_aux (x (k + 1)) (y k) (y (k + 1)) zb
            linarith [hDy k, hDmax k])
        have hd : 0 < deriv φ (ℓ (k + 1) - ζ) := hφ.2.2.2.2.2 _ ⟨by linarith, by linarith⟩
        rw [← hD, hb]
        calc (1 : ℝ) ≤ _ := this
          _ ≤ _ := mul_le_mul_of_nonneg_left hVk hd.le
      have hφc : Tendsto (fun k => φ (ℓ (k + 1) - ζ)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun k => ℓ (k + 1) - ζ) atTop (𝓝[Set.Ico 0 η] 0) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using hℓ1.sub_const ζ, ?_⟩
          filter_upwards [hℓ1.eventually (gt_mem_nhds (by linarith : ζ < ζ + η))] with k hk
          exact ⟨by linarith [hgt (k + 1)], by linarith⟩
        have := (hφ.1 0 ⟨le_rfl, hη⟩).tendsto.comp h0
        rwa [hφ.2.2.2.1] at this
      have ev1 : ∀ᶠ k in atTop, D k < ρ / 3 := hDt.eventually (gt_mem_nhds (by linarith))
      have ev2 : ∀ᶠ k in atTop, (b / a) * φ (ℓ (k + 1) - ζ) < ρ / 3 := by
        have := hφc.const_mul (b / a); rw [mul_zero] at this
        exact this.eventually (gt_mem_nhds (by linarith))
      have ev3 : ∀ᶠ k in atTop, ℓ (k + 1) < ζ + η := hℓ1.eventually (gt_mem_nhds (by linarith))
      have fr : ∃ᶠ k in atTop, ‖pt (x (k + 1)) (y (k + 1)) - zb‖ < ρ / 3 := by
        have e := hψt.eventually (Metric.ball_mem_nhds zb (by linarith : 0 < ρ / 3))
        rw [frequently_atTop]; intro a0
        obtain ⟨j, hj⟩ := (e.and (hψi.eventually_ge_atTop a0)).exists
        refine ⟨ψ j, hj.2, ?_⟩
        have := hj.1; rwa [dist_eq_norm] at this
      obtain ⟨N, hN1, hN2, hN3, hN4⟩ := (fr.and_eventually (ev1.and (ev2.and ev3))).exists
      have hs := capture (fun k => pt (x k) (y k)) ℓ ζ a b η ρ φ zb ha0 hb0 hφ
        (fun k => by have := hdesc k; rw [hD] at this; exact this) hgt hkl N
        (by rw [← hD]; linarith) hN4
      exact hs.congr fun k => (hD k).symm
  refine ⟨hsum.congr hD, zb, hcrit, ?_⟩
  have hcs : CauchySeq (fun k => pt (x k) (y k)) :=
    cauchySeq_of_summable_dist (hsum.congr fun k => by rw [hD, dist_eq_norm, norm_sub_rev])
  obtain ⟨zl, hzl⟩ := cauchySeq_tendsto_of_complete hcs
  have : zl = zb := tendsto_nhds_unique (hzl.comp hψ1) hψt
  rw [← this]; exact hzl

end P8324

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL ProxAltMin.Conv Filter Topology in
theorem solution {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hKL : ∀ z : Z n m, (LimitingSubdiff (L f Q g) z).Nonempty → HasKLProperty (L f Q g) z)
    (hrun : IsPAMRun f Q g lam mu x y) :
    Tendsto (fun k => ‖pt (x k) (y k)‖) atTop atTop ∨
      (Summable (fun k => ‖x (k + 1) - x k‖ + ‖y (k + 1) - y k‖) ∧
        ∃ zlim : Z n m, (0 : Z n m) ∈ LimitingSubdiff (L f Q g) zlim ∧
          Tendsto (fun k => pt (x k) (y k)) atTop (𝓝 zlim)) := by
  have hfb : ∀ u, f u ≠ ⊥ := hH.f_proper.1
  have hgb : ∀ v, g v ≠ ⊥ := hH.g_proper.1
  obtain ⟨u0, hu0⟩ := hH1.slice_proper
  obtain ⟨h1, h2⟩ := hrun 0
  have A : L f Q g (pt (x 1) (y 0)) ≠ ⊤ := P8324.ne_top_of_le (h1 u0) hu0
  have hf1 : f (x 1) ≠ ⊤ := fun hc => A (P8324.L_top f Q g hfb hgb _ _ (Or.inl hc))
  have B : L f Q g (pt (x 1) (y 1)) ≠ ⊤ := P8324.ne_top_of_le (h2 (y 0)) A
  have hg1 : g (y 1) ≠ ⊤ := fun hc => B (P8324.L_top f Q g hfb hgb _ _ (Or.inr hc))
  obtain ⟨c, hc⟩ := hH1.inf_gt_bot
  have hrun' : IsPAMRun f Q g (fun k => lam (k + 1)) (fun k => mu (k + 1)) (fun k => x (k + 1))
      (fun k => y (k + 1)) := fun k => hrun (k + 1)
  rcases P8324.core f Q g _ _ rm rp c _ _ hH hc hH1.rm_pos (fun k => hH1.steps (k + 1)) hKL
      hrun' hf1 hg1 with h | ⟨hs, zl, hzl, ht⟩
  · left
    exact (tendsto_add_atTop_iff_nat (f := fun k => ‖pt (x k) (y k)‖) 1).mp h
  · right
    refine ⟨?_, zl, hzl, (tendsto_add_atTop_iff_nat (f := fun k => pt (x k) (y k)) 1).mp ht⟩
    have : Summable (fun k => ‖x (k + 1 + 1) - x (k + 1)‖ + ‖y (k + 1 + 1) - y (k + 1)‖) :=
      Summable.of_nonneg_of_le (fun k => by positivity) (fun k => by
        have e1 := P8324.norm_fst_le_pt (x (k + 1 + 1) - x (k + 1)) (y (k + 1 + 1) - y (k + 1))
        have e2 := P8324.norm_snd_le_pt (x (k + 1 + 1) - x (k + 1)) (y (k + 1 + 1) - y (k + 1))
        rw [← P8324.pt_sub] at e1 e2
        show _ ≤ 2 * _
        linarith) (hs.mul_left 2)
    exact (summable_nat_add_iff (f := fun k => ‖x (k + 1) - x k‖ + ‖y (k + 1) - y k‖) 1).mp this
