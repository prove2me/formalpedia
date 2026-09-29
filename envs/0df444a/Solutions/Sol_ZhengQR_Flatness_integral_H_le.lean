-- Prove2me | solution 1 for ZhengQR.Flatness.integral_H_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:22:18.115813+00:00
-- url     : https://prove2.me/submissions/27b101c5-da55-4c41-8d1d-a4e0cb50f2a1

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

open MeasureTheory Set

lemma aux_ihl_integrable (M : QRModel) (y : ℝ) :
    Integrable (fun x : ℝ => M.h * max (y - x) 0 + M.p * max (x - y) 0) M.μ := by
  have := M.isProb
  have h1 : Integrable (fun x : ℝ => y - x) M.μ := (integrable_const y).sub M.integrable
  have h2 : Integrable (fun x : ℝ => x - y) M.μ := M.integrable.sub (integrable_const y)
  exact (h1.pos_part.const_mul M.h).add (h2.pos_part.const_mul M.p)

lemma aux_ihl_G (M : QRModel) (y : ℝ) :
    M.G y = ∫ x, (M.h * max (y - x) 0 + M.p * max (x - y) 0) ∂M.μ := rfl

lemma aux_ihl_right (M : QRModel) (y t : ℝ) (ht : 0 ≤ t) :
    M.G (y + t) ≤ M.G y + M.h * t := by
  have := M.isProb
  rw [aux_ihl_G, aux_ihl_G]
  have hi := aux_ihl_integrable M y
  calc ∫ x, (M.h * max (y + t - x) 0 + M.p * max (x - (y + t)) 0) ∂M.μ
      ≤ ∫ x, ((M.h * max (y - x) 0 + M.p * max (x - y) 0) + M.h * t) ∂M.μ := by
        apply integral_mono (aux_ihl_integrable M (y + t)) (hi.add (integrable_const _))
        intro x
        have hh := M.h_pos
        have hp := M.p_pos
        have e1 : max (y + t - x) 0 ≤ max (y - x) 0 + t := by
          apply max_le
          · linarith [le_max_left (y - x) 0]
          · linarith [le_max_right (y - x) 0]
        have e2 : max (x - (y + t)) 0 ≤ max (x - y) 0 := by
          apply max_le
          · linarith [le_max_left (x - y) 0]
          · exact le_max_right _ _
        simp only [Pi.add_apply]
        nlinarith [mul_le_mul_of_nonneg_left e1 hh.le, mul_le_mul_of_nonneg_left e2 hp.le]
    _ = _ := by
        rw [integral_add hi (integrable_const _), integral_const]
        simp

lemma aux_ihl_left (M : QRModel) (y t : ℝ) (ht : 0 ≤ t) :
    M.G (y - t) ≤ M.G y + M.p * t := by
  have := M.isProb
  rw [aux_ihl_G, aux_ihl_G]
  have hi := aux_ihl_integrable M y
  calc ∫ x, (M.h * max (y - t - x) 0 + M.p * max (x - (y - t)) 0) ∂M.μ
      ≤ ∫ x, ((M.h * max (y - x) 0 + M.p * max (x - y) 0) + M.p * t) ∂M.μ := by
        apply integral_mono (aux_ihl_integrable M (y - t)) (hi.add (integrable_const _))
        intro x
        have hh := M.h_pos
        have hp := M.p_pos
        have e1 : max (y - t - x) 0 ≤ max (y - x) 0 := by
          apply max_le
          · linarith [le_max_left (y - x) 0]
          · exact le_max_right _ _
        have e2 : max (x - (y - t)) 0 ≤ max (x - y) 0 + t := by
          apply max_le
          · linarith [le_max_left (x - y) 0]
          · linarith [le_max_right (x - y) 0]
        simp only [Pi.add_apply]
        nlinarith [mul_le_mul_of_nonneg_left e1 hh.le, mul_le_mul_of_nonneg_left e2 hp.le]
    _ = _ := by
        rw [integral_add hi (integrable_const _), integral_const]
        simp

lemma aux_ihl_lb1 (M : QRModel) (z : ℝ) : M.h * (z - ∫ x, x ∂M.μ) ≤ M.G z := by
  have := M.isProb
  rw [aux_ihl_G]
  have hi : Integrable (fun x : ℝ => M.h * (z - x)) M.μ :=
    ((integrable_const z).sub M.integrable).const_mul M.h
  have e : M.h * (z - ∫ x, x ∂M.μ) = ∫ x, M.h * (z - x) ∂M.μ := by
    rw [integral_const_mul, integral_sub (integrable_const z) M.integrable, integral_const]
    simp
  rw [e]
  apply integral_mono hi (aux_ihl_integrable M z)
  intro x
  have hh := M.h_pos
  have hp := M.p_pos
  have e1 : z - x ≤ max (z - x) 0 := le_max_left _ _
  have e2 : 0 ≤ max (x - z) 0 := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left e1 hh.le, mul_nonneg hp.le e2]

lemma aux_ihl_lb2 (M : QRModel) (z : ℝ) : M.p * ((∫ x, x ∂M.μ) - z) ≤ M.G z := by
  have := M.isProb
  rw [aux_ihl_G]
  have hi : Integrable (fun x : ℝ => M.p * (x - z)) M.μ :=
    (M.integrable.sub (integrable_const z)).const_mul M.p
  have e : M.p * ((∫ x, x ∂M.μ) - z) = ∫ x, M.p * (x - z) ∂M.μ := by
    rw [integral_const_mul, integral_sub M.integrable (integrable_const z), integral_const]
    simp
  rw [e]
  apply integral_mono hi (aux_ihl_integrable M z)
  intro x
  have hh := M.h_pos
  have hp := M.p_pos
  have e1 : x - z ≤ max (x - z) 0 := le_max_left _ _
  have e2 : 0 ≤ max (z - x) 0 := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left e1 hp.le, mul_nonneg hh.le e2]

lemma aux_ihl_convex (M : QRModel) : ConvexOn ℝ univ M.G := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have := M.isProb
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  have ix := (aux_ihl_integrable M x).const_mul a
  have iy := (aux_ihl_integrable M y).const_mul (1 - a)
  rw [aux_ihl_G, aux_ihl_G, aux_ihl_G, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ix iy]
  apply integral_mono (aux_ihl_integrable M _) (ix.add iy)
  intro t
  have hh := M.h_pos
  have hp := M.p_pos
  have e1 : max (a * x + (1 - a) * y - t) 0 ≤ a * max (x - t) 0 + (1 - a) * max (y - t) 0 := by
    apply max_le
    · nlinarith [mul_nonneg ha (sub_nonneg.2 (le_max_left (x - t) 0)),
        mul_nonneg hb (sub_nonneg.2 (le_max_left (y - t) 0))]
    · nlinarith [mul_nonneg ha (le_max_right (x - t) 0), mul_nonneg hb (le_max_right (y - t) 0)]
  have e2 : max (t - (a * x + (1 - a) * y)) 0 ≤ a * max (t - x) 0 + (1 - a) * max (t - y) 0 := by
    apply max_le
    · nlinarith [mul_nonneg ha (sub_nonneg.2 (le_max_left (t - x) 0)),
        mul_nonneg hb (sub_nonneg.2 (le_max_left (t - y) 0))]
    · nlinarith [mul_nonneg ha (le_max_right (t - x) 0), mul_nonneg hb (le_max_right (t - y) 0)]
  show M.h * max (a * x + (1 - a) * y - t) 0 + M.p * max (t - (a * x + (1 - a) * y)) 0 ≤
    a * (M.h * max (x - t) 0 + M.p * max (t - x) 0) +
      (1 - a) * (M.h * max (y - t) 0 + M.p * max (t - y) 0)
  nlinarith [mul_le_mul_of_nonneg_left e1 hh.le, mul_le_mul_of_nonneg_left e2 hp.le]

lemma aux_ihl_cont (M : QRModel) : Continuous M.G := by
  have hh := M.h_pos
  have hp := M.p_pos
  have key : ∀ x y, dist (M.G x) (M.G y) ≤ (M.h + M.p) * dist x y := by
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total x y with hxy | hxy
    · have h1 := aux_ihl_right M x (y - x) (by linarith)
      have h2 := aux_ihl_left M y (y - x) (by linarith)
      rw [show x + (y - x) = y by ring] at h1
      rw [show y - (y - x) = x by ring] at h2
      rw [abs_sub_comm x y, abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x), abs_le]
      have hd : 0 ≤ y - x := by linarith
      constructor <;> nlinarith [mul_nonneg hh.le hd, mul_nonneg hp.le hd]
    · have h1 := aux_ihl_right M y (x - y) (by linarith)
      have h2 := aux_ihl_left M x (x - y) (by linarith)
      rw [show y + (x - y) = x by ring] at h1
      rw [show x - (x - y) = y by ring] at h2
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y), abs_le]
      have hd : 0 ≤ x - y := by linarith
      constructor <;> nlinarith [mul_nonneg hh.le hd, mul_nonneg hp.le hd]
  exact (LipschitzWith.of_dist_le' key).continuous

lemma aux_ihl_incr (G : ℝ → ℝ) (hG : ConvexOn ℝ univ G) (x y d : ℝ) (hxy : x ≤ y)
    (hd : 0 ≤ d) : G (x + d) - G x ≤ G (y + d) - G y := by
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · exact le_rfl
  rcases eq_or_lt_of_le hd with rfl | hd'
  · simp
  have hLpos : 0 < y + d - x := by linarith
  have hs : 0 ≤ (y - x) / (y + d - x) := div_nonneg (by linarith) hLpos.le
  have ht : 0 ≤ d / (y + d - x) := div_nonneg hd hLpos.le
  have hst : (y - x) / (y + d - x) + d / (y + d - x) = 1 := by
    field_simp; ring
  have hts : d / (y + d - x) + (y - x) / (y + d - x) = 1 := by linarith
  have h1 := hG.2 (mem_univ x) (mem_univ (y + d)) hs ht hst
  have h2 := hG.2 (mem_univ x) (mem_univ (y + d)) ht hs hts
  simp only [smul_eq_mul] at h1 h2
  have e1 : (y - x) / (y + d - x) * x + d / (y + d - x) * (y + d) = x + d := by
    field_simp; ring
  have e2 : d / (y + d - x) * x + (y - x) / (y + d - x) * (y + d) = y := by
    field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have htv : d / (y + d - x) = 1 - (y - x) / (y + d - x) := by linarith
  rw [htv] at h1 h2
  nlinarith

lemma aux_ihl_deriv (G : ℝ → ℝ) (hG : Continuous G) (Q r : ℝ) :
    HasDerivAt (fun r => ∫ y in r..r + Q, G y) (G (r + Q) - G r) r := by
  have e : (fun r => ∫ y in r..r + Q, G y) =
      fun r => (∫ y in (0:ℝ)..r + Q, G y) - ∫ y in (0:ℝ)..r, G y := by
    funext r
    rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
  rw [e]
  have h1 : HasDerivAt (fun r => ∫ y in (0:ℝ)..r + Q, G y) (G (r + Q)) r :=
    ((hG.integral_hasStrictDerivAt 0 (r + Q)).hasDerivAt).comp_add_const r Q
  have h2 : HasDerivAt (fun r => ∫ y in (0:ℝ)..r, G y) (G r) r :=
    (hG.integral_hasStrictDerivAt 0 r).hasDerivAt
  exact h1.sub h2

lemma aux_ihl_exists (G : ℝ → ℝ) (hc : Continuous G) (hconv : ConvexOn ℝ univ G)
    (hmin : ∃ y0, ∀ z, G y0 ≤ G z) (Q : ℝ) (hQ : 0 < Q) :
    ∃ r, ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  obtain ⟨y0, hy0⟩ := hmin
  have hφc : Continuous (fun r => G (r + Q) - G r) := by fun_prop
  have h0 : (0:ℝ) ∈ Icc ((fun r => G (r + Q) - G r) (y0 - Q)) ((fun r => G (r + Q) - G r) y0) := by
    constructor
    · simp only [sub_add_cancel]; linarith [hy0 (y0 - Q)]
    · simp only; linarith [hy0 (y0 + Q)]
  obtain ⟨r0, -, hr0⟩ :=
    intermediate_value_Icc (show y0 - Q ≤ y0 by linarith) hφc.continuousOn h0
  simp only at hr0
  refine ⟨r0, fun r' => ?_⟩
  have hder : ∀ r, HasDerivAt (fun r => ∫ y in r..r + Q, G y) (G (r + Q) - G r) r :=
    fun r => aux_ihl_deriv G hc Q r
  have hFc : Continuous (fun r => ∫ y in r..r + Q, G y) :=
    continuous_iff_continuousAt.2 fun r => (hder r).continuousAt
  have hmono : ∀ a b, a ≤ b → G (a + Q) - G a ≤ G (b + Q) - G b :=
    fun a b hab => aux_ihl_incr G hconv a b Q hab hQ.le
  rcases le_total r0 r' with h | h
  · have hm : MonotoneOn (fun r => ∫ y in r..r + Q, G y) (Ici r0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici r0) hFc.continuousOn
      · intro x _; exact (hder x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        rw [(hder x).deriv]
        have := hmono r0 x (le_of_lt hx)
        linarith
    exact hm (Set.mem_Ici.2 le_rfl) h h
  · have hm : AntitoneOn (fun r => ∫ y in r..r + Q, G y) (Iic r0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic r0) hFc.continuousOn
      · intro x _; exact (hder x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Iic] at hx
        rw [(hder x).deriv]
        have := hmono x r0 (le_of_lt hx)
        linarith
    exact hm h (Set.mem_Iic.2 le_rfl) h

lemma aux_ihl_isOpt (G : ℝ → ℝ) (hc : Continuous G) (hconv : ConvexOn ℝ univ G)
    (hmin : ∃ y0, ∀ z, G y0 ≤ G z) (lam K Q : ℝ) (hQ : 0 < Q) :
    IsOptReorder G lam K Q (optReorder G lam K Q) := by
  have hex : ∃ r, IsOptReorder G lam K Q r := by
    obtain ⟨r, hr⟩ := aux_ihl_exists G hc hconv hmin Q hQ
    refine ⟨r, fun r' => ?_⟩
    unfold qrCost
    exact div_le_div_of_nonneg_right (by linarith [hr r']) hQ.le
  unfold optReorder
  rw [dif_pos hex]
  exact hex.choose_spec

lemma aux_ihl_eq (G : ℝ → ℝ) (hc : Continuous G) (lam K Q r : ℝ) (hQ : 0 < Q)
    (hr : IsOptReorder G lam K Q r) : G r = G (r + Q) := by
  have hloc : IsLocalMin (fun r => qrCost G lam K Q r) r :=
    Filter.Eventually.of_forall (fun r' => hr r')
  have hd : HasDerivAt (fun r => qrCost G lam K Q r) ((G (r + Q) - G r) / Q) r := by
    unfold qrCost
    exact ((aux_ihl_deriv G hc Q r).const_add (lam * K)).div_const Q
  have := hloc.hasDerivAt_eq_zero hd
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · linarith
  · linarith

lemma aux_ihl_level (G : ℝ → ℝ) (hconv : ConvexOn ℝ univ G) (r1 Q : ℝ) (hQ : 0 < Q)
    (heq : G r1 = G (r1 + Q)) (r : ℝ) : G r1 ≤ max (G r) (G (r + Q)) := by
  rcases lt_trichotomy r r1 with h | rfl | h
  · have : G r1 ≤ G r := by
      apply hconv.le_left_of_right_le (mem_univ r) (mem_univ (r1 + Q))
      · rw [openSegment_eq_Ioo (by linarith)]; exact ⟨h, by linarith⟩
      · rw [heq]
    exact le_max_of_le_left this
  · exact le_max_left _ _
  · have : G (r1 + Q) ≤ G (r + Q) := by
      apply hconv.le_right_of_left_le (mem_univ r1) (mem_univ (r + Q))
      · rw [openSegment_eq_Ioo (by linarith)]; exact ⟨by linarith, by linarith⟩
      · rw [heq]
    rw [heq]; exact le_max_of_le_right this

lemma aux_ihl_facts (M : QRModel) :
    Continuous M.G ∧ ConvexOn ℝ univ M.G ∧ ∃ y0, ∀ z, M.G y0 ≤ M.G z :=
  ⟨aux_ihl_cont M, aux_ihl_convex M, M.unique_min.exists⟩

lemma aux_ihl_Hval (M : QRModel) (y : ℝ) (hy : 0 < y) :
    M.H y = M.G (optReorder M.G M.lam M.K y) := by
  show Hfun M.G M.lam M.K y = _
  unfold Hfun
  rw [if_pos hy]

lemma aux_ihl_opteq (M : QRModel) (y : ℝ) (hy : 0 < y) :
    M.G (optReorder M.G M.lam M.K y) = M.G (optReorder M.G M.lam M.K y + y) := by
  obtain ⟨hc, hconv, hmin⟩ := aux_ihl_facts M
  exact aux_ihl_eq M.G hc M.lam M.K y _ hy (aux_ihl_isOpt M.G hc hconv hmin M.lam M.K y hy)

lemma aux_ihl_mono (M : QRModel) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : M.H a ≤ M.H b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨hc, hconv, hmin⟩ := aux_ihl_facts M
  rw [aux_ihl_Hval M a ha, aux_ihl_Hval M b hb]
  have hea := aux_ihl_opteq M a ha
  have heb := aux_ihl_opteq M b hb
  have h1 := aux_ihl_level M.G hconv _ a ha hea (optReorder M.G M.lam M.K b)
  have h2 : M.G (optReorder M.G M.lam M.K b + a) ≤
      max (M.G (optReorder M.G M.lam M.K b)) (M.G (optReorder M.G M.lam M.K b + b)) := by
    apply hconv.le_on_segment (mem_univ _) (mem_univ _)
    rw [segment_eq_Icc (by linarith)]
    exact ⟨by linarith, by linarith⟩
  rw [← heb, max_self] at h2
  exact h1.trans (max_le le_rfl h2)

lemma aux_ihl_scale (M : QRModel) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    a * M.H b ≤ b * M.H a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨hc, hconv, hmin⟩ := aux_ihl_facts M
  have hh := M.h_pos
  have hp := M.p_pos
  rw [aux_ihl_Hval M a ha, aux_ihl_Hval M b hb]
  have hea := aux_ihl_opteq M a ha
  have heb := aux_ihl_opteq M b hb
  generalize optReorder M.G M.lam M.K a = ra at hea ⊢
  generalize optReorder M.G M.lam M.K b = rb at heb ⊢
  have j1 : M.p * ((∫ x, x ∂M.μ) - ra) ≤ M.G ra := aux_ihl_lb2 M ra
  have j2 : M.h * (ra + a - ∫ x, x ∂M.μ) ≤ M.G ra := by rw [hea]; exact aux_ihl_lb1 M (ra + a)
  have hw : a * (M.h * M.p) ≤ M.G ra * (M.h + M.p) := by
    nlinarith [mul_le_mul_of_nonneg_left j1 hh.le, mul_le_mul_of_nonneg_left j2 hp.le]
  have he : 0 ≤ b - a := by linarith
  have hs : 0 < M.h + M.p := by linarith
  have hu : 0 ≤ (b - a) * M.h / (M.h + M.p) := by positivity
  have hv : 0 ≤ (b - a) * M.p / (M.h + M.p) := by positivity
  have huv : (b - a) * M.h / (M.h + M.p) + (b - a) * M.p / (M.h + M.p) = b - a := by
    field_simp
  have g1 := aux_ihl_left M ra _ hu
  have g2 := aux_ihl_right M (ra + a) _ hv
  rw [← hea] at g2
  have h1 := aux_ihl_level M.G hconv rb b hb heb (ra - (b - a) * M.h / (M.h + M.p))
  have e1 : ra - (b - a) * M.h / (M.h + M.p) + b = ra + a + (b - a) * M.p / (M.h + M.p) := by
    linarith
  rw [e1] at h1
  have hpu : M.p * ((b - a) * M.h / (M.h + M.p)) = (b - a) * (M.h * M.p) / (M.h + M.p) := by
    field_simp
  have hhv : M.h * ((b - a) * M.p / (M.h + M.p)) = (b - a) * (M.h * M.p) / (M.h + M.p) := by
    field_simp
  have key : a * ((b - a) * (M.h * M.p) / (M.h + M.p)) ≤ (b - a) * M.G ra := by
    rw [show a * ((b - a) * (M.h * M.p) / (M.h + M.p)) =
      (b - a) * (a * (M.h * M.p)) / (M.h + M.p) by ring, div_le_iff₀ hs]
    nlinarith [mul_le_mul_of_nonneg_left hw he]
  have hmax : max (M.G (ra - (b - a) * M.h / (M.h + M.p)))
      (M.G (ra + a + (b - a) * M.p / (M.h + M.p))) ≤
      M.G ra + (b - a) * (M.h * M.p) / (M.h + M.p) :=
    max_le (by linarith) (by linarith)
  calc a * M.G rb ≤ a * (M.G ra + (b - a) * (M.h * M.p) / (M.h + M.p)) :=
        mul_le_mul_of_nonneg_left (h1.trans hmax) ha.le
    _ = a * M.G ra + a * ((b - a) * (M.h * M.p) / (M.h + M.p)) := by ring
    _ ≤ a * M.G ra + (b - a) * M.G ra := by linarith
    _ = b * M.G ra := by ring

end ZhengQR.Flatness

open ZhengQR.Flatness

theorem solution (M : QRModel) (α Q : ℝ) (hα : 0 < α) (hQ : 0 < Q) :
    (∫ y in Q..α * Q, M.H y) ≤ (α ^ 2 - 1) / 2 * Q * M.H Q := by
  have hαQ : 0 < α * Q := mul_pos hα hQ
  have hmonoOn : MonotoneOn M.H (Set.uIcc Q (α * Q)) := by
    intro x hx y _ hxy
    have hx0 : 0 < x := by
      rcases Set.mem_uIcc.1 hx with h | h
      · linarith [h.1]
      · linarith [h.1]
    exact aux_ihl_mono M x y hx0 hxy
  have hint : IntervalIntegrable M.H MeasureTheory.volume Q (α * Q) :=
    hmonoOn.intervalIntegrable
  have hlin : IntervalIntegrable (fun y : ℝ => y * M.H Q / Q) MeasureTheory.volume Q (α * Q) :=
    ((continuous_id.mul continuous_const).div_const Q).intervalIntegrable _ _
  have hcomp : (∫ y in Q..α * Q, y * M.H Q / Q) = (α ^ 2 - 1) / 2 * Q * M.H Q := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const, integral_id]
    field_simp
  rcases le_total 1 α with h1 | h1
  · have hle : Q ≤ α * Q := by nlinarith
    rw [← hcomp]
    apply intervalIntegral.integral_mono_on hle hint hlin
    intro y hy
    have := aux_ihl_scale M Q y hQ hy.1
    rw [le_div_iff₀ hQ]
    linarith
  · have hle : α * Q ≤ Q := by nlinarith
    rw [intervalIntegral.integral_symm (α * Q) Q, ← hcomp,
      intervalIntegral.integral_symm (α * Q) Q, neg_le_neg_iff]
    apply intervalIntegral.integral_mono_on hle hlin.symm hint.symm
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hαQ hy.1
    have := aux_ihl_scale M y Q hy0 hy.2
    rw [div_le_iff₀ hQ]
    linarith
