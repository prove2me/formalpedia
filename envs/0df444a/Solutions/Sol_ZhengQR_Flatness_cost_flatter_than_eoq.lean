-- Prove2me | solution 1 for ZhengQR.Flatness.cost_flatter_than_eoq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:00:09.194909+00:00
-- url     : https://prove2.me/submissions/c05f59ac-8902-4ab8-8b67-b7945682e7ae

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

theorem ihl_thm (M : QRModel) (α Q : ℝ) (hα : 0 < α) (hQ : 0 < Q) :
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

open Filter Topology
lemma aux_cif_int (M : QRModel) (y : ℝ) :
    Integrable (fun x : ℝ => M.h * max (y - x) 0 + M.p * max (x - y) 0) M.μ := by
  have := M.isProb
  have h1 : Integrable (fun x : ℝ => y - x) M.μ := (integrable_const y).sub M.integrable
  have h2 : Integrable (fun x : ℝ => x - y) M.μ := M.integrable.sub (integrable_const y)
  exact (h1.pos_part.const_mul M.h).add (h2.pos_part.const_mul M.p)

lemma aux_cif_lip (M : QRModel) (y y' : ℝ) :
    |M.G y - M.G y'| ≤ (M.h + M.p) * |y - y'| := by
  have := M.isProb
  have hh := M.h_pos.le
  have hp := M.p_pos.le
  show |newsvendorCost M.h M.p M.μ y - newsvendorCost M.h M.p M.μ y'| ≤ _
  unfold newsvendorCost
  rw [← integral_sub (aux_cif_int M y) (aux_cif_int M y')]
  have hb : ∀ x : ℝ, ‖(M.h * max (y - x) 0 + M.p * max (x - y) 0) -
      (M.h * max (y' - x) 0 + M.p * max (x - y') 0)‖ ≤ (M.h + M.p) * |y - y'| := by
    intro x
    rw [Real.norm_eq_abs]
    have e1 : |max (y - x) 0 - max (y' - x) 0| ≤ |y - y'| := by
      have := abs_max_sub_max_le_abs (y - x) (y' - x) 0
      rw [show y - x - (y' - x) = y - y' by ring] at this
      exact this
    have e2 : |max (x - y) 0 - max (x - y') 0| ≤ |y - y'| := by
      have := abs_max_sub_max_le_abs (x - y) (x - y') 0
      rw [show x - y - (x - y') = -(y - y') by ring, abs_neg] at this
      exact this
    calc |(M.h * max (y - x) 0 + M.p * max (x - y) 0) -
          (M.h * max (y' - x) 0 + M.p * max (x - y') 0)|
        = |M.h * (max (y - x) 0 - max (y' - x) 0) +
            M.p * (max (x - y) 0 - max (x - y') 0)| := by congr 1; ring
      _ ≤ |M.h * (max (y - x) 0 - max (y' - x) 0)| +
            |M.p * (max (x - y) 0 - max (x - y') 0)| := abs_add_le _ _
      _ = M.h * |max (y - x) 0 - max (y' - x) 0| +
            M.p * |max (x - y) 0 - max (x - y') 0| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hh, abs_of_nonneg hp]
      _ ≤ M.h * |y - y'| + M.p * |y - y'| := by gcongr
      _ = (M.h + M.p) * |y - y'| := by ring
  have := norm_integral_le_of_norm_le_const (μ := M.μ) (Filter.Eventually.of_forall hb)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma aux_cif_convex (M : QRModel) : ConvexOn ℝ univ M.G := by
  have := M.isProb
  have hh := M.h_pos.le
  have hp := M.p_pos.le
  refine ⟨convex_univ, ?_⟩
  intro y1 _ y2 _ a b ha hb hab
  simp only [smul_eq_mul]
  show newsvendorCost M.h M.p M.μ (a * y1 + b * y2) ≤
    a * newsvendorCost M.h M.p M.μ y1 + b * newsvendorCost M.h M.p M.μ y2
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_cif_int M y1).const_mul a) ((aux_cif_int M y2).const_mul b)]
  refine integral_mono (aux_cif_int M _)
    (((aux_cif_int M y1).const_mul a).add ((aux_cif_int M y2).const_mul b)) ?_
  intro x
  simp only
  have c1 : a * y1 + b * y2 - x = a * (y1 - x) + b * (y2 - x) := by
    linear_combination x * hab
  have c2 : x - (a * y1 + b * y2) = a * (x - y1) + b * (x - y2) := by
    linear_combination (-x) * hab
  have e1 : max (a * y1 + b * y2 - x) 0 ≤ a * max (y1 - x) 0 + b * max (y2 - x) 0 := by
    apply max_le
    · rw [c1]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have e2 : max (x - (a * y1 + b * y2)) 0 ≤ a * max (x - y1) 0 + b * max (x - y2) 0 := by
    apply max_le
    · rw [c2]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  nlinarith [mul_le_mul_of_nonneg_left e1 hh, mul_le_mul_of_nonneg_left e2 hp]

lemma aux_cif_P {G : ℝ → ℝ} (hc : ConvexOn ℝ univ G) {a b : ℝ} (hab : a < b)
    (he : G a = G b) :
    (∀ y ∈ Icc a b, G y ≤ G a) ∧ (∀ y, y ∉ Ioc a b → G a ≤ G y) := by
  constructor
  · intro y hy
    have := hc.le_on_segment (mem_univ a) (mem_univ b)
      (show y ∈ segment ℝ a b by rw [segment_eq_Icc hab.le]; exact hy)
    rw [← he, max_self] at this
    exact this
  · intro y hy
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with hy | hy
    · rcases hy.lt_or_eq with hy | hy
      · exact hc.le_left_of_right_le (mem_univ y) (mem_univ b)
          (show a ∈ openSegment ℝ y b by rw [openSegment_eq_Ioo (hy.trans hab)]; exact ⟨hy, hab⟩)
          (le_of_eq he.symm)
      · rw [hy]
    · have := hc.le_right_of_left_le (mem_univ a) (mem_univ y)
        (show b ∈ openSegment ℝ a y by rw [openSegment_eq_Ioo (hab.trans hy)]; exact ⟨hab, hy⟩)
        (le_of_eq he)
      rw [he]; exact this

lemma aux_cif_L {G : ℝ → ℝ} (hG : Continuous G) (hc : ConvexOn ℝ univ G) {a b : ℝ}
    (hab : a < b) (he : G a = G b) (r q : ℝ) (hq : 0 ≤ q) :
    (∫ y in a..b, G y) + (q - (b - a)) * G a ≤ ∫ y in r..r + q, G y := by
  obtain ⟨P1, P2⟩ := aux_cif_P hc hab he
  have hg : Continuous (fun y => G y - G a) := hG.sub continuous_const
  have eI : ∫ y in r..r + q, (G y - G a) = (∫ y in r..r + q, G y) - q * G a := by
    rw [intervalIntegral.integral_sub (hG.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have eJ : ∫ y in a..b, (G y - G a) = (∫ y in a..b, G y) - (b - a) * G a := by
    rw [intervalIntegral.integral_sub (hG.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have key : ∫ y in a..b, (G y - G a) ≤ ∫ y in r..r + q, (G y - G a) := by
    rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le (by linarith)]
    have hIi : IntegrableOn (fun y => G y - G a) (Ioc r (r + q)) := hg.integrableOn_Ioc
    have hJi : IntegrableOn (fun y => G y - G a) (Ioc a b) := hg.integrableOn_Ioc
    have s1 := integral_inter_add_sdiff (s := Ioc r (r + q)) (t := Ioc a b)
      measurableSet_Ioc hIi
    have s2 := integral_inter_add_sdiff (s := Ioc a b) (t := Ioc r (r + q))
      measurableSet_Ioc hJi
    rw [inter_comm (Ioc a b) (Ioc r (r + q))] at s2
    have h1 : 0 ≤ ∫ y in Ioc r (r + q) \ Ioc a b, (G y - G a) :=
      setIntegral_nonneg (measurableSet_Ioc.diff measurableSet_Ioc)
        (fun y hy => by have := P2 y hy.2; linarith)
    have h2 : ∫ y in Ioc a b \ Ioc r (r + q), (G y - G a) ≤ 0 :=
      setIntegral_nonpos (measurableSet_Ioc.diff measurableSet_Ioc)
        (fun y hy => by have := P1 y (Ioc_subset_Icc_self hy.1); linarith)
    linarith
  linarith

lemma aux_cif_foc {G : ℝ → ℝ} (hG : Continuous G) (q r : ℝ)
    (hmin : ∀ r', (∫ y in r..r + q, G y) ≤ ∫ y in r'..r' + q, G y) : G r = G (r + q) := by
  have hd : ∀ s, HasDerivAt (fun s => ∫ y in s..s + q, G y) (G (s + q) - G s) s := by
    intro s
    have h1 : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, G x) (G (s + q)) (s + q) :=
      (hG.integral_hasStrictDerivAt 0 (s + q)).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s + q) 1 s := (hasDerivAt_id' s).add_const q
    have h3 := (h1.comp s h2).sub (hG.integral_hasStrictDerivAt 0 s).hasDerivAt
    rw [mul_one] at h3
    have e : (fun s => ∫ y in s..s + q, G y) =
        ((fun u => ∫ x in (0:ℝ)..u, G x) ∘ fun s => s + q) - fun u => ∫ x in (0:ℝ)..u, G x := by
      funext t
      simp only [Function.comp, Pi.sub_apply]
      rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
        (hG.intervalIntegrable _ _)]
    rw [e]
    exact h3
  have hlm : IsLocalMin (fun s => ∫ y in s..s + q, G y) r := Filter.Eventually.of_forall hmin
  have := hlm.hasDerivAt_eq_zero (hd r)
  linarith

lemma aux_cif_ivt {G : ℝ → ℝ} (hG : Continuous G) {y0 : ℝ} (hy0 : ∀ z, G y0 ≤ G z) {q : ℝ}
    (hq : 0 < q) : ∃ r, G r = G (r + q) := by
  have hc : ContinuousOn (fun s => G (s + q) - G s) (Icc (y0 - q) y0) :=
    ((hG.comp (continuous_add_const q)).sub hG).continuousOn
  have h0 : (0:ℝ) ∈ Icc ((fun s => G (s + q) - G s) (y0 - q)) ((fun s => G (s + q) - G s) y0) := by
    simp only [sub_add_cancel]
    constructor
    · linarith [hy0 (y0 - q)]
    · linarith [hy0 (y0 + q)]
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by linarith) hc h0
  exact ⟨s, by simp only at hs; linarith⟩

lemma aux_cif_opt {G : ℝ → ℝ} (hG : Continuous G) (hc : ConvexOn ℝ univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K : ℝ) {q : ℝ} (hq : 0 < q) :
    (∀ r', (∫ y in optReorder G lam K q..optReorder G lam K q + q, G y) ≤
      ∫ y in r'..r' + q, G y) ∧
    G (optReorder G lam K q) = G (optReorder G lam K q + q) := by
  obtain ⟨s, hs⟩ := aux_cif_ivt hG hy0 hq
  have hex : ∃ r, IsOptReorder G lam K q r := by
    refine ⟨s, fun r' => ?_⟩
    unfold qrCost
    have := aux_cif_L hG hc (show s < s + q by linarith) hs r' q hq.le
    rw [show q - (s + q - s) = 0 by ring, zero_mul, add_zero] at this
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have hopt : IsOptReorder G lam K q (optReorder G lam K q) := by
    unfold optReorder
    rw [dif_pos hex]
    exact hex.choose_spec
  have hmin : ∀ r', (∫ y in optReorder G lam K q..optReorder G lam K q + q, G y) ≤
      ∫ y in r'..r' + q, G y := by
    intro r'
    have := hopt r'
    unfold qrCost at this
    rw [div_le_div_iff_of_pos_right hq] at this
    linarith
  exact ⟨hmin, aux_cif_foc hG q _ hmin⟩

lemma aux_cif_main (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in M.r Q..M.r Q + Q, M.G y) = (∫ y in (0 : ℝ)..Q, M.H y) := by
  have hG : Continuous M.G := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (M.h + M.p)) fun y y' => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [M.h_pos, M.p_pos])]
    exact aux_cif_lip M y y'
  have hc := aux_cif_convex M
  obtain ⟨y1, hy1, -⟩ := M.unique_min
  have hex : ∃ y, ∀ z, M.G y ≤ M.G z := ⟨y1, hy1⟩
  have hy0 : ∀ z, M.G (minPoint M.G) ≤ M.G z := by
    unfold minPoint
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨F, hFq⟩ : ∃ F : ℝ → ℝ, ∀ q, F q = ∫ y in M.r q..M.r q + q, M.G y :=
    ⟨fun q => ∫ y in M.r q..M.r q + q, M.G y, fun q => rfl⟩
  have hH : ∀ q, 0 < q → M.H q = M.G (M.r q) := fun q hq => by
    show Hfun M.G M.lam M.K q = _
    unfold Hfun
    rw [if_pos hq]
    rfl
  have hH0 : ∀ q, ¬ 0 < q → M.H q = M.G (minPoint M.G) := fun q hq => by
    show Hfun M.G M.lam M.K q = _
    unfold Hfun
    rw [if_neg hq]
  have hopt : ∀ q, 0 < q → (∀ r', (∫ y in M.r q..M.r q + q, M.G y) ≤ ∫ y in r'..r' + q, M.G y)
      ∧ M.G (M.r q) = M.G (M.r q + q) :=
    fun q hq => aux_cif_opt hG hc hy0 M.lam M.K hq
  have hlow : ∀ q, 0 < q → ∀ q', 0 ≤ q' → F q + (q' - q) * M.H q ≤ F q' := by
    intro q hq q' hq'
    have := aux_cif_L hG hc (show M.r q < M.r q + q by linarith) (hopt q hq).2 (M.r q') q' hq'
    rw [show M.r q + q - M.r q = q by ring] at this
    rw [hH q hq, hFq, hFq]
    exact this
  have hup : ∀ q, 0 < q → ∀ q', 0 < q' →
      F q' ≤ F q + (q' - q) * M.H q + (M.h + M.p) * (q' - q) ^ 2 := by
    intro q hq q' hq'
    have h1 := (hopt q' hq').1 (M.r q)
    have hl : M.G (M.r q + q) = M.H q := by rw [hH q hq, (hopt q hq).2]
    rw [hFq, hFq]
    set a := M.r q
    have hsplit : (∫ y in a..a + q', M.G y) =
        (∫ y in a..a + q, M.G y) + ∫ y in a + q..a + q', M.G y :=
      (intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
        (hG.intervalIntegrable _ _)).symm
    have hbd : |(∫ y in a + q..a + q', M.G y) - (q' - q) * M.G (a + q)| ≤
        (M.h + M.p) * (q' - q) ^ 2 := by
      have e : (∫ y in a + q..a + q', M.G y) - (q' - q) * M.G (a + q) =
          ∫ y in a + q..a + q', (M.G y - M.G (a + q)) := by
        rw [intervalIntegral.integral_sub (hG.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [e]
      have hhp : 0 ≤ M.h + M.p := by linarith [M.h_pos, M.p_pos]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a + q) (b := a + q')
        (C := (M.h + M.p) * |q' - q|) (f := fun y => M.G y - M.G (a + q)) (fun x hx => by
          rw [Real.norm_eq_abs]
          have h2 := Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hx)
          rw [show a + q' - (a + q) = q' - q by ring] at h2
          calc |M.G x - M.G (a + q)| ≤ (M.h + M.p) * |x - (a + q)| := aux_cif_lip M _ _
            _ ≤ (M.h + M.p) * |q' - q| := by gcongr)
      rw [Real.norm_eq_abs, show a + q' - (a + q) = q' - q by ring] at this
      calc _ ≤ _ := this
        _ = (M.h + M.p) * (q' - q) ^ 2 := by rw [mul_assoc, abs_mul_abs_self, sq]
    rw [hl] at hbd
    have := (abs_le.mp hbd).2
    linarith
  have hderiv : ∀ q, 0 < q → HasDerivAt F (M.H q) q := by
    intro q hq
    rw [hasDerivAt_iff_isLittleO]
    have hO : (fun x => F x - F q - (x - q) • M.H q) =O[𝓝 q] (fun x => ‖x - q‖ ^ 2) := by
      refine Asymptotics.IsBigO.of_bound (M.h + M.p) ?_
      filter_upwards [Ioi_mem_nhds hq] with x hx
      have l1 := hlow q hq x (le_of_lt hx)
      have l2 := hup q hq x hx
      simp only [Real.norm_eq_abs, sq_abs, abs_pow, smul_eq_mul]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (x - q), M.h_pos, M.p_pos]
    exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub q one_lt_two)
  have hF0 : F 0 = 0 := by rw [hFq]; simp
  have hcont : ContinuousOn F (Icc 0 Q) := by
    intro x hx
    rcases hx.1.lt_or_eq with hx0 | hx0
    · exact (hderiv x hx0).continuousAt.continuousWithinAt
    · subst hx0
      have hlo : ∀ x ∈ Icc (0:ℝ) Q, x * M.G (minPoint M.G) ≤ F x := by
        intro x hx
        rw [hFq]
        have := intervalIntegral.integral_mono_on (μ := volume)
          (show M.r x ≤ M.r x + x by linarith [hx.1])
          intervalIntegrable_const (hG.intervalIntegrable _ _) (fun y _ => hy0 y)
        rw [intervalIntegral.integral_const, smul_eq_mul,
          show M.r x + x - M.r x = x by ring] at this
        exact this
      have hhi : ∀ x ∈ Icc (0:ℝ) Q, F x ≤ ∫ y in (0:ℝ)..x, M.G y := by
        intro x hx
        rcases hx.1.lt_or_eq with hx' | hx'
        · have := (hopt x hx').1 0
          rw [zero_add] at this
          rw [hFq]
          exact this
        · subst hx'
          rw [hF0]
          simp
      show Tendsto F (𝓝[Icc 0 Q] 0) (𝓝 (F 0))
      rw [hF0]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun x => x * M.G (minPoint M.G))
        (h := fun x => ∫ y in (0:ℝ)..x, M.G y)
      · have : Tendsto (fun x : ℝ => x * M.G (minPoint M.G)) (𝓝 0)
            (𝓝 (0 * M.G (minPoint M.G))) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · have := (hG.integral_hasStrictDerivAt 0 0).hasDerivAt.continuousAt.tendsto
        rw [intervalIntegral.integral_same] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall hlo
      · exact eventually_nhdsWithin_of_forall hhi
  have hmono : MonotoneOn M.H (Icc 0 Q) := by
    intro x hx y hy hxy
    rcases hx.1.lt_or_eq with hx0 | hx0
    · have hy0' : 0 < y := lt_of_lt_of_le hx0 hxy
      have l1 := hlow x hx0 y hy0'.le
      have l2 := hlow y hy0' x hx0.le
      rcases hxy.lt_or_eq with h | h
      · nlinarith
      · rw [h]
    · rw [← hx0, hH0 0 (lt_irrefl 0)]
      by_cases hy' : 0 < y
      · rw [hH y hy']; exact hy0 _
      · rw [hH0 y hy']
  have hint : IntervalIntegrable M.H volume 0 Q := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hQ.le]
    exact hmono
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hQ.le hcont
    (fun x hx => hderiv x hx.1) hint
  rw [this, hF0, sub_zero, hFq]

theorem cif_thm (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in M.r Q..M.r Q + Q, M.G y) = (∫ y in (0 : ℝ)..Q, M.H y) ∧
      M.C Q = (M.lam * M.K + ∫ y in (0 : ℝ)..Q, M.H y) / Q := by
  have h1 := aux_cif_main M Q hQ
  refine ⟨h1, ?_⟩
  show (M.lam * M.K + ∫ y in M.r Q..M.r Q + Q, M.G y) / Q = _
  rw [h1]

lemma aux_cft_HC (M : QRModel) (Q : ℝ) (hQopt : M.IsOptQty Q) : M.H Q = M.C Q := by
  obtain ⟨hQ, hopt⟩ := hQopt
  obtain ⟨hc, hconv, hmin⟩ := aux_ihl_facts M
  have hCle : ∀ Q', 0 < Q' → ∀ r',
      M.C Q' ≤ (M.lam * M.K + ∫ y in r'..r' + Q', M.G y) / Q' := by
    intro Q' hQ' r'
    exact aux_ihl_isOpt M.G hc hconv hmin M.lam M.K Q' hQ' r'
  set r := optReorder M.G M.lam M.K Q with hr_def
  have hH : M.H Q = M.G r := aux_ihl_Hval M Q hQ
  have hC : M.C Q = (M.lam * M.K + ∫ y in r..r + Q, M.G y) / Q := rfl
  rw [hH, hC]
  set I := ∫ y in r..r + Q, M.G y with hI
  set c := (M.lam * M.K + I) / Q with hc_def
  have hcQ : c * Q = M.lam * M.K + I := div_mul_cancel₀ _ hQ.ne'
  rcases lt_trichotomy (M.G r) c with hlt | heq | hgt
  · exfalso
    set c' := (M.G r + c) / 2 with hc'
    have hev : ∀ᶠ z in 𝓝 r, M.G z < c' :=
      hc.continuousAt.eventually_lt continuousAt_const (by rw [hc']; linarith)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set ε := δ / 2 with hε_def
    have hε : 0 < ε := by positivity
    have hbound : ∫ y in (r - ε)..r, M.G y ≤ ε * c' := by
      have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : r - ε ≤ r)
        (hc.intervalIntegrable _ _) (intervalIntegrable_const (c := c'))
        (fun z hz => (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2])).le)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      have : r - (r - ε) = ε := by ring
      rw [this] at hm
      exact hm
    have hsplit : ∫ y in (r - ε)..(r - ε + (Q + ε)), M.G y = (∫ y in (r - ε)..r, M.G y) + I := by
      rw [show r - ε + (Q + ε) = r + Q by ring]
      exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)).symm
    have h1 := hCle (Q + ε) (by linarith) (r - ε)
    have h2 := hopt (Q + ε) (by linarith)
    have h3 : (M.lam * M.K + ∫ y in (r - ε)..(r - ε + (Q + ε)), M.G y) / (Q + ε) < c := by
      rw [div_lt_iff₀ (by linarith), hsplit]
      have : ε * c' < ε * c := mul_lt_mul_of_pos_left (by rw [hc']; linarith) hε
      nlinarith
    rw [hC] at h2
    linarith
  · exact heq
  · exfalso
    set c' := (M.G r + c) / 2 with hc'
    have hev : ∀ᶠ z in 𝓝 r, c' < M.G z :=
      continuousAt_const.eventually_lt hc.continuousAt (by rw [hc']; linarith)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set ε := min (δ / 2) (Q / 2) with hε_def
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    have hεδ : ε ≤ δ / 2 := min_le_left _ _
    have hεQ : ε ≤ Q / 2 := min_le_right _ _
    have hbound : ε * c' ≤ ∫ y in r..(r + ε), M.G y := by
      have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : r ≤ r + ε)
        (intervalIntegrable_const (c := c')) (hc.intervalIntegrable _ _)
        (fun z hz => (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2])).le)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      have : r + ε - r = ε := by ring
      rw [this] at hm
      exact hm
    have hsplit : I = (∫ y in r..(r + ε), M.G y) + ∫ y in (r + ε)..(r + ε + (Q - ε)), M.G y := by
      rw [show r + ε + (Q - ε) = r + Q by ring]
      exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)).symm
    have h1 := hCle (Q - ε) (by linarith) (r + ε)
    have h2 := hopt (Q - ε) (by linarith)
    have h3 : (M.lam * M.K + ∫ y in (r + ε)..(r + ε + (Q - ε)), M.G y) / (Q - ε) < c := by
      rw [div_lt_iff₀ (by linarith)]
      have : ε * c < ε * c' := mul_lt_mul_of_pos_left (by rw [hc']; linarith) hε
      nlinarith
    rw [hC] at h2
    linarith

lemma aux_cft_Cpos (M : QRModel) (Q : ℝ) (hQ : 0 < Q) : 0 < M.C Q := by
  have hG : ∀ y, 0 ≤ M.G y := by
    intro y
    show 0 ≤ ∫ x, (M.h * max (y - x) 0 + M.p * max (x - y) 0) ∂M.μ
    apply integral_nonneg
    intro x
    have := M.h_pos; have := M.p_pos
    have := le_max_right (y - x) 0; have := le_max_right (x - y) 0
    positivity
  show 0 < (M.lam * M.K + ∫ y in M.r Q..M.r Q + Q, M.G y) / Q
  apply div_pos _ hQ
  have := intervalIntegral.integral_nonneg (μ := volume) (by linarith : M.r Q ≤ M.r Q + Q)
    (fun y _ => hG y)
  have := M.lam_pos; have := M.K_pos
  nlinarith [mul_pos M.lam_pos M.K_pos]

lemma aux_cft_mono (M : QRModel) : MonotoneOn M.H (Set.Ici 0) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ a from ha) with h0 | h0
  · subst h0
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ b from hb) with hb0 | hb0
    · rw [← hb0]
    · have e0 : M.H 0 = M.G (minPoint M.G) := by
        show Hfun M.G M.lam M.K 0 = _
        unfold Hfun; rw [if_neg (lt_irrefl 0)]
      rw [e0, aux_ihl_Hval M b hb0]
      have hex : ∃ y, ∀ z, M.G y ≤ M.G z := M.unique_min.exists
      unfold minPoint
      rw [dif_pos hex]
      exact hex.choose_spec _
  · exact aux_ihl_mono M a b h0 hab

lemma aux_cft_int (M : QRModel) (x : ℝ) (hx : 0 ≤ x) :
    IntervalIntegrable M.H volume 0 x := by
  apply MonotoneOn.intervalIntegrable
  apply (aux_cft_mono M).mono
  intro y hy
  rw [Set.uIcc_of_le hx] at hy
  exact hy.1

theorem cft_core (M : QRModel) (Qs : ℝ) (hQs : M.IsOptQty Qs)
    (α : ℝ) (hα : 0 < α) :
    M.C (α * Qs) / M.C Qs ≤ 1 / 2 * (α + 1 / α) := by
  have hQ : 0 < Qs := hQs.1
  have hαQ : 0 < α * Qs := mul_pos hα hQ
  have hHC := aux_cft_HC M Qs hQs
  have hCpos := aux_cft_Cpos M Qs hQ
  have hf1 := (cif_thm M Qs hQ).2
  have hf2 := (cif_thm M (α * Qs) hαQ).2
  have hle := ihl_thm M α Qs hα hQ
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (aux_cft_int M Qs hQ.le) ((aux_cft_int M Qs hQ.le).symm.trans (aux_cft_int M _ hαQ.le))
  set c := M.C Qs with hc
  have hcQ : M.lam * M.K + ∫ y in (0:ℝ)..Qs, M.H y = c * Qs := by
    rw [hf1]; field_simp
  have key : M.C (α * Qs) ≤ c * (α ^ 2 + 1) / (2 * α) := by
    rw [hf2, div_le_div_iff₀ hαQ (by positivity), ← hsplit]
    rw [hHC] at hle
    nlinarith [hle, hcQ]
  rw [div_le_iff₀ hCpos]
  calc M.C (α * Qs) ≤ c * (α ^ 2 + 1) / (2 * α) := key
    _ = 1 / 2 * (α + 1 / α) * c := by field_simp

end ZhengQR.Flatness

open ZhengQR.Flatness


theorem solution (M : QRModel) (Qs : ℝ) (hQs : M.IsOptQty Qs)
    (α : ℝ) (hα : 0 < α) :
    M.C (α * Qs) / M.C Qs ≤ 1 / 2 * (α + 1 / α) := by
  exact cft_core M Qs hQs α hα
