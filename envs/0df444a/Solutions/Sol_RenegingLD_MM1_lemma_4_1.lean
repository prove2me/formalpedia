-- Prove2me | solution 1 for RenegingLD.MM1.lemma_4_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:13:01.501641+00:00
-- url     : https://prove2.me/submissions/2ad96164-cfce-49c7-8438-0869972e2d5c

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

open RenegingLD.MM1
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace RenegL44

/-- tangent line inequality for `ℓ`: `ℓ(y) ≥ ℓ(x) + log x (y - x)` for `x > 0`, `y ≥ 0`. -/
theorem ell_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    ell x + Real.log x * (y - x) ≤ ell y := by
  unfold ell
  rcases hy.eq_or_lt with h | h
  · subst h; simp; nlinarith
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hx h)
    rw [Real.log_div hx.ne' h.ne'] at h1
    have h2 : y * (Real.log x - Real.log y) ≤ y * (x / y - 1) := mul_le_mul_of_nonneg_left h1 h.le
    have h3 : y * (x / y - 1) = x - y := by field_simp
    nlinarith

theorem ell_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ ell y := by
  have := ell_tangent (x := 1) one_pos hy
  simpa [ell] using this

theorem ell_convex : ConvexOn ℝ (Set.Ici (0 : ℝ)) ell := by
  have h1 : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => -x) := (concaveOn_id (convex_Ici 0)).neg
  have h2 := (Real.convexOn_mul_log.add h1).add_const 1
  refine h2.congr ?_
  intro x _
  simp [ell]; ring

theorem ell_comb {y1 y2 w1 w2 : ℝ} (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (hw : w1 + w2 = 1) : ell (w1 * y1 + w2 * y2) ≤ w1 * ell y1 + w2 * ell y2 := by
  have := ell_convex.2 (Set.mem_Ici.2 hy1) (Set.mem_Ici.2 hy2) hw1 hw2 hw
  simpa [smul_eq_mul] using this

section
variable (lam mu : ℝ)

noncomputable def uu (s : ℝ) : ℝ := (Real.sqrt (s ^ 2 + 4 * lam * mu) + s) / (2 * lam)
noncomputable def vv (s : ℝ) : ℝ := (Real.sqrt (s ^ 2 + 4 * lam * mu) - s) / (2 * mu)
noncomputable def HH (s : ℝ) : ℝ := lam * ell (uu lam mu s) + mu * ell (vv lam mu s)

variable {lam mu}

theorem uu_vv (hlam : 0 < lam) (hmu : 0 < mu) (s : ℝ) :
    0 < uu lam mu s ∧ 0 < vv lam mu s ∧ uu lam mu s * vv lam mu s = 1 ∧
      lam * uu lam mu s - mu * vv lam mu s = s := by
  have hsq : Real.sqrt (s ^ 2 + 4 * lam * mu) ^ 2 = s ^ 2 + 4 * lam * mu :=
    Real.sq_sqrt (by nlinarith [sq_nonneg s, mul_pos hlam hmu])
  have h0 := Real.sqrt_nonneg (s ^ 2 + 4 * lam * mu)
  set r := Real.sqrt (s ^ 2 + 4 * lam * mu)
  have hgt : s < r := by nlinarith [mul_pos hlam hmu]
  have hgt' : -s < r := by nlinarith [mul_pos hlam hmu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold uu; apply div_pos <;> linarith
  · unfold vv; apply div_pos <;> linarith
  · unfold uu vv; field_simp; nlinarith [hsq]
  · unfold uu vv; field_simp; ring

theorem HH_min (hlam : 0 < lam) (hmu : 0 < mu) (s u' v' : ℝ) (hu : 0 ≤ u') (hv : 0 ≤ v')
    (hs : lam * u' - mu * v' = s) : HH lam mu s ≤ lam * ell u' + mu * ell v' := by
  obtain ⟨hu0, hv0, huv, hlin⟩ := uu_vv hlam hmu s
  have t1 := ell_tangent hu0 hu
  have t2 := ell_tangent hv0 hv
  have hlog : Real.log (vv lam mu s) = -Real.log (uu lam mu s) := by
    have : vv lam mu s = (uu lam mu s)⁻¹ := by field_simp; linarith
    rw [this, Real.log_inv]
  rw [hlog] at t2
  unfold HH
  have e : lam * (Real.log (uu lam mu s) * (u' - uu lam mu s))
      + mu * (-Real.log (uu lam mu s) * (v' - vv lam mu s)) = 0 := by
    have : lam * (u' - uu lam mu s) - mu * (v' - vv lam mu s) = 0 := by linarith
    linear_combination Real.log (uu lam mu s) * this
  nlinarith [mul_le_mul_of_nonneg_left t1 hlam.le, mul_le_mul_of_nonneg_left t2 hmu.le]

theorem HH_nonneg (hlam : 0 < lam) (hmu : 0 < mu) (s : ℝ) : 0 ≤ HH lam mu s := by
  obtain ⟨hu0, hv0, _, _⟩ := uu_vv hlam hmu s
  unfold HH
  have := ell_nonneg hu0.le; have := ell_nonneg hv0.le
  positivity

theorem HH_conv (hlam : 0 < lam) (hmu : 0 < mu) (s1 s2 a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    HH lam mu (a * s1 + b * s2) ≤ a * HH lam mu s1 + b * HH lam mu s2 := by
  obtain ⟨hu1, hv1, _, hl1⟩ := uu_vv hlam hmu s1
  obtain ⟨hu2, hv2, _, hl2⟩ := uu_vv hlam hmu s2
  have hmin := HH_min hlam hmu (a * s1 + b * s2)
    (a * uu lam mu s1 + b * uu lam mu s2) (a * vv lam mu s1 + b * vv lam mu s2)
    (by positivity) (by positivity) (by linear_combination a * hl1 + b * hl2)
  have c1 := ell_comb hu1.le hu2.le ha hb hab
  have c2 := ell_comb hv1.le hv2.le ha hb hab
  unfold HH at *
  nlinarith [mul_le_mul_of_nonneg_left c1 hlam.le, mul_le_mul_of_nonneg_left c2 hmu.le]

end

/-- the reneging part of the local rate -/
noncomputable def PP (θ x q : ℝ) : ℝ≥0∞ :=
  if 0 < x then ENNReal.ofReal (θ * x * ell (q / (θ * x))) else if 0 < q then ⊤ else 0

theorem PP_conv {θ : ℝ} (hθ : 0 < θ) {x q x' q' a : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) (hx' : 0 ≤ x')
    (hq' : 0 ≤ q') (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    PP θ (a * x + (1 - a) * x') (a * q + (1 - a) * q') ≤
      ENNReal.ofReal a * PP θ x q + ENNReal.ofReal (1 - a) * PP θ x' q' := by
  have ha0 : 0 < a := ha.1
  have hb0 : 0 < 1 - a := by linarith [ha.2]
  have hA : ENNReal.ofReal a ≠ 0 := by simp [ha0]
  have hB : ENNReal.ofReal (1 - a) ≠ 0 := by simp; linarith [ha.2]
  rcases hx.eq_or_lt with hx0 | hxp
  · subst hx0
    rcases hq.eq_or_lt with hq0 | hqp
    · subst hq0
      -- PP θ 0 0 = 0
      have h00 : PP θ 0 0 = 0 := by simp [PP]
      rw [h00, mul_zero, zero_add]
      simp only [mul_zero, zero_add]
      rcases hx'.eq_or_lt with hx'0 | hx'p
      · subst hx'0
        simp only [mul_zero]
        rcases hq'.eq_or_lt with hq'0 | hq'p
        · subst hq'0; simp [PP]
        · simp [PP, hq'p, hb0, ENNReal.mul_top hB]
      · have hpos : 0 < (1 - a) * x' := mul_pos hb0 hx'p
        simp only [PP, hpos, hx'p, if_true]
        rw [← ENNReal.ofReal_mul hb0.le]
        apply le_of_eq; congr 1
        have : (1 - a) * q' / (θ * ((1 - a) * x')) = q' / (θ * x') := by
          field_simp
        rw [this]; ring
    · have : PP θ 0 q = ⊤ := by simp [PP, hqp]
      rw [this, ENNReal.mul_top hA]; simp
  · rcases hx'.eq_or_lt with hx'0 | hx'p
    · subst hx'0
      rcases hq'.eq_or_lt with hq'0 | hq'p
      · subst hq'0
        have h00 : PP θ 0 0 = 0 := by simp [PP]
        rw [h00, mul_zero, add_zero]
        simp only [mul_zero, add_zero]
        have hpos : 0 < a * x := mul_pos ha0 hxp
        simp only [PP, hpos, hxp, if_true]
        rw [← ENNReal.ofReal_mul ha0.le]
        apply le_of_eq; congr 1
        have : a * q / (θ * (a * x)) = q / (θ * x) := by
          field_simp
        rw [this]; ring
      · have : PP θ 0 q' = ⊤ := by simp [PP, hq'p]
        rw [this, ENNReal.mul_top hB]; simp
    · -- both positive: perspective argument
      set X := a * x + (1 - a) * x' with hX
      have hXp : 0 < X := by positivity
      have hw : a * x / X + (1 - a) * x' / X = 1 := by field_simp; exact hX.symm
      have hc := ell_comb (y1 := q / (θ * x)) (y2 := q' / (θ * x'))
        (by positivity) (by positivity) (by positivity) (by positivity) hw
      have hQ : a * x / X * (q / (θ * x)) + (1 - a) * x' / X * (q' / (θ * x')) =
          (a * q + (1 - a) * q') / (θ * X) := by
        field_simp
      rw [hQ] at hc
      have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ θ * X by positivity)
      have hrhs : θ * X * (a * x / X * ell (q / (θ * x)) + (1 - a) * x' / X * ell (q' / (θ * x')))
          = a * (θ * x * ell (q / (θ * x))) + (1 - a) * (θ * x' * ell (q' / (θ * x'))) := by
        field_simp
      rw [hrhs] at hmul
      have e1 := ell_nonneg (y := q / (θ * x)) (by positivity)
      have e2 := ell_nonneg (y := q' / (θ * x')) (by positivity)
      simp only [PP, hXp, hxp, hx'p, if_true]
      rw [← ENNReal.ofReal_mul ha0.le, ← ENNReal.ofReal_mul hb0.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal hmul

theorem Lloc_eq (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (x p q : ℝ) :
    Lloc lam mu θ x p q = ENNReal.ofReal (HH lam mu (p + q)) + PP θ x q := by
  obtain ⟨hu0, hv0, _, _⟩ := uu_vv hlam hmu (p + q)
  have e1 := ell_nonneg hu0.le
  have e2 := ell_nonneg hv0.le
  unfold Lloc HH PP
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  rfl

theorem Lloc_conv (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) :
    ∀ x p q x' p' q' a : ℝ, 0 ≤ x → 0 ≤ q → 0 ≤ x' → 0 ≤ q' → a ∈ Set.Ioo (0 : ℝ) 1 →
      Lloc lam mu θ (a * x + (1 - a) * x') (a * p + (1 - a) * p') (a * q + (1 - a) * q') ≤
        ENNReal.ofReal a * Lloc lam mu θ x p q
          + ENNReal.ofReal (1 - a) * Lloc lam mu θ x' p' q' := by
  intro x p q x' p' q' a hx hq hx' hq' ha
  have ha0 : 0 < a := ha.1
  have hb0 : 0 < 1 - a := by linarith [ha.2]
  rw [Lloc_eq lam mu θ hlam hmu, Lloc_eq lam mu θ hlam hmu, Lloc_eq lam mu θ hlam hmu]
  have hs : a * p + (1 - a) * p' + (a * q + (1 - a) * q') = a * (p + q) + (1 - a) * (p' + q') := by
    ring
  rw [hs]
  have h1 : ENNReal.ofReal (HH lam mu (a * (p + q) + (1 - a) * (p' + q'))) ≤
      ENNReal.ofReal a * ENNReal.ofReal (HH lam mu (p + q))
        + ENNReal.ofReal (1 - a) * ENNReal.ofReal (HH lam mu (p' + q')) := by
    rw [← ENNReal.ofReal_mul ha0.le, ← ENNReal.ofReal_mul hb0.le,
      ← ENNReal.ofReal_add (mul_nonneg ha0.le (HH_nonneg hlam hmu _))
        (mul_nonneg hb0.le (HH_nonneg hlam hmu _))]
    exact ENNReal.ofReal_le_ofReal (HH_conv hlam hmu _ _ _ _ ha0.le hb0.le (by ring))
  have h2 := PP_conv hθ hx hq hx' hq' ha
  calc ENNReal.ofReal (HH lam mu (a * (p + q) + (1 - a) * (p' + q')))
        + PP θ (a * x + (1 - a) * x') (a * q + (1 - a) * q')
      ≤ (ENNReal.ofReal a * ENNReal.ofReal (HH lam mu (p + q))
          + ENNReal.ofReal (1 - a) * ENNReal.ofReal (HH lam mu (p' + q')))
        + (ENNReal.ofReal a * PP θ x q + ENNReal.ofReal (1 - a) * PP θ x' q') := add_le_add h1 h2
    _ = _ := by ring

end RenegL44

open RenegL44 in
theorem solution : ¬ (∀ (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam)
    (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T) (ξ ζ : ℝ → ℝ) (h : InCT x0 T ξ ζ),
    IT lam mu θ x0 T ξ ζ =
      ∫⁻ s in Set.Icc 0 T, Lloc lam mu θ (ξ s) (deriv ξ s) (deriv ζ s)) := by
  intro H
  set ξ : ℝ → ℝ := fun _ => 1 with hξ
  set ζ : ℝ → ℝ := fun t => 2 * t with hζ
  have hlipζ : LipschitzWith 2 ζ := by
    refine LipschitzWith.of_dist_le_mul fun x y => le_of_eq ?_
    simp only [hζ, Real.dist_eq, ← mul_sub, abs_mul]
    norm_num
  have hIn : InCT 1 10 ξ ζ := by
    refine ⟨⟨continuousOn_const, (continuous_const.mul continuous_id).continuousOn, ?_⟩, rfl,
      by simp [hζ], ?_, ?_, ?_, ?_⟩
    · intro t ht; exact ⟨zero_le_one, by simp only [hζ]; linarith [ht.1]⟩
    · exact (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
    · exact hlipζ.lipschitzOnWith.absolutelyContinuousOnInterval
    · exact Filter.Eventually.of_forall fun t h1 => absurd h1 one_ne_zero
    · intro a _ b _ hab; simp only [hζ]; linarith
  have heq := H 1 1 1 one_pos one_pos one_pos le_rfl 1 10 zero_le_one (by norm_num) ξ ζ hIn
  -- the right-hand side is at most 40
  have hdξ : ∀ s, deriv ξ s = 0 := fun s => by simp [hξ]
  have hdζ : ∀ s, deriv ζ s = 2 := fun s => by
    have := ((hasDerivAt_id s).const_mul (2 : ℝ)).deriv
    simpa [hζ] using this
  have hell2 : ell 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    unfold ell; nlinarith
  have hell2' : 0.38 < ell 2 := by
    have := Real.log_two_gt_d9
    unfold ell; nlinarith
  have hHH : HH 1 1 2 ≤ 3 := by
    obtain ⟨hu, hv, huv, hl⟩ := uu_vv (lam := 1) (mu := 1) one_pos one_pos 2
    have hsq : ∀ y : ℝ, 0 < y → ell y ≤ (y - 1) ^ 2 := by
      intro y hy
      have := Real.log_le_sub_one_of_pos hy
      unfold ell; nlinarith
    have hv1 : vv 1 1 2 ≤ 1 := by
      by_contra hc; push Not at hc
      have : 1 < uu 1 1 2 * vv 1 1 2 := by nlinarith
      linarith
    have hu3 : uu 1 1 2 ≤ 3 := by nlinarith
    unfold HH
    have := hsq _ hu; have := hsq _ hv
    nlinarith
  have hc : Lloc 1 1 1 1 0 2 ≤ ENNReal.ofReal 4 := by
    rw [Lloc_eq 1 1 1 one_pos one_pos]
    unfold PP
    rw [if_pos one_pos, ← ENNReal.ofReal_add (HH_nonneg one_pos one_pos _)
      (by have := ell_nonneg (y := 2 / (1 * 1)) (by norm_num); positivity)]
    apply ENNReal.ofReal_le_ofReal
    norm_num at hHH ⊢
    linarith
  have hRHS : ∫⁻ s in Set.Icc (0 : ℝ) 10, Lloc 1 1 1 (ξ s) (deriv ξ s) (deriv ζ s)
      ≤ ENNReal.ofReal 40 := by
    have : ∀ s, Lloc 1 1 1 (ξ s) (deriv ξ s) (deriv ζ s) = Lloc 1 1 1 1 0 2 := fun s => by
      rw [hdξ, hdζ]
    simp_rw [this]
    rw [setLIntegral_const, Real.volume_Icc]
    calc Lloc 1 1 1 1 0 2 * ENNReal.ofReal (10 - 0) ≤ ENNReal.ofReal 4 * ENNReal.ofReal 10 := by
          gcongr; norm_num
      _ = ENNReal.ofReal 40 := by rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  -- the left-hand side is at least 380
  have hLHS : ENNReal.ofReal (ell 2 * 1000) ≤ IT 1 1 1 1 10 ξ ζ := by
    unfold IT
    refine le_iInf fun _ => le_iInf₂ fun ϕ hϕ => ?_
    obtain ⟨_, _, _, _, _, _, hi3, heqU⟩ := hϕ
    -- ϕ₃ = 2 a.e. on [0, 10]
    have hd3 := hi3.ae_hasDerivAt_integral
    have hIoo : ∀ᵐ t ∂volume, t ∈ Set.Icc (0 : ℝ) 10 → t ∈ Set.Ioo (0 : ℝ) 10 := by
      filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 10))] with t h ht
      exact h.mpr ht
    have h2 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 10)), ϕ.2.2 t = 2 := by
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hd3, hIoo] with t ht1 ht2 ht
      have hto := ht2 ht
      have hu : uIcc (0 : ℝ) 10 = Set.Icc 0 10 := uIcc_of_le (by norm_num)
      have hder := ht1 (by rw [hu]; exact ht) 0 left_mem_uIcc
      have hev : (fun x => ∫ s in (0)..x, ϕ.2.2 s * ξ s) =ᶠ[𝓝 t] fun x => 2 * x := by
        filter_upwards [Icc_mem_nhds hto.1 hto.2] with r hr
        have := (heqU r hr).2
        simp only [hζ] at this
        linarith
      have h2d : HasDerivAt (fun x => ∫ s in (0)..x, ϕ.2.2 s * ξ s) 2 t := by
        have := ((hasDerivAt_id t).const_mul (2 : ℝ))
        simp only [id, mul_one] at this
        exact this.congr_of_eventuallyEq hev
      have := hder.unique h2d
      simpa [hξ] using this
    have hK : ∫⁻ s in Set.Icc (0 : ℝ) 10, ENNReal.ofReal (ξ s * ell (ϕ.2.2 s))
        = ENNReal.ofReal (ell 2) * ENNReal.ofReal 10 := by
      rw [setLIntegral_congr_fun_ae measurableSet_Icc
        (g := fun _ => ENNReal.ofReal (ell 2)) ?_]
      · rw [setLIntegral_const, Real.volume_Icc]; norm_num
      · rw [← ae_restrict_iff' measurableSet_Icc]
        filter_upwards [h2] with t ht
        rw [ht]; simp [hξ]
    unfold cost
    simp only [ENNReal.ofReal_one, one_mul]
    rw [hK]
    set K := ENNReal.ofReal (ell 2) * ENNReal.ofReal 10
    have step : ∀ (f : ℝ → ℝ≥0∞) (c : ℝ≥0∞),
        c * ENNReal.ofReal 10 ≤ ∫⁻ s in Set.Icc (0 : ℝ) 10, (f s + c) := by
      intro f c
      calc c * ENNReal.ofReal 10 = ∫⁻ s in Set.Icc (0 : ℝ) 10, c := by
            rw [setLIntegral_const, Real.volume_Icc]; norm_num
        _ ≤ _ := lintegral_mono fun s => le_add_self
    calc ENNReal.ofReal (ell 2 * 1000) = K * ENNReal.ofReal 10 * ENNReal.ofReal 10 := by
          simp only [K]
          rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by nlinarith),
            ← ENNReal.ofReal_mul (by nlinarith)]
          congr 1; ring
      _ ≤ (∫⁻ s in Set.Icc (0 : ℝ) 10, (ENNReal.ofReal (ell (ϕ.2.1 s)) + K)) * ENNReal.ofReal 10 := by
          gcongr; exact step _ _
      _ ≤ _ := step _ _
  have : ENNReal.ofReal (ell 2 * 1000) ≤ ENNReal.ofReal 40 :=
    hLHS.trans (heq.le.trans hRHS)
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  linarith
