-- Prove2me | solution 1 for RenegingLD.MM1.lemma_4_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:58:15.971546+00:00
-- url     : https://prove2.me/submissions/6f360a7c-08e2-4572-afcd-86fd20854298
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational
import Theorems.Thm_RenegingLD_MM1_lemma_4_1

open RenegingLD.MM1
open MeasureTheory Filter Topology
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

namespace RenegL44

theorem Lloc_meas (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    Measurable (fun v : ℝ × ℝ × ℝ => Lloc lam mu θ v.1 v.2.1 v.2.2) := by
  have hfun : (fun v : ℝ × ℝ × ℝ => Lloc lam mu θ v.1 v.2.1 v.2.2) =
      fun v => ENNReal.ofReal (HH lam mu (v.2.1 + v.2.2)) + PP θ v.1 v.2.2 := by
    funext v; exact Lloc_eq lam mu θ hlam hmu _ _ _
  rw [hfun]
  have hH : Measurable (fun v : ℝ × ℝ × ℝ => ENNReal.ofReal (HH lam mu (v.2.1 + v.2.2))) := by
    unfold HH uu vv ell
    fun_prop
  have hP0 : Measurable (fun v : ℝ × ℝ × ℝ =>
      ENNReal.ofReal (θ * v.1 * ell (v.2.2 / (θ * v.1)))) := by
    unfold ell; fun_prop
  have hP1 : Measurable (fun v : ℝ × ℝ × ℝ => if 0 < v.2.2 then (⊤ : ℝ≥0∞) else 0) :=
    Measurable.ite (p := {v : ℝ × ℝ × ℝ | 0 < v.2.2})
      (measurableSet_lt measurable_const (measurable_snd.snd)) measurable_const measurable_const
  have hP : Measurable (fun v : ℝ × ℝ × ℝ => PP θ v.1 v.2.2) :=
    Measurable.ite (p := {v : ℝ × ℝ × ℝ | 0 < v.1})
      (measurableSet_lt measurable_const measurable_fst) hP0 hP1
  exact hH.add hP

theorem Lloc_aemeas (lam mu θ T : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (ξ ζ : ℝ → ℝ)
    (hξ : ContinuousOn ξ (Set.Icc 0 T)) :
    AEMeasurable (fun s => Lloc lam mu θ (ξ s) (deriv ξ s) (deriv ζ s))
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have h1 : AEMeasurable ξ (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    hξ.aemeasurable measurableSet_Icc
  have h2 : AEMeasurable (fun s => (ξ s, deriv ξ s, deriv ζ s))
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    h1.prodMk (((measurable_deriv ξ).prodMk (measurable_deriv ζ)).aemeasurable)
  have h3 := (Lloc_meas lam mu θ hlam hmu).comp_aemeasurable h2
  exact h3

theorem deriv_comb (a : ℝ) (f g : ℝ → ℝ) (t : ℝ) (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) :
    deriv (fun s => a * f s + (1 - a) * g s) t = a * deriv f t + (1 - a) * deriv g t := by
  exact ((hf.hasDerivAt.const_mul a).add (hg.hasDerivAt.const_mul (1 - a))).deriv

theorem deriv_nonneg_of_monotoneOn {f : ℝ → ℝ} {T t : ℝ} (hm : MonotoneOn f (Set.Icc 0 T))
    (ht : t ∈ Set.Ioo 0 T) (hf : DifferentiableAt ℝ f t) : 0 ≤ deriv f t := by
  have hacc : AccPt t (𝓟 (Set.Icc 0 T)) := by
    have h0 : AccPt t (𝓟 (Set.univ : Set ℝ)) := PerfectSpace.univ_preperfect t (Set.mem_univ t)
    have := h0.nhds_inter (Icc_mem_nhds ht.1 ht.2)
    simpa using this
  exact hf.hasDerivAt.hasDerivWithinAt.nonneg_of_monotoneOn hacc hm

end RenegL44

open RenegL44 in
theorem solution (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T) :
    (∀ x p q x' p' q' a : ℝ, 0 ≤ x → 0 ≤ q → 0 ≤ x' → 0 ≤ q' → a ∈ Set.Ioo (0 : ℝ) 1 →
      Lloc lam mu θ (a * x + (1 - a) * x') (a * p + (1 - a) * p') (a * q + (1 - a) * q') ≤
        ENNReal.ofReal a * Lloc lam mu θ x p q
          + ENNReal.ofReal (1 - a) * Lloc lam mu θ x' p' q') ∧
    (∀ ξ₁ ζ₁ ξ₂ ζ₂ : ℝ → ℝ, ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      InCT x0 T ξ₁ ζ₁ → InCT x0 T ξ₂ ζ₂ →
      InCT x0 T (fun t => a * ξ₁ t + (1 - a) * ξ₂ t) (fun t => a * ζ₁ t + (1 - a) * ζ₂ t) ∧
      IT lam mu θ x0 T (fun t => a * ξ₁ t + (1 - a) * ξ₂ t)
          (fun t => a * ζ₁ t + (1 - a) * ζ₂ t) ≤
        ENNReal.ofReal a * IT lam mu θ x0 T ξ₁ ζ₁
          + ENNReal.ofReal (1 - a) * IT lam mu θ x0 T ξ₂ ζ₂) := by
  have hconv := Lloc_conv lam mu θ hlam hmu hθ
  refine ⟨hconv, ?_⟩
  intro ξ1 ζ1 ξ2 ζ2 a ha h1 h2
  have ha0 : 0 < a := ha.1
  have hb0 : 0 < 1 - a := by linarith [ha.2]
  obtain ⟨⟨hc1ξ, hc1ζ, hnn1⟩, h1ξ0, h1ζ0, hac1ξ, hac1ζ, hae1, hmono1⟩ := id h1
  obtain ⟨⟨hc2ξ, hc2ζ, hnn2⟩, h2ξ0, h2ζ0, hac2ξ, hac2ζ, hae2, hmono2⟩ := id h2
  have hu : Set.uIcc 0 T = Set.Icc 0 T := Set.uIcc_of_le hT.le
  have hgood : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ∈ Set.Icc 0 T ∧
      DifferentiableAt ℝ ξ1 t ∧ DifferentiableAt ℝ ξ2 t ∧ DifferentiableAt ℝ ζ1 t ∧
      DifferentiableAt ℝ ζ2 t ∧ (ξ1 t = 0 → deriv ζ1 t = 0) ∧ (ξ2 t = 0 → deriv ζ2 t = 0) := by
    have d1 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) T) hac1ξ.ae_differentiableAt
    have d2 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) T) hac2ξ.ae_differentiableAt
    have d3 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) T) hac1ζ.ae_differentiableAt
    have d4 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) T) hac2ζ.ae_differentiableAt
    filter_upwards [ae_restrict_mem measurableSet_Icc, d1, d2, d3, d4, hae1, hae2]
      with t ht e1 e2 e3 e4 e5 e6
    rw [hu] at e1 e2 e3 e4
    exact ⟨ht, e1 ht, e2 ht, e3 ht, e4 ht, e5, e6⟩
  have hcomb : InCT x0 T (fun t => a * ξ1 t + (1 - a) * ξ2 t)
      (fun t => a * ζ1 t + (1 - a) * ζ2 t) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (continuousOn_const.mul hc1ξ).add (continuousOn_const.mul hc2ξ)
    · exact (continuousOn_const.mul hc1ζ).add (continuousOn_const.mul hc2ζ)
    · intro t ht
      obtain ⟨p1, q1⟩ := hnn1 t ht
      obtain ⟨p2, q2⟩ := hnn2 t ht
      exact ⟨add_nonneg (mul_nonneg ha0.le p1) (mul_nonneg hb0.le p2),
        add_nonneg (mul_nonneg ha0.le q1) (mul_nonneg hb0.le q2)⟩
    · show a * ξ1 0 + (1 - a) * ξ2 0 = x0
      rw [h1ξ0, h2ξ0]; ring
    · show a * ζ1 0 + (1 - a) * ζ2 0 = 0
      rw [h1ζ0, h2ζ0]; ring
    · exact (hac1ξ.const_mul a).add (hac2ξ.const_mul (1 - a))
    · exact (hac1ζ.const_mul a).add (hac2ζ.const_mul (1 - a))
    · filter_upwards [hgood] with t ⟨ht, e1, e2, e3, e4, e5, e6⟩ hz
      have hz' : a * ξ1 t + (1 - a) * ξ2 t = 0 := hz
      have p1 := (hnn1 t ht).1
      have p2 := (hnn2 t ht).1
      have z1 : ξ1 t = 0 := by nlinarith [mul_nonneg ha0.le p1, mul_nonneg hb0.le p2]
      have z2 : ξ2 t = 0 := by nlinarith [mul_nonneg ha0.le p1, mul_nonneg hb0.le p2]
      rw [deriv_comb a ζ1 ζ2 t e3 e4, e5 z1, e6 z2]; ring
    · intro s hs r hr hsr
      exact add_le_add (mul_le_mul_of_nonneg_left (hmono1 hs hr hsr) ha0.le)
        (mul_le_mul_of_nonneg_left (hmono2 hs hr hsr) hb0.le)
  refine ⟨hcomb, ?_⟩
  rw [lemma_4_1 lam mu θ hlam hmu hθ hlm x0 T hx0 hT _ _ hcomb,
    lemma_4_1 lam mu θ hlam hmu hθ hlm x0 T hx0 hT _ _ h1,
    lemma_4_1 lam mu θ hlam hmu hθ hlm x0 T hx0 hT _ _ h2,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left' ((Lloc_aemeas lam mu θ T hlam hmu ξ1 ζ1 hc1ξ).const_mul _)]
  apply lintegral_mono_ae
  have hIoo : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ∈ Set.Ioo 0 T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T))] with t h ht
    exact h.mpr ht
  filter_upwards [hgood, hIoo] with t ⟨ht, e1, e2, e3, e4, _, _⟩ hto
  show Lloc lam mu θ (a * ξ1 t + (1 - a) * ξ2 t)
      (deriv (fun t => a * ξ1 t + (1 - a) * ξ2 t) t)
      (deriv (fun t => a * ζ1 t + (1 - a) * ζ2 t) t) ≤ _
  rw [deriv_comb a ξ1 ξ2 t e1 e2, deriv_comb a ζ1 ζ2 t e3 e4]
  exact hconv _ _ _ _ _ _ a (hnn1 t ht).1 (deriv_nonneg_of_monotoneOn hmono1 hto e3)
    (hnn2 t ht).1 (deriv_nonneg_of_monotoneOn hmono2 hto e4) ha
