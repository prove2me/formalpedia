-- Prove2me | solution 1 for RiskAverseSDDP.Subdiff.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T18:29:14.267993+00:00
-- url     : https://prove2.me/submissions/3d67b742-61f3-4c72-a699-ea945faa49b4

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

set_option autoImplicit false

open Set
open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff.Aux

theorem comb_lt (a b r1 r2 t1 t2 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h1 : r1 < t1) (h2 : r2 < t2) : a * r1 + b * r2 < a * t1 + b * t2 := by
  have hm : 0 < min (t1 - r1) (t2 - r2) := lt_min (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left (t1 - r1) (t2 - r2)) ha,
    mul_le_mul_of_nonneg_left (min_le_right (t1 - r1) (t2 - r2)) hb]

/-- Metric form of the relative interior. -/
theorem ri_ball {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {D : Set H} {z : H}
    (h : z ∈ intrinsicInterior ℝ D) :
    z ∈ D ∧ ∃ δ > 0, ∀ w ∈ vectorSpan ℝ D, ‖w‖ < δ → z + w ∈ D := by
  refine ⟨intrinsicInterior_subset h, ?_⟩
  rw [mem_intrinsicInterior] at h
  obtain ⟨y, hy, rfl⟩ := h
  rw [mem_interior_iff_mem_nhds, nhds_subtype, Filter.mem_comap] at hy
  obtain ⟨U, hU, hUs⟩ := hy
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, fun w hw hwn => ?_⟩
  have hmem : w + (y : H) ∈ affineSpan ℝ D := by
    have := AffineSubspace.vadd_mem_of_mem_direction
      (by rwa [direction_affineSpan] : w ∈ (affineSpan ℝ D).direction) y.2
    simpa [vadd_eq_add] using this
  have hin : ((⟨w + y, hmem⟩ : affineSpan ℝ D) : H) ∈ U :=
    hball (by simpa [Metric.mem_ball, dist_eq_norm] using hwn)
  have : (⟨w + y, hmem⟩ : affineSpan ℝ D) ∈ ((↑) ⁻¹' D : Set (affineSpan ℝ D)) := hUs hin
  simpa [add_comm] using this

/-- Convex combination in the epigraph. -/
theorem epi_comb {H : Type*} [AddCommGroup H] [Module ℝ H] {φ : H → EReal}
    (hφ : RiskAverseSDDP.Convergence.EConvex φ) {z1 z2 : H} {r1 r2 : ℝ}
    (h1 : φ z1 ≤ (r1 : EReal)) (h2 : φ z2 ≤ (r2 : EReal)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : φ (a • z1 + b • z2) ≤ ((a * r1 + b * r2 : ℝ) : EReal) := by
  have m1 : ((z1, r1) : H × ℝ) ∈ {q : H × ℝ | φ q.1 ≤ (q.2 : EReal)} := h1
  have m2 : ((z2, r2) : H × ℝ) ∈ {q : H × ℝ | φ q.1 ≤ (q.2 : EReal)} := h2
  have hc := hφ m1 m2 ha hb hab
  simpa [smul_eq_mul] using hc

theorem no_bot {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (φ : H → EReal)
    (hφ : RiskAverseSDDP.Convergence.EConvex φ) (zb : H) (hbot : φ zb ≠ ⊥)
    (hri : zb ∈ intrinsicInterior ℝ (edom φ)) : ∀ z, φ z ≠ ⊥ := by
  obtain ⟨hzD, δ, hδ, hball⟩ := ri_ball hri
  have htop : φ zb ≠ ⊤ := hzD
  intro z hz
  have hzd : z ∈ edom φ := by show φ z ≠ ⊤; rw [hz]; exact bot_ne_top
  have hw : z - zb ∈ vectorSpan ℝ (edom φ) := by
    simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hzd hzD
  set θ : ℝ := δ / (2 * (‖z - zb‖ + δ)) with hθ
  have hθpos : 0 < θ := by positivity
  have hθw : ‖-(θ • (z - zb))‖ < δ := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hθpos.le]
    have hθ2 : θ * ‖z - zb‖ ≤ δ / 2 := by
      rw [hθ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [norm_nonneg (z - zb)]
    linarith
  have hz' : zb + -(θ • (z - zb)) ∈ edom φ :=
    hball _ (Submodule.neg_mem _ (Submodule.smul_mem _ θ hw)) hθw
  set r' : ℝ := (φ (zb + -(θ • (z - zb)))).toReal
  have h1 : φ (zb + -(θ • (z - zb))) ≤ (r' : EReal) := EReal.le_coe_toReal hz'
  set r0 : ℝ := (φ zb).toReal
  have e0 : φ zb = (r0 : EReal) := (EReal.coe_toReal htop hbot).symm
  set a : ℝ := 1 / (1 + θ) with ha_def
  set b : ℝ := θ / (1 + θ) with hb_def
  have ha : 0 ≤ a := by positivity
  have hb : 0 < b := by positivity
  have hab : a + b = 1 := by rw [ha_def, hb_def]; field_simp
  have hbθ : b - a * θ = 0 := by rw [ha_def, hb_def]; field_simp; ring
  set M : ℝ := (a * r' - r0 + 1) / b with hM
  have h2 : φ z ≤ ((-M : ℝ) : EReal) := by rw [hz]; exact bot_le
  have hc := epi_comb hφ h1 h2 ha hb.le hab
  have hcomb : a • (zb + -(θ • (z - zb))) + b • z = zb := by
    have : a • (zb + -(θ • (z - zb))) + b • z = (a + b) • zb + (b - a * θ) • (z - zb) := by
      module
    rw [this, hab, hbθ, one_smul, zero_smul, add_zero]
  rw [hcomb, e0, EReal.coe_le_coe_iff] at hc
  have hbM : b * M = a * r' - r0 + 1 := by rw [hM]; field_simp
  have : a * r' + b * -M = r0 - 1 := by rw [mul_neg, hbM]; ring
  linarith

/-- Rockafellar, Convex Analysis, Thm 23.4: a convex function finite at a point of the relative
interior of its effective domain has a subgradient there. -/
theorem subgrad_exists_ri {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (φ : H → EReal) (hφ : RiskAverseSDDP.Convergence.EConvex φ)
    (zb : H) (hbot : φ zb ≠ ⊥) (hri : zb ∈ intrinsicInterior ℝ (edom φ)) :
    ∃ ℓ : H →L[ℝ] ℝ, ∀ z, φ zb + ((ℓ (z - zb) : ℝ) : EReal) ≤ φ z := by
  classical
  have hnb := no_bot φ hφ zb hbot hri
  obtain ⟨hzD, δ, hδ, hball⟩ := ri_ball hri
  have htop : φ zb ≠ ⊤ := hzD
  set W : Submodule ℝ H := vectorSpan ℝ (edom φ) with hW
  set r0 : ℝ := (φ zb).toReal with hr0
  have e0 : φ zb = (r0 : EReal) := (EReal.coe_toReal htop hbot).symm
  have hUD : ∀ w : W, ‖w‖ < δ → zb + (w : H) ∈ edom φ :=
    fun w hw => hball w w.2 (by simpa using hw)
  set ψ : W → ℝ := fun w => (φ (zb + (w : H))).toReal with hψ
  have eψ : ∀ w : W, ‖w‖ < δ → φ (zb + (w : H)) = ((ψ w : ℝ) : EReal) :=
    fun w hw => (EReal.coe_toReal (hUD w hw) (hnb _)).symm
  have hψ0 : ψ 0 = r0 := by simp [hψ, hr0]
  have hψc : ConvexOn ℝ (Metric.ball (0 : W) δ) ψ := by
    refine ⟨convex_ball 0 δ, fun w1 hw1 w2 hw2 a b ha hb hab => ?_⟩
    have hw1' : ‖w1‖ < δ := by simpa using hw1
    have hw2' : ‖w2‖ < δ := by simpa using hw2
    have hc := epi_comb hφ (le_of_eq (eψ w1 hw1')) (le_of_eq (eψ w2 hw2')) ha hb hab
    have hmem : a • w1 + b • w2 ∈ Metric.ball (0 : W) δ := convex_ball 0 δ hw1 hw2 ha hb hab
    have hm' : ‖a • w1 + b • w2‖ < δ := by simpa using hmem
    have e : a • (zb + (w1 : H)) + b • (zb + (w2 : H)) = (a + b) • zb + ((a • w1 + b • w2 : W) : H) := by
      simp only [Submodule.coe_add, Submodule.coe_smul]; module
    rw [e, hab, one_smul, eψ _ hm', EReal.coe_le_coe_iff] at hc
    simpa [smul_eq_mul] using hc
  have hcont : ContinuousOn ψ (Metric.ball (0 : W) δ) := hψc.continuousOn Metric.isOpen_ball
  set O : Set (W × ℝ) := {q | q.1 ∈ Metric.ball (0 : W) δ ∧ ψ q.1 < q.2} with hO
  have hOo : IsOpen O := by
    have : O = (Metric.ball (0 : W) δ ×ˢ univ) ∩ (fun q : W × ℝ => q.2 - ψ q.1) ⁻¹' Ioi 0 := by
      ext q; simp [hO, sub_pos]
    rw [this]
    refine ContinuousOn.isOpen_inter_preimage ?_ (Metric.isOpen_ball.prod isOpen_univ) isOpen_Ioi
    exact continuous_snd.continuousOn.sub (hcont.comp continuousOn_fst (fun q hq => hq.1))
  have hOc : Convex ℝ O := by
    rintro ⟨w1, t1⟩ ⟨hw1, h1⟩ ⟨w2, t2⟩ ⟨hw2, h2⟩ a b ha hb hab
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst]; exact convex_ball 0 δ hw1 hw2 ha hb hab
    · have := hψc.2 hw1 hw2 ha hb hab
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this ⊢
      exact lt_of_le_of_lt this (comb_lt a b _ _ _ _ ha hb hab h1 h2)
  have hp0 : ((0 : W), ψ 0) ∉ O := fun h => lt_irrefl _ h.2
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hOc hOo hp0
  set c : ℝ := L ((0 : W), (1 : ℝ)) with hc
  have hLd : ∀ (w : W) (t : ℝ), L (w, t) = L (w, 0) + t * c := by
    intro w t
    rw [show ((w, t) : W × ℝ) = (w, 0) + t • ((0 : W), (1 : ℝ)) by ext <;> simp, map_add,
      map_smul, smul_eq_mul]
  have hL00 : L ((0 : W), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero, map_zero]
  have hcpos : 0 < c := by
    have := hL ((0 : W), ψ 0 + 1) ⟨Metric.mem_ball_self hδ, by simp⟩
    rw [hLd, hLd 0 (ψ 0 + 1), hL00] at this
    linarith
  have hloc : ∀ w : W, w ∈ Metric.ball (0 : W) δ → ψ 0 * c ≤ L (w, 0) + ψ w * c := by
    intro w hw
    by_contra hcon
    push Not at hcon
    set d := ψ 0 * c - (L (w, 0) + ψ w * c) with hd_def
    have hd : 0 < d := by linarith
    have hdc : 0 < d / (2 * c) := by positivity
    have := hL (w, ψ w + d / (2 * c)) ⟨hw, by linarith⟩
    rw [hLd, hLd w, hL00] at this
    have e : (ψ w + d / (2 * c)) * c = ψ w * c + d / 2 := by field_simp
    linarith
  set lam : W →ₗ[ℝ] ℝ := (-(1 / c)) • ((L : W × ℝ →L[ℝ] ℝ).toLinearMap.comp (LinearMap.inl ℝ W ℝ))
    with hlam
  obtain ⟨g, hg⟩ := LinearMap.exists_extend lam
  refine ⟨LinearMap.toContinuousLinearMap g, fun z => ?_⟩
  by_cases hzt : φ z = ⊤
  · rw [hzt]; exact le_top
  have hzd : z ∈ edom φ := hzt
  have hw : z - zb ∈ W := by
    simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hzd hzD
  set r : ℝ := (φ z).toReal
  have er : φ z = (r : EReal) := (EReal.coe_toReal hzt (hnb z)).symm
  set w0 : W := ⟨z - zb, hw⟩ with hw0
  have hgw : (LinearMap.toContinuousLinearMap g) (z - zb) = -(1 / c) * L (w0, 0) := by
    have := LinearMap.congr_fun hg w0
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [LinearMap.coe_toContinuousLinearMap', show z - zb = (w0 : H) from rfl, this, hlam]
    simp
  set θ : ℝ := δ / (2 * (‖z - zb‖ + δ)) with hθ
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]; nlinarith [norm_nonneg (z - zb)]
  have hθw : ‖θ • w0‖ < δ := by
    rw [norm_smul, Real.norm_of_nonneg hθpos.le]
    have : ‖w0‖ = ‖z - zb‖ := rfl
    rw [this]
    have hθ2 : θ * ‖z - zb‖ ≤ δ / 2 := by
      rw [hθ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [norm_nonneg (z - zb)]
    linarith
  have hcomb := epi_comb hφ (le_of_eq e0) (le_of_eq er) (by linarith : 0 ≤ 1 - θ) hθpos.le
    (by ring : 1 - θ + θ = 1)
  have e : (1 - θ) • zb + θ • z = zb + ((θ • w0 : W) : H) := by
    simp only [Submodule.coe_smul, hw0]; module
  rw [e, eψ _ hθw, EReal.coe_le_coe_iff] at hcomb
  have hl := hloc (θ • w0) (by simpa using hθw)
  have hLθ : L (θ • w0, 0) = θ * L (w0, 0) := by
    rw [show ((θ • w0, (0 : ℝ)) : W × ℝ) = θ • (w0, (0 : ℝ)) by ext <;> simp, map_smul,
      smul_eq_mul]
  rw [hLθ, hψ0] at hl
  rw [e0, er, hgw, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have key : r0 * c ≤ L (w0, 0) + r * c := by
    have h3 : r0 * c ≤ θ * L (w0, 0) + ((1 - θ) * r0 + θ * r) * c := by
      nlinarith
    have h4 : θ * (r0 * c) ≤ θ * (L (w0, 0) + r * c) := by nlinarith
    exact le_of_mul_le_mul_left h4 hθpos
  have : -(1 / c) * L (w0, 0) = -(L (w0, 0) / c) := by ring
  rw [this]
  have : L (w0, 0) / c ≥ r0 - r := by
    rw [ge_iff_le, le_div_iff₀ hcpos]; linarith
  linarith

theorem ereal_cases {x : EReal} (hx : x ≠ ⊥) : x = ⊤ ∨ ∃ r : ℝ, x = (r : EReal) := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | coe r => exact Or.inr ⟨r, rfl⟩
  | top => exact Or.inl rfl

theorem ri_of_ball {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {D : Set H} {z : H}
    (hz : z ∈ D) (h : ∃ δ > 0, ∀ w ∈ vectorSpan ℝ D, ‖w‖ < δ → z + w ∈ D) :
    z ∈ intrinsicInterior ℝ D := by
  obtain ⟨δ, hδ, hball⟩ := h
  rw [mem_intrinsicInterior]
  refine ⟨⟨z, mem_affineSpan ℝ hz⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds, nhds_subtype, Filter.mem_comap]
  refine ⟨Metric.ball z δ, Metric.ball_mem_nhds z hδ, fun y hy => ?_⟩
  have hdir : (y : H) - z ∈ vectorSpan ℝ D := by
    rw [← direction_affineSpan]
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction y.2 (mem_affineSpan ℝ hz)
  have := hball _ hdir (by simpa [Metric.mem_ball, dist_eq_norm] using hy)
  simpa using this

theorem add_coe_le_iff (x : EReal) (c r : ℝ) :
    x + (c : EReal) ≤ (r : EReal) ↔ x ≤ ((r - c : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => simp
  | coe a => norm_cast; constructor <;> intro h <;> linarith
  | top => simp only [EReal.top_add_coe, top_le_iff, EReal.coe_ne_top]

theorem econvex_add_affine {H : Type*} [AddCommGroup H] [Module ℝ H] {F : H → EReal}
    (hF : RiskAverseSDDP.Convergence.EConvex F) (c : ℝ) (L : H →ₗ[ℝ] ℝ) :
    RiskAverseSDDP.Convergence.EConvex (fun z => F z + ((c + L z : ℝ) : EReal)) := by
  intro q1 hq1 q2 hq2 a b ha hb hab
  simp only [mem_setOf_eq] at hq1 hq2 ⊢
  rw [add_coe_le_iff] at hq1 hq2 ⊢
  have := epi_comb hF hq1 hq2 ha hb hab
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this ⊢
  refine le_trans this (le_of_eq ?_)
  congr 1
  simp only [map_add, map_smul, smul_eq_mul]
  linear_combination (-c) * hab

theorem sum_top {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by
  rcases ereal_cases hx with rfl | ⟨r, rfl⟩ <;> rcases ereal_cases hy with rfl | ⟨s, rfl⟩
  · simp
  · simp
  · simp
  · simp only [EReal.coe_ne_top, or_self, iff_false]; exact_mod_cast EReal.coe_ne_top (r + s)

set_option maxHeartbeats 1000000 in
/-- Rockafellar, Convex Analysis, Thm 23.8 (two functions): if the relative interiors of the
effective domains meet, the subdifferential of the sum is the sum of the subdifferentials. -/
theorem sum_rule_ri {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (F1 F2 : H → EReal) (h1 : RiskAverseSDDP.Convergence.EConvex F1)
    (h2 : RiskAverseSDDP.Convergence.EConvex F2) (hb1 : ∀ z, F1 z ≠ ⊥) (hb2 : ∀ z, F2 z ≠ ⊥)
    (zb : H) (hri1 : zb ∈ intrinsicInterior ℝ (edom F1))
    (hri2 : zb ∈ intrinsicInterior ℝ (edom F2))
    (z0 : H) (ht1 : F1 z0 ≠ ⊤) (ht2 : F2 z0 ≠ ⊤) (ℓ : H →L[ℝ] ℝ)
    (hsub : ∀ z, F1 z0 + F2 z0 + ((ℓ (z - z0) : ℝ) : EReal) ≤ F1 z + F2 z) :
    ∃ ℓ1 ℓ2 : H →L[ℝ] ℝ, ℓ = ℓ1 + ℓ2 ∧ (∀ z, F1 z0 + ((ℓ1 (z - z0) : ℝ) : EReal) ≤ F1 z) ∧
      (∀ z, F2 z0 + ((ℓ2 (z - z0) : ℝ) : EReal) ≤ F2 z) := by
  classical
  set a1 : ℝ := (F1 z0).toReal with ha1
  set a2 : ℝ := (F2 z0).toReal with ha2
  have e1 : F1 z0 = (a1 : EReal) := (EReal.coe_toReal ht1 (hb1 z0)).symm
  have e2 : F2 z0 = (a2 : EReal) := (EReal.coe_toReal ht2 (hb2 z0)).symm
  set k1 : H → EReal := fun z => F1 z + ((-a1 - ℓ (z - z0) : ℝ) : EReal) with hk1
  set k2 : H → EReal := fun z => F2 z + ((-a2 : ℝ) : EReal) with hk2
  have hk1c : RiskAverseSDDP.Convergence.EConvex k1 := by
    have hfun : k1 = fun z => F1 z + ((-a1 + ℓ z0 + (-(ℓ : H →ₗ[ℝ] ℝ)) z : ℝ) : EReal) := by
      funext z
      simp only [hk1]
      congr 2
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe, map_sub]
      ring
    rw [hfun]; exact econvex_add_affine h1 _ _
  have hk2c : RiskAverseSDDP.Convergence.EConvex k2 := by
    have hfun : k2 = fun z => F2 z + ((-a2 + (0 : H →ₗ[ℝ] ℝ) z : ℝ) : EReal) := by
      funext z; simp only [hk2, LinearMap.zero_apply, add_zero]
    rw [hfun]; exact econvex_add_affine h2 _ _
  have hk1b : ∀ z, k1 z ≠ ⊥ := fun z => by
    simp only [hk1, ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, or_false]; exact hb1 z
  have hk2b : ∀ z, k2 z ≠ ⊥ := fun z => by
    simp only [hk2, ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, or_false]; exact hb2 z
  have hk1t : ∀ z, k1 z = ⊤ ↔ F1 z = ⊤ := fun z => by
    show F1 z + _ = ⊤ ↔ _
    rw [sum_top (hb1 z) (EReal.coe_ne_bot _), or_iff_left (EReal.coe_ne_top _)]
  have hk2t : ∀ z, k2 z = ⊤ ↔ F2 z = ⊤ := fun z => by
    show F2 z + _ = ⊤ ↔ _
    rw [sum_top (hb2 z) (EReal.coe_ne_bot _), or_iff_left (EReal.coe_ne_top _)]
  have hk10 : k1 z0 = 0 := by
    show F1 z0 + ((-a1 - ℓ (z0 - z0) : ℝ) : EReal) = 0
    rw [e1, sub_self, map_zero, sub_zero, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hk20 : k2 z0 = 0 := by
    show F2 z0 + ((-a2 : ℝ) : EReal) = 0
    rw [e2, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  set p : H → EReal := fun e => ⨅ z, k1 (z + e) + k2 z with hp
  -- p 0 = 0
  have hp0 : p 0 = 0 := by
    refine le_antisymm (iInf_le_of_le z0 (by simp [hk10, hk20])) (le_iInf fun z => ?_)
    simp only [add_zero]
    rcases ereal_cases (hb1 z) with h | ⟨r1, hr1⟩
    · rw [(hk1t z).2 h, EReal.top_add_of_ne_bot (hk2b z)]; exact le_top
    rcases ereal_cases (hb2 z) with h' | ⟨r2, hr2⟩
    · rw [(hk2t z).2 h', EReal.add_top_of_ne_bot (hk1b z)]; exact le_top
    have hs := hsub z
    rw [e1, e2, hr1, hr2] at hs
    simp only [hk1, hk2, hr1, hr2]
    norm_cast at hs ⊢
    linarith
  -- convexity of p
  have hpc : RiskAverseSDDP.Convergence.EConvex p := by
    rintro ⟨e1', r1⟩ hq1 ⟨e2', r2⟩ hq2 a b ha hb hab
    simp only [mem_setOf_eq] at hq1 hq2 ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    apply le_of_forall_gt_imp_ge_of_dense
    intro x hx
    induction x using EReal.rec with
    | bot => exact absurd hx not_lt_bot
    | top => exact le_top
    | coe d =>
      have hd := EReal.coe_lt_coe_iff.mp hx
      set ε := d - (a * r1 + b * r2) with hε_def
      have hε : 0 < ε := by linarith
      have pick : ∀ (e : H) (r : ℝ), p e ≤ (r : EReal) → ∃ (z : H) (s t : ℝ), k1 (z + e) = (s : EReal) ∧
          k2 z = (t : EReal) ∧ s + t < r + ε := by
        intro e r hr
        obtain ⟨z, hz⟩ := iInf_lt_iff.mp (lt_of_le_of_lt hr
          (EReal.coe_lt_coe_iff.mpr (by linarith : r < r + ε)))
        have hne : k1 (z + e) + k2 z ≠ ⊤ := ne_top_of_lt hz
        rw [ne_eq, sum_top (hk1b _) (hk2b _), not_or] at hne
        refine ⟨z, (k1 (z + e)).toReal, (k2 z).toReal, (EReal.coe_toReal hne.1 (hk1b _)).symm,
          (EReal.coe_toReal hne.2 (hk2b _)).symm, ?_⟩
        rw [← EReal.coe_toReal hne.1 (hk1b _), ← EReal.coe_toReal hne.2 (hk2b _)] at hz
        exact_mod_cast hz
      obtain ⟨z1, s1, t1, hs1, ht1', hst1⟩ := pick e1' r1 hq1
      obtain ⟨z2, s2, t2, hs2, ht2', hst2⟩ := pick e2' r2 hq2
      have hA := epi_comb hk1c hs1.le hs2.le ha hb hab
      have hB := epi_comb hk2c ht1'.le ht2'.le ha hb hab
      have ez : (a • z1 + b • z2) + (a • e1' + b • e2') = a • (z1 + e1') + b • (z2 + e2') := by
        module
      calc p (a • e1' + b • e2') ≤ k1 ((a • z1 + b • z2) + (a • e1' + b • e2')) +
            k2 (a • z1 + b • z2) := iInf_le (fun z => k1 (z + (a • e1' + b • e2')) + k2 z) _
        _ ≤ ((a * s1 + b * s2 : ℝ) : EReal) + ((a * t1 + b * t2 : ℝ) : EReal) := by
          rw [ez]; exact add_le_add hA hB
        _ ≤ (d : EReal) := by
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]
          have := comb_lt a b _ _ _ _ ha hb hab hst1 hst2
          have e3 : a * (r1 + ε) + b * (r2 + ε) = d := by
            rw [hε_def]; linear_combination (d - (a * r1 + b * r2)) * hab
          linarith
  -- the domain of p
  have hdomp : ∀ e, e ∈ edom p ↔ ∃ z, z + e ∈ edom F1 ∧ z ∈ edom F2 := by
    intro e
    show p e ≠ ⊤ ↔ _
    rw [ne_eq, hp, iInf_eq_top, not_forall]
    simp only [sum_top (hk1b _) (hk2b _), hk1t, hk2t, not_or]
    rfl
  obtain ⟨hzD1, δ1, hδ1, hball1⟩ := ri_ball hri1
  obtain ⟨hzD2, δ2, hδ2, hball2⟩ := ri_ball hri2
  set V1 := vectorSpan ℝ (edom F1) with hV1
  set V2 := vectorSpan ℝ (edom F2) with hV2
  have hspan : vectorSpan ℝ (edom p) ≤ V1 ⊔ V2 := by
    have hmem : ∀ e ∈ edom p, e ∈ V1 ⊔ V2 := by
      intro e he
      obtain ⟨z, hz1, hz2⟩ := (hdomp e).1 he
      have : e = ((z + e) - zb) + -(z - zb) := by abel
      rw [this]
      exact Submodule.add_mem_sup
        (by simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hz1 hzD1)
        (Submodule.neg_mem _ (by simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hz2 hzD2))
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨e, he, e', he', rfl⟩
    simpa [vsub_eq_sub] using Submodule.sub_mem _ (hmem e he) (hmem e' he')
  set T : V1 × V2 →ₗ[ℝ] H := V1.subtype.coprod V2.subtype with hT
  have hrange : LinearMap.range T = V1 ⊔ V2 := by
    rw [hT, LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype]
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective T.rangeRestrict
    (LinearMap.range_rangeRestrict T)
  have hRc : Continuous R := LinearMap.continuous_of_finiteDimensional R
  obtain ⟨η, hη, hηR⟩ := Metric.continuousAt_iff.mp hRc.continuousAt (min δ1 δ2)
    (lt_min hδ1 hδ2)
  have hri : (0 : H) ∈ intrinsicInterior ℝ (edom p) := by
    refine ri_of_ball ((hdomp 0).2 ⟨zb, by simpa using hzD1, hzD2⟩) ⟨η, hη, fun w hw hwn => ?_⟩
    have hwT : w ∈ LinearMap.range T := by rw [hrange]; exact hspan hw
    set w' : LinearMap.range T := ⟨w, hwT⟩ with hw'
    have hRw : dist (R w') (R 0) < min δ1 δ2 := hηR (by
      rw [dist_zero_right]; exact hwn)
    rw [map_zero, dist_zero_right] at hRw
    have hsum : ((R w').1 : H) + ((R w').2 : H) = w := by
      have h := congrArg Subtype.val (LinearMap.congr_fun hR w')
      simpa [hT] using h
    refine (hdomp (0 + w)).2 ⟨zb - ((R w').2 : H), ?_, ?_⟩
    · have : zb - ((R w').2 : H) + (0 + w) = zb + ((R w').1 : H) := by rw [← hsum]; abel
      rw [this]
      refine hball1 _ (R w').1.2 ?_
      have : ‖((R w').1 : H)‖ = ‖(R w').1‖ := rfl
      rw [this]
      exact lt_of_le_of_lt (norm_fst_le (R w')) (lt_of_lt_of_le hRw (min_le_left _ _))
    · rw [sub_eq_add_neg]
      refine hball2 _ (V2.neg_mem (R w').2.2) ?_
      rw [norm_neg]
      have : ‖((R w').2 : H)‖ = ‖(R w').2‖ := rfl
      rw [this]
      exact lt_of_le_of_lt (norm_snd_le (R w')) (lt_of_lt_of_le hRw (min_le_right _ _))
  obtain ⟨ζ, hζ⟩ := subgrad_exists_ri p hpc 0 (by rw [hp0]; exact EReal.zero_ne_bot) hri
  have hζ' : ∀ e, ((ζ e : ℝ) : EReal) ≤ p e := fun e => by
    have := hζ e; rwa [hp0, zero_add, sub_zero] at this
  refine ⟨ℓ + ζ, -ζ, by ext; simp, fun z => ?_, fun z => ?_⟩
  · rcases ereal_cases (hb1 z) with h | ⟨r, hr⟩
    · rw [h]; exact le_top
    have := le_trans (hζ' (z - z0)) (iInf_le _ z0)
    simp only [add_sub_cancel, hk20, add_zero, hk1, hr] at this
    rw [e1, hr, ← EReal.coe_add, EReal.coe_le_coe_iff]
    norm_cast at this
    simp only [ContinuousLinearMap.add_apply]
    linarith
  · rcases ereal_cases (hb2 z) with h | ⟨r, hr⟩
    · rw [h]; exact le_top
    have := le_trans (hζ' (z0 - z)) (iInf_le _ z)
    simp only [add_sub_cancel, hk10, zero_add, hk2, hr] at this
    rw [e2, hr, ← EReal.coe_add, EReal.coe_le_coe_iff]
    norm_cast at this
    simp only [ContinuousLinearMap.neg_apply, map_sub]
    simp only [map_sub] at this
    linarith

set_option maxHeartbeats 1000000 in
/-- Slater multipliers (Rockafellar, Convex Analysis, Thm 28.2): `z₀` minimizes a convex
`φ` over `K ∩ {g ≤ 0}` with a strict Slater point, so there are `μ ≥ 0` with complementary
slackness and `z₀` minimizes `φ + Σ μᵢ gᵢ` over `K`. -/
theorem slater_multipliers {H : Type*} [AddCommGroup H] [Module ℝ H] {p : ℕ}
    (φ : H → EReal) (hφ : RiskAverseSDDP.Convergence.EConvex φ) (hbot : ∀ z, φ z ≠ ⊥)
    (K : Set H) (hK : Convex ℝ K)
    (g : Fin p → H → ℝ) (hg : ∀ i, ConvexOn ℝ univ (g i))
    (zb : H) (hzbK : zb ∈ K) (hzbφ : φ zb ≠ ⊤) (hzbg : ∀ i, g i zb < 0)
    (z0 : H) (hz0K : z0 ∈ K) (hz0g : ∀ i, g i z0 ≤ 0) (hz0 : φ z0 = 0)
    (hmin : ∀ z ∈ K, (∀ i, g i z ≤ 0) → 0 ≤ φ z) :
    ∃ μ : Fin p → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, μ i * g i z0 = 0) ∧
      ∀ z ∈ K, 0 ≤ φ z + ((∑ i, μ i * g i z : ℝ) : EReal) := by
  classical
  set S : Set (ℝ × (Fin p → ℝ)) :=
    {a | ∃ z ∈ K, φ z < (a.1 : EReal) ∧ ∀ i, g i z < a.2 i} with hS
  -- strict inequality for convex combinations
  have key : ∀ (a b r1 r2 t1 t2 : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 → r1 < t1 → r2 < t2 →
      a * r1 + b * r2 < a * t1 + b * t2 := by
    intro a b r1 r2 t1 t2 ha hb hab h1 h2
    have hm : 0 < min (t1 - r1) (t2 - r2) := lt_min (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left (t1 - r1) (t2 - r2)) ha,
      mul_le_mul_of_nonneg_left (min_le_right (t1 - r1) (t2 - r2)) hb]
  have hSc : Convex ℝ S := by
    rintro ⟨t1, v1⟩ ⟨z1, hz1K, hz1φ, hz1g⟩ ⟨t2, v2⟩ ⟨z2, hz2K, hz2φ, hz2g⟩ a b ha hb hab
    refine ⟨a • z1 + b • z2, hK hz1K hz2K ha hb hab, ?_, ?_⟩
    · have hr1 : φ z1 ≠ ⊤ := ne_top_of_lt hz1φ
      have hr2 : φ z2 ≠ ⊤ := ne_top_of_lt hz2φ
      have e1 : φ z1 = ((φ z1).toReal : EReal) := (EReal.coe_toReal hr1 (hbot z1)).symm
      have e2 : φ z2 = ((φ z2).toReal : EReal) := (EReal.coe_toReal hr2 (hbot z2)).symm
      have m1 : ((z1, (φ z1).toReal) : H × ℝ) ∈ {q : H × ℝ | φ q.1 ≤ (q.2 : EReal)} := by
        show φ z1 ≤ _; rw [← e1]
      have m2 : ((z2, (φ z2).toReal) : H × ℝ) ∈ {q : H × ℝ | φ q.1 ≤ (q.2 : EReal)} := by
        show φ z2 ≤ _; rw [← e2]
      have hc := hφ m1 m2 ha hb hab
      simp only [mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hc
      refine lt_of_le_of_lt hc ?_
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [EReal.coe_lt_coe_iff]
      have h1 : (φ z1).toReal < t1 := by
        rw [e1] at hz1φ; exact EReal.coe_lt_coe_iff.mp hz1φ
      have h2 : (φ z2).toReal < t2 := by
        rw [e2] at hz2φ; exact EReal.coe_lt_coe_iff.mp hz2φ
      exact key a b _ _ _ _ ha hb hab h1 h2
    · intro i
      have hc := (hg i).2 (mem_univ z1) (mem_univ z2) ha hb hab
      simp only [smul_eq_mul] at hc
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact lt_of_le_of_lt hc (key a b _ _ _ _ ha hb hab (hz1g i) (hz2g i))
  have hSo : IsOpen S := by
    have : S = ⋃ z ∈ K, ({a : ℝ × (Fin p → ℝ) | φ z < (a.1 : EReal)} ∩
        Prod.snd ⁻¹' (Set.pi univ fun i => Ioi (g i z))) := by
      ext a; simp [hS, Set.mem_iUnion]
      constructor <;> rintro ⟨z, h1, h2, h3⟩ <;> exact ⟨z, h2, h1, h3⟩
    rw [this]
    refine isOpen_biUnion fun z _ => IsOpen.inter ?_ ?_
    · exact isOpen_lt continuous_const (continuous_coe_real_ereal.comp continuous_fst)
    · exact (isOpen_set_pi finite_univ fun i _ => isOpen_Ioi).preimage continuous_snd
  have h0 : ((0 : ℝ), (0 : Fin p → ℝ)) ∉ S := by
    rintro ⟨z, hzK, hzφ, hzg⟩
    have := hmin z hzK fun i => (hzg i).le
    exact absurd hzφ (not_lt.mpr (by simpa using this))
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hSc hSo h0
  -- decompose f
  set α : ℝ := f (1, 0) with hα
  set β : Fin p → ℝ := fun i => f (0, Pi.single i 1) with hβ
  have hfdec : ∀ t : ℝ, ∀ v : Fin p → ℝ, f (t, v) = t * α + ∑ i, v i * β i := by
    intro t v
    have hv : ((t, v) : ℝ × (Fin p → ℝ)) = t • ((1 : ℝ), (0 : Fin p → ℝ)) +
        ∑ i, v i • ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin p → ℝ)) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hv, map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul]
    rfl
  have hf0 : f (0, 0) = 0 := by rw [Prod.mk_zero_zero]; exact f.map_zero
  have hneg : ∀ t v, ((t, v) : ℝ × (Fin p → ℝ)) ∈ S → t * α + ∑ i, v i * β i < 0 := by
    intro t v hm; have := hf _ hm; rw [hfdec, hf0] at this; exact this
  -- the Slater point
  set rb : ℝ := (φ zb).toReal with hrb
  have erb : φ zb = (rb : EReal) := (EReal.coe_toReal hzbφ (hbot zb)).symm
  have memb : ∀ t : ℝ, rb < t → ∀ v : Fin p → ℝ, (∀ i, g i zb < v i) →
      ((t, v) : ℝ × (Fin p → ℝ)) ∈ S := by
    intro t ht v hv
    exact ⟨zb, hzbK, by rw [erb]; exact EReal.coe_lt_coe_iff.mpr ht, hv⟩
  have hαneg : α < 0 := by
    set T : ℝ := max 1 (rb + 1)
    have hT : rb < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have := hneg T 0 (memb T hT 0 fun i => hzbg i)
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at this
    have hT1 : (0 : ℝ) < T := lt_of_lt_of_le one_pos (le_max_left _ _)
    nlinarith
  have hβnp : ∀ i, β i ≤ 0 := by
    intro i
    by_contra hpos
    push Not at hpos
    set w : Fin p → ℝ := fun j => g j zb + 1
    set C : ℝ := (rb + 1) * α + ∑ j, w j * β j
    have hs : ∀ s : ℝ, 0 ≤ s → C + s * β i < 0 := by
      intro s hs0
      have hv : ∀ j, g j zb < (w + s • (Pi.single i (1 : ℝ) : Fin p → ℝ)) j := by
        intro j
        simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        split_ifs <;> nlinarith
      have h := hneg (rb + 1) _ (memb _ (by linarith) _ hv)
      have he : ∑ j, (w + s • (Pi.single i (1 : ℝ) : Fin p → ℝ)) j * β j = ∑ j, w j * β j + s * β i := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
          Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [he] at h
      simp only [C]; linarith
    have := hs (|C| / β i + 1) (by positivity)
    have e : (|C| / β i + 1) * β i = |C| + β i := by
      rw [add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    rw [e] at this
    linarith [neg_abs_le C]
  set μ : Fin p → ℝ := fun i => β i / α with hμ
  have hμnn : ∀ i, 0 ≤ μ i := fun i => div_nonneg_of_nonpos (hβnp i) hαneg.le
  have hβμ : ∀ i, β i = μ i * α := fun i => (div_mul_cancel₀ (β i) hαneg.ne).symm
  have hmain : ∀ z ∈ K, 0 ≤ φ z + ((∑ i, μ i * g i z : ℝ) : EReal) := by
    intro z hzK
    by_cases htop : φ z = ⊤
    · rw [htop, EReal.top_add_coe]; exact le_top
    set r : ℝ := (φ z).toReal
    have er : φ z = (r : EReal) := (EReal.coe_toReal htop (hbot z)).symm
    rw [er, ← EReal.coe_add, EReal.coe_nonneg]
    have hε : ∀ ε : ℝ, 0 < ε → 0 < r + ∑ i, μ i * g i z + ε * (1 + ∑ i, μ i) := by
      intro ε hε0
      have hm : ((r + ε, fun i => g i z + ε) : ℝ × (Fin p → ℝ)) ∈ S :=
        ⟨z, hzK, by rw [er]; exact EReal.coe_lt_coe_iff.mpr (by linarith),
          fun i => by simp only; linarith⟩
      have h := hneg _ _ hm
      have he : ∑ i, (g i z + ε) * β i = (∑ i, μ i * g i z + ε * ∑ i, μ i) * α := by
        simp only [hβμ, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring
      rw [he] at h
      nlinarith
    by_contra hX
    push Not at hX
    have hM : 0 < 1 + ∑ i, μ i := by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hμnn i
      linarith
    set X := r + ∑ i, μ i * g i z
    have := hε (-X / (2 * (1 + ∑ i, μ i))) (div_pos (by linarith) (by linarith))
    have e : -X / (2 * (1 + ∑ i, μ i)) * (1 + ∑ i, μ i) = -X / 2 := by
      field_simp
    linarith
  refine ⟨μ, hμnn, ?_, hmain⟩
  have h0 := hmain z0 hz0K
  rw [hz0, zero_add, EReal.coe_nonneg] at h0
  have hnp : ∀ i ∈ Finset.univ, μ i * g i z0 ≤ 0 :=
    fun i _ => mul_nonpos_of_nonneg_of_nonpos (hμnn i) (hz0g i)
  have hsum : ∑ i, μ i * g i z0 = 0 := le_antisymm (Finset.sum_nonpos hnp) h0
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hsum i (Finset.mem_univ i)


section Vec
open RiskAverseSDDP.Subdiff

variable {m n : ℕ}

theorem pair_add_left (u v z : E m × E n) : pair (u + v) z = pair u z + pair v z := by
  simp only [pair, Prod.fst_add, Prod.snd_add, inner_add_left]; ring

theorem pair_smul_left (c : ℝ) (u z : E m × E n) : pair (c • u) z = c * pair u z := by
  simp only [pair, Prod.smul_fst, Prod.smul_snd, real_inner_smul_left]; ring

theorem pair_zero_left (z : E m × E n) : pair 0 z = 0 := by simp [pair]

theorem pair_sum_left {ι : Type*} (s : Finset ι) (u : ι → E m × E n) (z : E m × E n) :
    pair (∑ i ∈ s, u i) z = ∑ i ∈ s, pair (u i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add_left, ih]

theorem pair_self_nonneg (u : E m × E n) : 0 ≤ pair u u := by
  simp only [pair]; exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg

theorem pair_self_eq_zero {u : E m × E n} (h : pair u u ≤ 0) : u = 0 := by
  simp only [pair] at h
  have h1 := real_inner_self_nonneg (x := u.1)
  have h2 := real_inner_self_nonneg (x := u.2)
  have e1 : inner ℝ u.1 u.1 = 0 := by linarith
  have e2 : inner ℝ u.2 u.2 = 0 := by linarith
  ext1
  · exact inner_self_eq_zero.mp e1
  · exact inner_self_eq_zero.mp e2

theorem pair_ext {u v : E m × E n} (h : ∀ z, pair u z = pair v z) : u = v := by
  have := h (u - v)
  have h0 : pair (u - v) (u - v) = 0 := by
    have e : pair (u - v) (u - v) = pair u (u - v) - pair v (u - v) := by
      simp only [pair, Prod.fst_sub, Prod.snd_sub, inner_sub_left]; ring
    rw [e, this, sub_self]
  exact sub_eq_zero.mp (pair_self_eq_zero h0.le)

noncomputable def pairL (u : E m × E n) : (E m × E n) →L[ℝ] ℝ :=
  (innerSL ℝ u.1).comp (ContinuousLinearMap.fst ℝ (E m) (E n)) +
    (innerSL ℝ u.2).comp (ContinuousLinearMap.snd ℝ (E m) (E n))

theorem pairL_apply (u z : E m × E n) : pairL u z = pair u z := by
  simp [pairL, pair, innerSL_apply_apply]

theorem rep (ℓ : (E m × E n) →L[ℝ] ℝ) : ∃ u : E m × E n, ∀ z, ℓ z = pair u z := by
  refine ⟨((InnerProductSpace.toDual ℝ (E m)).symm (ℓ.comp (ContinuousLinearMap.inl ℝ (E m) (E n))),
    (InnerProductSpace.toDual ℝ (E n)).symm (ℓ.comp (ContinuousLinearMap.inr ℝ (E m) (E n)))),
    fun z => ?_⟩
  simp only [pair, InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]
  congr 1
  ext <;> simp

/-- Vector form of the sum rule (Rockafellar Thm 23.8) on `ℝ^m × ℝ^n`. -/
theorem subdiffProd_add_ri (F1 F2 : E m × E n → EReal)
    (h1 : RiskAverseSDDP.Convergence.EConvex F1) (h2 : RiskAverseSDDP.Convergence.EConvex F2)
    (hb1 : ∀ z, F1 z ≠ ⊥) (hb2 : ∀ z, F2 z ≠ ⊥) (zb : E m × E n)
    (hri1 : zb ∈ intrinsicInterior ℝ (edom F1)) (hri2 : zb ∈ intrinsicInterior ℝ (edom F2))
    (z0 u : E m × E n) (hu : u ∈ subdiffProd (fun z => F1 z + F2 z) z0) :
    ∃ u1 ∈ subdiffProd F1 z0, ∃ u2 ∈ subdiffProd F2 z0, u = u1 + u2 := by
  obtain ⟨htop, -, hineq⟩ := hu
  have ht : F1 z0 ≠ ⊤ ∧ F2 z0 ≠ ⊤ := by
    have h := htop
    rw [ne_eq, sum_top (hb1 z0) (hb2 z0), not_or] at h
    exact h
  obtain ⟨ℓ1, ℓ2, hℓ, hs1, hs2⟩ := sum_rule_ri F1 F2 h1 h2 hb1 hb2 zb hri1 hri2 z0 ht.1 ht.2
    (pairL u) (fun z => by rw [pairL_apply]; exact hineq z)
  obtain ⟨u1, hu1⟩ := rep ℓ1
  obtain ⟨u2, hu2⟩ := rep ℓ2
  refine ⟨u1, ⟨ht.1, hb1 z0, fun z => by rw [← hu1]; exact hs1 z⟩, u2,
    ⟨ht.2, hb2 z0, fun z => by rw [← hu2]; exact hs2 z⟩, pair_ext fun z => ?_⟩
  rw [pair_add_left, ← hu1, ← hu2, ← pairL_apply, hℓ, ContinuousLinearMap.add_apply]

theorem ri_inter {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {A B : Set H} {z : H}
    (hA : z ∈ intrinsicInterior ℝ A) (hB : z ∈ intrinsicInterior ℝ B) :
    z ∈ intrinsicInterior ℝ (A ∩ B) := by
  obtain ⟨hzA, δ1, hδ1, h1⟩ := ri_ball hA
  obtain ⟨hzB, δ2, hδ2, h2⟩ := ri_ball hB
  refine ri_of_ball ⟨hzA, hzB⟩ ⟨min δ1 δ2, lt_min hδ1 hδ2, fun w hw hwn =>
    ⟨h1 w (vectorSpan_mono ℝ inter_subset_left hw) (lt_of_lt_of_le hwn (min_le_left _ _)),
     h2 w (vectorSpan_mono ℝ inter_subset_right hw) (lt_of_lt_of_le hwn (min_le_right _ _))⟩⟩

theorem ri_univ {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (z : H) :
    z ∈ intrinsicInterior ℝ (univ : Set H) :=
  ri_of_ball (mem_univ z) ⟨1, one_pos, fun _ _ _ => mem_univ _⟩

theorem ri_affine {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [AddCommGroup F]
    [Module ℝ F] (T : H →ₗ[ℝ] F) (c : F) (z : H) (hz : T z = c) :
    z ∈ intrinsicInterior ℝ {x | T x = c} := by
  refine ri_of_ball hz ⟨1, one_pos, fun w hw _ => ?_⟩
  have hker : vectorSpan ℝ {x | T x = c} ≤ LinearMap.ker T := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' : T a = c := ha
    have hb' : T b = c := hb
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub, ha', hb', sub_self]
  have := hker hw
  rw [LinearMap.mem_ker] at this
  show T (z + w) = c
  rw [map_add, this, add_zero, hz]

theorem ri_prodY (Y : Set (E n)) (xb : E m) (yb : E n) (hy : yb ∈ intrinsicInterior ℝ Y) :
    (xb, yb) ∈ intrinsicInterior ℝ {z : E m × E n | z.2 ∈ Y} := by
  obtain ⟨hyY, δ, hδ, hball⟩ := ri_ball hy
  refine ri_of_ball hyY ⟨δ, hδ, fun w hw hwn => ?_⟩
  have hsnd : ∀ w ∈ vectorSpan ℝ {z : E m × E n | z.2 ∈ Y}, w.2 ∈ vectorSpan ℝ Y := by
    intro w hw
    rw [vectorSpan_def] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have := vsub_mem_vectorSpan ℝ (show a.2 ∈ Y from ha) (show b.2 ∈ Y from hb)
      simpa [vsub_eq_sub] using this
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
  exact hball _ (hsnd w hw) (lt_of_le_of_lt (norm_snd_le w) hwn)

theorem econvex_of_convexOn {H : Type*} [AddCommGroup H] [Module ℝ H] {f : H → ℝ}
    (hf : ConvexOn ℝ univ f) : RiskAverseSDDP.Convergence.EConvex (fun z => (f z : EReal)) := by
  intro q1 hq1 q2 hq2 a b ha hb hab
  simp only [mem_setOf_eq, EReal.coe_le_coe_iff] at hq1 hq2 ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have := hf.2 (mem_univ q1.1) (mem_univ q2.1) ha hb hab
  simp only [smul_eq_mul] at this
  nlinarith

theorem convexOn_fsum {H ι : Type*} [AddCommGroup H] [Module ℝ H] [DecidableEq ι]
    (s : Finset ι) (h : ι → H → ℝ) (hc : ∀ i, ConvexOn ℝ univ (h i)) :
    ConvexOn ℝ univ (fun z => ∑ i ∈ s, h i z) := by
  induction s using Finset.induction_on with
  | empty => simpa using (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set H)))
  | insert a s ha ih =>
    have e : (fun z => ∑ i ∈ insert a s, h i z) = h a + (fun z => ∑ i ∈ s, h i z) := by
      funext z; simp [Finset.sum_insert ha]
    rw [e]; exact (hc a).add ih

/-- Finite sum rule for real-valued convex functions. -/
theorem subdiff_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → E m × E n → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (z0 u : E m × E n)
    (hu : ∀ z, ∑ i ∈ s, h i z0 + pair u (z - z0) ≤ ∑ i ∈ s, h i z) :
    ∃ w : ι → E m × E n, (∀ i ∈ s, ∀ z, h i z0 + pair (w i) (z - z0) ≤ h i z) ∧
      u = ∑ i ∈ s, w i := by
  induction s using Finset.induction_on generalizing u with
  | empty =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    have := hu (z0 + u)
    simp only [Finset.sum_empty, zero_add, add_sub_cancel_left] at this
    simpa using pair_self_eq_zero this
  | insert a s ha ih =>
    have hconv : ConvexOn ℝ univ (fun z => ∑ i ∈ s, h i z) := convexOn_fsum s h hc
    have hsub : u ∈ subdiffProd (fun z => ((h a z : ℝ) : EReal) + ((∑ i ∈ s, h i z : ℝ) : EReal)) z0 := by
      refine ⟨by simp [← EReal.coe_add], by simp [← EReal.coe_add], fun z => ?_⟩
      have := hu z
      rw [Finset.sum_insert ha, Finset.sum_insert ha] at this
      simp only [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
    obtain ⟨u1, ⟨-, -, hu1⟩, u2, ⟨-, -, hu2⟩, rfl⟩ := subdiffProd_add_ri _ _
      (econvex_of_convexOn (hc a)) (econvex_of_convexOn hconv) (fun _ => EReal.coe_ne_bot _)
      (fun _ => EReal.coe_ne_bot _) z0
      (by simpa [edom] using ri_univ z0) (by simpa [edom] using ri_univ z0) z0 u hsub
    obtain ⟨w, hw, hws⟩ := ih u2 (fun z => by
      have := hu2 z; simp only [← EReal.coe_add, EReal.coe_le_coe_iff] at this; exact this)
    refine ⟨Function.update w a u1, fun i hi z => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hi with rfl | hi'
      · have := hu1 z
        simp only [Function.update_self, ← EReal.coe_add, EReal.coe_le_coe_iff] at this ⊢
        exact this
      · have hne : i ≠ a := fun h' => ha (h' ▸ hi')
        rw [Function.update_of_ne hne]; exact hw i hi' z
    · rw [Finset.sum_insert ha, Function.update_self, hws]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (by rintro rfl; exact ha hi)]

end Vec

section Prog
open RiskAverseSDDP.Subdiff

variable {m n q p : ℕ}

theorem adjT {k : ℕ} (A : Matrix (Fin q) (Fin k) ℝ) (lam : E q) (x : E k) :
    inner ℝ lam (Matrix.toEuclideanLin A x) = inner ℝ (Matrix.toEuclideanLin A.transpose lam) x := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left]

theorem lin_continuous (P : ConvexProgram m n q p) :
    Continuous (fun z : E m × E n => P.lin z.1 z.2) := by
  unfold ConvexProgram.lin
  exact ((Matrix.toEuclideanLin P.A).continuous_of_finiteDimensional.comp continuous_fst).add
    ((Matrix.toEuclideanLin P.B).continuous_of_finiteDimensional.comp continuous_snd)

theorem sol_nonempty (P : ConvexProgram m n q p) (X : Set (E m))
    (hY : P.Y.Nonempty ∧ IsCompact P.Y ∧ Convex ℝ P.Y) (hH : P.AssumptionH X) (x0 : E m)
    (hS : (P.S x0).Nonempty) : (P.Sol x0).Nonempty := by
  have hc : Continuous (fun y : E n => ((x0, y) : E m × E n)) := continuous_const.prodMk continuous_id
  have hcl : IsClosed (P.S x0) := by
    have h1 : IsClosed P.Y := hY.2.1.isClosed
    have hlc : Continuous fun y : E n => P.lin x0 y := by
      unfold ConvexProgram.lin
      exact continuous_const.add (Matrix.toEuclideanLin P.B).continuous_of_finiteDimensional
    have h2 : IsClosed {y : E n | P.lin x0 y = P.b} := isClosed_eq hlc continuous_const
    have h3 : IsClosed {y : E n | ∀ i, P.g i (x0, y) ≤ 0} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun i => ((hH.2.1 i).1.isClosed_preimage 0).preimage hc
    have : P.S x0 = P.Y ∩ {y | P.lin x0 y = P.b} ∩ {y | ∀ i, P.g i (x0, y) ≤ 0} := by
      ext y
      exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
    rw [this]; exact (h1.inter h2).inter h3
  have hcpt : IsCompact (P.S x0) := hY.2.1.of_isClosed_subset hcl (fun y hy => hy.1)
  have hfl : LowerSemicontinuous P.f := hH.1.1
  have hl2 : LowerSemicontinuous (fun y : E n => P.f (x0, y)) := hfl.comp hc
  have hlsc : LowerSemicontinuousOn (fun y => P.f (x0, y)) (P.S x0) := hl2.lowerSemicontinuousOn _
  obtain ⟨y, hy, hmin⟩ := hlsc.exists_isMinOn hS hcpt
  refine ⟨y, hy, le_antisymm (le_iInf₂ fun y' hy' => isMinOn_iff.mp hmin y' hy') (iInf₂_le y hy)⟩

theorem normal_C1 (P : ConvexProgram m n q p) (z0 : E m × E n) (hz0 : P.lin z0.1 z0.2 = P.b)
    (u : E m × E n) (h : ∀ z : E m × E n, P.lin z.1 z.2 = P.b → pair u (z - z0) ≤ 0) :
    ∃ lam : E q, u = (Matrix.toEuclideanLin P.A.transpose lam,
      Matrix.toEuclideanLin P.B.transpose lam) := by
  set Mf : (E m × E n) →ₗ[ℝ] E q := (Matrix.toEuclideanLin P.A).comp (LinearMap.fst ℝ _ _) +
    (Matrix.toEuclideanLin P.B).comp (LinearMap.snd ℝ _ _) with hMf
  have hMlin : ∀ z : E m × E n, Mf z = P.lin z.1 z.2 := fun z => by
    simp [hMf, ConvexProgram.lin]
  have hker : ∀ w ∈ LinearMap.ker Mf, pair u w = 0 := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have h1 := h (z0 + w) (by rw [← hMlin, map_add, hw, add_zero, hMlin, hz0])
    have h2 := h (z0 - w) (by rw [← hMlin, map_sub, hw, sub_zero, hMlin, hz0])
    simp only [add_sub_cancel_left, sub_sub_cancel_left] at h1 h2
    have : pair u (-w) = -pair u w := by
      simp only [pair, Prod.fst_neg, Prod.snd_neg, inner_neg_right]; ring
    rw [this] at h2; linarith
  have hmem : (pairL u : (E m × E n) →L[ℝ] ℝ).toLinearMap ∈
      (LinearMap.ker Mf).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw; rw [ContinuousLinearMap.coe_coe, pairL_apply]; exact hker w hw
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨l', hl'⟩ := hmem
  set lam : E q := (InnerProductSpace.toDual ℝ (E q)).symm (LinearMap.toContinuousLinearMap l')
    with hlam_def
  have hlam : ∀ v, inner ℝ lam v = l' v := fun v => by
    simp [hlam_def, InnerProductSpace.toDual_symm_apply]
  refine ⟨lam, pair_ext fun z => ?_⟩
  have e1 : pair u z = l' (Mf z) := by
    rw [← pairL_apply, ← ContinuousLinearMap.coe_coe, ← hl']; rfl
  rw [e1, ← hlam, hMf]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    inner_add_right, pair]
  rw [adjT P.A, adjT P.B]

theorem normal_Y (Y : Set (E n)) (z0 : E m × E n) (hz0 : z0.2 ∈ Y) (u : E m × E n)
    (h : ∀ z : E m × E n, z.2 ∈ Y → pair u (z - z0) ≤ 0) :
    u.1 = 0 ∧ u.2 ∈ FirstOrderOpt.ConvexTheory.normalCone Y z0.2 := by
  constructor
  · have := h (z0 + (u.1, 0)) (by simpa using hz0)
    simp only [add_sub_cancel_left, pair, inner_zero_right, add_zero] at this
    exact inner_self_eq_zero.mp (le_antisymm this real_inner_self_nonneg)
  · intro y hy
    have := h (z0.1, y) hy
    simpa [pair] using this

theorem easy_dir (P : ConvexProgram m n q p) (x0 : E m) (y0 : E n) (hy0 : y0 ∈ P.Sol x0)
    (hbot : P.f (x0, y0) ≠ ⊥) (s : E m) (u : E m × E n) (hu : u ∈ subdiffProd P.f (x0, y0))
    (lam : E q) (μ : Fin p → ℝ) (w : Fin p → E m × E n) (ν : E n)
    (hν : ν ∈ FirstOrderOpt.ConvexTheory.normalCone P.Y y0)
    (hμw : ∀ i ∈ P.active x0 y0, 0 ≤ μ i ∧ w i ∈ subdiffProd (P.g i) (x0, y0))
    (hs : s = u.1 + Matrix.toEuclideanLin P.A.transpose lam + ∑ i ∈ P.active x0 y0, μ i • (w i).1)
    (h0 : (0 : E n) = u.2 + Matrix.toEuclideanLin P.B.transpose lam +
      ∑ i ∈ P.active x0 y0, μ i • (w i).2 + ν) :
    s ∈ subdiff P.Q x0 := by
  have hQ : P.Q x0 = P.f (x0, y0) := hy0.2.symm
  refine ⟨by rw [hQ]; exact hu.1, by rw [hQ]; exact hbot, fun x => ?_⟩
  refine le_iInf₂ fun y hy => ?_
  rw [hQ]
  refine le_trans ?_ (hu.2.2 (x, y))
  refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
  set I := P.active x0 y0
  have hu1 : u.1 = s - Matrix.toEuclideanLin P.A.transpose lam - ∑ i ∈ I, μ i • (w i).1 := by
    rw [hs]; abel
  have hu2 : u.2 = -(Matrix.toEuclideanLin P.B.transpose lam + ∑ i ∈ I, μ i • (w i).2 + ν) :=
    eq_neg_of_add_eq_zero_left (by rw [← h0.symm]; abel)
  have F1 : inner ℝ (Matrix.toEuclideanLin P.A.transpose lam) (x - x0) +
      inner ℝ (Matrix.toEuclideanLin P.B.transpose lam) (y - y0) = 0 := by
    rw [← adjT, ← adjT, ← inner_add_right, map_sub, map_sub]
    have h1 : P.lin x y = P.b := hy.2.1
    have h2 : P.lin x0 y0 = P.b := hy0.1.2.1
    unfold ConvexProgram.lin at h1 h2
    have : Matrix.toEuclideanLin P.A x - Matrix.toEuclideanLin P.A x0 +
        (Matrix.toEuclideanLin P.B y - Matrix.toEuclideanLin P.B y0) = 0 := by
      rw [show Matrix.toEuclideanLin P.A x - Matrix.toEuclideanLin P.A x0 +
        (Matrix.toEuclideanLin P.B y - Matrix.toEuclideanLin P.B y0) =
        (Matrix.toEuclideanLin P.A x + Matrix.toEuclideanLin P.B y) -
        (Matrix.toEuclideanLin P.A x0 + Matrix.toEuclideanLin P.B y0) by abel, h1, h2, sub_self]
    rw [this, inner_zero_right]
  have F2 : ∑ i ∈ I, μ i * inner ℝ (w i).1 (x - x0) + ∑ i ∈ I, μ i * inner ℝ (w i).2 (y - y0)
      ≤ 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonpos fun i hi => ?_
    obtain ⟨hμ, hw⟩ := hμw i hi
    have hact : P.g i (x0, y0) = 0 := by
      simp only [I, ConvexProgram.active, Finset.mem_filter] at hi; exact hi.2
    have hg := hw.2.2 (x, y)
    rw [hact, zero_add] at hg
    have hgle : P.g i (x, y) ≤ 0 := hy.2.2 i
    have hp : pair (w i) ((x, y) - (x0, y0)) ≤ 0 := EReal.coe_nonpos.mp (le_trans hg hgle)
    simp only [pair, Prod.mk_sub_mk] at hp
    rw [← mul_add]
    exact mul_nonpos_of_nonneg_of_nonpos hμ hp
  have F3 : inner ℝ ν (y - y0) ≤ 0 := hν y hy.1
  simp only [pair, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
  rw [hu1, hu2]
  simp only [inner_sub_left, inner_add_left, inner_neg_left, sum_inner, real_inner_smul_left]
  linarith

end Prog

section Hard
open RiskAverseSDDP.Subdiff

noncomputable def rst {H : Type*} (C : Set H) (h : H → ℝ) (z : H) : EReal := by
  classical
  exact if z ∈ C then (h z : EReal) else ⊤

theorem rst_mem {H : Type*} {C : Set H} (h : H → ℝ) {z : H} (hz : z ∈ C) :
    rst C h z = (h z : EReal) := by
  simp [rst, hz]

theorem rst_not_mem {H : Type*} {C : Set H} (h : H → ℝ) {z : H} (hz : z ∉ C) :
    rst C h z = ⊤ := by
  simp [rst, hz]

theorem rst_ne_bot {H : Type*} (C : Set H) (h : H → ℝ) (z : H) : rst C h z ≠ ⊥ := by
  by_cases hz : z ∈ C
  · rw [rst_mem h hz]; exact EReal.coe_ne_bot _
  · rw [rst_not_mem h hz]; simp

theorem edom_rst {H : Type*} (C : Set H) (h : H → ℝ) : edom (rst C h) = C := by
  ext z
  by_cases hz : z ∈ C
  · simp only [edom, mem_setOf_eq, rst_mem h hz, hz, iff_true]; exact EReal.coe_ne_top _
  · simp only [edom, mem_setOf_eq, rst_not_mem h hz, hz, iff_false, ne_eq, not_not]

theorem rst_add_zero {H : Type*} (C D : Set H) (h : H → ℝ) (z : H) :
    rst C h z + rst D (fun _ => 0) z = rst (C ∩ D) h z := by
  by_cases hC : z ∈ C <;> by_cases hD : z ∈ D
  · rw [rst_mem h hC, rst_mem _ hD, rst_mem (C := C ∩ D) h ⟨hC, hD⟩]; simp
  · rw [rst_mem h hC, rst_not_mem _ hD, rst_not_mem h (fun hz => hD hz.2)]; simp
  · rw [rst_not_mem h hC, rst_mem _ hD, rst_not_mem h (fun hz => hC hz.1)]; simp
  · rw [rst_not_mem h hC, rst_not_mem _ hD, rst_not_mem h (fun hz => hC hz.1)]; simp

theorem econvex_rst {H : Type*} [AddCommGroup H] [Module ℝ H] (C : Set H) (hC : Convex ℝ C)
    (h : H → ℝ) (hh : ConvexOn ℝ C h) : RiskAverseSDDP.Convergence.EConvex (rst C h) := by
  intro q1 hq1 q2 hq2 a b ha hb hab
  simp only [mem_setOf_eq] at hq1 hq2 ⊢
  have h1 : q1.1 ∈ C := by
    by_contra hc
    rw [rst_not_mem h hc] at hq1
    exact EReal.coe_ne_top _ (top_le_iff.mp hq1)
  have h2 : q2.1 ∈ C := by
    by_contra hc
    rw [rst_not_mem h hc] at hq2
    exact EReal.coe_ne_top _ (top_le_iff.mp hq2)
  rw [rst_mem h h1, EReal.coe_le_coe_iff] at hq1
  rw [rst_mem h h2, EReal.coe_le_coe_iff] at hq2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [rst_mem h (hC h1 h2 ha hb hab), EReal.coe_le_coe_iff]
  have := hh.2 h1 h2 ha hb hab
  simp only [smul_eq_mul] at this
  nlinarith

theorem coe_le_add_coe (x : EReal) (r t : ℝ) (hx : (r : EReal) ≤ x) :
    ((r + t : ℝ) : EReal) ≤ x + (t : EReal) := by
  induction x using EReal.rec with
  | bot => exact absurd hx (by simp)
  | coe a => norm_cast at hx ⊢; linarith
  | top => simp

theorem add_coe_ne_bot {x : EReal} (hx : x ≠ ⊥) (r : ℝ) : x + (r : EReal) ≠ ⊥ := by
  rcases ereal_cases hx with rfl | ⟨a, rfl⟩
  · simp
  · exact_mod_cast EReal.coe_ne_bot (a + r)

theorem convexOn_toReal {H : Type*} [AddCommGroup H] [Module ℝ H] (φ : H → EReal)
    (hφ : RiskAverseSDDP.Convergence.EConvex φ) (ht : ∀ z, φ z ≠ ⊤) (hb : ∀ z, φ z ≠ ⊥) :
    ConvexOn ℝ univ (fun z => (φ z).toReal) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb' hab => ?_⟩
  have e : ∀ z, φ z = (((φ z).toReal : ℝ) : EReal) := fun z =>
    (EReal.coe_toReal (ht z) (hb z)).symm
  have := epi_comb hφ (e x).le (e y).le ha hb' hab
  rw [e (a • x + b • y), EReal.coe_le_coe_iff] at this
  simpa [smul_eq_mul] using this

variable {m n q p : ℕ}

theorem normal_of_rst {C : Set (E m × E n)} {z0 u : E m × E n}
    (hu : u ∈ subdiffProd (rst C (fun _ => 0)) z0) : z0 ∈ C ∧ ∀ z ∈ C, pair u (z - z0) ≤ 0 := by
  obtain ⟨ht, -, h⟩ := hu
  have hz0 : z0 ∈ C := by
    by_contra hc
    exact ht (rst_not_mem _ hc)
  refine ⟨hz0, fun z hz => ?_⟩
  have := h z
  rw [rst_mem _ hz0, rst_mem _ hz, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
  linarith

set_option maxHeartbeats 1000000 in
theorem hard_dir (P : ConvexProgram m n q p) (X : Set (E m))
    (hY : P.Y.Nonempty ∧ IsCompact P.Y ∧ Convex ℝ P.Y) (hH : P.AssumptionH X)
    (hR1 : ∀ i z, P.g i z ≠ ⊤) (hSlater : P.RepairedSlater X)
    (x0 : E m) (y0 : E n) (hy0 : y0 ∈ P.Sol x0) (s : E m) (hs : s ∈ subdiff P.Q x0) :
    ∃ u ∈ subdiffProd P.f (x0, y0), ∃ lam : E q, ∃ μ : Fin p → ℝ,
      ∃ w : Fin p → E m × E n, ∃ ν ∈ FirstOrderOpt.ConvexTheory.normalCone P.Y y0,
        (∀ i ∈ P.active x0 y0, 0 ≤ μ i ∧ w i ∈ subdiffProd (P.g i) (x0, y0)) ∧
        s = u.1 + Matrix.toEuclideanLin P.A.transpose lam + ∑ i ∈ P.active x0 y0, μ i • (w i).1 ∧
        (0 : E n) = u.2 + Matrix.toEuclideanLin P.B.transpose lam +
          ∑ i ∈ P.active x0 y0, μ i • (w i).2 + ν := by
  classical
  obtain ⟨xb, -, yb, hyb, hlinb, hgb, hrib⟩ := hSlater
  have hfE : RiskAverseSDDP.Convergence.EConvex P.f := hH.1.2.2
  have hfbot : ∀ z, P.f z ≠ ⊥ := hH.1.2.1.1
  have hQ : P.Q x0 = P.f (x0, y0) := hy0.2.symm
  have hfz0top : P.f (x0, y0) ≠ ⊤ := hQ ▸ hs.1
  obtain ⟨a, hfa⟩ : ∃ a : ℝ, P.f (x0, y0) = (a : EReal) :=
    ⟨_, (EReal.coe_toReal hfz0top (hfbot (x0, y0))).symm⟩
  obtain ⟨g', hg'def⟩ : ∃ g' : Fin p → E m × E n → ℝ, g' = fun i z => (P.g i z).toReal := ⟨_, rfl⟩
  have hgcoe : ∀ i z, P.g i z = ((g' i z : ℝ) : EReal) := fun i z => by
    rw [hg'def]; exact (EReal.coe_toReal (hR1 i z) ((hH.2.1 i).2.2 z)).symm
  have hg'c : ∀ i, ConvexOn ℝ univ (g' i) := fun i => by
    rw [hg'def]; exact convexOn_toReal (P.g i) (hH.2.1 i).2.1 (hR1 i) (hH.2.1 i).2.2
  -- the linear constraint map and the sets
  obtain ⟨Mf, hMf⟩ : ∃ Mf : (E m × E n) →ₗ[ℝ] E q,
      Mf = (Matrix.toEuclideanLin P.A).comp (LinearMap.fst ℝ _ _) +
        (Matrix.toEuclideanLin P.B).comp (LinearMap.snd ℝ _ _) := ⟨_, rfl⟩
  have hMlin : ∀ z : E m × E n, Mf z = P.lin z.1 z.2 := fun z => by
    simp [hMf, ConvexProgram.lin]
  obtain ⟨C1, hC1⟩ : ∃ C : Set (E m × E n), C = {z | Mf z = P.b} := ⟨_, rfl⟩
  obtain ⟨CY, hCY⟩ : ∃ C : Set (E m × E n), C = {z | z.2 ∈ P.Y} := ⟨_, rfl⟩
  have hmC1 : ∀ z, z ∈ C1 ↔ P.lin z.1 z.2 = P.b := fun z => by
    rw [hC1, mem_setOf_eq, hMlin]
  have hmCY : ∀ z, z ∈ CY ↔ z.2 ∈ P.Y := fun z => by rw [hCY, mem_setOf_eq]
  have hC1c : Convex ℝ C1 := by
    rw [hC1]
    intro z1 h1 z2 h2 a' b' _ _ hab'
    simp only [mem_setOf_eq] at h1 h2 ⊢
    rw [map_add, map_smul, map_smul, h1, h2, ← add_smul, hab', one_smul]
  have hCYc : Convex ℝ CY := by
    rw [hCY]
    intro z1 h1 z2 h2 a' b' ha' hb' hab'
    simp only [mem_setOf_eq, Prod.snd_add, Prod.smul_snd] at h1 h2 ⊢
    exact hY.2.2 h1 h2 ha' hb' hab'
  have hKc : Convex ℝ (C1 ∩ CY) := hC1c.inter hCYc
  have hzbC1 : (xb, yb) ∈ C1 := (hmC1 _).2 hlinb
  have hzbCY : (xb, yb) ∈ CY := (hmCY _).2 (intrinsicInterior_subset hyb)
  have hz0C1 : (x0, y0) ∈ C1 := (hmC1 _).2 hy0.1.2.1
  have hz0CY : (x0, y0) ∈ CY := (hmCY _).2 hy0.1.1
  have hzbf : P.f (xb, yb) ≠ ⊤ := intrinsicInterior_subset hrib
  have hriC1 : (xb, yb) ∈ intrinsicInterior ℝ C1 := by
    rw [hC1]; exact ri_affine Mf P.b (xb, yb) (by rw [hMlin]; exact hlinb)
  have hriCY : (xb, yb) ∈ intrinsicInterior ℝ CY := by
    rw [hCY]; exact ri_prodY P.Y xb yb hyb
  -- the shifted objective φ
  obtain ⟨L, hL⟩ : ∃ L : (E m × E n) →ₗ[ℝ] ℝ,
      L = -((innerSL ℝ s).comp (ContinuousLinearMap.fst ℝ (E m) (E n))).toLinearMap := ⟨_, rfl⟩
  have hLz : ∀ z : E m × E n, L z = -inner ℝ s z.1 := fun z => by
    simp [hL]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -a + inner ℝ s x0 := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : E m × E n → EReal, φ = fun z => P.f z + ((c + L z : ℝ) : EReal) :=
    ⟨_, rfl⟩
  have hφE : RiskAverseSDDP.Convergence.EConvex φ := by rw [hφ]; exact econvex_add_affine hfE c L
  have hφbot : ∀ z, φ z ≠ ⊥ := fun z => by rw [hφ]; exact add_coe_ne_bot (hfbot z) _
  have hφz0 : φ (x0, y0) = 0 := by
    rw [hφ]
    show P.f (x0, y0) + ((c + L (x0, y0) : ℝ) : EReal) = 0
    have e : c + L (x0, y0) = -a := by rw [hLz, hc]; ring
    rw [hfa, e, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hφzb : φ (xb, yb) ≠ ⊤ := by
    rw [hφ]
    intro h
    exact ((sum_top (hfbot _) (EReal.coe_ne_bot _)).1 h).elim hzbf (EReal.coe_ne_top _)
  have hmin : ∀ z ∈ C1 ∩ CY, (∀ i, g' i z ≤ 0) → 0 ≤ φ z := by
    intro z hz hgz
    have hzS : z.2 ∈ P.S z.1 := ⟨(hmCY z).1 hz.2, (hmC1 z).1 hz.1,
      fun i => by rw [hgcoe]; exact_mod_cast hgz i⟩
    have hQz : P.Q z.1 ≤ P.f z := iInf₂_le z.2 hzS
    have hsz := hs.2.2 z.1
    rw [hQ, hfa] at hsz
    have h1 : ((a + inner ℝ s (z.1 - x0) : ℝ) : EReal) ≤ P.f z := by
      rw [EReal.coe_add]; exact hsz.trans hQz
    have h2 := coe_le_add_coe (P.f z) _ (c + L z) h1
    have e : a + inner ℝ s (z.1 - x0) + (c + L z) = 0 := by
      rw [hLz, hc, inner_sub_right]; ring
    rw [e, EReal.coe_zero] at h2
    rw [hφ]; exact h2
  obtain ⟨μ, hμ0, hcompl, hKμ⟩ := slater_multipliers φ hφE hφbot (C1 ∩ CY) hKc g' hg'c
    (xb, yb) ⟨hzbC1, hzbCY⟩ hφzb
    (fun i => by have := hgb i; rw [hgcoe] at this; exact_mod_cast this)
    (x0, y0) ⟨hz0C1, hz0CY⟩
    (fun i => by have := hy0.1.2.2 i; rw [hgcoe] at this; exact_mod_cast this) hφz0 hmin
  -- the Lagrangian part G
  have hμg : ∀ i, ConvexOn ℝ univ (fun z => μ i * g' i z) := fun i => by
    have := ConvexOn.smul (hμ0 i) (hg'c i)
    simpa only [smul_eq_mul] using this
  obtain ⟨G, hG⟩ : ∃ G : E m × E n → ℝ, G = fun z => ∑ i, μ i * g' i z := ⟨_, rfl⟩
  have hGc : ConvexOn ℝ univ G := by
    rw [hG]; exact convexOn_fsum Finset.univ (fun i z => μ i * g' i z) hμg
  have hGz0 : G (x0, y0) = 0 := by
    rw [hG]; exact Finset.sum_eq_zero fun i _ => hcompl i
  -- step A: (s, 0) is a subgradient of f + (G restricted to K)
  have hA : ((s, 0) : E m × E n) ∈
      subdiffProd (fun z => P.f z + rst (C1 ∩ CY) G z) (x0, y0) := by
    have hr0 : rst (C1 ∩ CY) G (x0, y0) = ((0 : ℝ) : EReal) := by
      rw [rst_mem (C := C1 ∩ CY) G ⟨hz0C1, hz0CY⟩, hGz0]
    refine ⟨?_, ?_, fun z => ?_⟩
    · simp only [hr0, hfa]; rw [← EReal.coe_add]; exact EReal.coe_ne_top _
    · simp only [hr0, hfa]; rw [← EReal.coe_add]; exact EReal.coe_ne_bot _
    · simp only [hr0, hfa]
      by_cases hz : z ∈ C1 ∩ CY
      · rw [rst_mem G hz]
        have h1 : 0 ≤ P.f z + ((c + L z : ℝ) : EReal) + ((∑ i, μ i * g' i z : ℝ) : EReal) := by
          have := hKμ z hz; rw [hφ] at this; exact this
        rcases ereal_cases (hfbot z) with h | ⟨r, h⟩
        · rw [h]; simp
        · rw [h] at h1 ⊢
          have hp : pair ((s, 0) : E m × E n) (z - (x0, y0)) = inner ℝ s z.1 - inner ℝ s x0 := by
            simp [pair, inner_sub_right]
          have hGz : G z = ∑ i, μ i * g' i z := by rw [hG]
          rw [hp, hGz]
          rw [hLz, hc] at h1
          norm_cast at h1 ⊢
          linarith
      · rw [rst_not_mem G hz]
        have : P.f z + ⊤ = ⊤ := (sum_top (hfbot z) (by simp)).2 (Or.inr rfl)
        rw [this]; exact le_top
  -- step B: split off ∂f
  obtain ⟨u1, hu1, u2, hu2, hsu⟩ := subdiffProd_add_ri P.f (rst (C1 ∩ CY) G) hfE
    (econvex_rst _ hKc G (hGc.subset (subset_univ _) hKc)) hfbot (rst_ne_bot _ G) (xb, yb) hrib
    (by rw [edom_rst]; exact ri_inter hriC1 hriCY) (x0, y0) (s, 0) hA
  -- step C: split off the normal cone of Y
  have eC : (fun z => rst C1 G z + rst CY (fun _ => 0) z) = rst (C1 ∩ CY) G :=
    funext fun z => rst_add_zero C1 CY G z
  obtain ⟨u3, hu3, u4, hu4, hu2s⟩ := subdiffProd_add_ri (rst C1 G) (rst CY (fun _ => 0))
    (econvex_rst _ hC1c G (hGc.subset (subset_univ _) hC1c))
    (econvex_rst _ hCYc _ (convexOn_const 0 hCYc)) (rst_ne_bot _ _) (rst_ne_bot _ _) (xb, yb)
    (by rw [edom_rst]; exact hriC1) (by rw [edom_rst]; exact hriCY)
    (x0, y0) u2 (by rw [eC]; exact hu2)
  -- step D: split off the normal cone of the affine set
  have eD : (fun z => rst univ G z + rst C1 (fun _ => 0) z) = rst C1 G :=
    funext fun z => by rw [rst_add_zero, univ_inter]
  obtain ⟨u5, hu5, u6, hu6, hu3s⟩ := subdiffProd_add_ri (rst univ G) (rst C1 (fun _ => 0))
    (econvex_rst _ convex_univ G hGc) (econvex_rst _ hC1c _ (convexOn_const 0 hC1c))
    (rst_ne_bot _ _) (rst_ne_bot _ _) (xb, yb)
    (by rw [edom_rst]; exact ri_univ _) (by rw [edom_rst]; exact hriC1)
    (x0, y0) u3 (by rw [eD]; exact hu3)
  -- step E: the normal cones
  obtain ⟨-, hn6⟩ := normal_of_rst hu6
  obtain ⟨lam, hlam⟩ := normal_C1 P (x0, y0) hy0.1.2.1 u6
    (fun z hz => hn6 z ((hmC1 z).2 hz))
  obtain ⟨-, hn4⟩ := normal_of_rst hu4
  obtain ⟨hu41, hν⟩ := normal_Y P.Y (x0, y0) hy0.1.1 u4 (fun z hz => hn4 z ((hmCY z).2 hz))
  -- step F: finite sum rule for G
  have hu5' : ∀ z, ∑ i ∈ Finset.univ, (fun i z => μ i * g' i z) i (x0, y0) +
      pair u5 (z - (x0, y0)) ≤ ∑ i ∈ Finset.univ, (fun i z => μ i * g' i z) i z := by
    intro z
    have := hu5.2.2 z
    rw [rst_mem G (mem_univ _), rst_mem G (mem_univ _), ← EReal.coe_add,
      EReal.coe_le_coe_iff, hG] at this
    exact this
  obtain ⟨ω, hω, hu5s⟩ := subdiff_sum Finset.univ (fun i z => μ i * g' i z) hμg (x0, y0) u5 hu5'
  -- step G: rescale to subgradients of the g_i
  have hex : ∀ i, ∃ wi : E m × E n, wi ∈ subdiffProd (P.g i) (x0, y0) ∧ ω i = μ i • wi := by
    intro i
    have hωi := hω i (Finset.mem_univ i)
    rcases (hμ0 i).lt_or_eq with hpos | hzero
    · refine ⟨(μ i)⁻¹ • ω i, ⟨by rw [hgcoe]; exact EReal.coe_ne_top _,
        by rw [hgcoe]; exact EReal.coe_ne_bot _, fun z => ?_⟩, ?_⟩
      · rw [hgcoe, hgcoe, ← EReal.coe_add, EReal.coe_le_coe_iff, pair_smul_left]
        have := hωi z
        refine le_of_mul_le_mul_left ?_ hpos
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
        exact this
      · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · have h0 := hωi ((x0, y0) + ω i)
      rw [← hzero] at h0
      simp only [zero_mul, zero_add, add_sub_cancel_left] at h0
      have hω0 : ω i = 0 := pair_self_eq_zero h0
      have hed : edom (P.g i) = univ := eq_univ_of_forall (hR1 i)
      obtain ⟨ℓ, hℓ⟩ := subgrad_exists_ri (P.g i) (hH.2.1 i).2.1 (x0, y0)
        ((hH.2.1 i).2.2 _) (by rw [hed]; exact ri_univ _)
      obtain ⟨wi, hwi⟩ := rep ℓ
      exact ⟨wi, ⟨hR1 i _, (hH.2.1 i).2.2 _, fun z => by rw [← hwi]; exact hℓ z⟩,
        by rw [hω0, ← hzero, zero_smul]⟩
  choose w hw using hex
  -- step H: restrict the sum to the active set
  have hsumω : u5 = ∑ i ∈ P.active x0 y0, μ i • w i := by
    rw [hu5s, Finset.sum_congr rfl (fun i _ => (hw i).2)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
    simp only [ConvexProgram.active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hne : g' i (x0, y0) ≠ 0 := fun h0 => hi (by rw [hgcoe, h0, EReal.coe_zero])
    rw [(mul_eq_zero.mp (hcompl i)).resolve_right hne, zero_smul]
  have hdec : ((s, 0) : E m × E n) = u1 + ((u5 + u6) + u4) := by rw [hsu, hu2s, hu3s]
  refine ⟨u1, hu1, lam, μ, w, u4.2, hν, fun i _ => ⟨hμ0 i, (hw i).1⟩, ?_, ?_⟩
  · have h1 := congrArg Prod.fst hdec
    rw [hsumω, hlam] at h1
    simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, hu41] at h1
    exact h1.trans (by abel)
  · have h2 := congrArg Prod.snd hdec
    rw [hsumω, hlam] at h2
    simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd] at h2
    exact h2.trans (by abel)

end Hard

end RiskAverseSDDP.Subdiff.Aux

open RiskAverseSDDP.Subdiff RiskAverseSDDP.Subdiff.ConvexProgram in
theorem solution {m n q p : ℕ} (P : ConvexProgram m n q p) (X : Set (E m))
    (hX : X.Nonempty ∧ IsCompact X ∧ Convex ℝ X)
    (hY : P.Y.Nonempty ∧ IsCompact P.Y ∧ Convex ℝ P.Y)
    (hH : P.AssumptionH X)
    (hR1 : ∀ i z, P.g i z ≠ ⊤)
    (hSlater : P.RepairedSlater X)
    (x₀ : E m) (hx₀ : x₀ ∈ X) (hS : (P.S x₀).Nonempty) :
    (P.Sol x₀).Nonempty ∧ ∀ y₀ ∈ P.Sol x₀, ∀ s : E m,
      s ∈ subdiff P.Q x₀ ↔
        ∃ u ∈ subdiffProd P.f (x₀, y₀), ∃ lam : E q, ∃ μ : Fin p → ℝ,
          ∃ w : Fin p → E m × E n, ∃ ν ∈ FirstOrderOpt.ConvexTheory.normalCone P.Y y₀,
            (∀ i ∈ P.active x₀ y₀, 0 ≤ μ i ∧ w i ∈ subdiffProd (P.g i) (x₀, y₀)) ∧
            s = u.1 + Matrix.toEuclideanLin P.A.transpose lam + ∑ i ∈ P.active x₀ y₀, μ i • (w i).1 ∧
            (0 : E n) = u.2 + Matrix.toEuclideanLin P.B.transpose lam +
              ∑ i ∈ P.active x₀ y₀, μ i • (w i).2 + ν := by
  refine ⟨Aux.sol_nonempty P X hY hH x₀ hS, fun y₀ hy₀ s =>
    ⟨fun hs => Aux.hard_dir P X hY hH hR1 hSlater x₀ y₀ hy₀ s hs, ?_⟩⟩
  rintro ⟨u, hu, lam, μ, w, ν, hν, hμw, hs, h0⟩
  exact Aux.easy_dir P x₀ y₀ hy₀ (hH.1.2.1.1 _) s u hu lam μ w ν hν hμw hs h0
