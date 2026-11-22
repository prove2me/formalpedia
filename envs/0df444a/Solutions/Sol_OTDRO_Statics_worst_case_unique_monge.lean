-- Prove2me | solution 1 for OTDRO.Statics.worst_case_unique_monge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:23:25.48127+00:00
-- url     : https://prove2.me/submissions/32938815-0920-4062-bad0-71d8bca3a374

import Mathlib
import Definitions.Def_OTDRO_Statics_Assumptions
import Definitions.Def_OTDRO_Statics_Transport
import Theorems.Thm_OTDRO_StrongCvx_F_strongly_concave
import Theorems.Thm_OTDRO_WorstCase_worst_case_randomized_monge
import Theorems.Thm_OTDRO_WorstCase_dual_lambda_derivatives
import Theorems.Thm_OTDRO_Dual_dual_reformulation
import Theorems.Thm_OTDRO_Dual_sup_transport_eq_ellRob
import Theorems.Thm_OTDRO_Dual_inf_quad_hyperplane

open MeasureTheory Matrix

section Helpers

private lemma ell_quadratic_bounds {d : ℕ}
    {P0 : Measure (EuclideanSpace ℝ (Fin d))} {ℓ : ℝ → ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))} {M : ℝ}
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M) (u : ℝ) :
    ℓ 0 + deriv ℓ 0 * u ≤ ℓ u ∧ ℓ u ≤ ℓ 0 + deriv ℓ 0 * u + (M / 2) * u ^ 2 := by
  constructor
  · -- Lower bound by convexity and differentiability of ℓ
    let g₁ : ℝ → ℝ := fun t => ℓ t - ℓ 0 - deriv ℓ 0 * t
    have hg₁_deriv : ∀ t, HasDerivAt g₁ (deriv ℓ t - deriv ℓ 0) t := by
      intro t
      have hℓt := (h3.differentiable t).hasDerivAt
      have h1 : HasDerivAt (fun s => ℓ s - ℓ 0) (deriv ℓ t) t := hℓt.sub_const (ℓ 0)
      have h2' : HasDerivAt (fun s => deriv ℓ 0 * s) (deriv ℓ 0) t := by
        simpa using (hasDerivAt_id t).const_mul (deriv ℓ 0)
      exact h1.sub h2'
    have hmono_deriv : Monotone (deriv ℓ) := by
      intro a b hab
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact le_rfl
      · have hda := (h3.differentiable a).hasDerivAt
        have hdb := (h3.differentiable b).hasDerivAt
        have hslope_le : deriv ℓ a ≤ (ℓ b - ℓ a) / (b - a) := by
          have := h2.convex.le_slope_of_hasDerivWithinAt
            (Set.mem_univ a) (Set.mem_univ b) hlt hda.hasDerivWithinAt
          simpa [slope_def_field] using this
        have hle_slope : (ℓ b - ℓ a) / (b - a) ≤ deriv ℓ b := by
          have := h2.convex.slope_le_of_hasDerivWithinAt
            (Set.mem_univ a) (Set.mem_univ b) hlt hdb.hasDerivWithinAt
          simpa [slope_def_field] using this
        exact hslope_le.trans hle_slope
    have hg₁0 : g₁ 0 = 0 := by simp [g₁]
    have hg₁_cont : Continuous g₁ :=
      continuous_iff_continuousAt.mpr fun t => (hg₁_deriv t).differentiableAt.continuousAt
    have hnonneg : 0 ≤ g₁ u := by
      rcases le_total 0 u with hu | hu
      · have hmono : MonotoneOn g₁ (Set.Ici 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hg₁_cont.continuousOn
          · exact fun t _ => (hg₁_deriv t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [(hg₁_deriv t).deriv]
            have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
            exact sub_nonneg.mpr (hmono_deriv ht0)
        rw [← hg₁0]
        exact hmono (Set.mem_Ici.mpr le_rfl) hu hu
      · have hanti : AntitoneOn g₁ (Set.Iic 0) := by
          apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hg₁_cont.continuousOn
          · exact fun t _ => (hg₁_deriv t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [(hg₁_deriv t).deriv]
            have ht0 : t ≤ 0 := le_of_lt (by simpa [interior_Iic] using ht)
            exact sub_nonpos.mpr (hmono_deriv ht0)
        rw [← hg₁0]
        exact hanti hu (Set.mem_Iic.mpr le_rfl) hu
    dsimp [g₁] at hnonneg
    linarith
  · -- Upper bound from ℓ'' ≤ M
    let g₂ : ℝ → ℝ := fun t => ℓ 0 + deriv ℓ 0 * t + (M / 2) * t ^ 2 - ℓ t
    have hg₂_deriv : ∀ t, HasDerivAt g₂ (deriv ℓ 0 + M * t - deriv ℓ t) t := by
      intro t
      have hℓt := (h3.differentiable t).hasDerivAt
      have hlin : HasDerivAt (fun s => ℓ 0 + deriv ℓ 0 * s) (deriv ℓ 0) t := by
        simpa using ((hasDerivAt_id t).const_mul (deriv ℓ 0)).const_add (ℓ 0)
      have hquad : HasDerivAt (fun s => (M / 2) * s ^ 2) (M * t) t := by
        have hp := (hasDerivAt_pow 2 t).const_mul (M / 2)
        have hmul : M / 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = M * t := by
          simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
          ring
        rwa [hmul] at hp
      exact (hlin.add hquad).sub hℓt
    have hderiv_mono : Monotone (fun t => deriv ℓ 0 + M * t - deriv ℓ t) := by
      apply monotone_of_deriv_nonneg
      · intro t
        exact (((differentiableAt_id.const_mul M).const_add (deriv ℓ 0)).sub
          (h3.deriv_differentiable t))
      · intro t
        have hd : HasDerivAt (fun s => deriv ℓ 0 + M * s - deriv ℓ s)
            (M - deriv (deriv ℓ) t) t := by
          have h1 : HasDerivAt (fun s => deriv ℓ 0 + M * s) M t := by
            simpa using ((hasDerivAt_id t).const_mul M).const_add (deriv ℓ 0)
          exact h1.sub (h3.deriv_differentiable t).hasDerivAt
        rw [hd.deriv]
        linarith [h3.second_deriv_le t]
    have hg₂0 : g₂ 0 = 0 := by simp [g₂]
    have hg₂_cont : Continuous g₂ :=
      continuous_iff_continuousAt.mpr fun t => (hg₂_deriv t).differentiableAt.continuousAt
    have hnonneg : 0 ≤ g₂ u := by
      rcases le_total 0 u with hu | hu
      · have hmono : MonotoneOn g₂ (Set.Ici 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hg₂_cont.continuousOn
          · exact fun t _ => (hg₂_deriv t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [(hg₂_deriv t).deriv]
            have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
            have h0 := hderiv_mono ht0
            simp only [mul_zero, add_zero, sub_self] at h0
            exact h0
        rw [← hg₂0]
        exact hmono (Set.mem_Ici.mpr le_rfl) hu hu
      · have hanti : AntitoneOn g₂ (Set.Iic 0) := by
          apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hg₂_cont.continuousOn
          · exact fun t _ => (hg₂_deriv t).differentiableAt.differentiableWithinAt
          · intro t ht
            rw [(hg₂_deriv t).deriv]
            have ht0 : t ≤ 0 := le_of_lt (by simpa [interior_Iic] using ht)
            have h0 := hderiv_mono ht0
            simp only [mul_zero, add_zero, sub_self] at h0
            exact h0
        rw [← hg₂0]
        exact hanti hu (Set.mem_Iic.mpr le_rfl) hu
    dsimp [g₂] at hnonneg
    linarith

private lemma growthKappa_le_half_M {d : ℕ}
    {P0 : Measure (EuclideanSpace ℝ (Fin d))} {ℓ : ℝ → ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))} {M : ℝ}
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M) :
    OTDRO.Dual.growthKappa ℓ ≤ 1 / 2 * M := by
  unfold OTDRO.Dual.growthKappa
  apply le_of_forall_pos_le_add
  intro ε hε
  have hs_mem : 1 / 2 * M + ε ∈
      {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)} := by
    refine ⟨by linarith [h3.M_pos], ?_⟩
    refine ⟨ℓ 0 + (deriv ℓ 0) ^ 2 / (4 * ε), ?_⟩
    rintro _ ⟨u, rfl⟩
    have hle := (ell_quadratic_bounds h2 h3 u).2
    have hsq : 0 ≤ ε * (u - deriv ℓ 0 / (2 * ε)) ^ 2 := by positivity
    have hcalc : (deriv ℓ 0) ^ 2 / (4 * ε) - (deriv ℓ 0 * u - ε * u ^ 2) =
        ε * (u - deriv ℓ 0 / (2 * ε)) ^ 2 := by
      field_simp
      ring
    linarith
  have hbdd : BddBelow {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)} :=
    ⟨0, fun s hs => hs.1⟩
  exact csInf_le hbdd hs_mem

private lemma quadInv_ae_bounds {d : ℕ}
    {P0 : Measure (EuclideanSpace ℝ (Fin d))}
    {A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {ρmin ρmax : ℝ} (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    {β : EuclideanSpace ℝ (Fin d)} (hβ : β ≠ 0) :
    ∀ᵐ x ∂P0, ‖β‖ ^ 2 / ρmax ≤ OTDRO.Dual.quadInv A β x ∧
      OTDRO.Dual.quadInv A β x ≤ ‖β‖ ^ 2 / ρmin := by
  filter_upwards [hA.eig_bounds] with x heig
  have hPD : (A x).PosDef := hA.posDef x
  have hβ_ofLp : β.ofLp ≠ 0 := by
    intro h0
    apply hβ
    ext i
    exact congrFun h0 i
  have hq_pos : 0 < OTDRO.Dual.quadInv A β x := by
    unfold OTDRO.Dual.quadInv
    simpa [star_trivial] using hPD.inv.dotProduct_mulVec_pos hβ_ofLp
  constructor
  · have hleast := OTDRO.Dual.inf_quad_hyperplane (A x) hPD β hβ (inner ℝ β β)
    have hmem : dotProduct β.ofLp (A x *ᵥ β.ofLp) ∈
        {q : ℝ | ∃ Δ : EuclideanSpace ℝ (Fin d),
          inner ℝ β Δ = inner ℝ β β ∧ q = dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp)} :=
      ⟨β, rfl, rfl⟩
    have hle1 : (inner ℝ β β) ^ 2 / OTDRO.Dual.quadInv A β x ≤
        dotProduct β.ofLp (A x *ᵥ β.ofLp) := hleast.2 hmem
    have hle2 : dotProduct β.ofLp (A x *ᵥ β.ofLp) ≤ ρmax * ‖β‖ ^ 2 := (heig β).2
    have hinner : inner ℝ β β = ‖β‖ ^ 2 := real_inner_self_eq_norm_sq β
    rw [hinner] at hle1
    have hle3 : (‖β‖ ^ 2) ^ 2 / OTDRO.Dual.quadInv A β x ≤ ρmax * ‖β‖ ^ 2 := hle1.trans hle2
    have hβ2_pos : 0 < ‖β‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hβ)
    rw [div_le_iff₀ hq_pos] at hle3
    rw [div_le_iff₀ hA.rhoMax_pos]
    nlinarith
  · let w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)
    have hAw : A x *ᵥ w.ofLp = β.ofLp := by
      change A x *ᵥ ((A x)⁻¹ *ᵥ β.ofLp) = β.ofLp
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit),
        Matrix.one_mulVec]
    have hwAw : dotProduct w.ofLp (A x *ᵥ w.ofLp) = OTDRO.Dual.quadInv A β x := by
      rw [hAw, dotProduct_comm]
      rfl
    have hw_inner : inner ℝ β w = OTDRO.Dual.quadInv A β x := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [w, OTDRO.Dual.quadInv, dotProduct_comm]
    have hcs : OTDRO.Dual.quadInv A β x ≤ ‖β‖ * ‖w‖ := by
      rw [← hw_inner]
      exact real_inner_le_norm β w
    have hlow : ρmin * ‖w‖ ^ 2 ≤ OTDRO.Dual.quadInv A β x := by
      rw [← hwAw]
      exact (heig w).1
    have hw_bound : ‖w‖ ≤ ‖β‖ / ρmin := by
      rw [le_div_iff₀ hA.rhoMin_pos]
      by_cases hw0 : ‖w‖ = 0
      · rw [hw0, zero_mul]
        exact norm_nonneg β
      · have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw0)
        nlinarith
    calc OTDRO.Dual.quadInv A β x ≤ ‖β‖ * ‖w‖ := hcs
      _ ≤ ‖β‖ * (‖β‖ / ρmin) := mul_le_mul_of_nonneg_left hw_bound (norm_nonneg β)
      _ = ‖β‖ ^ 2 / ρmin := by ring

private lemma essSup_quadInv_pos {d : ℕ}
    {P0 : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P0]
    {A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {ρmin ρmax : ℝ} (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    {β : EuclideanSpace ℝ (Fin d)} (hβ : β ≠ 0) :
    0 < essSup (fun x => OTDRO.Dual.quadInv A β x) P0 := by
  have hbounds := quadInv_ae_bounds hA hβ
  have hc_pos : 0 < ‖β‖ ^ 2 / ρmax := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hβ)) hA.rhoMax_pos
  have hle : ‖β‖ ^ 2 / ρmax ≤ essSup (fun x => OTDRO.Dual.quadInv A β x) P0 := by
    have hconst : essSup (fun _ : EuclideanSpace ℝ (Fin d) => ‖β‖ ^ 2 / ρmax) P0 =
        ‖β‖ ^ 2 / ρmax := essSup_const' (‖β‖ ^ 2 / ρmax)
    rw [← hconst]
    apply essSup_mono_ae
    · exact hbounds.mono fun _ hx => hx.1
    · exact Filter.isCoboundedUnder_le_of_le _ fun _ => le_rfl
    · exact ⟨‖β‖ ^ 2 / ρmin, Filter.eventually_map.mpr (hbounds.mono fun _ hx => hx.2)⟩
  exact lt_of_lt_of_le hc_pos hle

private lemma measurable_det_of_entries {α : Type*} [MeasurableSpace α] {d : ℕ}
    {M : α → Matrix (Fin d) (Fin d) ℝ}
    (hM : ∀ i j : Fin d, Measurable (fun x => M x i j)) :
    Measurable (fun x => (M x).det) := by
  have heq : (fun x => (M x).det) =
      fun x => ∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℝ) * ∏ i : Fin d, M x (σ i) i := by
    ext x
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Units.smul_def, zsmul_eq_mul]
  rw [heq]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hM (σ i) i)

private lemma measurable_A_and_invDir {d : ℕ}
    {P0 : Measure (EuclideanSpace ℝ (Fin d))}
    {A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {ρmin ρmax : ℝ} (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (β : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun x => WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)) ∧
      Measurable (fun x => OTDRO.Dual.quadInv A β x) := by
  have hquad_meas : ∀ v : EuclideanSpace ℝ (Fin d),
      Measurable (fun x => dotProduct v.ofLp (A x *ᵥ v.ofLp)) := by
    intro v
    have hlsc : LowerSemicontinuous (fun x => dotProduct v.ofLp (A x *ᵥ v.ofLp)) := by
      have hsub : Continuous (fun x : EuclideanSpace ℝ (Fin d) => x - v) :=
        continuous_id.sub continuous_const
      have hcomp := hA.lsc.comp (Continuous.prodMk continuous_id hsub)
      convert hcomp using 1
      ext x
      simp [OTDRO.Dual.mahalCost]
    exact hlsc.measurable
  have hA_entry : ∀ i j : Fin d, Measurable (fun x => A x i j) := by
    intro i j
    let ei : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
    let ej : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single j 1
    have hpol : (fun x => A x i j) = fun x =>
        (dotProduct (ei + ej).ofLp (A x *ᵥ (ei + ej).ofLp) -
          dotProduct ei.ofLp (A x *ᵥ ei.ofLp) -
          dotProduct ej.ofLp (A x *ᵥ ej.ofLp)) / 2 := by
      ext x
      have hsym : A x j i = A x i j := by
        have hh := (hA.posDef x).isHermitian
        have h := congrFun (congrFun hh i) j
        simpa [Matrix.conjTranspose_apply, star_trivial] using h
      have h1 : dotProduct ei.ofLp (A x *ᵥ ei.ofLp) = A x i i := by
        simp [ei, dotProduct, Matrix.mulVec]
      have h2 : dotProduct ej.ofLp (A x *ᵥ ej.ofLp) = A x j j := by
        simp [ej, dotProduct, Matrix.mulVec]
      have h3 : dotProduct (ei + ej).ofLp (A x *ᵥ (ei + ej).ofLp) =
          A x i i + A x i j + A x j i + A x j j := by
        have hadd : (ei + ej).ofLp = ei.ofLp + ej.ofLp := rfl
        rw [hadd, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
        have hij : dotProduct ei.ofLp (A x *ᵥ ej.ofLp) = A x i j := by
          simp [ei, ej, dotProduct, Matrix.mulVec]
        have hji : dotProduct ej.ofLp (A x *ᵥ ei.ofLp) = A x j i := by
          simp [ei, ej, dotProduct, Matrix.mulVec]
        rw [h1, h2, hij, hji]
        ring
      rw [h1, h2, h3, hsym]
      ring
    rw [hpol]
    exact (((hquad_meas (ei + ej)).sub (hquad_meas ei)).sub (hquad_meas ej)).div_const 2
  have hdet : Measurable (fun x => (A x).det⁻¹) :=
    (measurable_det_of_entries hA_entry).inv
  have hcram : Measurable (fun x => (A x).cramer β.ofLp) := by
    rw [measurable_pi_iff]
    intro j
    have heq : (fun x => (A x).cramer β.ofLp j) =
        fun x => ((A x).updateCol j β.ofLp).det := by
      ext x
      exact Matrix.cramer_apply (A x) β.ofLp j
    rw [heq]
    apply measurable_det_of_entries
    intro r c
    by_cases hcj : c = j
    · subst hcj
      simp [Matrix.updateCol_self]
    · simpa [Matrix.updateCol_ne hcj] using hA_entry r c
  have hinv_vec : Measurable (fun x => (A x)⁻¹ *ᵥ β.ofLp) := by
    have heq : (fun x => (A x)⁻¹ *ᵥ β.ofLp) =
        fun x => (A x).det⁻¹ • (A x).cramer β.ofLp := by
      ext x
      rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, Matrix.cramer_eq_adjugate_mulVec]
    rw [heq]
    exact hdet.smul hcram
  have hinvDir : Measurable (fun x => WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)) :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp hinv_vec
  have hquadInv : Measurable (fun x => OTDRO.Dual.quadInv A β x) := by
    unfold OTDRO.Dual.quadInv
    have hcont : Continuous (fun v : Fin d → ℝ => dotProduct β.ofLp v) :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
    exact hcont.measurable.comp hinv_vec
  exact ⟨hinvDir, hquadInv⟩

private lemma integrable_ell_inner {d : ℕ}
    {P0 : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P0]
    {ℓ : ℝ → ℝ} {B : Set (EuclideanSpace ℝ (Fin d))} {M : ℝ}
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (β : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x => ℓ (inner ℝ β x)) P0 := by
  have hcont : Continuous (fun x => ℓ (inner ℝ β x)) :=
    h3.differentiable.continuous.comp (continuous_const.inner continuous_id)
  let C1 : ℝ := |ℓ 0| + |deriv ℓ 0| + (|deriv ℓ 0| + M / 2) * ‖β‖ ^ 2
  let C2 : ℝ := (|deriv ℓ 0| + M / 2) * ‖β‖ ^ 2
  have hdom : Integrable (fun x => C1 + C2 * ‖x‖ ^ 4) P0 :=
    (integrable_const C1).add (h2.moment4.const_mul C2)
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hb := ell_quadratic_bounds h2 h3 (inner ℝ β x)
  have hM0 : 0 ≤ M / 2 := by linarith [h3.M_pos]
  have habs : |ℓ (inner ℝ β x)| ≤
      |ℓ 0| + |deriv ℓ 0| * |inner ℝ β x| + (M / 2) * (inner ℝ β x) ^ 2 := by
    rw [abs_le]
    have h1 : -(|ℓ 0| + |deriv ℓ 0| * |inner ℝ β x|) ≤ ℓ 0 + deriv ℓ 0 * inner ℝ β x := by
      have := neg_abs_le (ℓ 0)
      have := neg_abs_le (deriv ℓ 0 * inner ℝ β x)
      rw [abs_mul] at this
      linarith
    have h2' : ℓ 0 + deriv ℓ 0 * inner ℝ β x ≤ |ℓ 0| + |deriv ℓ 0| * |inner ℝ β x| := by
      have := le_abs_self (ℓ 0)
      have := le_abs_self (deriv ℓ 0 * inner ℝ β x)
      rw [abs_mul] at this
      linarith
    have hsq : 0 ≤ (M / 2) * (inner ℝ β x) ^ 2 := by positivity
    constructor <;> linarith
  have hcs : |inner ℝ β x| ≤ ‖β‖ * ‖x‖ := abs_real_inner_le_norm β x
  have hsq1 : |inner ℝ β x| ≤ 1 + (inner ℝ β x) ^ 2 := by
    nlinarith [sq_nonneg (|inner ℝ β x| - 1), sq_abs (inner ℝ β x)]
  have hsq2 : (inner ℝ β x) ^ 2 ≤ ‖β‖ ^ 2 * ‖x‖ ^ 2 := by
    have h1 := mul_self_le_mul_self (abs_nonneg _) hcs
    nlinarith [sq_abs (inner ℝ β x)]
  have hsq3 : ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 4 := by
    nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]
  rw [Real.norm_eq_abs]
  have hd0 : 0 ≤ |deriv ℓ 0| := abs_nonneg _
  have hβ0 : 0 ≤ ‖β‖ ^ 2 := sq_nonneg _
  have hcoef : 0 ≤ |deriv ℓ 0| + M / 2 := add_nonneg hd0 hM0
  calc |ℓ (inner ℝ β x)|
      ≤ |ℓ 0| + |deriv ℓ 0| * |inner ℝ β x| + (M / 2) * (inner ℝ β x) ^ 2 := habs
    _ ≤ |ℓ 0| + |deriv ℓ 0| * (1 + (inner ℝ β x) ^ 2) + (M / 2) * (inner ℝ β x) ^ 2 := by
        nlinarith
    _ = |ℓ 0| + |deriv ℓ 0| + (|deriv ℓ 0| + M / 2) * (inner ℝ β x) ^ 2 := by ring
    _ ≤ |ℓ 0| + |deriv ℓ 0| + (|deriv ℓ 0| + M / 2) * (‖β‖ ^ 2 * ‖x‖ ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq2 hcoef)
    _ ≤ |ℓ 0| + |deriv ℓ 0| + (|deriv ℓ 0| + M / 2) * (‖β‖ ^ 2 * (1 + ‖x‖ ^ 4)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq3 hβ0) hcoef)
    _ = C1 + C2 * ‖x‖ ^ 4 := by dsimp [C1, C2]; ring

private lemma integrable_of_extIntegral_ne_top_ne_bot {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : Measurable g)
    (htop : ModelRiskOT.Duality.extIntegral μ (fun x => (g x : EReal)) ≠ ⊤)
    (hbot : ModelRiskOT.Duality.extIntegral μ (fun x => (g x : EReal)) ≠ ⊥) :
    Integrable g μ ∧
      ModelRiskOT.Duality.extIntegral μ (fun x => (g x : EReal)) = ((∫ x, g x ∂μ : ℝ) : EReal) := by
  unfold ModelRiskOT.Duality.extIntegral at htop hbot ⊢
  set a : ENNReal := ∫⁻ x, ((g x : EReal)).toENNReal ∂μ
  set b : ENNReal := ∫⁻ x, (-(g x : EReal)).toENNReal ∂μ
  have ha_eq : a = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
    apply lintegral_congr
    intro x
    simp
  have hb_eq : b = ∫⁻ x, ENNReal.ofReal (-g x) ∂μ := by
    apply lintegral_congr
    intro x
    rw [← EReal.coe_neg]
    simp
  have hb_lt : b < ⊤ := by
    by_contra hb_top
    rw [not_lt, top_le_iff] at hb_top
    apply hbot
    rw [hb_top]
    simp [sub_eq_add_neg]
  have ha_lt : a < ⊤ := by
    by_contra ha_top
    rw [not_lt, top_le_iff] at ha_top
    apply htop
    rw [ha_top]
    have hb_ne : (b : EReal) ≠ ⊤ := by
      simpa using hb_lt.ne
    rw [sub_eq_add_neg]
    exact EReal.top_add_of_ne_bot (by simpa [EReal.neg_eq_bot_iff] using hb_ne)
  have hfin : HasFiniteIntegral g μ := by
    change ∫⁻ x, ‖g x‖ₑ ∂μ < ⊤
    have hle : ∀ x, ‖g x‖ₑ ≤ ENNReal.ofReal (g x) + ENNReal.ofReal (-g x) := by
      intro x
      rw [Real.enorm_eq_ofReal_abs]
      rcases le_total 0 (g x) with hx | hx
      · rw [abs_of_nonneg hx, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hx), add_zero]
      · rw [abs_of_nonpos hx, ENNReal.ofReal_eq_zero.mpr hx, zero_add]
    calc ∫⁻ x, ‖g x‖ₑ ∂μ
        ≤ ∫⁻ x, (ENNReal.ofReal (g x) + ENNReal.ofReal (-g x)) ∂μ :=
          lintegral_mono hle
      _ = (∫⁻ x, ENNReal.ofReal (g x) ∂μ) + (∫⁻ x, ENNReal.ofReal (-g x) ∂μ) :=
          lintegral_add_left (hg.ennreal_ofReal) _
      _ = a + b := by rw [ha_eq, hb_eq]
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ha_lt, hb_lt⟩
  have hint : Integrable g μ := ⟨hg.aestronglyMeasurable, hfin⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint, ← ha_eq, ← hb_eq, EReal.coe_sub]
  have hcoe : ∀ z : ENNReal, z ≠ ⊤ → ((z.toReal : ℝ) : EReal) = (z : EReal) := by
    intro z hz
    calc ((z.toReal : ℝ) : EReal)
        = ((max z.toReal 0 : ℝ) : EReal) := by rw [max_eq_left ENNReal.toReal_nonneg]
      _ = ((ENNReal.ofReal z.toReal : ENNReal) : EReal) := EReal.coe_ennreal_ofReal.symm
      _ = (z : EReal) := by rw [ENNReal.ofReal_toReal hz]
  rw [hcoe a ha_lt.ne, hcoe b hb_lt.ne]

private lemma unique_pointwise_shift {d : ℕ}
    {A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {ℓ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    {β : EuclideanSpace ℝ (Fin d)} (hβ : β ≠ 0)
    {lamStar : ℝ} (hlam : 0 < lamStar)
    {x y : EuclideanSpace ℝ (Fin d)} {g : ℝ}
    (hPD : (A x).PosDef)
    (hmax : OTDRO.Dual.maximizers ℓ A δ β lamStar x = {g})
    (heq : ℓ (inner ℝ β y) - (lamStar / Real.sqrt δ) * (OTDRO.Dual.mahalCost A x y - δ) =
      OTDRO.Dual.Fobj ℓ A δ g β lamStar x) :
    y = x + (Real.sqrt δ * g) • WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp) := by
  have hsqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hβ_ofLp : β.ofLp ≠ 0 := by
    intro h0
    apply hβ
    ext i
    exact congrFun h0 i
  have hq_pos : 0 < OTDRO.Dual.quadInv A β x := by
    unfold OTDRO.Dual.quadInv
    simpa [star_trivial] using hPD.inv.dotProduct_mulVec_pos hβ_ofLp
  let Δ : EuclideanSpace ℝ (Fin d) := y - x
  let q : ℝ := OTDRO.Dual.quadInv A β x
  let γ : ℝ := inner ℝ β Δ / (Real.sqrt δ * q)
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)
  let Δ0 : EuclideanSpace ℝ (Fin d) := (Real.sqrt δ * γ) • v
  let u : EuclideanSpace ℝ (Fin d) := Δ - Δ0
  have hAv : A x *ᵥ v.ofLp = β.ofLp := by
    change A x *ᵥ ((A x)⁻¹ *ᵥ β.ofLp) = β.ofLp
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit),
      Matrix.one_mulVec]
  have hinner_βv : inner ℝ β v = q := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [v, q, OTDRO.Dual.quadInv, dotProduct_comm]
  have hinner_βΔ : inner ℝ β Δ = γ * Real.sqrt δ * q := by
    have hq_ne : q ≠ 0 := hq_pos.ne'
    dsimp [γ]
    field_simp [hsqrt_pos.ne', hq_ne]
  have hinner_βΔ0 : inner ℝ β Δ0 = inner ℝ β Δ := by
    dsimp [Δ0]
    rw [inner_smul_right, hinner_βv, hinner_βΔ]
    ring
  have hinner_βu : inner ℝ β u = 0 := by
    dsimp [u]
    rw [inner_sub_right, hinner_βΔ0, sub_self]
  have hAΔ0 : A x *ᵥ Δ0.ofLp = (Real.sqrt δ * γ) • β.ofLp := by
    have hof : Δ0.ofLp = (Real.sqrt δ * γ) • v.ofLp := rfl
    rw [hof, Matrix.mulVec_smul, hAv]
  have huAΔ0 : dotProduct u.ofLp (A x *ᵥ Δ0.ofLp) = 0 := by
    rw [hAΔ0, dotProduct_smul, smul_eq_mul]
    have hdot : dotProduct u.ofLp β.ofLp = inner ℝ β u := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct_comm]
    rw [hdot, hinner_βu, mul_zero]
  have hΔ0Au : dotProduct Δ0.ofLp (A x *ᵥ u.ofLp) = 0 := by
    have hsym : (A x)ᵀ = A x := by
      have hh : (A x).IsSymm := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hPD.isHermitian
      exact hh.eq
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm, huAΔ0]
  have hΔ0AΔ0 : dotProduct Δ0.ofLp (A x *ᵥ Δ0.ofLp) = δ * γ ^ 2 * q := by
    have hof : Δ0.ofLp = (Real.sqrt δ * γ) • v.ofLp := rfl
    rw [hAΔ0, hof, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hdot : dotProduct v.ofLp β.ofLp = q := by
      rw [dotProduct_comm]
      rfl
    rw [hdot]
    calc Real.sqrt δ * γ * (Real.sqrt δ * γ * q)
        = (Real.sqrt δ * Real.sqrt δ) * γ ^ 2 * q := by ring
      _ = δ * γ ^ 2 * q := by rw [Real.mul_self_sqrt hδ.le]
  have hcost : OTDRO.Dual.mahalCost A x y = δ * γ ^ 2 * q + dotProduct u.ofLp (A x *ᵥ u.ofLp) := by
    unfold OTDRO.Dual.mahalCost
    have hneg : (x - y).ofLp = -Δ.ofLp := by
      ext i
      change x i - y i = -(y i - x i)
      ring
    rw [hneg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    have hsplit : Δ.ofLp = Δ0.ofLp + u.ofLp := by
      ext i
      change Δ i = Δ0 i + (Δ i - Δ0 i)
      ring
    rw [hsplit, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      hΔ0AΔ0, hΔ0Au, huAΔ0]
    ring
  have hinner_y : inner ℝ β y = inner ℝ β x + γ * Real.sqrt δ * q := by
    have hy : y = x + Δ := by dsimp [Δ]; abel
    rw [hy, inner_add_right, hinner_βΔ]
  have hF_decomp :
      ℓ (inner ℝ β y) - (lamStar / Real.sqrt δ) * (OTDRO.Dual.mahalCost A x y - δ) =
        OTDRO.Dual.Fobj ℓ A δ γ β lamStar x -
          (lamStar / Real.sqrt δ) * dotProduct u.ofLp (A x *ᵥ u.ofLp) := by
    rw [hinner_y, hcost]
    unfold OTDRO.Dual.Fobj
    have hsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ.le
    have hdiv : lamStar / Real.sqrt δ * (δ * γ ^ 2 * q - δ) =
        lamStar * Real.sqrt δ * (γ ^ 2 * q - 1) := by
      have h1 : δ * γ ^ 2 * q - δ = (Real.sqrt δ * Real.sqrt δ) * (γ ^ 2 * q - 1) := by
        rw [hsq]; ring
      rw [h1]
      field_simp [hsqrt_pos.ne']
    dsimp [q]
    linarith
  have hg_mem : g ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x := by
    rw [hmax]
    exact Set.mem_singleton g
  have hF_le : OTDRO.Dual.Fobj ℓ A δ γ β lamStar x ≤ OTDRO.Dual.Fobj ℓ A δ g β lamStar x :=
    hg_mem γ
  have huAu_nonneg : 0 ≤ dotProduct u.ofLp (A x *ᵥ u.ofLp) := by
    simpa [star_trivial] using hPD.posSemidef.dotProduct_mulVec_nonneg u.ofLp
  have hlam'_pos : 0 < lamStar / Real.sqrt δ := div_pos hlam hsqrt_pos
  have huAu_zero : dotProduct u.ofLp (A x *ᵥ u.ofLp) = 0 := by
    nlinarith
  have hu_zero : u = 0 := by
    by_contra hu_ne
    have hu_ofLp : u.ofLp ≠ 0 := by
      intro h0
      apply hu_ne
      ext i
      exact congrFun h0 i
    have hpos := hPD.dotProduct_mulVec_pos hu_ofLp
    simp only [star_trivial] at hpos
    linarith
  have hF_eq : OTDRO.Dual.Fobj ℓ A δ γ β lamStar x = OTDRO.Dual.Fobj ℓ A δ g β lamStar x := by
    nlinarith
  have hγ_mem : γ ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x := by
    intro c
    rw [hF_eq]
    exact hg_mem c
  have hγ_eq : γ = g := by
    rw [hmax, Set.mem_singleton_iff] at hγ_mem
    exact hγ_mem
  have hΔ_eq : Δ = Δ0 := sub_eq_zero.mp hu_zero
  calc y = x + Δ := by dsimp [Δ]; abel
    _ = x + Δ0 := by rw [hΔ_eq]
    _ = x + (Real.sqrt δ * g) • WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp) := by
        dsimp [Δ0, v]
        rw [hγ_eq]

end Helpers

theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lamStar : ℝ) (hlam : 0 ≤ lamStar)
    (hmin : IsMinOn (fun lam => OTDRO.Dual.fDelta P0 ℓ A δ β lam) (Set.Ici 0) lamStar)
    (hthr : OTDRO.Dual.lamThr' P0 A M δ β < lamStar) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ,
      AEMeasurable G P0 ∧
      AEMeasurable (OTDRO.Statics.shiftMap A δ β G) P0 ∧
      (∀ᵐ x ∂P0, OTDRO.Dual.maximizers ℓ A δ β lamStar x = {G x}) ∧
      OTDRO.WorstCase.graphCoupling P0 (OTDRO.Statics.shiftMap A δ β G) ∈
        ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ ∧
      ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x))
        (OTDRO.WorstCase.graphCoupling P0 (OTDRO.Statics.shiftMap A δ β G)) =
        ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
          (fun x => ℓ (inner ℝ β x)) P0 δ ∧
      (∀ π ∈ ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ,
        ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π =
          ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
            (fun x => ℓ (inner ℝ β x)) P0 δ →
        π.map Prod.snd = P0.map (OTDRO.Statics.shiftMap A δ β G)) ∧
      (∫⁻ p, ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2)
          ∂(OTDRO.WorstCase.graphCoupling P0 (OTDRO.Statics.shiftMap A δ β G))) = ENNReal.ofReal δ := by
  -- Step 1: Threshold comparison lamThr ≤ lamThr' < lamStar and 0 < lamStar
  have hess_pos : 0 < essSup (fun x => OTDRO.Dual.quadInv A β x) P0 := essSup_quadInv_pos hA hβ
  have hsqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hthr'_pos : 0 < OTDRO.Dual.lamThr' P0 A M δ β := by
    unfold OTDRO.Dual.lamThr'
    have hM := h3.M_pos
    positivity
  have hlam_pos : 0 < lamStar := lt_trans hthr'_pos hthr
  have hthr_le : OTDRO.Dual.lamThr P0 ℓ A δ β ≤ OTDRO.Dual.lamThr' P0 A M δ β := by
    unfold OTDRO.Dual.lamThr OTDRO.Dual.lamThr'
    have hκ := growthKappa_le_half_M h2 h3
    have hpos : 0 ≤ Real.sqrt δ * essSup (fun x => OTDRO.Dual.quadInv A β x) P0 := by positivity
    calc OTDRO.Dual.growthKappa ℓ * Real.sqrt δ * essSup (fun x => OTDRO.Dual.quadInv A β x) P0
        = OTDRO.Dual.growthKappa ℓ * (Real.sqrt δ * essSup (fun x => OTDRO.Dual.quadInv A β x) P0) := by ring
      _ ≤ (1 / 2 * M) * (Real.sqrt δ * essSup (fun x => OTDRO.Dual.quadInv A β x) P0) :=
          mul_le_mul_of_nonneg_right hκ hpos
      _ = 1 / 2 * M * Real.sqrt δ * essSup (fun x => OTDRO.Dual.quadInv A β x) P0 := by ring
  have hthr_kappa : OTDRO.Dual.lamThr P0 ℓ A δ β < lamStar := lt_of_le_of_lt hthr_le hthr

  -- Step 2: Almost-sure singleton maximizer from Lemma 8 (F_strongly_concave)
  have hstrong := OTDRO.StrongCvx.F_strongly_concave P0 A ρmin ρmax hA ℓ h2 δ hδ B hB M h3
  have hsingleton_ae : ∀ᵐ x ∂P0, ∃ γ : ℝ, OTDRO.Dual.maximizers ℓ A δ β lamStar x = {γ} :=
    hstrong.mono fun x hx => by
      rcases hx β hβB hβ lamStar hthr with ⟨_, _, _, huniq, _⟩
      exact huniq

  -- Step 3: Existence of optimal randomized Monge plan from Theorem 6(c)
  obtain ⟨Gminus, Gplus, hGm_meas, _hGp_meas, hG_max, _hint_m, _hint_p,
      hq0, hq1, hmix_feas, hmix_opt, hmix_cost⟩ :=
    OTDRO.WorstCase.worst_case_randomized_monge P0 A ρmin ρmax hA ℓ h2 δ hδ B hB β hβB hβ
      lamStar hlam hmin hthr_kappa

  -- Choose a genuinely measurable representative G = hGm_meas.mk Gminus
  let G : EuclideanSpace ℝ (Fin d) → ℝ := hGm_meas.mk Gminus
  have hG_meas : Measurable G := hGm_meas.measurable_mk
  have hGm_eq : Gminus =ᵐ[P0] G := hGm_meas.ae_eq_mk
  have hG_singleton : ∀ᵐ x ∂P0, OTDRO.Dual.maximizers ℓ A δ β lamStar x = {G x} := by
    filter_upwards [hsingleton_ae, hG_max, hGm_eq] with x ⟨γ, hγ⟩ hmem hmeq
    have hGm_in : Gminus x ∈ ({γ} : Set ℝ) := by rw [← hγ]; exact hmem.1
    have hEq : Gminus x = γ := Set.mem_singleton_iff.mp hGm_in
    rw [hγ, ← hEq, hmeq]
  have hGp_eq : Gplus =ᵐ[P0] G := by
    filter_upwards [hG_singleton, hG_max] with x hx hmem
    have hGp_in : Gplus x ∈ ({G x} : Set ℝ) := by rw [← hx]; exact hmem.2.1
    exact Set.mem_singleton_iff.mp hGp_in

  -- Step 4: Measurability of invDir, quadInv, and shiftMap A δ β G
  obtain ⟨hinvDir_meas, hquadInv_meas⟩ := measurable_A_and_invDir hA β
  have hT_meas : Measurable (OTDRO.Statics.shiftMap A δ β G) := by
    unfold OTDRO.Statics.shiftMap
    exact measurable_id.add ((measurable_const.mul hG_meas).smul hinvDir_meas)

  -- Step 5: Mixture coupling collapses to the deterministic graph coupling
  have hgraph_m : OTDRO.WorstCase.graphCoupling P0 (OTDRO.WorstCase.shiftMap A δ β Gminus) =
      OTDRO.WorstCase.graphCoupling P0 (OTDRO.Statics.shiftMap A δ β G) := by
    unfold OTDRO.WorstCase.graphCoupling
    apply Measure.map_congr
    filter_upwards [hGm_eq] with x hx
    change (x, x + (Real.sqrt δ * Gminus x) • WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)) =
      (x, x + (Real.sqrt δ * G x) • WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp))
    rw [hx]
  have hgraph_p : OTDRO.WorstCase.graphCoupling P0 (OTDRO.WorstCase.shiftMap A δ β Gplus) =
      OTDRO.WorstCase.graphCoupling P0 (OTDRO.Statics.shiftMap A δ β G) := by
    unfold OTDRO.WorstCase.graphCoupling
    apply Measure.map_congr
    filter_upwards [hGp_eq] with x hx
    change (x, x + (Real.sqrt δ * Gplus x) • WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)) =
      (x, x + (Real.sqrt δ * G x) • WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp))
    rw [hx]
  have hmix_eq : OTDRO.WorstCase.mixtureCoupling P0 A δ β Gminus Gplus =
      OTDRO.WorstCase.graphCoupling P0 (OTDRO.Statics.shiftMap A δ β G) := by
    unfold OTDRO.WorstCase.mixtureCoupling
    set q := OTDRO.WorstCase.bernoulliWeight (OTDRO.WorstCase.sqMoment P0 A β Gplus)
      (OTDRO.WorstCase.sqMoment P0 A β Gminus)
    rw [hgraph_m, hgraph_p, ← add_smul, ← ENNReal.ofReal_add hq0 (sub_nonneg.mpr hq1)]
    have h1 : q + (1 - q) = 1 := by ring
    rw [h1, ENNReal.ofReal_one, one_smul]

  rw [hmix_eq] at hmix_feas hmix_opt hmix_cost

  -- Step 6: Uniqueness of the worst-case law for every optimal feasible coupling π
  have hunique : ∀ π ∈ ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ,
      ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π =
        ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
          (fun x => ℓ (inner ℝ β x)) P0 δ →
      π.map Prod.snd = P0.map (OTDRO.Statics.shiftMap A δ β G) := by
    -- Dual value = fDelta at lamStar and is finite
    have hint_ell : Integrable (fun x => ℓ (inner ℝ β x)) P0 := integrable_ell_inner h2 h3 β
    have hdual_eq : ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
        (fun x => ℓ (inner ℝ β x)) P0 δ = OTDRO.Dual.fDelta P0 ℓ A δ β lamStar := by
      have hdr := (OTDRO.Dual.dual_reformulation P0 A ρmin ρmax hA ℓ
        h3.differentiable.continuous.upperSemicontinuous δ hδ B hB β hβB hint_ell).1
      rw [hdr]
      apply le_antisymm
      · exact biInf_le (fun lam => OTDRO.Dual.fDelta P0 ℓ A δ β lam) hlam
      · exact le_iInf₂ fun lam hlam' => hmin hlam'
    have hfin_fDelta := (OTDRO.WorstCase.dual_lambda_derivatives P0 A ρmin ρmax hA ℓ h2 δ hδ
      B hB β hβB hβ).1 lamStar hthr_kappa
    -- Real representative φ(x) = Fobj ℓ A δ (G x) β lamStar x agrees a.e. with ellRob
    let φ : EuclideanSpace ℝ (Fin d) → ℝ := fun x => OTDRO.Dual.Fobj ℓ A δ (G x) β lamStar x
    have hφ_meas : Measurable φ := by
      unfold φ OTDRO.Dual.Fobj
      have h1 : Measurable (fun x => inner ℝ β x + G x * Real.sqrt δ * OTDRO.Dual.quadInv A β x) :=
        (continuous_const.inner continuous_id).measurable.add
          ((hG_meas.mul measurable_const).mul hquadInv_meas)
      have h2' : Measurable (fun x => lamStar * Real.sqrt δ * (G x ^ 2 * OTDRO.Dual.quadInv A β x - 1)) :=
        measurable_const.mul (((hG_meas.pow_const 2).mul hquadInv_meas).sub measurable_const)
      exact (h3.differentiable.continuous.measurable.comp h1).sub h2'
    have hellRob_ae : (fun x => OTDRO.Dual.ellRob ℓ A δ β lamStar x) =ᵐ[P0]
        (fun x => (φ x : EReal)) := by
      filter_upwards [hG_singleton] with x hx
      have hGx : G x ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x := by
        rw [hx]; exact Set.mem_singleton (G x)
      unfold OTDRO.Dual.ellRob φ
      apply le_antisymm
      · exact iSup_le fun c => EReal.coe_le_coe_iff.mpr (hGx c)
      · exact le_iSup (fun c => (OTDRO.Dual.Fobj ℓ A δ c β lamStar x : EReal)) (G x)
    have hfDelta_eq_ext : OTDRO.Dual.fDelta P0 ℓ A δ β lamStar =
        ModelRiskOT.Duality.extIntegral P0 (fun x => (φ x : EReal)) := by
      unfold OTDRO.Dual.fDelta ModelRiskOT.Duality.extIntegral
      have hpos : ∫⁻ x, (OTDRO.Dual.ellRob ℓ A δ β lamStar x).toENNReal ∂P0 =
          ∫⁻ x, ((φ x : EReal)).toENNReal ∂P0 :=
        lintegral_congr_ae (hellRob_ae.mono fun _ hx => by dsimp only at hx ⊢; rw [hx])
      have hneg : ∫⁻ x, (-OTDRO.Dual.ellRob ℓ A δ β lamStar x).toENNReal ∂P0 =
          ∫⁻ x, (-(φ x : EReal)).toENNReal ∂P0 :=
        lintegral_congr_ae (hellRob_ae.mono fun _ hx => by dsimp only at hx ⊢; rw [hx])
      rw [hpos, hneg]
    have hφ_int_and_eq : Integrable φ P0 ∧
        OTDRO.Dual.fDelta P0 ℓ A δ β lamStar = ((∫ x, φ x ∂P0 : ℝ) : EReal) := by
      rw [hfDelta_eq_ext] at hfin_fDelta ⊢
      exact integrable_of_extIntegral_ne_top_ne_bot hφ_meas hfin_fDelta.1 hfin_fDelta.2
    -- Now fix an optimal feasible coupling π
    intro π hπ_feas hπ_opt
    obtain ⟨hπ_prob, hπ_fst, hπ_cost⟩ := hπ_feas
    have : IsProbabilityMeasure π := hπ_prob
    -- Integrability of ℓ(βᵀ p.2) under π and equality of integrals
    have hf_meas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ℓ (inner ℝ β p.2)) :=
      (h3.differentiable.continuous.comp
        ((continuous_const.inner continuous_id).comp continuous_snd)).measurable
    have hπ_obj_fin : ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π ≠ ⊤ ∧
        ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π ≠ ⊥ := by
      rw [hπ_opt, hdual_eq]
      exact hfin_fDelta
    have hf_int_and_eq := integrable_of_extIntegral_ne_top_ne_bot hf_meas hπ_obj_fin.1 hπ_obj_fin.2
    have hint_eq : ∫ p, ℓ (inner ℝ β p.2) ∂π = ∫ x, φ x ∂P0 := by
      have hE : ((∫ p, ℓ (inner ℝ β p.2) ∂π : ℝ) : EReal) = ((∫ x, φ x ∂P0 : ℝ) : EReal) := by
        rw [← hf_int_and_eq.2, ← hφ_int_and_eq.2, ← hdual_eq]
        exact hπ_opt
      exact EReal.coe_eq_coe_iff.mp hE
    -- Integrability of c(p.1, p.2) under π and ∫ c dπ ≤ δ
    have hc_meas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        OTDRO.Dual.mahalCost A p.1 p.2) := hA.lsc.measurable
    have hc_nonneg : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        0 ≤ OTDRO.Dual.mahalCost A p.1 p.2 := by
      intro p
      unfold OTDRO.Dual.mahalCost
      simpa [star_trivial] using (hA.posDef p.1).posSemidef.dotProduct_mulVec_nonneg (p.1 - p.2).ofLp
    have hc_int : Integrable (fun p => OTDRO.Dual.mahalCost A p.1 p.2) π := by
      refine ⟨hc_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hc_nonneg)]
      exact lt_of_le_of_lt hπ_cost ENNReal.ofReal_lt_top
    have hc_int_le : ∫ p, OTDRO.Dual.mahalCost A p.1 p.2 ∂π ≤ δ := by
      have hpos : ∫ p, OTDRO.Dual.mahalCost A p.1 p.2 ∂π =
          (∫⁻ p, ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2) ∂π).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hc_nonneg)
          hc_meas.aestronglyMeasurable
      rw [hpos, ← ENNReal.toReal_ofReal hδ.le]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hπ_cost
    -- Integrability and integral of p ↦ φ p.1 under π
    have hφ1_int : Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        φ p.1) π := by
      have h := hφ_int_and_eq.1
      rw [← hπ_fst] at h
      exact h.comp_measurable measurable_fst
    have hφ1_integral : ∫ p, φ p.1 ∂π = ∫ x, φ x ∂P0 := by
      rw [← hπ_fst, integral_map measurable_fst.aemeasurable hφ_meas.aestronglyMeasurable]
    -- Lift a.e. properties from P0 to π via π.map Prod.fst = P0
    have hπ_singleton : ∀ᵐ p ∂π, OTDRO.Dual.maximizers ℓ A δ β lamStar p.1 = {G p.1} :=
      ae_of_ae_map (p := fun x => OTDRO.Dual.maximizers ℓ A δ β lamStar x = {G x})
        measurable_fst.aemeasurable (by rw [hπ_fst]; exact hG_singleton)
    have hπ_ellRob : ∀ᵐ p ∂π, OTDRO.Dual.ellRob ℓ A δ β lamStar p.1 = (φ p.1 : EReal) := by
      filter_upwards [hπ_singleton] with p hp
      have hGp : G p.1 ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar p.1 := by
        rw [hp]; exact Set.mem_singleton (G p.1)
      unfold OTDRO.Dual.ellRob φ
      apply le_antisymm
      · exact iSup_le fun c => EReal.coe_le_coe_iff.mpr (hGp c)
      · exact le_iSup (fun c => (OTDRO.Dual.Fobj ℓ A δ c β lamStar p.1 : EReal)) (G p.1)
    -- Define the nonnegative complementary-slackness gap h(p)
    let gap : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ := fun p =>
      φ p.1 - ℓ (inner ℝ β p.2) + (lamStar / Real.sqrt δ) * (OTDRO.Dual.mahalCost A p.1 p.2 - δ)
    have hgap_int : Integrable gap π :=
      (hφ1_int.sub hf_int_and_eq.1).add
        ((hc_int.sub (integrable_const δ)).const_mul (lamStar / Real.sqrt δ))
    have hgap_nonneg : 0 ≤ᵐ[π] gap := by
      filter_upwards [hπ_ellRob] with p hp
      have hsup := OTDRO.Dual.sup_transport_eq_ellRob A p.1 (hA.posDef p.1) ℓ δ hδ β lamStar hlam
      have hle : ((ℓ (inner ℝ β (p.1 + (p.2 - p.1))) -
          (lamStar / Real.sqrt δ) *
            (dotProduct (p.2 - p.1).ofLp (A p.1 *ᵥ (p.2 - p.1).ofLp) - δ) : ℝ) : EReal) ≤
          OTDRO.Dual.ellRob ℓ A δ β lamStar p.1 := by
        rw [← hsup]
        exact le_iSup (fun Δ : EuclideanSpace ℝ (Fin d) =>
          ((ℓ (inner ℝ β (p.1 + Δ)) - (lamStar / Real.sqrt δ) *
            (dotProduct Δ.ofLp (A p.1 *ᵥ Δ.ofLp) - δ) : ℝ) : EReal)) (p.2 - p.1)
      rw [hp, EReal.coe_le_coe_iff] at hle
      have hadd : p.1 + (p.2 - p.1) = p.2 := add_sub_cancel p.1 p.2
      have hcost_eq : dotProduct (p.2 - p.1).ofLp (A p.1 *ᵥ (p.2 - p.1).ofLp) =
          OTDRO.Dual.mahalCost A p.1 p.2 := by
        unfold OTDRO.Dual.mahalCost
        have hneg : (p.1 - p.2).ofLp = -(p.2 - p.1).ofLp := by
          ext i
          change p.1 i - p.2 i = -(p.2 i - p.1 i)
          ring
        rw [hneg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
      rw [hadd, hcost_eq] at hle
      dsimp [gap]
      linarith
    have hgap_int_le : ∫ p, gap p ∂π ≤ 0 := by
      have h1 : ∫ p, (φ p.1 - ℓ (inner ℝ β p.2)) ∂π =
          (∫ p, φ p.1 ∂π) - (∫ p, ℓ (inner ℝ β p.2) ∂π) :=
        integral_sub hφ1_int hf_int_and_eq.1
      have h2' : ∫ p, (OTDRO.Dual.mahalCost A p.1 p.2 - δ) ∂π =
          (∫ p, OTDRO.Dual.mahalCost A p.1 p.2 ∂π) - δ := by
        rw [integral_sub hc_int (integrable_const δ), integral_const]
        simp [Measure.real]
      have h3' : ∫ p, (lamStar / Real.sqrt δ) * (OTDRO.Dual.mahalCost A p.1 p.2 - δ) ∂π =
          (lamStar / Real.sqrt δ) * ((∫ p, OTDRO.Dual.mahalCost A p.1 p.2 ∂π) - δ) := by
        rw [integral_const_mul, h2']
      have h1_int : Integrable (fun p => φ p.1 - ℓ (inner ℝ β p.2)) π :=
        hφ1_int.sub hf_int_and_eq.1
      have h3_int : Integrable
          (fun p => (lamStar / Real.sqrt δ) * (OTDRO.Dual.mahalCost A p.1 p.2 - δ)) π :=
        (hc_int.sub (integrable_const δ)).const_mul (lamStar / Real.sqrt δ)
      have hcalc : ∫ p, gap p ∂π =
          (∫ p, φ p.1 ∂π) - (∫ p, ℓ (inner ℝ β p.2) ∂π) +
            (lamStar / Real.sqrt δ) * ((∫ p, OTDRO.Dual.mahalCost A p.1 p.2 ∂π) - δ) := by
        change ∫ p, ((φ p.1 - ℓ (inner ℝ β p.2)) +
          (lamStar / Real.sqrt δ) * (OTDRO.Dual.mahalCost A p.1 p.2 - δ)) ∂π = _
        rw [integral_add h1_int h3_int, h1, h3']
      rw [hcalc, hφ1_integral, hint_eq, sub_self, zero_add]
      have hlam'_nonneg : 0 ≤ lamStar / Real.sqrt δ := div_nonneg hlam hsqrt_pos.le
      nlinarith
    have hgap_int_zero : ∫ p, gap p ∂π = 0 :=
      le_antisymm hgap_int_le (integral_nonneg_of_ae hgap_nonneg)
    have hgap_zero_ae : gap =ᵐ[π] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hgap_nonneg hgap_int).mp hgap_int_zero
    -- Pointwise identification p.2 = shiftMap A δ β G p.1 for π-a.e. p
    have hp_ae : ∀ᵐ p ∂π, p.2 = OTDRO.Statics.shiftMap A δ β G p.1 := by
      filter_upwards [hπ_singleton, hgap_zero_ae] with p hsing hgap0
      have heq : ℓ (inner ℝ β p.2) -
          (lamStar / Real.sqrt δ) * (OTDRO.Dual.mahalCost A p.1 p.2 - δ) =
          OTDRO.Dual.Fobj ℓ A δ (G p.1) β lamStar p.1 := by
        dsimp [gap, φ] at hgap0
        linarith
      exact unique_pointwise_shift hδ hβ hlam_pos (hA.posDef p.1) hsing heq
    -- Conclude π.map Prod.snd = P0.map (shiftMap A δ β G)
    calc π.map Prod.snd
        = π.map (OTDRO.Statics.shiftMap A δ β G ∘ Prod.fst) := Measure.map_congr hp_ae
      _ = (π.map Prod.fst).map (OTDRO.Statics.shiftMap A δ β G) :=
          (Measure.map_map hT_meas measurable_fst).symm
      _ = P0.map (OTDRO.Statics.shiftMap A δ β G) := by rw [hπ_fst]

  exact ⟨G, hG_meas.aemeasurable, hT_meas.aemeasurable, hG_singleton,
    hmix_feas, hmix_opt, hunique, hmix_cost⟩
