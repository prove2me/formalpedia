-- Prove2me | solution 1 for OTDRO.Statics.dual_optimizer_unique
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:03:16.329549+00:00
-- url     : https://prove2.me/submissions/20514fa9-fb49-41bd-bb69-c3d99f7669a4

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions
import Theorems.Thm_OTDRO_Dual_dual_reformulation
import Theorems.Thm_OTDRO_Cvx_dual_proper_convex
import Theorems.Thm_OTDRO_StrongCvx_ell_deriv_sq_bounds
import Theorems.Thm_OTDRO_StrongCvx_dual_optimizer_in_V
import Theorems.Thm_OTDRO_StrongCvx_prop9_a
import Theorems.Thm_OTDRO_StrongCvx_F_strongly_concave
import Theorems.Thm_OTDRO_StrongCvx_maximizer_first_order
import Theorems.Thm_OTDRO_WorstCase_dual_lambda_derivatives

open MeasureTheory Filter Topology Matrix

private lemma quadInv_pos {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hQ : (A x).PosDef)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) :
    0 < OTDRO.Dual.quadInv A β x := by
  have hβ' : β.ofLp ≠ 0 := by
    intro h
    apply hβ
    ext i
    simpa using congrFun h i
  simpa [OTDRO.Dual.quadInv] using hQ.inv.dotProduct_mulVec_pos hβ'

private lemma quadInv_le_ae {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) :
    ∀ᵐ x ∂P0, OTDRO.Dual.quadInv A β x ≤ ‖β‖ ^ 2 / ρmin := by
  filter_upwards [hA.eig_bounds] with x hx
  have hQ : (A x).PosDef := hA.posDef x
  have hqpos : 0 < OTDRO.Dual.quadInv A β x := quadInv_pos A x hQ β hβ
  let u : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)
  have hAu : A x *ᵥ u.ofLp = β.ofLp := by
    change A x *ᵥ ((A x)⁻¹ *ᵥ β.ofLp) = β.ofLp
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (A x) (isUnit_iff_ne_zero.mpr hQ.det_pos.ne'),
      Matrix.one_mulVec]
  have huAu : dotProduct u.ofLp (A x *ᵥ u.ofLp) = OTDRO.Dual.quadInv A β x := by
    rw [hAu, dotProduct_comm]
    rfl
  have hlow : ρmin * ‖u‖ ^ 2 ≤ OTDRO.Dual.quadInv A β x := by
    simpa [huAu] using (hx u).1
  have hinner : OTDRO.Dual.quadInv A β x = inner ℝ u β := by
    rw [OTDRO.Dual.quadInv, EuclideanSpace.inner_eq_star_dotProduct]
    simp [u]
  have hcs : OTDRO.Dual.quadInv A β x ≤ ‖u‖ * ‖β‖ := by
    rw [hinner]
    exact (le_abs_self _).trans (abs_real_inner_le_norm u β)
  have hρ : 0 < ρmin := hA.rhoMin_pos
  have hsq : ρmin * (OTDRO.Dual.quadInv A β x) ^ 2 ≤ ‖β‖ ^ 2 * OTDRO.Dual.quadInv A β x := by
    have h1 : (OTDRO.Dual.quadInv A β x) ^ 2 ≤ (‖u‖ * ‖β‖) ^ 2 := by
      nlinarith [hqpos, hcs]
    have h2 : ρmin * (OTDRO.Dual.quadInv A β x) ^ 2 ≤ ρmin * (‖u‖ * ‖β‖) ^ 2 := by
      nlinarith [hρ, h1]
    have h3 : ρmin * (‖u‖ * ‖β‖) ^ 2 = ‖β‖ ^ 2 * (ρmin * ‖u‖ ^ 2) := by ring
    have h4 : ‖β‖ ^ 2 * (ρmin * ‖u‖ ^ 2) ≤ ‖β‖ ^ 2 * OTDRO.Dual.quadInv A β x := by
      nlinarith [sq_nonneg ‖β‖, hlow]
    linarith
  rw [le_div_iff₀ hρ]
  nlinarith [hqpos, hsq]

private lemma essSup_quadInv_nonneg {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) :
    0 ≤ essSup (fun x => OTDRO.Dual.quadInv A β x) P0 := by
  have h0 : essSup (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) P0 = 0 := essSup_const' 0
  rw [← h0]
  have hnonneg : (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) ≤ᵐ[P0]
      (fun x => OTDRO.Dual.quadInv A β x) :=
    Filter.Eventually.of_forall fun x => le_of_lt (quadInv_pos A x (hA.posDef x) β hβ)
  have hc0 : IsCoboundedUnder (· ≤ ·) (ae P0) (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) :=
    ⟨0, fun _ ha => (Filter.eventually_map.mp ha).exists.choose_spec⟩
  have hbdd : IsBoundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) :=
    ⟨‖β‖ ^ 2 / ρmin, quadInv_le_ae P0 A ρmin ρmax hA β hβ⟩
  exact essSup_mono_ae hnonneg hc0 hbdd

private lemma ell_le_quad {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M) :
    ∀ u : ℝ, ℓ u ≤ ℓ 0 + deriv ℓ 0 * u + (1 / 2) * M * u ^ 2 := by
  let g : ℝ → ℝ := fun u => ℓ 0 + deriv ℓ 0 * u + (1 / 2) * M * u ^ 2 - ℓ u
  have hg' : ∀ u : ℝ, HasDerivAt g (deriv ℓ 0 + M * u - deriv ℓ u) u := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ => ℓ 0 + deriv ℓ 0 * t) (deriv ℓ 0) u := by
      have hm := ((hasDerivAt_id u).const_mul (deriv ℓ 0)).const_add (ℓ 0)
      simpa using hm
    have h2 : HasDerivAt (fun t : ℝ => (1 / 2) * M * t ^ 2) (M * u) u := by
      have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * u) u := by
        simpa using hasDerivAt_pow 2 u
      have hm := hp.const_mul ((1 / 2) * M)
      have heq : (1 / 2) * M * (2 * u) = M * u := by ring
      rwa [heq] at hm
    exact (h1.add h2).sub (h3.differentiable u).hasDerivAt
  have hg'_deriv : ∀ u : ℝ, deriv g u = deriv ℓ 0 + M * u - deriv ℓ u :=
    fun u => (hg' u).deriv
  have hg'_mono : Monotone (deriv g) := by
    apply monotone_of_deriv_nonneg
    · intro u
      rw [show deriv g = fun t => deriv ℓ 0 + M * t - deriv ℓ t from funext hg'_deriv]
      exact ((differentiableAt_const _).add ((differentiableAt_id).const_mul M)).sub
        (h3.deriv_differentiable u)
    · intro u
      have hd : HasDerivAt (deriv g) (M - deriv (deriv ℓ) u) u := by
        rw [show deriv g = fun t => deriv ℓ 0 + M * t - deriv ℓ t from funext hg'_deriv]
        have h1 : HasDerivAt (fun t : ℝ => deriv ℓ 0 + M * t) M u := by
          have hm := ((hasDerivAt_id u).const_mul M).const_add (deriv ℓ 0)
          simpa using hm
        exact h1.sub (h3.deriv_differentiable u).hasDerivAt
      rw [hd.deriv]
      linarith [h3.second_deriv_le u]
  have hg_diff : Differentiable ℝ g := fun x => (hg' x).differentiableAt
  have hg'0 : deriv g 0 = 0 := by simp [hg'_deriv]
  have hg0 : g 0 = 0 := by simp [g]
  intro u
  have hgu : 0 ≤ g u := by
    rcases le_total 0 u with hu | hu
    · have hmono : MonotoneOn g (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact hg_diff.continuous.continuousOn
        · exact fun x _ => (hg_diff x).differentiableWithinAt
        · intro x hx
          rw [interior_Ici] at hx
          rw [← hg'0]
          exact hg'_mono (le_of_lt hx)
      rw [← hg0]
      exact hmono (Set.mem_Ici.mpr le_rfl) hu hu
    · have hanti : AntitoneOn g (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact hg_diff.continuous.continuousOn
        · exact fun x _ => (hg_diff x).differentiableWithinAt
        · intro x hx
          rw [interior_Iic] at hx
          rw [← hg'0]
          exact hg'_mono (le_of_lt hx)
      rw [← hg0]
      exact hanti hu (Set.mem_Iic.mpr le_rfl) hu
  dsimp [g] at hgu
  linarith

private lemma growthKappa_le_half_M {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M) :
    OTDRO.Dual.growthKappa ℓ ≤ 1 / 2 * M := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hmem : 1 / 2 * M + ε ∈
      {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)} := by
    refine ⟨by linarith [h3.M_pos], ⟨ℓ 0 + (deriv ℓ 0) ^ 2 / (4 * ε), ?_⟩⟩
    rintro _ ⟨u, rfl⟩
    have hq := ell_le_quad P0 ℓ B M h3 u
    have hsq : 0 ≤ ε * (u - deriv ℓ 0 / (2 * ε)) ^ 2 := by positivity
    have hid : ℓ 0 + deriv ℓ 0 * u - ε * u ^ 2 =
        ℓ 0 + (deriv ℓ 0) ^ 2 / (4 * ε) - ε * (u - deriv ℓ 0 / (2 * ε)) ^ 2 := by
      field_simp [hε.ne']
      ring
    linarith
  have hbddBelow : BddBelow {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)} :=
    ⟨0, fun s hs => hs.1⟩
  exact csInf_le hbddBelow hmem

private lemma lamThr_le_lamThr' {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) :
    OTDRO.Dual.lamThr P0 ℓ A δ β ≤ OTDRO.Dual.lamThr' P0 A M δ β := by
  unfold OTDRO.Dual.lamThr OTDRO.Dual.lamThr'
  have hκ := growthKappa_le_half_M P0 ℓ B M h3
  have hsq : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hess : 0 ≤ essSup (fun x => OTDRO.Dual.quadInv A β x) P0 :=
    essSup_quadInv_nonneg P0 A ρmin ρmax hA β hβ
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ hsq) hess

private lemma ell_ge_tangent {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ) (hℓ : Differentiable ℝ ℓ) :
    ∀ u : ℝ, ℓ 0 + deriv ℓ 0 * u ≤ ℓ u := by
  intro u
  have hderiv : HasDerivAt (fun t : ℝ => ℓ (t * u)) (deriv ℓ 0 * u) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * u) u 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const u
    have h2' : HasDerivAt ℓ (deriv ℓ 0) ((0 : ℝ) * u) := by
      rw [zero_mul]
      exact (hℓ 0).hasDerivAt
    exact h2'.comp (0 : ℝ) h1
  have htend : Tendsto (fun t : ℝ => t⁻¹ * (ℓ (t * u) - ℓ 0)) (𝓝[>] (0 : ℝ))
      (𝓝 (deriv ℓ 0 * u)) := by
    simpa [slope_def_field, zero_mul, sub_zero, div_eq_inv_mul] using
      hderiv.tendsto_slope_zero_right
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t⁻¹ * (ℓ (t * u) - ℓ 0) ≤ ℓ u - ℓ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    have hcvx := h2.convex.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ u)
      (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hcvx
    have hsub : ℓ (t * u) - ℓ 0 ≤ t * (ℓ u - ℓ 0) := by linarith
    have htpos : 0 < t := ht.1
    rw [inv_mul_le_iff₀ htpos]
    exact hsub
  have hle : deriv ℓ 0 * u ≤ ℓ u - ℓ 0 := le_of_tendsto htend hev
  linarith

private lemma integrable_ell_inner {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d)))
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (β : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x => ℓ (inner ℝ β x)) P0 := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ℓ (inner ℝ β x)) :=
    h3.differentiable.continuous.comp (continuous_const.inner continuous_id)
  let C : ℝ := |ℓ 0| + |deriv ℓ 0| * ‖β‖ + (1 / 2) * M * ‖β‖ ^ 2
  have hdom : Integrable (fun x : EuclideanSpace ℝ (Fin d) => C + C * ‖x‖ ^ 4) P0 :=
    (integrable_const C).add (h2.moment4.const_mul C)
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hlo := ell_ge_tangent P0 ℓ h2 h3.differentiable (inner ℝ β x)
  have hhi := ell_le_quad P0 ℓ B M h3 (inner ℝ β x)
  have hcs : |inner ℝ β x| ≤ ‖β‖ * ‖x‖ := abs_real_inner_le_norm β x
  have hsq1 : (inner ℝ β x) ^ 2 ≤ (‖β‖ * ‖x‖) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (inner ℝ β x), hcs]
  have hx1 : ‖x‖ ≤ 1 + ‖x‖ ^ 4 := by
    have h1 : 0 ≤ (‖x‖ - 1) ^ 2 := sq_nonneg _
    have h2' : 0 ≤ (‖x‖ ^ 2 - 1) ^ 2 := sq_nonneg _
    nlinarith [norm_nonneg x]
  have hx2 : ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 4 := by
    have h2' : 0 ≤ (‖x‖ ^ 2 - 1) ^ 2 := sq_nonneg _
    nlinarith
  have hM : 0 ≤ M := h3.M_pos.le
  have hterm1 : |deriv ℓ 0 * inner ℝ β x| ≤ |deriv ℓ 0| * ‖β‖ * (1 + ‖x‖ ^ 4) := by
    rw [abs_mul]
    calc |deriv ℓ 0| * |inner ℝ β x|
        ≤ |deriv ℓ 0| * (‖β‖ * ‖x‖) := by gcongr
      _ = |deriv ℓ 0| * ‖β‖ * ‖x‖ := by ring
      _ ≤ |deriv ℓ 0| * ‖β‖ * (1 + ‖x‖ ^ 4) := by gcongr
  have hterm2 : (1 / 2) * M * (inner ℝ β x) ^ 2 ≤ (1 / 2) * M * ‖β‖ ^ 2 * (1 + ‖x‖ ^ 4) := by
    calc (1 / 2) * M * (inner ℝ β x) ^ 2
        ≤ (1 / 2) * M * (‖β‖ * ‖x‖) ^ 2 := by gcongr
      _ = (1 / 2) * M * ‖β‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ (1 / 2) * M * ‖β‖ ^ 2 * (1 + ‖x‖ ^ 4) := by gcongr
  have hbound : |ℓ (inner ℝ β x)| ≤ C * (1 + ‖x‖ ^ 4) := by
    rw [abs_le]
    have h1 : -(deriv ℓ 0 * inner ℝ β x) ≤ |deriv ℓ 0 * inner ℝ β x| := neg_le_abs _
    have h2' : deriv ℓ 0 * inner ℝ β x ≤ |deriv ℓ 0 * inner ℝ β x| := le_abs_self _
    have h3' : -(ℓ 0) ≤ |ℓ 0| := neg_le_abs _
    have h4' : ℓ 0 ≤ |ℓ 0| := le_abs_self _
    have h5' : 0 ≤ |ℓ 0| * ‖x‖ ^ 4 := by positivity
    have h6' : 0 ≤ (1 / 2) * M * ‖β‖ ^ 2 * (1 + ‖x‖ ^ 4) := by positivity
    dsimp only [C]
    constructor <;> linarith
  rw [Real.norm_eq_abs]
  linarith

private lemma strong_concave_sign {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ℓ : ℝ → ℝ) (hℓ : Differentiable ℝ ℓ)
    (δ : ℝ) (β x : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (m : ℝ)
    (hstr : ∀ γ₁ γ₂ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * OTDRO.Dual.Fobj ℓ A δ γ₁ β lam x + (1 - t) * OTDRO.Dual.Fobj ℓ A δ γ₂ β lam x +
          m / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 ≤
        OTDRO.Dual.Fobj ℓ A δ (t * γ₁ + (1 - t) * γ₂) β lam x)
    (g : ℝ) (hg : g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x) :
    m / 2 * g ^ 2 ≤ Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv ℓ (inner ℝ β x) * g := by
  let F : ℝ → ℝ := fun γ => OTDRO.Dual.Fobj ℓ A δ γ β lam x
  let q : ℝ := OTDRO.Dual.quadInv A β x
  have hF0 : HasDerivAt F (Real.sqrt δ * q * deriv ℓ (inner ℝ β x)) 0 := by
    have hlin : HasDerivAt (fun γ : ℝ => inner ℝ β x + γ * Real.sqrt δ * q)
        (Real.sqrt δ * q) 0 := by
      have h1 : HasDerivAt (fun γ : ℝ => inner ℝ β x + γ * (Real.sqrt δ * q))
          (Real.sqrt δ * q) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Real.sqrt δ * q)).const_add (inner ℝ β x)
      have hfun : (fun γ : ℝ => inner ℝ β x + γ * (Real.sqrt δ * q)) =
          (fun γ : ℝ => inner ℝ β x + γ * Real.sqrt δ * q) := by
        ext γ
        ring
      rwa [hfun] at h1
    have hcomp : HasDerivAt (fun γ : ℝ => ℓ (inner ℝ β x + γ * Real.sqrt δ * q))
        (deriv ℓ (inner ℝ β x) * (Real.sqrt δ * q)) 0 := by
      have hℓ0 : HasDerivAt ℓ (deriv ℓ (inner ℝ β x))
          (inner ℝ β x + (0 : ℝ) * Real.sqrt δ * q) := by
        simpa using (hℓ (inner ℝ β x)).hasDerivAt
      exact hℓ0.comp (0 : ℝ) hlin
    have hquad : HasDerivAt (fun γ : ℝ => lam * Real.sqrt δ * (γ ^ 2 * q - 1)) 0 0 := by
      have hp : HasDerivAt (fun γ : ℝ => γ ^ 2) (2 * (0 : ℝ)) 0 := by
        simpa using hasDerivAt_pow 2 (0 : ℝ)
      have hq' : HasDerivAt (fun γ : ℝ => γ ^ 2 * q - 1) (2 * (0 : ℝ) * q) 0 := by
        simpa using (hp.mul_const q).sub_const 1
      have hm := hq'.const_mul (lam * Real.sqrt δ)
      have hzero : lam * Real.sqrt δ * (2 * (0 : ℝ) * q) = 0 := by ring
      rwa [hzero] at hm
    have hsub := hcomp.sub hquad
    have hderiv_eq : deriv ℓ (inner ℝ β x) * (Real.sqrt δ * q) - 0 =
        Real.sqrt δ * q * deriv ℓ (inner ℝ β x) := by ring
    rwa [hderiv_eq] at hsub
  have hFg : HasDerivAt (fun t : ℝ => F (t * g))
      (Real.sqrt δ * q * deriv ℓ (inner ℝ β x) * g) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * g) g 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const g
    have hF0' : HasDerivAt F (Real.sqrt δ * q * deriv ℓ (inner ℝ β x)) ((0 : ℝ) * g) := by
      rwa [zero_mul]
    exact hF0'.comp (0 : ℝ) h1
  have htend_rhs : Tendsto (fun t : ℝ => t⁻¹ * (F (t * g) - F 0)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt δ * q * deriv ℓ (inner ℝ β x) * g)) := by
    simpa [slope_def_field, zero_mul, sub_zero, div_eq_inv_mul] using
      hFg.tendsto_slope_zero_right
  have htend_lhs : Tendsto (fun t : ℝ => m / 2 * (1 - t) * g ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (m / 2 * g ^ 2)) := by
    have hc : Continuous (fun t : ℝ => m / 2 * (1 - t) * g ^ 2) := by fun_prop
    have ht : Tendsto (fun t : ℝ => m / 2 * (1 - t) * g ^ 2) (𝓝 (0 : ℝ))
        (𝓝 (m / 2 * (1 - 0) * g ^ 2)) := hc.continuousAt.tendsto
    simpa using ht.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      m / 2 * (1 - t) * g ^ 2 ≤ t⁻¹ * (F (t * g) - F 0) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    have h1 := hstr g 0 t ht.1.le ht.2.le
    have hmax : F 0 ≤ F g := hg 0
    have h2 : t * (m / 2 * (1 - t) * g ^ 2) ≤ F (t * g) - F 0 := by
      dsimp only [F] at hmax ⊢
      have hmul : 0 ≤ t * (OTDRO.Dual.Fobj ℓ A δ g β lam x - OTDRO.Dual.Fobj ℓ A δ 0 β lam x) :=
        mul_nonneg ht.1.le (sub_nonneg.mpr hmax)
      have harg : t * g + (1 - t) * 0 = t * g := by ring
      rw [harg] at h1
      linarith
    rw [le_inv_mul_iff₀ ht.1]
    exact h2
  exact le_of_tendsto_of_tendsto htend_lhs htend_rhs hev

private lemma pointwise_maximizer_sq_strict_decrease {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hℓ : Differentiable ℝ ℓ)
    (β x : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lam1 lam2 : ℝ) (hlam1_pos : 0 < lam1) (hlt : lam1 < lam2)
    (m1 m2 g1 g2 : ℝ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (hstr1 : ∀ γ₁ γ₂ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * OTDRO.Dual.Fobj ℓ A δ γ₁ β lam1 x + (1 - t) * OTDRO.Dual.Fobj ℓ A δ γ₂ β lam1 x +
          m1 / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 ≤
        OTDRO.Dual.Fobj ℓ A δ (t * γ₁ + (1 - t) * γ₂) β lam1 x)
    (hstr2 : ∀ γ₁ γ₂ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * OTDRO.Dual.Fobj ℓ A δ γ₁ β lam2 x + (1 - t) * OTDRO.Dual.Fobj ℓ A δ γ₂ β lam2 x +
          m2 / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 ≤
        OTDRO.Dual.Fobj ℓ A δ (t * γ₁ + (1 - t) * γ₂) β lam2 x)
    (hg1_mem : g1 ∈ OTDRO.Dual.maximizers ℓ A δ β lam1 x)
    (hg2_mem : g2 ∈ OTDRO.Dual.maximizers ℓ A δ β lam2 x) :
    g2 ^ 2 ≤ g1 ^ 2 ∧ (deriv ℓ (inner ℝ β x) ≠ 0 → g2 ^ 2 < g1 ^ 2) := by
  have hlam2_pos : 0 < lam2 := lt_trans hlam1_pos hlt
  have hqpos : 0 < OTDRO.Dual.quadInv A β x := quadInv_pos A x (hA.posDef x) β hβ
  have hsqδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hle1 : OTDRO.Dual.Fobj ℓ A δ g2 β lam1 x ≤ OTDRO.Dual.Fobj ℓ A δ g1 β lam1 x := hg1_mem g2
  have hle2 : OTDRO.Dual.Fobj ℓ A δ g1 β lam2 x ≤ OTDRO.Dual.Fobj ℓ A δ g2 β lam2 x := hg2_mem g1
  have hdiff : (lam2 - lam1) * Real.sqrt δ * OTDRO.Dual.quadInv A β x * (g2 ^ 2 - g1 ^ 2) ≤ 0 := by
    dsimp only [OTDRO.Dual.Fobj] at hle1 hle2
    linarith
  have hfac_pos : 0 < (lam2 - lam1) * Real.sqrt δ * OTDRO.Dual.quadInv A β x :=
    mul_pos (mul_pos (sub_pos.mpr hlt) hsqδ) hqpos
  have hsq_le : g2 ^ 2 ≤ g1 ^ 2 := by
    have hsub : g2 ^ 2 - g1 ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hdiff hfac_pos
    linarith
  refine ⟨hsq_le, fun hder => ?_⟩
  have hfo1 := OTDRO.StrongCvx.maximizer_first_order P0 A ρmin ρmax hA ℓ h2 δ hδ B hB β hβB hβ x
    lam1 hlam1_pos hℓ ⟨g1, hg1_mem⟩ g1 hg1_mem
  have hfo2 := OTDRO.StrongCvx.maximizer_first_order P0 A ρmin ρmax hA ℓ h2 δ hδ B hB β hβB hβ x
    lam2 hlam2_pos hℓ ⟨g2, hg2_mem⟩ g2 hg2_mem
  have hg1_ne : g1 ≠ 0 := by
    intro h0
    have hpos : 0 < |deriv ℓ (inner ℝ β x)| / (2 * lam1) :=
      div_pos (abs_pos.mpr hder) (by linarith)
    have h1 := hfo1.2
    rw [h0, abs_zero] at h1
    linarith
  have hg2_ne : g2 ≠ 0 := by
    intro h0
    have hpos : 0 < |deriv ℓ (inner ℝ β x)| / (2 * lam2) :=
      div_pos (abs_pos.mpr hder) (by linarith)
    have h2' := hfo2.2
    rw [h0, abs_zero] at h2'
    linarith
  have hsign1 := strong_concave_sign A ℓ hℓ δ β x lam1 m1 hstr1 g1 hg1_mem
  have hsign2 := strong_concave_sign A ℓ hℓ δ β x lam2 m2 hstr2 g2 hg2_mem
  let c : ℝ := Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv ℓ (inner ℝ β x)
  have hcg1 : 0 < c * g1 :=
    lt_of_lt_of_le (mul_pos (half_pos hm1) (sq_pos_of_ne_zero hg1_ne)) hsign1
  have hcg2 : 0 < c * g2 :=
    lt_of_lt_of_le (mul_pos (half_pos hm2) (sq_pos_of_ne_zero hg2_ne)) hsign2
  have hprod_pos : 0 < g1 * g2 := by
    have hmul : 0 < c ^ 2 * (g1 * g2) := by
      have := mul_pos hcg1 hcg2
      linarith [show (c * g1) * (c * g2) = c ^ 2 * (g1 * g2) by ring]
    exact pos_of_mul_pos_right hmul (sq_nonneg c)
  refine lt_of_le_of_ne hsq_le fun heq => ?_
  have hfac : (g1 - g2) * (g1 + g2) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with hsub | hadd
  · have hg_eq : g1 = g2 := sub_eq_zero.mp hsub
    have he1 : g1 * (2 * lam1) =
        deriv ℓ (inner ℝ β x + Real.sqrt δ * g1 * OTDRO.Dual.quadInv A β x) :=
      (eq_div_iff (by linarith : (2 * lam1 : ℝ) ≠ 0)).mp hfo1.1
    have he2 : g2 * (2 * lam2) =
        deriv ℓ (inner ℝ β x + Real.sqrt δ * g2 * OTDRO.Dual.quadInv A β x) :=
      (eq_div_iff (by linarith : (2 * lam2 : ℝ) ≠ 0)).mp hfo2.1
    rw [← hg_eq] at he2
    have hzero : 2 * (lam1 - lam2) * g1 = 0 := by linarith
    rcases mul_eq_zero.mp hzero with h1' | h2'
    · linarith
    · exact hg1_ne h2'
  · have hg_neg : g2 = -g1 := by linarith
    rw [hg_neg] at hprod_pos
    have hneg : g1 * -g1 = -(g1 ^ 2) := by ring
    linarith [sq_nonneg g1]

private lemma dual_minimizer_eq_of_lt {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lam1 lam2 : ℝ) (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2)
    (hmin1 : IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam1)
    (hmin2 : IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam2)
    (hthr1 : OTDRO.Dual.lamThr' P0 A M δ β < lam1)
    (hlt : lam1 < lam2) : False := by
  have hthr_le : OTDRO.Dual.lamThr P0 ℓ A δ β ≤ OTDRO.Dual.lamThr' P0 A M δ β :=
    lamThr_le_lamThr' P0 A ρmin ρmax hA ℓ B M h3 δ β hβ
  have hthr1_old : OTDRO.Dual.lamThr P0 ℓ A δ β < lam1 := lt_of_le_of_lt hthr_le hthr1
  have hthr2 : OTDRO.Dual.lamThr' P0 A M δ β < lam2 := lt_trans hthr1 hlt
  have hthr2_old : OTDRO.Dual.lamThr P0 ℓ A δ β < lam2 := lt_of_le_of_lt hthr_le hthr2
  have hlam1_pos : 0 < lam1 := by
    have h0 : 0 ≤ OTDRO.Dual.lamThr' P0 A M δ β := by
      unfold OTDRO.Dual.lamThr'
      have hM : 0 ≤ M := h3.M_pos.le
      have hsq : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
      have hess : 0 ≤ essSup (fun x => OTDRO.Dual.quadInv A β x) P0 :=
        essSup_quadInv_nonneg P0 A ρmin ρmax hA β hβ
      positivity
    linarith
  have hcvx := OTDRO.Cvx.dual_proper_convex P0 A ρmin ρmax hA ℓ δ hδ B hB h2
  have hdl := OTDRO.WorstCase.dual_lambda_derivatives P0 A ρmin ρmax hA ℓ h2 δ hδ B hB β hβB hβ
  have hf1_fin : OTDRO.Dual.fDelta P0 ℓ A δ β lam1 ≠ ⊤ ∧ OTDRO.Dual.fDelta P0 ℓ A δ β lam1 ≠ ⊥ :=
    hdl.1 lam1 hthr1_old
  have hf_eq12 : OTDRO.Dual.fDelta P0 ℓ A δ β lam1 = OTDRO.Dual.fDelta P0 ℓ A δ β lam2 :=
    le_antisymm (hmin1 hlam2) (hmin2 hlam1)
  let f : ℝ → ℝ := fun l => (OTDRO.Dual.fDelta P0 ℓ A δ β l).toReal
  have hf_const : ∀ l ∈ Set.Icc lam1 lam2, f l = f lam1 := by
    intro l hl
    have hl0 : 0 ≤ l := le_trans hlam1 hl.1
    have hge : OTDRO.Dual.fDelta P0 ℓ A δ β lam1 ≤ OTDRO.Dual.fDelta P0 ℓ A δ β l := hmin1 hl0
    let α : ℝ := (lam2 - l) / (lam2 - lam1)
    have hα0 : 0 ≤ α := div_nonneg (sub_nonneg.mpr hl.2) (sub_pos.mpr hlt).le
    have hα1 : α ≤ 1 := by
      rw [div_le_one (sub_pos.mpr hlt)]
      linarith [hl.1]
    have hβcomb : α • β + (1 - α) • β = β := by
      rw [← add_smul]
      simp
    have hlcomb : α * lam1 + (1 - α) * lam2 = l := by
      dsimp only [α]
      field_simp [(sub_pos.mpr hlt).ne']
      ring
    have hle_cvx := hcvx.2.2 β hβB β hβB lam1 lam2 hlam1 hlam2 α hα0 hα1
    rw [hβcomb, hlcomb, ← hf_eq12] at hle_cvx
    have hcoe : ((f lam1 : ℝ) : EReal) = OTDRO.Dual.fDelta P0 ℓ A δ β lam1 :=
      EReal.coe_toReal hf1_fin.1 hf1_fin.2
    have hle : OTDRO.Dual.fDelta P0 ℓ A δ β l ≤ OTDRO.Dual.fDelta P0 ℓ A δ β lam1 := by
      calc OTDRO.Dual.fDelta P0 ℓ A δ β l
          ≤ (α : EReal) * OTDRO.Dual.fDelta P0 ℓ A δ β lam1 +
              ((1 - α : ℝ) : EReal) * OTDRO.Dual.fDelta P0 ℓ A δ β lam1 := hle_cvx
        _ = (α : EReal) * ((f lam1 : ℝ) : EReal) +
              ((1 - α : ℝ) : EReal) * ((f lam1 : ℝ) : EReal) := by rw [hcoe]
        _ = (((α * f lam1 + (1 - α) * f lam1 : ℝ) : EReal)) := by
            norm_cast
        _ = ((f lam1 : ℝ) : EReal) := by
            congr 1; ring
        _ = OTDRO.Dual.fDelta P0 ℓ A δ β lam1 := hcoe
    have heq : OTDRO.Dual.fDelta P0 ℓ A δ β l = OTDRO.Dual.fDelta P0 ℓ A δ β lam1 :=
      le_antisymm hle hge
    simp [f, heq]
  have hd1_zero : HasDerivWithinAt f 0 (Set.Ici lam1) lam1 := by
    have hc : HasDerivWithinAt (fun _ : ℝ => f lam1) 0 (Set.Ici lam1) lam1 :=
      hasDerivWithinAt_const lam1 (Set.Ici lam1) (f lam1)
    refine hc.congr_of_eventuallyEq ?_ rfl
    have hmem : Set.Icc lam1 lam2 ∈ 𝓝[Set.Ici lam1] lam1 := Icc_mem_nhdsGE hlt
    filter_upwards [hmem] with l hl
    exact hf_const l hl
  have hd2_zero : HasDerivWithinAt f 0 (Set.Iic lam2) lam2 := by
    have hc : HasDerivWithinAt (fun _ : ℝ => f lam1) 0 (Set.Iic lam2) lam2 :=
      hasDerivWithinAt_const lam2 (Set.Iic lam2) (f lam1)
    refine hc.congr_of_eventuallyEq ?_ (hf_const lam2 ⟨hlt.le, le_rfl⟩)
    have hmem : Set.Icc lam1 lam2 ∈ 𝓝[Set.Iic lam2] lam2 := Icc_mem_nhdsLE hlt
    filter_upwards [hmem] with l hl
    exact hf_const l hl
  have hdl1 := hdl.2 lam1 hthr1_old
  have hdl2 := hdl.2 lam2 hthr2_old
  have hd1_eq : Real.sqrt δ * (1 - ∫ x, OTDRO.Dual.quadInv A β x *
      sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam1 x) ∂P0) = 0 :=
    (HasDerivWithinAt.derivWithin hdl1.2.2.2.1 (uniqueDiffWithinAt_Ici lam1)).symm.trans
      (HasDerivWithinAt.derivWithin hd1_zero (uniqueDiffWithinAt_Ici lam1))
  have hd2_eq : Real.sqrt δ * (1 - ∫ x, OTDRO.Dual.quadInv A β x *
      sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam2 x) ∂P0) = 0 :=
    (HasDerivWithinAt.derivWithin hdl2.2.2.2.2 (uniqueDiffWithinAt_Iic lam2)).symm.trans
      (HasDerivWithinAt.derivWithin hd2_zero (uniqueDiffWithinAt_Iic lam2))
  have hsqδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  let φ1 : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    OTDRO.Dual.quadInv A β x *
      sInf ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam1 x)
  let φ2 : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    OTDRO.Dual.quadInv A β x *
      sSup ((fun g : ℝ => g ^ 2) '' OTDRO.Dual.maximizers ℓ A δ β lam2 x)
  have hint1 : Integrable φ1 P0 := hdl1.2.1
  have hint2 : Integrable φ2 P0 := hdl2.2.2.1
  have hi1 : ∫ x, φ1 x ∂P0 = 1 := by
    have : 1 - ∫ x, φ1 x ∂P0 = 0 := (mul_eq_zero.mp hd1_eq).resolve_left hsqδ.ne'
    linarith
  have hi2 : ∫ x, φ2 x ∂P0 = 1 := by
    have : 1 - ∫ x, φ2 x ∂P0 = 0 := (mul_eq_zero.mp hd2_eq).resolve_left hsqδ.ne'
    linarith
  have hsc := OTDRO.StrongCvx.F_strongly_concave P0 A ρmin ρmax hA ℓ h2 δ hδ B hB M h3
  have h_ae : ∀ᵐ x ∂P0, 0 ≤ φ1 x - φ2 x ∧
      (deriv ℓ (inner ℝ β x) ≠ 0 → 0 < φ1 x - φ2 x) := by
    filter_upwards [hsc] with x hx
    obtain ⟨m1, hm1, hstr1, ⟨g1, hg1⟩, _⟩ := hx β hβB hβ lam1 hthr1
    obtain ⟨m2, hm2, hstr2, ⟨g2, hg2⟩, _⟩ := hx β hβB hβ lam2 hthr2
    have hqpos : 0 < OTDRO.Dual.quadInv A β x := quadInv_pos A x (hA.posDef x) β hβ
    have hφ1 : φ1 x = OTDRO.Dual.quadInv A β x * g1 ^ 2 := by simp [φ1, hg1]
    have hφ2 : φ2 x = OTDRO.Dual.quadInv A β x * g2 ^ 2 := by simp [φ2, hg2]
    have hg1_mem : g1 ∈ OTDRO.Dual.maximizers ℓ A δ β lam1 x := by simp [hg1]
    have hg2_mem : g2 ∈ OTDRO.Dual.maximizers ℓ A δ β lam2 x := by simp [hg2]
    have hpt := pointwise_maximizer_sq_strict_decrease P0 A ρmin ρmax hA ℓ h2 δ hδ B hB
      h3.differentiable β x hβB hβ lam1 lam2 hlam1_pos hlt m1 m2 g1 g2 hm1 hm2 hstr1 hstr2
      hg1_mem hg2_mem
    rw [hφ1, hφ2]
    exact ⟨sub_nonneg.mpr (mul_le_mul_of_nonneg_left hpt.1 hqpos.le),
      fun hder => sub_pos.mpr (mul_lt_mul_of_pos_left (hpt.2 hder) hqpos)⟩
  have hnonneg_ae : (0 : EuclideanSpace ℝ (Fin d) → ℝ) ≤ᵐ[P0] (fun x => φ1 x - φ2 x) :=
    h_ae.mono fun x hx => hx.1
  have hint_sub : Integrable (fun x => φ1 x - φ2 x) P0 := hint1.sub hint2
  have hint_zero : ∫ x, (φ1 x - φ2 x) ∂P0 = 0 := by
    rw [integral_sub hint1 hint2, hi1, hi2, sub_self]
  have hzero_ae : (fun x => φ1 x - φ2 x) =ᵐ[P0] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg_ae hint_sub).mp hint_zero
  have hder_zero : ∀ᵐ x ∂P0, deriv ℓ (inner ℝ β x) = 0 := by
    filter_upwards [h_ae, hzero_ae] with x hx hz
    by_contra hne
    have hpos : 0 < φ1 x - φ2 x := hx.2 hne
    have hz' : φ1 x - φ2 x = 0 := hz
    linarith
  exact h3.nonzero_deriv β hβB hder_zero

theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (h5 : OTDRO.StrongCvx.Assumption5 P0 ℓ B)
    (Llow Lbar : ℝ)
    (hL : 0 < Llow ∧ ∀ β ∈ B,
      Llow ≤ ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ∧
      ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ≤ Lbar)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0) :
    ∃ δ1 : ℝ, 0 < δ1 ∧ δ1 < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (OTDRO.Statics.Rβ B) M ∧
      ∀ δ ∈ Set.Ioo 0 δ1,
        (∃! lam : ℝ, 0 ≤ lam ∧
          IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam) ∧
        ∀ lam : ℝ, 0 ≤ lam →
          IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam →
          OTDRO.Dual.lamThr' P0 A M δ β < lam := by
  let _ := h5
  have hR_pos : 0 < OTDRO.Statics.Rβ B := by
    have hcomp : IsCompact ((fun b : EuclideanSpace ℝ (Fin d) => ‖b‖) '' B) :=
      hB4.compact.image continuous_norm
    have hmem : ‖β‖ ∈ (fun b : EuclideanSpace ℝ (Fin d) => ‖b‖) '' B := ⟨β, hβB, rfl⟩
    exact lt_of_lt_of_le (norm_pos_iff.mpr hβ) (le_csSup hcomp.bddAbove hmem)
  have hδ0_pos : 0 < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (OTDRO.Statics.Rβ B) M := by
    unfold OTDRO.StrongCvx.delta0
    have h1 := hA.rhoMin_pos
    have h2' := hA.rhoMax_pos
    have h3' := hL.1
    have h4 := h3.M_pos
    positivity
  have hDSB : OTDRO.StrongCvx.DerivSqBounds P0 ℓ B Llow Lbar := by
    obtain ⟨L1, L2, hL12⟩ := OTDRO.StrongCvx.ell_deriv_sq_bounds P0 ℓ h2 B hB4 hBne M h3
    have hLbar_pos : 0 < Lbar := lt_of_lt_of_le hL.1 ((hL.2 β hβB).1.trans (hL.2 β hβB).2)
    exact ⟨hL.1, hLbar_pos, fun b hb => ⟨(hL12.2.2 b hb).1, (hL.2 b hb).1, (hL.2 b hb).2⟩⟩
  refine ⟨OTDRO.StrongCvx.delta0 ρmin ρmax Llow (OTDRO.Statics.Rβ B) M / 2,
    half_pos hδ0_pos, half_lt_self hδ0_pos, ?_⟩
  intro δ hδIoo
  have hδ : 0 < δ := hδIoo.1
  have hδ0 : δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (OTDRO.StrongCvx.Rbeta B) M := by
    change δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (OTDRO.Statics.Rβ B) M
    linarith [hδIoo.2, hδ0_pos]
  have hthr_min : ∀ lam : ℝ, 0 ≤ lam →
      IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam →
      OTDRO.Dual.lamThr' P0 A M δ β < lam := by
    intro lam hlam hmin
    have hV : (β, lam) ∈ OTDRO.StrongCvx.regionV B δ M (OTDRO.StrongCvx.Rbeta B)
        ρmin ρmax Llow Lbar :=
      OTDRO.StrongCvx.dual_optimizer_in_V P0 A ρmin ρmax hA ℓ h2 δ hδ B hB hB4 hBne M h3
        Llow Lbar hDSB β hβB lam hlam hmin
    have hp9 := OTDRO.StrongCvx.prop9_a P0 A ρmin ρmax hA ℓ h2 δ hδ B hB hB4 hBne M h3
      Llow Lbar hDSB hδ0
    have hW := hp9.1 hV
    obtain ⟨x, hx⟩ := hp9.2.exists
    exact (hx (β, lam) hW hβ).1
  refine ⟨?_, hthr_min⟩
  have hint_ell : Integrable (fun x => ℓ (inner ℝ β x)) P0 :=
    integrable_ell_inner P0 ℓ h2 B M h3 β
  obtain ⟨_, lamStar, hlamStar0, hlamStar_eq⟩ :=
    OTDRO.Dual.dual_reformulation P0 A ρmin ρmax hA ℓ h3.differentiable.continuous.upperSemicontinuous
      δ hδ B hB β hβB hint_ell
  have hlamStar_min : IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lamStar := by
    intro l hl
    change OTDRO.Dual.fDelta P0 ℓ A δ β lamStar ≤ OTDRO.Dual.fDelta P0 ℓ A δ β l
    rw [hlamStar_eq]
    exact iInf₂_le l hl
  refine ⟨lamStar, ⟨hlamStar0, hlamStar_min⟩, ?_⟩
  intro lam ⟨hlam0, hlam_min⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact dual_minimizer_eq_of_lt P0 A ρmin ρmax hA ℓ h2 δ hδ B hB M h3 β hβB hβ
      lam lamStar hlam0 hlamStar0 hlam_min hlamStar_min (hthr_min lam hlam0 hlam_min) hlt
  · exact dual_minimizer_eq_of_lt P0 A ρmin ρmax hA ℓ h2 δ hδ B hB M h3 β hβB hβ
      lamStar lam hlamStar0 hlam0 hlamStar_min hlam_min (hthr_min lamStar hlamStar0 hlamStar_min) hgt
