-- Prove2me | solution 1 for PDScenRed.Mean.theorem3_mean_minimizes_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:25:33.109717+00:00
-- url     : https://prove2.me/submissions/2fa4a910-7266-4bfc-80e3-5f5b9e2c6802

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting
open scoped InnerProductSpace
open MeasureTheory

set_option autoImplicit false

namespace PDScenRedMeanAux

open SmartPTO.Fisher

lemma bddAbove_img {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} {R : ℝ}
    (hR : ∀ w ∈ S, ‖w‖ ≤ R) (c : EuclideanSpace ℝ (Fin d)) :
    BddAbove ((fun w => ⟪c, w⟫_ℝ) '' S) := by
  refine ⟨‖c‖ * R, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hR w hw) (norm_nonneg _))

lemma le_xi {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} {R : ℝ}
    (hR : ∀ w ∈ S, ‖w‖ ≤ R) {w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ S)
    (c : EuclideanSpace ℝ (Fin d)) : ⟪c, w⟫_ℝ ≤ xi S c :=
  le_csSup (bddAbove_img hR c) ⟨w, hw, rfl⟩

lemma xi_le {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} (hne : S.Nonempty) {R : ℝ}
    (hR : ∀ w ∈ S, ‖w‖ ≤ R) (c : EuclideanSpace ℝ (Fin d)) : xi S c ≤ R * ‖c‖ := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  calc ⟪c, w⟫_ℝ ≤ ‖c‖ * ‖w‖ := real_inner_le_norm _ _
    _ ≤ ‖c‖ * R := mul_le_mul_of_nonneg_left (hR w hw) (norm_nonneg _)
    _ = R * ‖c‖ := mul_comm _ _

lemma xi_lip {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} (hne : S.Nonempty) {R : ℝ}
    (hR : ∀ w ∈ S, ‖w‖ ≤ R) (a b : EuclideanSpace ℝ (Fin d)) :
    xi S a ≤ xi S b + R * ‖a - b‖ := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  have h1 : ⟪a, w⟫_ℝ = ⟪b, w⟫_ℝ + ⟪a - b, w⟫_ℝ := by rw [inner_sub_left]; ring
  have h2 : ⟪b, w⟫_ℝ ≤ xi S b := le_xi hR hw b
  have h3 : ⟪a - b, w⟫_ℝ ≤ R * ‖a - b‖ := by
    calc ⟪a - b, w⟫_ℝ ≤ ‖a - b‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ ‖a - b‖ * R := mul_le_mul_of_nonneg_left (hR w hw) (norm_nonneg _)
      _ = R * ‖a - b‖ := mul_comm _ _
  linarith

lemma xi_cont {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} (hne : S.Nonempty) {R : ℝ}
    (hR : ∀ w ∈ S, ‖w‖ ≤ R) (hR0 : 0 ≤ R) : Continuous (xi S) := by
  refine (LipschitzWith.of_le_add_mul (Real.toNNReal R) (fun a b => ?_)).continuous
  rw [Real.coe_toNNReal _ hR0, dist_eq_norm]
  exact xi_lip hne hR a b

lemma xi_neg_of_mem_Wstar {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} {R : ℝ}
    (hR : ∀ w ∈ S, ‖w‖ ≤ R) {c w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ Wstar S c) :
    xi S (-c) = ⟪-c, w⟫_ℝ := by
  refine le_antisymm ?_ (le_xi hR hw.1 _)
  refine csSup_le ⟨_, ⟨w, hw.1, rfl⟩⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [inner_neg_left]
  exact neg_le_neg (hw.2 v hv)

lemma zstar_of_mem_Wstar {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {c w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ Wstar S c) :
    zstar S c = ⟪c, w⟫_ℝ := by
  have hbdd : BddBelow ((fun v => ⟪c, v⟫_ℝ) '' S) := by
    refine ⟨⟪c, w⟫_ℝ, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hw.2 v hv
  refine le_antisymm (csInf_le hbdd ⟨w, hw.1, rfl⟩) ?_
  refine le_csInf ⟨_, ⟨w, hw.1, rfl⟩⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hw.2 v hv

end PDScenRedMeanAux

open PDScenRed.Mean MeasureTheory InnerProductSpace in
theorem solution {d r : ℕ}
    (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ) (hmeas : Measurable zsel)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hac : μ ≪ volume) (hU : μ ((Uset (polytope P qv))ᶜ) = 0)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ξ) μ)
    (hpos : 0 < ⟪zsel (∫ ξ, ξ ∂μ), ∫ ξ, ξ ∂μ⟫_ℝ)
    (hsym : SmartPTO.Fisher.CentrallySymmetric μ) :
    ∀ ζ : EuclideanSpace ℝ (Fin d),
      upperBoundObj (polytope P qv) zsel μ (∫ ξ, ξ ∂μ) ≤
        upperBoundObj (polytope P qv) zsel μ ζ ∧
      wassersteinOneObj μ (∫ ξ, ξ ∂μ) ≤ wassersteinOneObj μ ζ := by
  intro ζ
  set Z := polytope P qv with hZ
  set m : EuclideanSpace ℝ (Fin d) := ∫ ξ, ξ ∂μ with hm
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ hne.some_mem)
  let T : EuclideanSpace ℝ (Fin d) ≃ᵐ EuclideanSpace ℝ (Fin d) :=
    (Homeomorph.subLeft ((2 : ℝ) • m)).toMeasurableEquiv
  have hTapp : ∀ ξ, T ξ = (2 : ℝ) • m - ξ := fun _ => rfl
  have hmap : μ.map T = μ := hsym
  have hzint : Integrable zsel μ :=
    Integrable.mono' (integrable_const R) hmeas.aestronglyMeasurable
      (ae_of_all _ fun ξ => hR _ (hsel ξ).1)
  have hwmeas : Measurable fun ξ => zsel (T ξ) := hmeas.comp T.measurable
  have hwint : Integrable (fun ξ => zsel (T ξ)) μ :=
    Integrable.mono' (integrable_const R) hwmeas.aestronglyMeasurable
      (ae_of_all _ fun ξ => hR _ (hsel _).1)
  have hint_eq : ∫ ξ, zsel (T ξ) ∂μ = ∫ ξ, zsel ξ ∂μ := by
    have := integral_map_equiv (μ := μ) T zsel
    rw [hmap] at this
    exact this.symm
  have hAint : Integrable (fun ξ => ⟪ξ, zsel (T ξ)⟫_ℝ) μ := by
    refine Integrable.mono' (hint.norm.const_mul R)
      (measurable_id.inner hwmeas).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs]
    calc |⟪ξ, zsel (T ξ)⟫_ℝ| ≤ ‖ξ‖ * ‖zsel (T ξ)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖ξ‖ * R := mul_le_mul_of_nonneg_left (hR _ (hsel _).1) (norm_nonneg _)
      _ = R * ‖ξ‖ := mul_comm _ _
  -- the affine minorant G, whose integral does not depend on the scenario
  have hG : ∀ ζ' : EuclideanSpace ℝ (Fin d),
      ∫ ξ, (⟪ξ, zsel (T ξ)⟫_ℝ - 2 * ⟪ζ', zsel (T ξ)⟫_ℝ + 2 * ⟪ζ', zsel ξ⟫_ℝ) ∂μ
        = ∫ ξ, ⟪ξ, zsel (T ξ)⟫_ℝ ∂μ := by
    intro ζ'
    have hB : Integrable (fun ξ => 2 * ⟪ζ', zsel (T ξ)⟫_ℝ) μ :=
      (hwint.const_inner (𝕜 := ℝ) ζ').const_mul 2
    have hC : Integrable (fun ξ => 2 * ⟪ζ', zsel ξ⟫_ℝ) μ :=
      (hzint.const_inner (𝕜 := ℝ) ζ').const_mul 2
    have hAB : Integrable (fun ξ => ⟪ξ, zsel (T ξ)⟫_ℝ - 2 * ⟪ζ', zsel (T ξ)⟫_ℝ) μ := hAint.sub hB
    rw [integral_add hAB hC, integral_sub hAint hB, integral_const_mul,
      integral_const_mul, integral_inner (𝕜 := ℝ) hwint, integral_inner (𝕜 := ℝ) hzint, hint_eq]
    ring
  -- pointwise lower bound
  have hlow : ∀ ξ, ⟪ξ, zsel (T ξ)⟫_ℝ - 2 * ⟪ζ, zsel (T ξ)⟫_ℝ + 2 * ⟪ζ, zsel ξ⟫_ℝ
      ≤ lossL Z zsel ξ ζ := by
    intro ξ
    have h1 : ⟪ξ - (2 : ℝ) • ζ, zsel (T ξ)⟫_ℝ ≤ SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ) :=
      PDScenRedMeanAux.le_xi hR (hsel _).1 _
    rw [inner_sub_left, real_inner_smul_left] at h1
    have h2 : ⟪zsel ξ, ζ⟫_ℝ = ⟪ζ, zsel ξ⟫_ℝ := real_inner_comm _ _
    show _ ≤ max (SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ)) 0 + 2 * max ⟪zsel ξ, ζ⟫_ℝ 0
    have h3 := le_max_left (SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ)) 0
    have h4 := le_max_left ⟪zsel ξ, ζ⟫_ℝ 0
    linarith
  -- a.e. equality at the mean
  have hnull : μ {ξ | ¬ (0 ≤ SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • m))} = 0 := by
    refine measure_mono_null (t := T ⁻¹' (Uset Z)ᶜ) ?_ ?_
    · intro ξ hξ
      simp only [Set.mem_ofPred_eq, not_le] at hξ
      simp only [Set.mem_preimage, Set.mem_compl_iff, Uset, Set.mem_ofPred_eq, not_lt]
      have e1 := PDScenRedMeanAux.zstar_of_mem_Wstar (hsel (T ξ))
      have e2 := PDScenRedMeanAux.xi_neg_of_mem_Wstar hR (hsel (T ξ))
      have e3 : -(T ξ) = ξ - (2 : ℝ) • m := by rw [hTapp]; abel
      rw [inner_neg_left, e3] at e2
      rw [e1]
      linarith
    · rw [← T.map_apply, hmap]
      exact hU
  have hae : ∀ᵐ ξ ∂μ, lossL Z zsel ξ m
      = ⟪ξ, zsel (T ξ)⟫_ℝ - 2 * ⟪m, zsel (T ξ)⟫_ℝ + 2 * ⟪m, zsel ξ⟫_ℝ := by
    filter_upwards [ae_iff.mpr hnull] with ξ hξ
    show max (SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • m)) 0 + 2 * max ⟪zsel ξ, m⟫_ℝ 0 = _
    have e2 := PDScenRedMeanAux.xi_neg_of_mem_Wstar hR (hsel (T ξ))
    have e3 : -(T ξ) = ξ - (2 : ℝ) • m := by rw [hTapp]; abel
    rw [e3, inner_sub_left, real_inner_smul_left] at e2
    have hp : 0 ≤ ⟪zsel ξ, m⟫_ℝ := by
      have := (hsel m).2 (zsel ξ) (hsel ξ).1
      have h1 : ⟪zsel m, m⟫_ℝ = ⟪m, zsel m⟫_ℝ := real_inner_comm _ _
      have h2 : ⟪zsel ξ, m⟫_ℝ = ⟪m, zsel ξ⟫_ℝ := real_inner_comm _ _
      linarith
    rw [max_eq_left hξ, max_eq_left hp, e2, real_inner_comm m (zsel ξ)]
  -- integrability of the loss
  have hxic := PDScenRedMeanAux.xi_cont hne hR hR0
  have hLint : Integrable (fun ξ => lossL Z zsel ξ ζ) μ := by
    have hmeasL : Measurable (fun ξ => lossL Z zsel ξ ζ) := by
      show Measurable (fun ξ =>
        max (SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ)) 0 + 2 * max ⟪zsel ξ, ζ⟫_ℝ 0)
      exact ((hxic.measurable.comp (measurable_id.sub_const _)).max measurable_const).add
        (measurable_const.mul ((hmeas.inner measurable_const).max measurable_const))
    refine Integrable.mono'
      (((hint.sub (integrable_const ((2 : ℝ) • ζ))).norm.const_mul R).add
        (integrable_const (2 * (R * ‖ζ‖)))) hmeasL.aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    show ‖max (SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ)) 0 + 2 * max ⟪zsel ξ, ζ⟫_ℝ 0‖ ≤
      R * ‖ξ - (2 : ℝ) • ζ‖ + 2 * (R * ‖ζ‖)
    have hx := PDScenRedMeanAux.xi_le hne hR (ξ - (2 : ℝ) • ζ)
    have hi : ⟪zsel ξ, ζ⟫_ℝ ≤ R * ‖ζ‖ := by
      calc ⟪zsel ξ, ζ⟫_ℝ ≤ ‖zsel ξ‖ * ‖ζ‖ := real_inner_le_norm _ _
        _ ≤ R * ‖ζ‖ := mul_le_mul_of_nonneg_right (hR _ (hsel ξ).1) (norm_nonneg _)
    have hn1 : 0 ≤ R * ‖ξ - (2 : ℝ) • ζ‖ := mul_nonneg hR0 (norm_nonneg _)
    have hn2 : 0 ≤ R * ‖ζ‖ := mul_nonneg hR0 (norm_nonneg _)
    rw [Real.norm_of_nonneg (add_nonneg (le_max_right _ _)
      (mul_nonneg two_pos.le (le_max_right _ _)))]
    have := max_le hx hn1
    have := max_le hi hn2
    linarith
  have hGint : Integrable (fun ξ =>
      ⟪ξ, zsel (T ξ)⟫_ℝ - 2 * ⟪ζ, zsel (T ξ)⟫_ℝ + 2 * ⟪ζ, zsel ξ⟫_ℝ) μ :=
    (hAint.sub ((hwint.const_inner (𝕜 := ℝ) ζ).const_mul 2)).add
      ((hzint.const_inner (𝕜 := ℝ) ζ).const_mul 2)
  refine ⟨?_, ?_⟩
  · unfold upperBoundObj
    rw [integral_congr_ae hae, hG m, ← hG ζ]
    exact integral_mono hGint hLint hlow
  · unfold wassersteinOneObj
    by_cases hfin : ∫⁻ ξ, ENNReal.ofReal (‖ξ - ζ‖ ^ (2 : ℕ)) ∂μ = ⊤
    · rw [hfin]; exact le_top
    have hf : Integrable (fun ξ => ‖ξ - ζ‖ ^ (2 : ℕ)) μ :=
      ⟨((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => by positivity)).2
          (lt_top_iff_ne_top.2 hfin)⟩
    have key : ∀ ξ : EuclideanSpace ℝ (Fin d), ‖ξ - ζ‖ ^ (2 : ℕ) =
        ‖ξ - m‖ ^ (2 : ℕ) - 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ) + ‖ζ - m‖ ^ (2 : ℕ) := by
      intro ξ
      rw [show ξ - ζ = (ξ - m) - (ζ - m) by abel, norm_sub_sq_real,
        real_inner_comm (ζ - m) (ξ - m), inner_sub_right]
    have hv : Integrable (fun ξ => ⟪ζ - m, ξ⟫_ℝ) μ := hint.const_inner (𝕜 := ℝ) (ζ - m)
    have hg : Integrable (fun ξ => ‖ξ - m‖ ^ (2 : ℕ)) μ := by
      have hv2 : Integrable (fun ξ => 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ)) μ :=
        (hv.sub (integrable_const _)).const_mul 2
      have h1 : Integrable (fun ξ => ‖ξ - ζ‖ ^ (2 : ℕ) + 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ)
          - ‖ζ - m‖ ^ (2 : ℕ)) μ := (hf.add hv2).sub (integrable_const _)
      refine h1.congr (ae_of_all _ fun ξ => ?_)
      show ‖ξ - ζ‖ ^ (2 : ℕ) + 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ) - ‖ζ - m‖ ^ (2 : ℕ)
        = ‖ξ - m‖ ^ (2 : ℕ)
      rw [key ξ]; ring
    rw [← ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ fun _ => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hfun : (fun ξ : EuclideanSpace ℝ (Fin d) => ‖ξ - ζ‖ ^ (2 : ℕ)) =
        fun ξ => ‖ξ - m‖ ^ (2 : ℕ) - 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ) + ‖ζ - m‖ ^ (2 : ℕ) :=
      funext key
    have hI : ∫ ξ, (‖ξ - m‖ ^ (2 : ℕ) - 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ) +
        ‖ζ - m‖ ^ (2 : ℕ)) ∂μ = ∫ ξ, ‖ξ - m‖ ^ (2 : ℕ) ∂μ + ‖ζ - m‖ ^ (2 : ℕ) := by
      have hv2 : Integrable (fun ξ => 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ)) μ :=
        (hv.sub (integrable_const _)).const_mul 2
      have hgv : Integrable (fun ξ => ‖ξ - m‖ ^ (2 : ℕ) - 2 * (⟪ζ - m, ξ⟫_ℝ - ⟪ζ - m, m⟫_ℝ)) μ :=
        hg.sub hv2
      rw [integral_add hgv (integrable_const _), integral_sub hg hv2, integral_const_mul,
        integral_sub hv (integrable_const _), integral_inner (𝕜 := ℝ) hint, ← hm]
      simp
    rw [hfun, hI]
    linarith [sq_nonneg ‖ζ - m‖]
