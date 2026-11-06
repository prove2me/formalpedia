-- Prove2me | solution 1 for OTDRO.Cvx.dual_proper_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:29:21.857842+00:00
-- url     : https://prove2.me/submissions/e41ffe0e-2da0-44a8-9fae-33e6e971a827

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Theorems.Thm_OTDRO_Cvx_ellRob_convex

open MeasureTheory Matrix

namespace OTDROCvxAux

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma ext_mono_ae {φ ψ : X → EReal} (h : ∀ᵐ x ∂μ, φ x ≤ ψ x) :
    ModelRiskOT.Duality.extIntegral μ φ ≤ ModelRiskOT.Duality.extIntegral μ ψ := by
  unfold ModelRiskOT.Duality.extIntegral
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono_ae (h.mono fun x hx => EReal.toENNReal_le_toENNReal hx))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono_ae (h.mono fun x hx => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 hx)))

lemma toENNReal_coe_real (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

lemma ext_coe {g : X → ℝ} (hg : Integrable g μ) :
    ModelRiskOT.Duality.extIntegral μ (fun x => (g x : EReal)) = ((∫ x, g x ∂μ : ℝ) : EReal) := by
  unfold ModelRiskOT.Duality.extIntegral
  have h2 : ∀ x, (-(g x : EReal)).toENNReal = ENNReal.ofReal (-g x) := fun x => by
    rw [← EReal.coe_neg, toENNReal_coe_real]
  simp only [toENNReal_coe_real, h2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg, EReal.coe_sub,
    EReal.coe_ennreal_toReal hg.lintegral_lt_top.ne,
    EReal.coe_ennreal_toReal (x := ∫⁻ a, ENNReal.ofReal (-g a) ∂μ) hg.neg.lintegral_lt_top.ne]

lemma ext_ne_bot {φ : X → EReal} {h : X → ℝ} (hh : Integrable h μ)
    (hle : ∀ x, (h x : EReal) ≤ φ x) :
    ModelRiskOT.Duality.extIntegral μ φ ≠ ⊥ := by
  unfold ModelRiskOT.Duality.extIntegral
  have hb : ∫⁻ x, (-φ x).toENNReal ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hh.neg.lintegral_lt_top.ne (lintegral_mono fun x => ?_)
    calc (-φ x).toENNReal ≤ (-(h x : EReal)).toENNReal :=
          EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hle x))
      _ = ENNReal.ofReal (-h x) := by rw [← EReal.coe_neg, toENNReal_coe_real]
  rw [← EReal.coe_ennreal_toReal hb, sub_eq_add_neg, ← EReal.coe_neg]
  exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ennreal_ne_bot _, EReal.coe_ne_bot _⟩

lemma ext_ne_top {φ : X → EReal} {g : X → ℝ} (hg : Integrable g μ)
    (hle : ∀ᵐ x ∂μ, φ x ≤ (g x : EReal)) :
    ModelRiskOT.Duality.extIntegral μ φ ≠ ⊤ := by
  unfold ModelRiskOT.Duality.extIntegral
  have ha : ∫⁻ x, (φ x).toENNReal ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hg.lintegral_lt_top.ne (lintegral_mono_ae (hle.mono fun x hx => ?_))
    exact (EReal.toENNReal_le_toENNReal hx).trans_eq (toENNReal_coe_real _)
  rw [← EReal.coe_ennreal_toReal ha, sub_eq_add_neg]
  refine EReal.add_ne_top (EReal.coe_ne_top _) ?_
  rw [Ne, EReal.neg_eq_top_iff]
  exact EReal.coe_ennreal_ne_bot _

/-- If `φ ≥ h` with `h` integrable, `φ` a.e.-measurable and `extIntegral φ ≠ ⊤`, then `φ` is a.e.
finite, its real part is integrable and `extIntegral φ = ∫ φ.toReal`. -/
lemma ext_eq_integral {φ : X → EReal} {h : X → ℝ} (hh : Integrable h μ)
    (hle : ∀ x, (h x : EReal) ≤ φ x) (hm : AEMeasurable φ μ)
    (htop : ModelRiskOT.Duality.extIntegral μ φ ≠ ⊤) :
    (∀ᵐ x ∂μ, φ x ≠ ⊤) ∧ Integrable (fun x => (φ x).toReal) μ ∧
      ModelRiskOT.Duality.extIntegral μ φ = ((∫ x, (φ x).toReal ∂μ : ℝ) : EReal) := by
  have hbot : ∀ x, φ x ≠ ⊥ := fun x => ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hle x)
  have hm1 : AEMeasurable (fun x => (φ x).toENNReal) μ := measurable_ereal_toENNReal.comp_aemeasurable hm
  have ha : ∫⁻ x, (φ x).toENNReal ∂μ ≠ ⊤ := by
    intro H
    apply htop
    unfold ModelRiskOT.Duality.extIntegral
    rw [H]
    have hb : ∫⁻ x, (-φ x).toENNReal ∂μ ≠ ⊤ := by
      refine ne_top_of_le_ne_top hh.neg.lintegral_lt_top.ne (lintegral_mono fun x => ?_)
      calc (-φ x).toENNReal ≤ (-(h x : EReal)).toENNReal :=
            EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hle x))
        _ = ENNReal.ofReal (-h x) := by rw [← EReal.coe_neg, toENNReal_coe_real]
    rw [← EReal.coe_ennreal_toReal hb]
    exact EReal.top_sub_coe _
  have hfin : ∀ᵐ x ∂μ, φ x ≠ ⊤ := by
    filter_upwards [ae_lt_top' hm1 ha] with x hx H
    rw [H] at hx; simp at hx
  have hint : Integrable (fun x => (φ x).toReal) μ := by
    have hi1 : Integrable (fun x => ((φ x).toENNReal).toReal) μ :=
      integrable_toReal_of_lintegral_ne_top hm1 ha
    refine Integrable.mono' (hi1.add hh.abs) ?_ ?_
    · exact (measurable_ereal_toReal.comp_aemeasurable hm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      by_cases hT : φ x = ⊤
      · rw [hT]; simp only [EReal.toReal_top, norm_zero, Pi.add_apply]; positivity
      · obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = r := ⟨(φ x).toReal, (EReal.coe_toReal hT (hbot x)).symm⟩
        have hx : h x ≤ r := by have := hle x; rw [hr] at this; exact EReal.coe_le_coe_iff.1 this
        simp only [Pi.add_apply, hr, EReal.toReal_coe, Real.norm_eq_abs]
        rw [toENNReal_coe_real, ENNReal.toReal_ofReal']
        rcases le_or_gt 0 r with h0 | h0
        · rw [abs_of_nonneg h0, max_eq_left h0]; linarith [abs_nonneg (h x)]
        · rw [abs_of_neg h0, max_eq_right h0.le]; linarith [neg_abs_le (h x)]
  refine ⟨hfin, hint, ?_⟩
  have hae : ∀ᵐ x ∂μ, φ x = ((φ x).toReal : EReal) := by
    filter_upwards [hfin] with x hx using (EReal.coe_toReal hx (hbot x)).symm
  rw [← ext_coe hint]
  exact le_antisymm (ext_mono_ae (hae.mono fun x hx => hx.le))
    (ext_mono_ae (hae.mono fun x hx => hx.ge))


variable {d : ℕ}

lemma polar (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian) (u w : Fin d → ℝ) :
    u ⬝ᵥ (M *ᵥ w) = ((u + w) ⬝ᵥ (M *ᵥ (u + w)) - (u - w) ⬝ᵥ (M *ᵥ (u - w))) / 4 := by
  have hT : Mᵀ = M := by
    have := hM.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hsym : w ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ w) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, hT]
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub]
  rw [hsym]; ring

lemma entry_eq (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    M i j = (Pi.single i 1 : Fin d → ℝ) ⬝ᵥ (M *ᵥ Pi.single j 1) := by
  simp [mulVec, dotProduct, Pi.single_apply]

lemma measurable_quadInv
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hPD : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (β : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun x => OTDRO.Dual.quadInv A β x) := by
  have hq : ∀ v : Fin d → ℝ, Measurable (fun x => v ⬝ᵥ (A x *ᵥ v)) := by
    intro v
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => (x, x - WithLp.toLp 2 v)) :=
      continuous_id.prodMk (continuous_id.sub continuous_const)
    have := (hlsc.comp hc).measurable
    convert this using 1
    funext x
    simp [OTDRO.Dual.mahalCost]
  have hent : ∀ i j, Measurable (fun x => A x i j) := by
    intro i j
    have : (fun x => A x i j) = fun x =>
        (((Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) ⬝ᵥ (A x *ᵥ (Pi.single i 1 + Pi.single j 1))
          - (Pi.single i 1 - Pi.single j 1 : Fin d → ℝ) ⬝ᵥ
            (A x *ᵥ (Pi.single i 1 - Pi.single j 1))) / 4) := by
      funext x
      rw [entry_eq (A x) i j, polar (A x) (hPD x).1]
    rw [this]
    exact ((hq _).sub (hq _)).div_const 4
  have hc : Continuous (fun M : Fin d → Fin d → ℝ => Matrix.of M) := continuous_id
  have hG : Measurable (fun M : Fin d → Fin d → ℝ =>
      ((Matrix.of M).det)⁻¹ * (β.ofLp ⬝ᵥ ((Matrix.of M).adjugate *ᵥ β.ofLp))) := by
    refine Measurable.mul (Continuous.matrix_det hc).measurable.inv ?_
    exact (continuous_const.dotProduct
      ((Continuous.matrix_adjugate hc).matrix_mulVec continuous_const)).measurable
  have hA : Measurable (fun x => (fun i j => A x i j : Fin d → Fin d → ℝ)) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hent i j
  convert hG.comp hA using 1
  funext x
  simp only [Function.comp, OTDRO.Dual.quadInv, Matrix.inv_def, Ring.inverse_eq_inv',
    smul_mulVec, dotProduct_smul, smul_eq_mul]
  rfl


lemma measurable_ellRob
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hPD : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2)) (ℓ : ℝ → ℝ) (hℓ : Continuous ℓ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    Measurable (fun x => OTDRO.Dual.ellRob ℓ A δ β lam x) := by
  have hq := measurable_quadInv A hPD hlsc β
  have hin : Measurable (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ β x) :=
    (continuous_const.inner continuous_id).measurable
  have mf : ∀ γ : ℝ, Measurable (fun x => ((OTDRO.Dual.Fobj ℓ A δ γ β lam x : ℝ) : EReal)) := by
    intro γ
    refine measurable_coe_real_ereal.comp ?_
    unfold OTDRO.Dual.Fobj
    exact (hℓ.measurable.comp (hin.add (measurable_const.mul hq))).sub
      (measurable_const.mul ((measurable_const.mul hq).sub measurable_const))
  have cf : ∀ x, LowerSemicontinuous
      (fun γ : ℝ => ((OTDRO.Dual.Fobj ℓ A δ γ β lam x : ℝ) : EReal)) := by
    intro x
    refine (continuous_coe_real_ereal.comp ?_).lowerSemicontinuous
    unfold OTDRO.Dual.Fobj
    fun_prop
  have := measurable_iSup_of_lowerSemicontinuous mf cf
  convert this using 1
  funext x
  simp [OTDRO.Dual.ellRob, iSup_apply]

lemma ell_bounds {ℓ : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ ℓ) {s C : ℝ}
    (hC : ∀ u, ℓ u - s * u ^ 2 ≤ C) (u : ℝ) :
    ℓ u ≤ C + s * u ^ 2 ∧ 2 * ℓ 0 - C - s * u ^ 2 ≤ ℓ u := by
  refine ⟨by linarith [hC u], ?_⟩
  have h := hc.2 (Set.mem_univ u) (Set.mem_univ (-u)) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1 / 2 * u + 1 / 2 * -u = 0 := by ring
  rw [e] at h
  have := hC (-u)
  rw [neg_sq] at this
  linarith

end OTDROCvxAux

open OTDROCvxAux in
theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ρmin ρmax : ℝ)
    (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (h2 : OTDRO.Dual.Assumption2 P0 ℓ) :
    (∀ β ∈ B, ∀ lam : ℝ, 0 ≤ lam → OTDRO.Dual.fDelta P0 ℓ A δ β lam ≠ ⊥) ∧
    (∀ β ∈ B, ∃ lam : ℝ, 0 ≤ lam ∧ OTDRO.Dual.fDelta P0 ℓ A δ β lam ≠ ⊤) ∧
    (∀ β₁ ∈ B, ∀ β₂ ∈ B, ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        OTDRO.Dual.fDelta P0 ℓ A δ (α • β₁ + (1 - α) • β₂) (α * lam₁ + (1 - α) * lam₂) ≤
          (α : EReal) * OTDRO.Dual.fDelta P0 ℓ A δ β₁ lam₁ +
            ((1 - α : ℝ) : EReal) * OTDRO.Dual.fDelta P0 ℓ A δ β₂ lam₂) := by
  have hℓc : Continuous ℓ := continuousOn_univ.1 (h2.convex.continuousOn isOpen_univ)
  obtain ⟨s, hs0, C, hC⟩ : ∃ s : ℝ, 0 ≤ s ∧ ∃ C : ℝ, ∀ u, ℓ u - s * u ^ 2 ≤ C := by
    obtain ⟨s, hs, C, hCm⟩ := h2.growth
    exact ⟨s, hs, C, fun u => hCm ⟨u, rfl⟩⟩
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hss : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  -- `‖X‖²` is integrable
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) P0 := by
    refine Integrable.mono' (h2.moment4.add (integrable_const 1))
      (continuous_norm.pow 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (by positivity)]
    have : ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 := by ring
    nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]
  -- the integrable lower bound `F(0, β, λ; x) = ℓ(βᵀx) + λ√δ`
  have hlow_int : ∀ (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ),
      Integrable (fun x => ℓ (inner ℝ β x) + lam * Real.sqrt δ) P0 := by
    intro β lam
    refine Integrable.add ?_ (integrable_const _)
    refine Integrable.mono' ((integrable_const (|C| + 2 * |ℓ 0|)).add
      (hsq.const_mul (s * ‖β‖ ^ 2)))
      (hℓc.comp (continuous_const.inner continuous_id)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨hu1, hu2⟩ := ell_bounds h2.convex hC (inner ℝ β x)
    have hi : (inner ℝ β x) ^ 2 ≤ ‖β‖ ^ 2 * ‖x‖ ^ 2 := by
      have := abs_real_inner_le_norm β x
      rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hi' := mul_le_mul_of_nonneg_left hi hs0
    simp only [Real.norm_eq_abs, Pi.add_apply, Function.comp]
    rw [abs_le]; constructor
    · nlinarith [le_abs_self C, neg_abs_le C, le_abs_self (ℓ 0), neg_abs_le (ℓ 0)]
    · nlinarith [le_abs_self C, neg_abs_le C, le_abs_self (ℓ 0), neg_abs_le (ℓ 0)]
  have hle_low : ∀ (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)),
      ((ℓ (inner ℝ β x) + lam * Real.sqrt δ : ℝ) : EReal) ≤ OTDRO.Dual.ellRob ℓ A δ β lam x := by
    intro β lam x
    refine le_trans (le_of_eq ?_) (le_iSup _ (0:ℝ))
    simp [OTDRO.Dual.Fobj]
  have hnb : ∀ (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ), OTDRO.Dual.fDelta P0 ℓ A δ β lam ≠ ⊥ :=
    fun β lam => ext_ne_bot (hlow_int β lam) (hle_low β lam)
  refine ⟨fun β _ lam _ => hnb β lam, ?_, ?_⟩
  · -- properness: finiteness for `λ` large
    intro β _
    have hρ := hA.rhoMin_pos
    set M := ‖β‖ ^ 2 / ρmin with hM
    set lam0 := 2 * s * Real.sqrt δ * M with hlam0
    have hM0 : 0 ≤ M := by positivity
    refine ⟨lam0, by positivity, ?_⟩
    refine ext_ne_top (g := fun x => C + 2 * s * ‖β‖ ^ 2 * ‖x‖ ^ 2 + lam0 * Real.sqrt δ)
      (((integrable_const C).add (hsq.const_mul (2 * s * ‖β‖ ^ 2))).add (integrable_const _)) ?_
    filter_upwards [hA.eig_bounds] with x hx
    apply iSup_le; intro γ
    apply EReal.coe_le_coe_iff.2
    have hunit : IsUnit (A x).det :=
      (Matrix.isUnit_iff_isUnit_det (A x)).1 (hA.posDef x).isUnit
    set w := (A x)⁻¹ *ᵥ β.ofLp with hw
    have hAw : A x *ᵥ w = β.ofLp := by
      simp [w, mulVec_mulVec, mul_nonsing_inv _ hunit]
    have hqdef : OTDRO.Dual.quadInv A β x = β.ofLp ⬝ᵥ w := rfl
    set q := OTDRO.Dual.quadInv A β x with hq
    have hv := (hx (WithLp.toLp 2 w)).1
    simp only [WithLp.ofLp_toLp, hAw] at hv
    rw [dotProduct_comm, ← hqdef] at hv
    have hqin : q = inner ℝ β (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d)) := by
      rw [hqdef, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; simp
    have hqle : q ≤ ‖β‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))‖ := by
      rw [hqin]; exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    set n := ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))‖
    have hn0 : 0 ≤ n := norm_nonneg _
    have hq0 : 0 ≤ q := le_trans (by positivity) hv
    have hqM : q ≤ M := by
      rw [hM, le_div_iff₀ hρ]
      rcases eq_or_lt_of_le hq0 with h0 | h0
      · rw [← h0, zero_mul]; positivity
      · have h1 : q ^ 2 ≤ ‖β‖ ^ 2 * n ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ hq0 hqle 2
        nlinarith
    unfold OTDRO.Dual.Fobj
    rw [← hq]
    set a := inner ℝ β x
    set t := γ * Real.sqrt δ * q
    have hℓu := (ell_bounds h2.convex hC (a + t)).1
    have ha2 : a ^ 2 ≤ ‖β‖ ^ 2 * ‖x‖ ^ 2 := by
      have := abs_real_inner_le_norm β x
      rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h1 : s * (a + t) ^ 2 ≤ 2 * s * a ^ 2 + 2 * s * t ^ 2 := by
      nlinarith [mul_nonneg hs0 (sq_nonneg (a - t))]
    have ht2 : t ^ 2 = γ ^ 2 * δ * q ^ 2 := by
      simp only [t]; linear_combination (γ ^ 2 * q ^ 2) * hss
    have hlamq : lam0 * Real.sqrt δ * (γ ^ 2 * q) = 2 * s * δ * M * γ ^ 2 * q := by
      simp only [lam0]; linear_combination (2 * s * M * γ ^ 2 * q) * hss
    have h3 : 2 * s * δ * γ ^ 2 * q ^ 2 ≤ 2 * s * δ * M * γ ^ 2 * q := by
      have hk : 0 ≤ 2 * s * δ * γ ^ 2 * q := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hqM hk]
    have h4 := mul_le_mul_of_nonneg_left ha2 (by positivity : (0:ℝ) ≤ 2 * s)
    nlinarith
  · -- convexity
    intro β₁ hβ₁ β₂ hβ₂ lam₁ lam₂ hl₁ hl₂ α hα0 hα1
    rcases eq_or_lt_of_le hα0 with h0 | h0
    · subst h0; simp
    rcases eq_or_lt_of_le hα1 with h1 | h1
    · subst h1; simp
    have hα1' : 0 < 1 - α := by linarith
    by_cases hf1 : OTDRO.Dual.fDelta P0 ℓ A δ β₁ lam₁ = ⊤
    · rw [hf1, EReal.coe_mul_top_of_pos h0, EReal.top_add_of_ne_bot]
      · exact le_top
      · exact (EReal.mul_ne_bot _ _).2 ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hnb _ _),
          Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.2 hα1'.le)⟩
    by_cases hf2 : OTDRO.Dual.fDelta P0 ℓ A δ β₂ lam₂ = ⊤
    · rw [hf2, EReal.coe_mul_top_of_pos hα1', EReal.add_top_of_ne_bot]
      · exact le_top
      · exact (EReal.mul_ne_bot _ _).2 ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hnb _ _),
          Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.2 h0.le)⟩
    have hm : ∀ (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ),
        AEMeasurable (fun x => OTDRO.Dual.ellRob ℓ A δ β lam x) P0 :=
      fun β lam => (measurable_ellRob A hA.posDef hA.lsc ℓ hℓc δ β lam).aemeasurable
    obtain ⟨hfin1, hint1, heq1⟩ := ext_eq_integral (hlow_int β₁ lam₁) (hle_low β₁ lam₁)
      (hm β₁ lam₁) hf1
    obtain ⟨hfin2, hint2, heq2⟩ := ext_eq_integral (hlow_int β₂ lam₂) (hle_low β₂ lam₂)
      (hm β₂ lam₂) hf2
    have hcv := OTDRO.Cvx.ellRob_convex A hA.posDef hA.lsc ℓ h2.convex δ hδ B hB
    calc OTDRO.Dual.fDelta P0 ℓ A δ (α • β₁ + (1 - α) • β₂) (α * lam₁ + (1 - α) * lam₂)
        ≤ ModelRiskOT.Duality.extIntegral P0 (fun x =>
            ((α * (OTDRO.Dual.ellRob ℓ A δ β₁ lam₁ x).toReal +
              (1 - α) * (OTDRO.Dual.ellRob ℓ A δ β₂ lam₂ x).toReal : ℝ) : EReal)) := by
          apply ext_mono_ae
          filter_upwards [hfin1, hfin2] with x hx1 hx2
          have hb1 := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hle_low β₁ lam₁ x)
          have hb2 := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hle_low β₂ lam₂ x)
          refine (hcv x β₁ hβ₁ β₂ hβ₂ lam₁ lam₂ hl₁ hl₂ α hα0 hα1).trans (le_of_eq ?_)
          rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hx1 hb1,
            EReal.coe_toReal hx2 hb2]
      _ = (((α * ∫ x, (OTDRO.Dual.ellRob ℓ A δ β₁ lam₁ x).toReal ∂P0) +
            (1 - α) * ∫ x, (OTDRO.Dual.ellRob ℓ A δ β₂ lam₂ x).toReal ∂P0 : ℝ) : EReal) := by
          have hI : Integrable (fun x => α * (OTDRO.Dual.ellRob ℓ A δ β₁ lam₁ x).toReal +
              (1 - α) * (OTDRO.Dual.ellRob ℓ A δ β₂ lam₂ x).toReal) P0 :=
            (hint1.const_mul α).add (hint2.const_mul (1 - α))
          rw [ext_coe hI,
            integral_add (hint1.const_mul α) (hint2.const_mul (1 - α)),
            integral_const_mul, integral_const_mul]
      _ = _ := by
          rw [show OTDRO.Dual.fDelta P0 ℓ A δ β₁ lam₁ = _ from heq1,
            show OTDRO.Dual.fDelta P0 ℓ A δ β₂ lam₂ = _ from heq2,
            EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
