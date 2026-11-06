-- Prove2me | solution 1 for OTDRO.Statics.worst_case_comparative_statics
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:30:29.255481+00:00
-- url     : https://prove2.me/submissions/21ec8f12-bcc2-4b75-969c-38921e4e2e94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions
import Definitions.Def_OTDRO_Statics_Transport
import Theorems.Thm_OTDRO_Statics_dual_optimizer_unique
import Theorems.Thm_OTDRO_Statics_worst_case_unique_monge
import Theorems.Thm_OTDRO_Statics_maximizer_sign

open MeasureTheory Matrix

namespace SolWCStat

/-- The rescaled objective `H μ v = ℓ(a + v q) - μ v² q`. -/
noncomputable def H (ℓ : ℝ → ℝ) (a q μ v : ℝ) : ℝ := ℓ (a + v * q) - μ * v ^ 2 * q

lemma comp_A (ℓ : ℝ → ℝ) (a q μ μ' u u' : ℝ) (hq : 0 < q)
    (hu : ∀ v, H ℓ a q μ v ≤ H ℓ a q μ u) (hu' : ∀ v, H ℓ a q μ' v ≤ H ℓ a q μ' u')
    (hμ : μ' < μ) : u ^ 2 ≤ u' ^ 2 := by
  by_contra h
  replace h := lt_of_not_ge h
  have h1 := hu u'
  have h2 := hu' u
  unfold H at h1 h2
  have : 0 < (μ - μ') * q * (u ^ 2 - u' ^ 2) := by
    apply mul_pos (mul_pos (by linarith) hq) (by linarith)
  nlinarith

lemma comp_B (ℓ : ℝ → ℝ) (a q μ μ' u u' : ℝ) (hq : 0 < q)
    (huniq : ∀ w, (∀ v, H ℓ a q μ v ≤ H ℓ a q μ w) → w = u)
    (hu : ∀ v, H ℓ a q μ v ≤ H ℓ a q μ u) (hu' : ∀ v, H ℓ a q μ' v ≤ H ℓ a q μ' u')
    (hμ : μ ≤ μ') : u' ^ 2 ≤ u ^ 2 := by
  by_contra h
  replace h := lt_of_not_ge h
  have hmax : ∀ v, H ℓ a q μ v ≤ H ℓ a q μ u' := by
    intro v
    have h1 := hu v
    have h2 := hu' u
    unfold H at h1 h2 ⊢
    have : 0 ≤ (μ' - μ) * q * (u' ^ 2 - u ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) hq.le) (by linarith)
    nlinarith
  have := huniq u' hmax
  subst this
  exact lt_irrefl _ h

lemma comp_C (ℓ : ℝ → ℝ) (hℓ : Differentiable ℝ ℓ) (a q μ μ' u : ℝ) (hq : 0 < q)
    (hu : ∀ v, H ℓ a q μ v ≤ H ℓ a q μ u) (hu' : ∀ v, H ℓ a q μ' v ≤ H ℓ a q μ' u)
    (hμ : μ ≠ μ') : u = 0 := by
  have hd : ∀ m : ℝ, HasDerivAt (fun v => H ℓ a q m v)
      (deriv ℓ (a + u * q) * q - m * (2 * u) * q) u := by
    intro m
    have h1 : HasDerivAt (fun v => a + v * q) q u := by
      simpa using ((hasDerivAt_id u).mul_const q).const_add a
    have h2 : HasDerivAt (fun v => ℓ (a + v * q)) (deriv ℓ (a + u * q) * q) u :=
      (hℓ _).hasDerivAt.comp u h1
    have h3 : HasDerivAt (fun v : ℝ => m * v ^ 2 * q) (m * (2 * u) * q) u := by
      have := ((hasDerivAt_pow 2 u).const_mul m).mul_const q
      simpa using this
    exact h2.sub h3
  have e1 := IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hu) (hd μ)
  have e2 := IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hu') (hd μ')
  have : (μ - μ') * (2 * u * q) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hμ
  · rcases mul_eq_zero.mp h with h | h
    · linarith
    · linarith


open OTDRO.Statics in
lemma quadInv_pos {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (β x : EuclideanSpace ℝ (Fin d)) (hA : (A x).PosDef) (hβ : β ≠ 0) :
    0 < OTDRO.Dual.quadInv A β x := by
  have hb : β.ofLp ≠ 0 := by
    intro h; apply hβ; simpa using congrArg (WithLp.toLp 2) h
  have := (hA.inv).dotProduct_mulVec_pos hb
  simpa [OTDRO.Dual.quadInv] using this

lemma Fobj_eq {d : ℕ} (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ γ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    OTDRO.Dual.Fobj ℓ A δ γ β lam x =
      H ℓ (inner ℝ β x) (OTDRO.Dual.quadInv A β x) (lam / Real.sqrt δ) (γ * Real.sqrt δ)
        + lam * Real.sqrt δ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hss : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  unfold OTDRO.Dual.Fobj H
  have e : inner ℝ β x + γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x =
      inner ℝ β x + γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x := rfl
  rw [show γ * Real.sqrt δ * OTDRO.Dual.quadInv A β x
      = (γ * Real.sqrt δ) * OTDRO.Dual.quadInv A β x from rfl]
  field_simp
  ring

lemma max_to_H {d : ℕ} (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (g : ℝ) (hg : g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x) :
    ∀ v, H ℓ (inner ℝ β x) (OTDRO.Dual.quadInv A β x) (lam / Real.sqrt δ) v ≤
      H ℓ (inner ℝ β x) (OTDRO.Dual.quadInv A β x) (lam / Real.sqrt δ) (g * Real.sqrt δ) := by
  intro v
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have h := hg (v / Real.sqrt δ)
  rw [Fobj_eq ℓ A δ _ hδ, Fobj_eq ℓ A δ _ hδ] at h
  rw [div_mul_cancel₀ v hs.ne'] at h
  linarith

lemma H_to_max {d : ℕ} (ℓ : ℝ → ℝ) (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (hδ : 0 < δ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (w : ℝ)
    (hw : ∀ v, H ℓ (inner ℝ β x) (OTDRO.Dual.quadInv A β x) (lam / Real.sqrt δ) v ≤
      H ℓ (inner ℝ β x) (OTDRO.Dual.quadInv A β x) (lam / Real.sqrt δ) w) :
    w / Real.sqrt δ ∈ OTDRO.Dual.maximizers ℓ A δ β lam x := by
  intro c
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  rw [Fobj_eq ℓ A δ _ hδ, Fobj_eq ℓ A δ _ hδ, div_mul_cancel₀ w hs.ne']
  linarith [hw (c * Real.sqrt δ)]

lemma cost_shift {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hA : (A x).PosDef) :
    OTDRO.Dual.mahalCost A x (OTDRO.Statics.shiftMap A δ β G x) =
      (Real.sqrt δ * G x) ^ 2 * OTDRO.Dual.quadInv A β x := by
  have hu : IsUnit (A x).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hAA : A x *ᵥ ((A x)⁻¹ *ᵥ β.ofLp) = β.ofLp := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  unfold OTDRO.Dual.mahalCost OTDRO.Statics.shiftMap OTDRO.Dual.quadInv
  simp only [sub_add_cancel_left, WithLp.ofLp_neg, WithLp.ofLp_smul, Matrix.mulVec_neg,
    Matrix.mulVec_smul, hAA, neg_dotProduct, dotProduct_neg, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [dotProduct_comm]
  ring

lemma norm_shift {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖OTDRO.Statics.shiftMap A δ β G x - x‖ =
      |Real.sqrt δ * G x| * ‖(WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp) : EuclideanSpace ℝ (Fin d))‖ := by
  unfold OTDRO.Statics.shiftMap
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

end SolWCStat

open OTDRO.Statics SolWCStat in
theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
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
    ∃ δ1 : ℝ, 0 < δ1 ∧ δ1 < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (Rβ B) M ∧
      ∃ G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ δ ∈ Set.Ioo 0 δ1,
          AEMeasurable (G δ) P0 ∧
          AEMeasurable (shiftMap A δ β (G δ)) P0 ∧
          OTDRO.WorstCase.graphCoupling P0 (shiftMap A δ β (G δ)) ∈
            ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ ∧
          ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x))
            (OTDRO.WorstCase.graphCoupling P0 (shiftMap A δ β (G δ))) =
            ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
              (fun x => ℓ (inner ℝ β x)) P0 δ ∧
          ∀ π ∈ ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ,
            ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π =
              ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
                (fun x => ℓ (inner ℝ β x)) P0 δ →
            π.map Prod.snd = P0.map (shiftMap A δ β (G δ))) ∧
        (∀ δ δ' : ℝ, 0 < δ → δ < δ' → δ' < δ1 →
          ∀ᵐ x ∂P0,
            (0 < deriv ℓ (inner ℝ β x) →
              0 < Real.sqrt δ * G δ x ∧
              Real.sqrt δ * G δ x < Real.sqrt δ' * G δ' x) ∧
            (deriv ℓ (inner ℝ β x) < 0 →
              Real.sqrt δ' * G δ' x < Real.sqrt δ * G δ x ∧
              Real.sqrt δ * G δ x < 0) ∧
            ‖shiftMap A δ β (G δ) x - x‖ ≤
              ‖shiftMap A δ' β (G δ') x - x‖) ∧
        (∀ δ ∈ Set.Ioo 0 δ1,
          ∀ᵐ x ∂P0,
            deriv ℓ (inner ℝ β x) = 0 → G δ x = 0) := by
  classical
  obtain ⟨δ1, hδ1, hδ10, hdual⟩ := OTDRO.Statics.dual_optimizer_unique P0 A ρmin ρmax hA ℓ h2
    B hB hB4 hBne M h3 h5 Llow Lbar hL β hβB hβ
  have hlamEx : ∀ δ ∈ Set.Ioo 0 δ1, ∃ lam : ℝ, 0 ≤ lam ∧
      IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam :=
    fun δ hδ => (hdual δ hδ).1.exists
  let lamS : ℝ → ℝ := fun δ =>
    if h : δ ∈ Set.Ioo 0 δ1 then Classical.choose (hlamEx δ h) else 0
  have hlamS : ∀ δ (h : δ ∈ Set.Ioo 0 δ1), 0 ≤ lamS δ ∧
      IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) (lamS δ) ∧
      OTDRO.Dual.lamThr' P0 A M δ β < lamS δ := by
    intro δ h
    have e : lamS δ = Classical.choose (hlamEx δ h) := dif_pos h
    have hs := Classical.choose_spec (hlamEx δ h)
    rw [e]
    exact ⟨hs.1, hs.2, (hdual δ h).2 _ hs.1 hs.2⟩
  have hmonge := fun δ (h : δ ∈ Set.Ioo 0 δ1) =>
    OTDRO.Statics.worst_case_unique_monge P0 A ρmin ρmax hA ℓ h2 δ h.1 B hB M h3 β hβB hβ
      (lamS δ) (hlamS δ h).1 (hlamS δ h).2.1 (hlamS δ h).2.2
  let G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun δ =>
    if h : δ ∈ Set.Ioo 0 δ1 then Classical.choose (hmonge δ h) else fun _ => 0
  have hGspec := fun δ (h : δ ∈ Set.Ioo 0 δ1) => by
    have e : G δ = Classical.choose (hmonge δ h) := dif_pos h
    have hs := Classical.choose_spec (hmonge δ h)
    rw [← e] at hs
    exact hs
  have hsign := fun δ (h : δ ∈ Set.Ioo 0 δ1) =>
    OTDRO.Statics.maximizer_sign P0 A ρmin ρmax hA ℓ h2 δ h.1 B hB hB4 hBne M h3 Llow Lbar hL
      (lt_trans h.2 hδ10) β hβB hβ (lamS δ) (hlamS δ h).1 (hlamS δ h).2.1 (G δ) (hGspec δ h).2.2.1
  have hmeasC : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hA.lsc.measurable
  have hcost : ∀ δ (h : δ ∈ Set.Ioo 0 δ1),
      ∫⁻ x, ENNReal.ofReal ((G δ x * Real.sqrt δ) ^ 2 * OTDRO.Dual.quadInv A β x) ∂P0
        = ENNReal.ofReal δ := by
    intro δ h
    have hc := (hGspec δ h).2.2.2.2.2.2
    unfold OTDRO.WorstCase.graphCoupling at hc
    have hpair : AEMeasurable (fun x => (x, shiftMap A δ β (G δ) x)) P0 :=
      aemeasurable_id'.prodMk (hGspec δ h).2.1
    rw [lintegral_map' hmeasC.aemeasurable hpair] at hc
    rw [← hc]
    refine lintegral_congr fun x => ?_
    rw [cost_shift A δ β (G δ) x (hA.posDef x), mul_comm (G δ x)]
  refine ⟨δ1, hδ1, hδ10, G, ?_, ?_, ?_⟩
  · intro δ h
    obtain ⟨h1, h2, _, h4, h5, h6, _⟩ := hGspec δ h
    exact ⟨h1, h2, h4, h5, h6⟩
  · intro δ δ' hδ hδδ' hδ'
    have hI : δ ∈ Set.Ioo 0 δ1 := ⟨hδ, by linarith⟩
    have hI' : δ' ∈ Set.Ioo 0 δ1 := ⟨by linarith, hδ'⟩
    have hδ'0 : 0 < δ' := by linarith
    set μ := lamS δ / Real.sqrt δ with hμ
    set μ' := lamS δ' / Real.sqrt δ' with hμ'
    have hsing := (hGspec δ hI).2.2.1
    have hsing' := (hGspec δ' hI').2.2.1
    have hq : ∀ x, 0 < OTDRO.Dual.quadInv A β x := fun x => quadInv_pos A β x (hA.posDef x) hβ
    -- Step 1: the rescaled multiplier strictly decreases.
    have hμlt : μ' < μ := by
      by_contra hle
      replace hle := le_of_not_gt hle
      have hae : ∀ᵐ x ∂P0,
          ENNReal.ofReal ((G δ' x * Real.sqrt δ') ^ 2 * OTDRO.Dual.quadInv A β x) ≤
          ENNReal.ofReal ((G δ x * Real.sqrt δ) ^ 2 * OTDRO.Dual.quadInv A β x) := by
        filter_upwards [hsing, hsing'] with x hx hx'
        have hu := max_to_H ℓ A δ hδ β (lamS δ) x (G δ x) (by rw [hx]; rfl)
        have hu' := max_to_H ℓ A δ' hδ'0 β (lamS δ') x (G δ' x) (by rw [hx']; rfl)
        have huniq : ∀ w, (∀ v, H ℓ (inner ℝ β x) (OTDRO.Dual.quadInv A β x) μ v ≤
            H ℓ (inner ℝ β x) (OTDRO.Dual.quadInv A β x) μ w) → w = G δ x * Real.sqrt δ := by
          intro w hw
          have hm := H_to_max ℓ A δ hδ β (lamS δ) x w hw
          rw [hx] at hm
          have hm' : w / Real.sqrt δ = G δ x := hm
          rw [← hm', div_mul_cancel₀ w (Real.sqrt_pos.mpr hδ).ne']
        have := comp_B ℓ _ _ μ μ' _ _ (hq x) huniq hu hu' hle
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right this (hq x).le
      have := lintegral_mono_ae hae
      rw [hcost δ hI, hcost δ' hI'] at this
      rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at this
      linarith
    have hμne : μ ≠ μ' := ne_of_gt hμlt
    filter_upwards [hsing, hsing', hsign δ hI, hsign δ' hI'] with x hx hx' hs hs'
    have hu := max_to_H ℓ A δ hδ β (lamS δ) x (G δ x) (by rw [hx]; rfl)
    have hu' := max_to_H ℓ A δ' hδ'0 β (lamS δ') x (G δ' x) (by rw [hx']; rfl)
    have hsq := comp_A ℓ _ _ μ μ' _ _ (hq x) hu hu' hμlt
    have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    have hsd' : 0 < Real.sqrt δ' := Real.sqrt_pos.mpr hδ'0
    have hneq : G δ x * Real.sqrt δ ≠ 0 →
        G δ x * Real.sqrt δ ≠ G δ' x * Real.sqrt δ' := by
      intro h0 heq
      rw [← heq] at hu'
      exact h0 (comp_C ℓ h3.differentiable _ _ μ μ' _ (hq x) hu hu' hμne)
    simp only [mul_comm (Real.sqrt δ) (G δ x), mul_comm (Real.sqrt δ') (G δ' x)]
    refine ⟨?_, ?_, ?_⟩
    · intro hpos
      have g1 := hs.2.1 hpos
      have g2 := hs'.2.1 hpos
      have a1 : 0 < G δ x * Real.sqrt δ := mul_pos g1 hsd
      have a2 : 0 < G δ' x * Real.sqrt δ' := mul_pos g2 hsd'
      have hle : G δ x * Real.sqrt δ ≤ G δ' x * Real.sqrt δ' := by nlinarith
      exact ⟨a1, lt_of_le_of_ne hle (hneq a1.ne')⟩
    · intro hneg
      have g1 := hs.2.2.1 hneg
      have g2 := hs'.2.2.1 hneg
      have a1 : G δ x * Real.sqrt δ < 0 := mul_neg_of_neg_of_pos g1 hsd
      have a2 : G δ' x * Real.sqrt δ' < 0 := mul_neg_of_neg_of_pos g2 hsd'
      have hle : G δ' x * Real.sqrt δ' ≤ G δ x * Real.sqrt δ := by nlinarith
      exact ⟨lt_of_le_of_ne hle (fun e => hneq a1.ne (e.symm)), a1⟩
    · rw [norm_shift, norm_shift, mul_comm (Real.sqrt δ), mul_comm (Real.sqrt δ')]
      exact mul_le_mul_of_nonneg_right (sq_le_sq.mp hsq) (norm_nonneg _)
  · intro δ h
    filter_upwards [hsign δ h] with x hx
    exact hx.2.2.2
