-- Prove2me | solution 1 for ShortWDRODual.Legendre.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:03:16.740677+00:00
-- url     : https://prove2.me/submissions/834d8768-3386-4b36-bd95-728ce56c95d4

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre RWPI.SqrtLasso

namespace WDRO1L1

variable {X : Type*} [MeasurableSpace X]

lemma ofReal_coe_eq {r : ℝ} (hr : 0 ≤ r) : ((ENNReal.ofReal r : ENNReal) : EReal) = (r : EReal) := by
  rw [EReal.coe_ennreal_ofReal, max_eq_left hr]

lemma feas_iff {x : ENNReal} {r : ℝ} (hr : 0 ≤ r) :
    ((x : ENNReal) : EReal) ≤ (r : EReal) ↔ x ≤ ENNReal.ofReal r := by
  rw [← ofReal_coe_eq hr, EReal.coe_ennreal_le_coe_ennreal_iff]

/-- Combination lemma for the concavity step. -/
lemma comb_le {a b M : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) {k1 k2 : ℝ} (hk1 : 0 < k1) (hk2 : 0 < k2)
    (h : ∀ α β : ℝ, (α : EReal) < a → (β : EReal) < b → (((k1 * α + k2 * β : ℝ)) : EReal) ≤ M) :
    (k1 : EReal) * a + (k2 : EReal) * b ≤ M := by
  -- reduce to: every real below the left side is ≤ M
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top =>
    induction b using EReal.rec with
    | bot => exact absurd rfl hb
    | top =>
      -- choose α large
      induction z using EReal.rec with
      | bot => exact bot_le
      | top => exact absurd hz (not_lt.mpr le_top)
      | coe z =>
        have := h ((|z| + 1) / k1) 0 (EReal.coe_lt_top _) (EReal.coe_lt_top _)
        refine le_trans ?_ this
        have : z ≤ k1 * ((|z| + 1) / k1) + k2 * 0 := by
          rw [mul_div_cancel₀ _ hk1.ne']; linarith [le_abs_self z]
        exact_mod_cast this
    | coe b =>
      induction z using EReal.rec with
      | bot => exact bot_le
      | top => exact absurd hz (not_lt.mpr le_top)
      | coe z =>
        have := h ((|z| + |k2 * (b - 1)| + 1) / k1) (b - 1) (EReal.coe_lt_top _)
          (by exact_mod_cast (by linarith : b - 1 < b))
        refine le_trans ?_ this
        have : z ≤ k1 * ((|z| + |k2 * (b - 1)| + 1) / k1) + k2 * (b - 1) := by
          rw [mul_div_cancel₀ _ hk1.ne']
          linarith [le_abs_self z, neg_abs_le (k2 * (b - 1))]
        exact_mod_cast this
  | coe a =>
    induction b using EReal.rec with
    | bot => exact absurd rfl hb
    | top =>
      induction z using EReal.rec with
      | bot => exact bot_le
      | top => exact absurd hz (not_lt.mpr le_top)
      | coe z =>
        have := h (a - 1) ((|z| + |k1 * (a - 1)| + 1) / k2)
          (by exact_mod_cast (by linarith : a - 1 < a)) (EReal.coe_lt_top _)
        refine le_trans ?_ this
        have : z ≤ k1 * (a - 1) + k2 * ((|z| + |k1 * (a - 1)| + 1) / k2) := by
          rw [mul_div_cancel₀ _ hk2.ne']
          linarith [le_abs_self z, neg_abs_le (k1 * (a - 1))]
        exact_mod_cast this
    | coe b =>
      induction z using EReal.rec with
      | bot => exact bot_le
      | top =>
        rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hz
        exact absurd hz (not_lt.mpr le_top)
      | coe z =>
        rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hz
        have hz' : z < k1 * a + k2 * b := by exact_mod_cast hz
        set ε := (k1 * a + k2 * b - z) / (k1 + k2) with hε
        have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
        have := h (a - ε) (b - ε) (by exact_mod_cast (by linarith : a - ε < a))
          (by exact_mod_cast (by linarith : b - ε < b))
        refine le_trans ?_ this
        have e : k1 * (a - ε) + k2 * (b - ε) = z := by
          have : (k1 + k2) * ε = k1 * a + k2 * b - z := by
            rw [hε]; field_simp
          linarith
        rw [e]

/-- the diagonal coupling -/
lemma transportCost_self (c : X → X → ENNReal) (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0) (P : Measure X) [IsProbabilityMeasure P] :
    transportCost c P P = 0 := by
  have hd : Measurable (fun x : X => (x, x)) := measurable_id.prodMk measurable_id
  apply le_antisymm _ bot_le
  unfold transportCost
  refine iInf₂_le_of_le (P.map (fun x => (x, x))) ⟨Measure.isProbabilityMeasure_map hd.aemeasurable, ?_, ?_⟩ ?_
  · rw [Measure.map_map measurable_fst hd]; simp [Function.comp_def]
  · rw [Measure.map_map measurable_snd hd]; simp [Function.comp_def]
  · rw [lintegral_map hc hd]; simp [hc0]

end WDRO1L1

open WDRO1L1

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0) :
    (∀ ρ : ℝ, 0 ≤ ρ →
      extIntegral Phat (fun x => (f x : EReal)) ≤ robustLoss c f Phat ρ) ∧
    MonotoneOn (robustLoss c f Phat) (Set.Ici 0) ∧
    (∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      ((1 - t : ℝ) : EReal) * robustLoss c f Phat a +
          ((t : ℝ) : EReal) * robustLoss c f Phat b ≤
        robustLoss c f Phat ((1 - t) * a + t * b)) := by
  have hlb : ∀ ρ : ℝ, 0 ≤ ρ →
      extIntegral Phat (fun x => (f x : EReal)) ≤ robustLoss c f Phat ρ := by
    intro ρ hρ
    unfold robustLoss
    refine le_iSup₂_of_le (f := fun (P : Measure X)
      (_ : IsProbabilityMeasure P ∧ ((transportCost c Phat P : ENNReal) : EReal) ≤ (ρ : EReal)) =>
        extIntegral P (fun x => (f x : EReal))) Phat ⟨inferInstance, ?_⟩ le_rfl
    rw [transportCost_self c hc hc0 Phat]
    simpa using hρ
  have hmono : MonotoneOn (robustLoss c f Phat) (Set.Ici 0) := by
    intro a _ b _ hab
    unfold robustLoss
    refine iSup₂_le fun P hP => le_iSup₂_of_le (f := fun (P : Measure X)
      (_ : IsProbabilityMeasure P ∧ ((transportCost c Phat P : ENNReal) : EReal) ≤ (b : EReal)) =>
        extIntegral P (fun x => (f x : EReal))) P ⟨hP.1, hP.2.trans (by exact_mod_cast hab)⟩ le_rfl
  refine ⟨hlb, hmono, ?_⟩
  intro a b t ha hb ht0 ht1
  set L := robustLoss c f Phat
  rcases ht0.lt_or_eq with ht0' | ht0'
  swap
  · subst ht0'; simp
  rcases ht1.lt_or_eq with ht1' | ht1'
  swap
  · subst ht1'; simp
  have hm0 : 0 ≤ (1 - t) * a + t * b := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  have hLa : L a ≠ ⊥ := ne_bot_of_gt (hfint.trans_le (hlb a ha))
  have hLb : L b ≠ ⊥ := ne_bot_of_gt (hfint.trans_le (hlb b hb))
  refine comb_le hLa hLb (by linarith) ht0' fun α β hα hβ => ?_
  -- pick near-optimal feasible laws
  obtain ⟨Pa, ⟨hPa, hKa⟩, hEa⟩ : ∃ P : Measure X, (IsProbabilityMeasure P ∧
      ((transportCost c Phat P : ENNReal) : EReal) ≤ (a : EReal)) ∧
      (α : EReal) < extIntegral P (fun x => (f x : EReal)) := by
    have := hα; unfold L robustLoss at this
    rw [lt_iSup_iff] at this
    obtain ⟨P, hP⟩ := this
    rw [lt_iSup_iff] at hP
    obtain ⟨h1, h2⟩ := hP
    exact ⟨P, h1, h2⟩
  obtain ⟨Pb, ⟨hPb, hKb⟩, hEb⟩ : ∃ P : Measure X, (IsProbabilityMeasure P ∧
      ((transportCost c Phat P : ENNReal) : EReal) ≤ (b : EReal)) ∧
      (β : EReal) < extIntegral P (fun x => (f x : EReal)) := by
    have := hβ; unfold L robustLoss at this
    rw [lt_iSup_iff] at this
    obtain ⟨P, hP⟩ := this
    rw [lt_iSup_iff] at hP
    obtain ⟨h1, h2⟩ := hP
    exact ⟨P, h1, h2⟩
  rw [feas_iff ha] at hKa
  rw [feas_iff hb] at hKb
  set ca := ENNReal.ofReal (1 - t) with hca
  set cb := ENNReal.ofReal t with hcb
  have hcab : ca + cb = 1 := by
    rw [hca, hcb, ← ENNReal.ofReal_add (by linarith) ht0, sub_add_cancel, ENNReal.ofReal_one]
  set P := ca • Pa + cb • Pb with hPdef
  have hPprob : IsProbabilityMeasure P := ⟨by
    rw [hPdef, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hcab]⟩
  -- feasibility of the mixture
  have hKP : transportCost c Phat P ≤ ENNReal.ofReal ((1 - t) * a + t * b) := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hKa_ne : transportCost c Phat Pa ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKa
    have hKb_ne : transportCost c Phat Pb ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKb
    have hε' : (ε : ENNReal) ≠ 0 := by exact_mod_cast hε.ne'
    obtain ⟨πa, ⟨hπa, hπa1, hπa2⟩, hπac⟩ : ∃ π : Measure (X × X),
        (IsProbabilityMeasure π ∧ π.map Prod.fst = Phat ∧ π.map Prod.snd = Pa) ∧
        ∫⁻ w, c w.1 w.2 ∂π < transportCost c Phat Pa + ε := by
      have := ENNReal.lt_add_right hKa_ne hε'
      unfold transportCost at this
      conv_lhs at this => skip
      rw [iInf_lt_iff] at this
      obtain ⟨π, hπ⟩ := this
      rw [iInf_lt_iff] at hπ
      obtain ⟨h1, h2⟩ := hπ
      exact ⟨π, h1, by unfold transportCost; exact h2⟩
    obtain ⟨πb, ⟨hπb, hπb1, hπb2⟩, hπbc⟩ : ∃ π : Measure (X × X),
        (IsProbabilityMeasure π ∧ π.map Prod.fst = Phat ∧ π.map Prod.snd = Pb) ∧
        ∫⁻ w, c w.1 w.2 ∂π < transportCost c Phat Pb + ε := by
      have := ENNReal.lt_add_right hKb_ne hε'
      unfold transportCost at this
      rw [iInf_lt_iff] at this
      obtain ⟨π, hπ⟩ := this
      rw [iInf_lt_iff] at hπ
      obtain ⟨h1, h2⟩ := hπ
      exact ⟨π, h1, by unfold transportCost; exact h2⟩
    set π := ca • πa + cb • πb
    have hπprob : IsProbabilityMeasure π := ⟨by
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
        measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hcab]⟩
    have hπ1 : π.map Prod.fst = Phat := by
      rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, hπa1, hπb1,
        ← add_smul, hcab, one_smul]
    have hπ2 : π.map Prod.snd = P := by
      rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, hπa2, hπb2]
    calc transportCost c Phat P ≤ ∫⁻ w, c w.1 w.2 ∂π := by
          unfold transportCost
          exact iInf₂_le π ⟨hπprob, hπ1, hπ2⟩
      _ = ca * ∫⁻ w, c w.1 w.2 ∂πa + cb * ∫⁻ w, c w.1 w.2 ∂πb := by
          rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]; rfl
      _ ≤ ca * (ENNReal.ofReal a + ε) + cb * (ENNReal.ofReal b + ε) := by
          gcongr
          · exact hπac.le.trans (add_le_add hKa le_rfl)
          · exact hπbc.le.trans (add_le_add hKb le_rfl)
      _ = (ca * ENNReal.ofReal a + cb * ENNReal.ofReal b) + (ca + cb) * ε := by ring
      _ = ENNReal.ofReal ((1 - t) * a + t * b) + ε := by
          rw [hcab, one_mul, ENNReal.ofReal_add (by nlinarith) (by nlinarith),
            ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul ht0, hca, hcb]
  have hfeasP : ((transportCost c Phat P : ENNReal) : EReal) ≤ (((1 - t) * a + t * b : ℝ) : EReal) :=
    (feas_iff hm0).mpr hKP
  have hLm : extIntegral P (fun x => (f x : EReal)) ≤ L ((1 - t) * a + t * b) := by
    unfold L robustLoss
    exact le_iSup₂ (f := fun (P : Measure X)
      (_ : IsProbabilityMeasure P ∧ ((transportCost c Phat P : ENNReal) : EReal) ≤
        (((1 - t) * a + t * b : ℝ) : EReal)) => extIntegral P (fun x => (f x : EReal))) P ⟨hPprob, hfeasP⟩
  refine le_trans ?_ hLm
  -- the expectation of the mixture
  unfold extIntegral at hEa hEb ⊢
  set Ap := ∫⁻ x, ((f x : EReal)).toENNReal ∂Pa
  set Am := ∫⁻ x, (-(f x : EReal)).toENNReal ∂Pa
  set Bp := ∫⁻ x, ((f x : EReal)).toENNReal ∂Pb
  set Bm := ∫⁻ x, (-(f x : EReal)).toENNReal ∂Pb
  have hPp : ∫⁻ x, ((f x : EReal)).toENNReal ∂P = ca * Ap + cb * Bp := by
    rw [hPdef, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]; rfl
  have hPm : ∫⁻ x, (-(f x : EReal)).toENNReal ∂P = ca * Am + cb * Bm := by
    rw [hPdef, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]; rfl
  rw [hPp, hPm]
  have hAm : Am ≠ ⊤ := by
    intro h; rw [h, EReal.coe_ennreal_top, EReal.sub_top] at hEa; exact not_lt_bot hEa
  have hBm : Bm ≠ ⊤ := by
    intro h; rw [h, EReal.coe_ennreal_top, EReal.sub_top] at hEb; exact not_lt_bot hEb
  have hca0 : ca ≠ 0 := by rw [hca]; exact ENNReal.ofReal_pos.mpr (by linarith) |>.ne'
  have hcb0 : cb ≠ 0 := by rw [hcb]; exact (ENNReal.ofReal_pos.mpr ht0').ne'
  have hmfin : ca * Am + cb * Bm ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAm,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBm⟩
  by_cases hAp : Ap = ⊤
  · have : ca * Ap + cb * Bp = ⊤ := by rw [hAp, ENNReal.mul_top hca0, top_add]
    rw [this, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hmfin, EReal.top_sub_coe]; exact le_top
  by_cases hBp : Bp = ⊤
  · have : ca * Ap + cb * Bp = ⊤ := by rw [hBp, ENNReal.mul_top hcb0, add_top]
    rw [this, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hmfin, EReal.top_sub_coe]; exact le_top
  -- all finite: real arithmetic
  have cv : ∀ x : ENNReal, x ≠ ⊤ → ((x : ENNReal) : EReal) = ((x.toReal : ℝ) : EReal) :=
    fun x hx => (EReal.coe_ennreal_toReal hx).symm
  rw [cv _ hAp, cv _ hAm, ← EReal.coe_sub] at hEa
  rw [cv _ hBp, cv _ hBm, ← EReal.coe_sub] at hEb
  have hpfin : ca * Ap + cb * Bp ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAp,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBp⟩
  rw [cv _ hpfin, cv _ hmfin, ← EReal.coe_sub]
  have hEa' : α < Ap.toReal - Am.toReal := by exact_mod_cast hEa
  have hEb' : β < Bp.toReal - Bm.toReal := by exact_mod_cast hEb
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAp)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBp),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAm)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBm),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ht0]
  have h1t : 0 < 1 - t := by linarith
  exact_mod_cast (by nlinarith :
    (1 - t) * α + t * β ≤ (1 - t) * Ap.toReal + t * Bp.toReal - ((1 - t) * Am.toReal + t * Bm.toReal))
