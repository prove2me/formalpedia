-- Prove2me | solution 1 for ShortWDRODual.Legendre.theorem_1_hard
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:00:07.722545+00:00
-- url     : https://prove2.me/submissions/26982620-8f50-404e-8063-c07b80dc0fee

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting
import Theorems.Thm_ShortWDRODual_Legendre_lemma_1
import Theorems.Thm_ShortWDRODual_Legendre_softValue_eq_couplingSup

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre RWPI.SqrtLasso

namespace WDRO1Hard

lemma coe_conv (t x z : ℝ) :
    ((1 - t : ℝ) : EReal) * (x : EReal) + ((t : ℝ) : EReal) * (z : EReal) =
      (((1 - t) * x + t * z : ℝ) : EReal) := by
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]

lemma real_of {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : e = ((e.toReal : ℝ) : EReal) :=
  (EReal.coe_toReal h1 h2).symm

/-- three-slope inequality for a concave function: `r' < ρ < r`. -/
lemma concave_slope {r' ρ r A M B : ℝ} (h1 : r' < ρ) (h2 : ρ < r)
    (h : (1 - (ρ - r') / (r - r')) * A + ((ρ - r') / (r - r')) * B ≤ M) :
    (B - M) * (ρ - r') ≤ (M - A) * (r - ρ) := by
  have hrr : 0 < r - r' := by linarith
  have e1 : (1 - (ρ - r') / (r - r')) = (r - ρ) / (r - r') := by field_simp; ring
  rw [e1] at h
  have h' : (r - ρ) * A + (ρ - r') * B ≤ M * (r - r') := by
    have := mul_le_mul_of_nonneg_right h hrr.le
    have e2 : ((r - ρ) / (r - r') * A + (ρ - r') / (r - r') * B) * (r - r')
        = (r - ρ) * A + (ρ - r') * B := by field_simp
    linarith
  nlinarith

end WDRO1Hard

open WDRO1Hard

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (ρ : ℝ) (hρ : 0 < ρ) :
    IsLeast
      {y : EReal | ∃ lam : ℝ, 0 ≤ lam ∧
        y = ((lam * ρ : ℝ) : EReal) + ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam)}
      (robustLoss c f Phat ρ) := by
  obtain ⟨hlb, hmono, hconc⟩ := lemma_1 Phat f c hf hfint hc hc0
  set L := robustLoss c f Phat with hL
  have hsoft : ∀ lam : ℝ, 0 ≤ lam →
      (⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam)) = softValue c f Phat lam :=
    fun lam h => (softValue_eq_couplingSup Phat f c hf hfint hc hc0 lam h).symm
  -- weak duality: `𝓛(ρ) ≤ λρ + (P-soft)(λ)`
  have hweak : ∀ lam : ℝ, 0 ≤ lam → L ρ ≤ ((lam * ρ : ℝ) : EReal) + softValue c f Phat lam := by
    intro lam hlam
    rw [hL]; unfold robustLoss
    refine iSup₂_le fun P hP => ?_
    obtain ⟨hPp, hK⟩ := hP
    have hKtop : transportCost c Phat P ≠ ⊤ := by
      intro h
      rw [h, EReal.coe_ennreal_top] at hK
      exact absurd hK (not_le.mpr (EReal.coe_lt_top ρ))
    have hKr : ((transportCost c Phat P).toReal : EReal) = (transportCost c Phat P : EReal) :=
      EReal.coe_ennreal_toReal hKtop
    have hKle : (transportCost c Phat P).toReal ≤ ρ := by
      rw [← hKr] at hK
      exact_mod_cast hK
    have h1 : extIntegral P (fun x => (f x : EReal)) -
        ((lam * (transportCost c Phat P).toReal : ℝ) : EReal) ≤ softValue c f Phat lam := by
      unfold softValue
      exact le_iSup₂ (f := fun (P : Measure X) (_ : IsProbabilityMeasure P ∧ transportCost c Phat P < ⊤) =>
        extIntegral P (fun x => (f x : EReal)) -
          ((lam * (transportCost c Phat P).toReal : ℝ) : EReal)) P ⟨hPp, lt_top_iff_ne_top.mpr hKtop⟩
    calc extIntegral P (fun x => (f x : EReal))
        = extIntegral P (fun x => (f x : EReal)) -
            ((lam * (transportCost c Phat P).toReal : ℝ) : EReal) +
            ((lam * (transportCost c Phat P).toReal : ℝ) : EReal) := EReal.sub_add_cancel.symm
      _ ≤ softValue c f Phat lam + ((lam * (transportCost c Phat P).toReal : ℝ) : EReal) :=
          add_le_add h1 le_rfl
      _ ≤ softValue c f Phat lam + ((lam * ρ : ℝ) : EReal) := by
          gcongr
      _ = ((lam * ρ : ℝ) : EReal) + softValue c f Phat lam := add_comm _ _
  have hlow : ∀ y ∈ {y : EReal | ∃ lam : ℝ, 0 ≤ lam ∧
        y = ((lam * ρ : ℝ) : EReal) + ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam)},
      L ρ ≤ y := by
    rintro y ⟨lam, hlam, rfl⟩
    rw [hsoft lam hlam]
    exact hweak lam hlam
  refine ⟨?_, hlow⟩
  -- attainment
  suffices h : ∃ lam : ℝ, 0 ≤ lam ∧ ((lam * ρ : ℝ) : EReal) + softValue c f Phat lam ≤ L ρ by
    obtain ⟨lam, hlam, hle⟩ := h
    refine ⟨lam, hlam, ?_⟩
    rw [hsoft lam hlam]
    exact le_antisymm (hweak lam hlam) hle
  by_cases hLtop : L ρ = ⊤
  · exact ⟨0, le_rfl, by rw [hLtop]; exact le_top⟩
  -- `𝓛` is finite on `[0, ∞)`
  have hnbot : ∀ r : ℝ, 0 ≤ r → L r ≠ ⊥ := fun r hr => ne_bot_of_gt (hfint.trans_le (hlb r hr))
  have hL0top : L 0 ≠ ⊤ := ne_top_of_le_ne_top hLtop (hmono (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr hρ.le) hρ.le)
  have hntop : ∀ r : ℝ, 0 ≤ r → L r ≠ ⊤ := by
    intro r hr
    rcases le_or_gt r ρ with hrρ | hrρ
    · exact ne_top_of_le_ne_top hLtop (hmono (Set.mem_Ici.mpr hr) (Set.mem_Ici.mpr hρ.le) hrρ)
    · intro htop
      have hr0 : 0 < r := hρ.trans hrρ
      have ht0 : 0 < ρ / r := div_pos hρ hr0
      have ht1 : ρ / r ≤ 1 := (div_le_one hr0).mpr hrρ.le
      have h := hconc 0 r (ρ / r) le_rfl hr ht0.le ht1
      have hpt : (1 - ρ / r) * 0 + ρ / r * r = ρ := by rw [mul_zero, zero_add, div_mul_cancel₀ _ hr0.ne']
      rw [hpt, htop, EReal.mul_top_of_pos (by exact_mod_cast ht0)] at h
      rw [real_of hL0top (hnbot 0 le_rfl)] at h
      have : ((1 - ρ / r : ℝ) : EReal) * (((L 0).toReal : ℝ) : EReal) + ⊤ = ⊤ := by
        rw [← EReal.coe_mul]; exact EReal.coe_add_top _
      rw [this, top_le_iff] at h
      exact hLtop h
  set ℓ : ℝ → ℝ := fun r => (L r).toReal with hℓ
  have hLℓ : ∀ r : ℝ, 0 ≤ r → L r = ((ℓ r : ℝ) : EReal) := fun r hr => real_of (hntop r hr) (hnbot r hr)
  have hℓmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ℓ a ≤ ℓ b := by
    intro a b ha hab
    have := hmono (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab
    rw [hLℓ a ha, hLℓ b (ha.trans hab)] at this
    exact_mod_cast this
  have hℓconc : ∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      (1 - t) * ℓ a + t * ℓ b ≤ ℓ ((1 - t) * a + t * b) := by
    intro a b t ha hb ht0 ht1
    have h := hconc a b t ha hb ht0 ht1
    have hm : 0 ≤ (1 - t) * a + t * b := by
      have : 0 ≤ 1 - t := by linarith
      positivity
    rw [hLℓ a ha, hLℓ b hb, hLℓ _ hm, coe_conv] at h
    exact_mod_cast h
  -- the left slopes at `ρ`
  set slope : ℝ → ℝ := fun r => (ℓ ρ - ℓ r) / (ρ - r) with hslope
  set S := slope '' Set.Ico 0 ρ with hS
  have hSne : S.Nonempty := ⟨slope 0, Set.mem_image_of_mem _ ⟨le_rfl, hρ⟩⟩
  have hslope_nn : ∀ r ∈ Set.Ico 0 ρ, 0 ≤ slope r := by
    rintro r ⟨hr0, hrρ⟩
    exact div_nonneg (by linarith [hℓmono r ρ hr0 hrρ.le]) (by linarith)
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨r, hr, rfl⟩; exact hslope_nn r hr⟩
  set lamS := sInf S with hlamS
  have hlam0 : 0 ≤ lamS := le_csInf hSne (by rintro _ ⟨r, hr, rfl⟩; exact hslope_nn r hr)
  -- supergradient inequality
  have hsup : ∀ r : ℝ, 0 ≤ r → ℓ r ≤ ℓ ρ + lamS * (r - ρ) := by
    intro r hr
    rcases lt_trichotomy r ρ with hrρ | hrρ | hrρ
    · have h1 : lamS ≤ slope r := csInf_le hSbdd (Set.mem_image_of_mem _ ⟨hr, hrρ⟩)
      have h2 : lamS * (ρ - r) ≤ ℓ ρ - ℓ r := by
        have := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ ρ - r)
        rw [hslope] at this
        simp only at this
        rw [div_mul_cancel₀ _ (by linarith : ρ - r ≠ 0)] at this
        exact this
      nlinarith
    · subst hrρ; simp
    · have h1 : (ℓ r - ℓ ρ) / (r - ρ) ≤ lamS := by
        refine le_csInf hSne ?_
        rintro _ ⟨r', ⟨hr'0, hr'ρ⟩, rfl⟩
        set t := (ρ - r') / (r - r') with ht
        have hrr : 0 < r - r' := by linarith
        have ht0 : 0 ≤ t := div_nonneg (by linarith) hrr.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hrr]; linarith
        have hpt : (1 - t) * r' + t * r = ρ := by rw [ht]; field_simp; ring
        have h := hℓconc r' r t hr'0 hr ht0 ht1
        rw [hpt] at h
        have h3 := concave_slope hr'ρ hrρ h
        rw [hslope]; simp only
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      have := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ r - ρ)
      rw [div_mul_cancel₀ _ (by linarith : r - ρ ≠ 0)] at this
      linarith
  refine ⟨lamS, hlam0, ?_⟩
  -- `(P-soft)(λ*) ≤ 𝓛(ρ) − λ*ρ`
  have hsv : softValue c f Phat lamS ≤ ((ℓ ρ - lamS * ρ : ℝ) : EReal) := by
    unfold softValue
    refine iSup₂_le fun P hP => ?_
    obtain ⟨hPp, hKlt⟩ := hP
    have hKtop : transportCost c Phat P ≠ ⊤ := hKlt.ne
    set K := (transportCost c Phat P).toReal with hK
    have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
    have hKr : (K : EReal) = (transportCost c Phat P : EReal) := EReal.coe_ennreal_toReal hKtop
    have hfeas : extIntegral P (fun x => (f x : EReal)) ≤ L K := by
      rw [hL]; unfold robustLoss
      exact le_iSup₂ (f := fun (P : Measure X)
        (_ : IsProbabilityMeasure P ∧ ((transportCost c Phat P : ENNReal) : EReal) ≤ (K : EReal)) =>
        extIntegral P (fun x => (f x : EReal))) P ⟨hPp, hKr.symm.le⟩
    rw [hLℓ K hK0] at hfeas
    have h2 := hsup K hK0
    calc extIntegral P (fun x => (f x : EReal)) - ((lamS * K : ℝ) : EReal)
        ≤ ((ℓ K : ℝ) : EReal) - ((lamS * K : ℝ) : EReal) := EReal.sub_le_sub hfeas le_rfl
      _ = ((ℓ K - lamS * K : ℝ) : EReal) := (EReal.coe_sub _ _).symm
      _ ≤ ((ℓ ρ - lamS * ρ : ℝ) : EReal) := by exact_mod_cast (by nlinarith)
  calc ((lamS * ρ : ℝ) : EReal) + softValue c f Phat lamS
      ≤ ((lamS * ρ : ℝ) : EReal) + ((ℓ ρ - lamS * ρ : ℝ) : EReal) := add_le_add le_rfl hsv
    _ = ((ℓ ρ : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; ring
    _ = L ρ := (hLℓ ρ hρ.le).symm
