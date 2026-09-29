-- Prove2me | solution 1 for WangZahlKakeya.assertion_D_E_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-20T14:50:24.860913+00:00
-- url     : https://prove2.me/submissions/9d0eb6b2-0e06-490c-976b-83d82645e9de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WangZahlKakeya_assertion_D_iff_E
import Theorems.Thm_WangZahlKakeya_assertion_E_implies_D_gain
import Theorems.Thm_WangZahlKakeya_assertion_D_half_zero
import Theorems.Thm_WangZahlKakeya_tubeVol_comparable
import Theorems.Thm_WangZahlKakeya_tubeSystem_card_le
import Theorems.Thm_WangZahlKakeya_FSW_card_lower

/-!
# Theorem 1.9 of Wang–Zahl: the endpoint assertions `D(0,0)` and `E(0,0)`

This file reduces Theorem 1.9 to Propositions 1.6, 1.7 and 1.8 of the source, together with
three elementary quantitative facts about systems of `δ`-tubes.  The argument is the one given
on p. 7 of the source: starting from `D(1/2,0)` one runs the open/closed argument in `σ` on the
interval `[0,2/3]`, where openness comes from combining Propositions 1.6 and 1.7 with the
trade-off `E(σ,ω) ⟹ D(σ - g(σ,ω)/4, ω)` permitted by the cardinality bound `#T ≲ δ⁻⁴`.
-/

open MeasureTheory Metric Set

namespace WZGlue

open WangZahlKakeya

/-! ### Elementary facts about tube systems -/

private lemma tubeVol_nonneg (δ : ℝ) : 0 ≤ tubeVol δ := by
  unfold tubeVol
  exact ENNReal.toReal_nonneg

/-- A nonempty system of `δ`-tubes contained in the unit ball forces `δ ≤ 1`. -/
private lemma delta_le_one {δ : ℝ} {n : ℕ} {p v : Fin n → E3} {Y : Fin n → Set E3}
    (hT : IsTubeSystem δ n p v Y) (hn : 0 < n) : δ ≤ 1 := by
  obtain ⟨hδ, -, hsub, -, -, -⟩ := hT
  set i : Fin n := ⟨0, hn⟩ with hi
  have hball : closedBall (p i) δ ⊆ closedBall (0 : E3) 1 := by
    refine subset_trans ?_ (hsub i)
    intro x hx
    simp only [tube, mem_iUnion, exists_prop]
    exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simpa using hx⟩
  set u : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hu
  have hnu : ‖u‖ = 1 := by simp [hu]
  have hp : ∀ s : ℝ, |s| ≤ δ → ‖p i + s • u‖ ≤ 1 := by
    intro s hs
    have hmem : p i + s • u ∈ closedBall (p i) δ := by
      simp [mem_closedBall, dist_eq_norm, norm_smul, hnu, hs]
    simpa [mem_closedBall, dist_eq_norm] using hball hmem
  have h1 := hp δ (by rw [abs_of_pos hδ])
  have h2 := hp (-δ) (by rw [abs_neg, abs_of_pos hδ])
  have key : ‖(p i + δ • u) - (p i + (-δ) • u)‖ ≤ ‖p i + δ • u‖ + ‖p i + (-δ) • u‖ :=
    norm_sub_le _ _
  have heq : (p i + δ • u) - (p i + (-δ) • u) = (2 * δ) • u := by module
  rw [heq, norm_smul, hnu] at key
  simp only [mul_one, Real.norm_eq_abs] at key
  rw [abs_of_pos (by linarith : (0:ℝ) < 2 * δ)] at key
  linarith

/-! ### Monotonicity properties of Assertion `D` -/

/-- Increasing `σ` or increasing `ω` weakens Assertion `D`.  The proof uses the lower bound
`C_{F-SW}(𝕋) · (#𝕋)|T|^{1/2} ≥ c`, which keeps the factor `((#𝕋)|T|^{1/2})^{-σ}` from being
degraded by more than a subpolynomial amount. -/
private lemma assertionD_weaken {σ₁ σ₂ ω₁ ω₂ : ℝ} (hσ : σ₁ ≤ σ₂) (hω : ω₁ ≤ ω₂)
    (hD : AssertionD σ₁ ω₁) : AssertionD σ₂ ω₂ := by
  obtain ⟨c, hc, hclow⟩ := FSW_card_lower
  intro ε hε
  obtain ⟨κ, hκ, η, hη, H⟩ := hD (ε / 2) (by linarith)
  set d : ℝ := σ₂ - σ₁ with hd
  have hd0 : 0 ≤ d := by simp only [hd]; linarith
  have hden : (0:ℝ) < 2 * (d + 1) := by linarith
  set η' : ℝ := min η (ε / (2 * (d + 1))) with hη'def
  have hη'pos : 0 < η' := lt_min hη (by positivity)
  have hη'le : η' ≤ η := min_le_left _ _
  have hη'd : η' * d ≤ ε / 2 := by
    have h1 : η' ≤ ε / (2 * (d + 1)) := min_le_right _ _
    have h2 : η' * (2 * (d + 1)) ≤ ε := (le_div_iff₀ hden).mp h1
    nlinarith [hη'pos.le, hd0]
  refine ⟨κ * c ^ d, by positivity, η', hη'pos, ?_⟩
  intro δ hδ n p v Y hn hTS hdense hK hF
  have hδ1 : δ ≤ 1 := delta_le_one hTS hn
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hTVlow, -⟩ := tubeVol_comparable δ hδ hδ1
  have hTVpos : 0 < tubeVol δ := lt_of_lt_of_le (by positivity) hTVlow
  have hApos : 0 < (n : ℝ) * tubeVol δ ^ ((1:ℝ) / 2) :=
    mul_pos hnpos (Real.rpow_pos_of_pos hTVpos _)
  have hBnn : (0:ℝ) ≤ (n : ℝ) * tubeVol δ := by positivity
  have hdense' : IsDenseSystem δ n Y (δ ^ η) := by
    unfold IsDenseSystem at hdense ⊢
    exact le_trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη'le) hBnn) hdense
  have hK' : KTCW δ n p v ≤ δ ^ (-η) :=
    le_trans hK (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hF' : FSW δ n p v ≤ δ ^ (-η) :=
    le_trans hF (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have Hmain := H δ hδ n p v Y hn hTS hdense' hK' hF'
  set A : ℝ := (n : ℝ) * tubeVol δ ^ ((1:ℝ) / 2) with hAdef
  have hAlb : c * δ ^ η' ≤ A := by
    have h1 := hclow δ n p v Y hTS hn
    have h2 : FSW δ n p v * A ≤ δ ^ (-η') * A := mul_le_mul_of_nonneg_right hF hApos.le
    have h3 : c ≤ δ ^ (-η') * A := le_trans h1 h2
    have h4 : (0:ℝ) < δ ^ η' := Real.rpow_pos_of_pos hδ _
    have h5 : δ ^ η' * c ≤ δ ^ η' * (δ ^ (-η') * A) := by nlinarith
    rw [← mul_assoc, ← Real.rpow_add hδ] at h5
    simp only [add_neg_cancel, Real.rpow_zero, one_mul] at h5
    linarith [h5]
  have hbase : (0:ℝ) < c * δ ^ η' := by positivity
  have hsplit : A ^ (-σ₂) = A ^ (-σ₁) * A ^ (-d) := by
    have : -σ₂ = -σ₁ + -d := by simp only [hd]; ring
    rw [this, Real.rpow_add hApos]
  have hinv : A ^ (-d) ≤ c ^ (-d) * δ ^ (-(η' * d)) := by
    have hpow : (c * δ ^ η') ^ d ≤ A ^ d := Real.rpow_le_rpow hbase.le hAlb hd0
    have h1 : A ^ (-d) ≤ (c * δ ^ η') ^ (-d) := by
      rw [Real.rpow_neg hApos.le, Real.rpow_neg hbase.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hbase d) hpow
    have h2 : (c * δ ^ η') ^ (-d) = c ^ (-d) * δ ^ (-(η' * d)) := by
      rw [Real.mul_rpow hc.le (Real.rpow_pos_of_pos hδ _).le, ← Real.rpow_mul hδ.le]
      ring_nf
    rw [h2] at h1
    exact h1
  have hscalar : κ * c ^ d * δ ^ (ω₂ + ε) * A ^ (-d) ≤ κ * δ ^ (ω₁ + ε / 2) := by
    have h1 : κ * c ^ d * δ ^ (ω₂ + ε) * A ^ (-d)
        ≤ κ * c ^ d * δ ^ (ω₂ + ε) * (c ^ (-d) * δ ^ (-(η' * d))) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have h2 : κ * c ^ d * δ ^ (ω₂ + ε) * (c ^ (-d) * δ ^ (-(η' * d)))
        = κ * δ ^ (ω₂ + ε - η' * d) := by
      rw [Real.rpow_neg hc.le, Real.rpow_neg hδ.le (η' * d)]
      have hcd : (0:ℝ) < c ^ d := Real.rpow_pos_of_pos hc d
      have hdd : (0:ℝ) < δ ^ (η' * d) := Real.rpow_pos_of_pos hδ _
      have : δ ^ (ω₂ + ε - η' * d) = δ ^ (ω₂ + ε) * (δ ^ (η' * d))⁻¹ := by
        rw [← Real.rpow_neg hδ.le, ← Real.rpow_add hδ]; ring_nf
      rw [this]
      field_simp
    have h3 : κ * δ ^ (ω₂ + ε - η' * d) ≤ κ * δ ^ (ω₁ + ε / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) hκ.le
    linarith [h2 ▸ h1]
  have hfinal : κ * c ^ d * δ ^ (ω₂ + ε) * ((n : ℝ) * tubeVol δ) * A ^ (-σ₂)
      ≤ κ * δ ^ (ω₁ + ε / 2) * ((n : ℝ) * tubeVol δ) * A ^ (-σ₁) := by
    rw [hsplit]
    have hnn : (0:ℝ) ≤ ((n : ℝ) * tubeVol δ) * A ^ (-σ₁) := by positivity
    calc κ * c ^ d * δ ^ (ω₂ + ε) * ((n : ℝ) * tubeVol δ) * (A ^ (-σ₁) * A ^ (-d))
        = (κ * c ^ d * δ ^ (ω₂ + ε) * A ^ (-d)) * (((n : ℝ) * tubeVol δ) * A ^ (-σ₁)) := by
          ring
      _ ≤ (κ * δ ^ (ω₁ + ε / 2)) * (((n : ℝ) * tubeVol δ) * A ^ (-σ₁)) :=
          mul_le_mul_of_nonneg_right hscalar hnn
      _ = κ * δ ^ (ω₁ + ε / 2) * ((n : ℝ) * tubeVol δ) * A ^ (-σ₁) := by ring
  exact le_trans hfinal Hmain

/-- Trading a gain in `ω` for a gain in `σ`.  The proof uses the cardinality bound
`#𝕋 ≲ δ⁻⁴`, which gives `(#𝕋)|T|^{1/2} ≲ δ⁻³`. -/
private lemma assertionD_trade {σ₁ σ₂ ω₁ ω₂ : ℝ} (hσ : σ₂ ≤ σ₁)
    (hgap : 3 * (σ₁ - σ₂) ≤ ω₂ - ω₁) (hD : AssertionD σ₁ ω₁) : AssertionD σ₂ ω₂ := by
  obtain ⟨C, hC, hCle⟩ := tubeSystem_card_le
  set C₃ : ℝ := max 1 (3 * C) with hC₃def
  have hC₃1 : (1:ℝ) ≤ C₃ := le_max_left _ _
  have hC₃pos : (0:ℝ) < C₃ := lt_of_lt_of_le one_pos hC₃1
  intro ε hε
  obtain ⟨κ, hκ, η, hη, H⟩ := hD (ε / 2) (by linarith)
  set e : ℝ := σ₁ - σ₂ with he
  have he0 : 0 ≤ e := by simp only [he]; linarith
  refine ⟨κ * C₃ ^ (-e), by positivity, η, hη, ?_⟩
  intro δ hδ n p v Y hn hTS hdense hK hF
  have hδ1 : δ ≤ 1 := delta_le_one hTS hn
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hTVlow, hTVhigh⟩ := tubeVol_comparable δ hδ hδ1
  have hTVpos : 0 < tubeVol δ := lt_of_lt_of_le (by positivity) hTVlow
  set A : ℝ := (n : ℝ) * tubeVol δ ^ ((1:ℝ) / 2) with hAdef
  have hApos : 0 < A := mul_pos hnpos (Real.rpow_pos_of_pos hTVpos _)
  have Hmain := H δ hδ n p v Y hn hTS hdense hK hF
  have hsqrt : tubeVol δ ^ ((1:ℝ) / 2) ≤ 3 * δ := by
    have h1 : tubeVol δ ≤ (3 * δ) ^ 2 := by nlinarith
    have h2 : tubeVol δ ^ ((1:ℝ) / 2) ≤ ((3 * δ) ^ 2 : ℝ) ^ ((1:ℝ) / 2) :=
      Real.rpow_le_rpow (tubeVol_nonneg δ) h1 (by norm_num)
    have h3 : ((3 * δ) ^ 2 : ℝ) ^ ((1:ℝ) / 2) = 3 * δ := by
      rw [← Real.rpow_natCast (3 * δ) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    linarith [h3 ▸ h2]
  have hAub : A ≤ C₃ * δ ^ (-(3:ℝ)) := by
    have h1 : (n : ℝ) ≤ C * δ ^ (-(4:ℝ)) := hCle δ n p v Y hTS
    have h2 : A ≤ (C * δ ^ (-(4:ℝ))) * (3 * δ) :=
      mul_le_mul h1 hsqrt (Real.rpow_nonneg (tubeVol_nonneg δ) _) (by positivity)
    have h3 : (C * δ ^ (-(4:ℝ))) * (3 * δ) = (3 * C) * δ ^ (-(3:ℝ)) := by
      have hstep : δ ^ (-(4:ℝ)) * δ = δ ^ (-(3:ℝ)) := by
        nth_rewrite 2 [show δ = δ ^ (1:ℝ) from (Real.rpow_one δ).symm]
        rw [← Real.rpow_add hδ]
        norm_num
      calc (C * δ ^ (-(4:ℝ))) * (3 * δ) = 3 * C * (δ ^ (-(4:ℝ)) * δ) := by ring
        _ = (3 * C) * δ ^ (-(3:ℝ)) := by rw [hstep]
    have h4 : (3 * C) * δ ^ (-(3:ℝ)) ≤ C₃ * δ ^ (-(3:ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδ.le _)
    linarith [h3 ▸ h2]
  have hsplit : A ^ (-σ₂) = A ^ (-σ₁) * A ^ e := by
    have : -σ₂ = -σ₁ + e := by simp only [he]; ring
    rw [this, Real.rpow_add hApos]
  have hAe : A ^ e ≤ C₃ ^ e * δ ^ (-(3 * e)) := by
    have h1 : A ^ e ≤ (C₃ * δ ^ (-(3:ℝ))) ^ e := Real.rpow_le_rpow hApos.le hAub he0
    have h2 : (C₃ * δ ^ (-(3:ℝ))) ^ e = C₃ ^ e * δ ^ (-(3 * e)) := by
      rw [Real.mul_rpow hC₃pos.le (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
      ring_nf
    rw [h2] at h1
    exact h1
  have hscalar : κ * C₃ ^ (-e) * δ ^ (ω₂ + ε) * A ^ e ≤ κ * δ ^ (ω₁ + ε / 2) := by
    have h1 : κ * C₃ ^ (-e) * δ ^ (ω₂ + ε) * A ^ e
        ≤ κ * C₃ ^ (-e) * δ ^ (ω₂ + ε) * (C₃ ^ e * δ ^ (-(3 * e))) :=
      mul_le_mul_of_nonneg_left hAe (by positivity)
    have h2 : κ * C₃ ^ (-e) * δ ^ (ω₂ + ε) * (C₃ ^ e * δ ^ (-(3 * e)))
        = κ * δ ^ (ω₂ + ε - 3 * e) := by
      rw [Real.rpow_neg hC₃pos.le, Real.rpow_neg hδ.le (3 * e)]
      have hce : (0:ℝ) < C₃ ^ e := Real.rpow_pos_of_pos hC₃pos e
      have hde : (0:ℝ) < δ ^ (3 * e) := Real.rpow_pos_of_pos hδ _
      have : δ ^ (ω₂ + ε - 3 * e) = δ ^ (ω₂ + ε) * (δ ^ (3 * e))⁻¹ := by
        rw [← Real.rpow_neg hδ.le, ← Real.rpow_add hδ]; ring_nf
      rw [this]
      field_simp
    have h3 : κ * δ ^ (ω₂ + ε - 3 * e) ≤ κ * δ ^ (ω₁ + ε / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by simp only [he] at *; linarith)) hκ.le
    linarith [h2 ▸ h1]
  have hfinal : κ * C₃ ^ (-e) * δ ^ (ω₂ + ε) * ((n : ℝ) * tubeVol δ) * A ^ (-σ₂)
      ≤ κ * δ ^ (ω₁ + ε / 2) * ((n : ℝ) * tubeVol δ) * A ^ (-σ₁) := by
    rw [hsplit]
    have hnn : (0:ℝ) ≤ ((n : ℝ) * tubeVol δ) * A ^ (-σ₁) := by positivity
    calc κ * C₃ ^ (-e) * δ ^ (ω₂ + ε) * ((n : ℝ) * tubeVol δ) * (A ^ (-σ₁) * A ^ e)
        = (κ * C₃ ^ (-e) * δ ^ (ω₂ + ε) * A ^ e) * (((n : ℝ) * tubeVol δ) * A ^ (-σ₁)) := by
          ring
      _ ≤ (κ * δ ^ (ω₁ + ε / 2)) * (((n : ℝ) * tubeVol δ) * A ^ (-σ₁)) :=
          mul_le_mul_of_nonneg_right hscalar hnn
      _ = κ * δ ^ (ω₁ + ε / 2) * ((n : ℝ) * tubeVol δ) * A ^ (-σ₁) := by ring
  exact le_trans hfinal Hmain

/-- The set of `ω` for which `D(σ,ω)` holds is closed from above. -/
private lemma assertionD_limit_omega {σ ω : ℝ}
    (h : ∀ t : ℝ, 0 < t → AssertionD σ (ω + t)) : AssertionD σ ω := by
  intro ε hε
  obtain ⟨κ, hκ, η, hη, H⟩ := h (ε / 2) (by linarith) (ε / 2) (by linarith)
  refine ⟨κ, hκ, η, hη, ?_⟩
  intro δ hδ n p v Y hn hTS hdense hK hF
  have := H δ hδ n p v Y hn hTS hdense hK hF
  rwa [show ω + ε / 2 + ε / 2 = ω + ε by ring] at this

/-- The set of `σ` for which `D(σ,ω)` holds is closed from above. -/
private lemma assertionD_limit_sigma {σ ω : ℝ}
    (h : ∀ t : ℝ, 0 < t → AssertionD (σ + t) ω) : AssertionD σ ω := by
  refine assertionD_limit_omega ?_
  intro t ht
  refine assertionD_trade (σ₁ := σ + t / 3) (by linarith) (by linarith) (h (t / 3) (by linarith))

/-! ### The main argument -/

end WZGlue

open WangZahlKakeya WZGlue

theorem solution : AssertionD 0 0 ∧ AssertionE 0 0 := by
  obtain ⟨g, hgpos, hgimp⟩ := assertion_E_implies_D_gain
  have key : ∀ ω : ℝ, 0 < ω → ω ≤ 1 → AssertionD 0 ω := by
    intro ω hω0 hω1
    set S : Set ℝ := {σ : ℝ | 0 ≤ σ ∧ σ ≤ 2 / 3 ∧ AssertionD σ ω} with hSdef
    have hhalf : (1 / 2 : ℝ) ∈ S :=
      ⟨by norm_num, by norm_num, assertionD_weaken (le_refl _) hω0.le assertion_D_half_zero⟩
    have hne : S.Nonempty := ⟨1 / 2, hhalf⟩
    have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
    have hs0 : 0 ≤ sInf S := le_csInf hne (fun b hb => hb.1)
    have hs12 : sInf S ≤ 1 / 2 := csInf_le hbdd hhalf
    have h23 : AssertionD (2 / 3) ω :=
      assertionD_weaken (by norm_num) (le_refl _) hhalf.2.2
    have hgt : ∀ σ' : ℝ, sInf S < σ' → AssertionD σ' ω := by
      intro σ' hσ'
      by_cases hle : σ' ≤ 2 / 3
      · obtain ⟨x, hx, hxlt⟩ := exists_lt_of_csInf_lt hne hσ'
        exact assertionD_weaken hxlt.le (le_refl _) hx.2.2
      · exact assertionD_weaken (by linarith [not_le.mp hle]) (le_refl _) h23
    have hDs : AssertionD (sInf S) ω :=
      assertionD_limit_sigma (fun t ht => hgt (sInf S + t) (by linarith))
    rcases eq_or_lt_of_le hs0 with heq | hpos
    · rw [← heq] at hDs; exact hDs
    · exfalso
      have hE : AssertionE (sInf S) ω :=
        (assertion_D_iff_E (sInf S) ω hs0 (by linarith) hω0.le).mpr hDs
      obtain ⟨hg1, hg2⟩ := hgpos (sInf S) ω hs0 (by linarith) hω0 hω1
      have hD2 : AssertionD (sInf S) (ω - g (sInf S) ω) :=
        hgimp (sInf S) ω hs0 (by linarith) hω0 hω1 hE
      have hD3 : AssertionD (sInf S - g (sInf S) ω / 4) ω :=
        assertionD_trade (by linarith) (by linarith) hD2
      have hD4 : AssertionD (max 0 (sInf S - g (sInf S) ω / 4)) ω :=
        assertionD_weaken (le_max_right _ _) (le_refl _) hD3
      have hmem : max 0 (sInf S - g (sInf S) ω / 4) ∈ S := by
        refine ⟨le_max_left _ _, ?_, hD4⟩
        rcases max_cases (0 : ℝ) (sInf S - g (sInf S) ω / 4) with ⟨h, -⟩ | ⟨h, -⟩ <;>
          rw [h] <;> linarith
      have hle := csInf_le hbdd hmem
      rcases max_cases (0 : ℝ) (sInf S - g (sInf S) ω / 4) with ⟨h, -⟩ | ⟨h, -⟩ <;>
        rw [h] at hle <;> linarith
  have hD00 : AssertionD 0 0 := by
    refine assertionD_limit_omega ?_
    intro t ht
    by_cases h1 : t ≤ 1
    · simpa using key t ht h1
    · exact assertionD_weaken (le_refl (0 : ℝ))
        (show (1 : ℝ) ≤ 0 + t by linarith [not_le.mp h1]) (key 1 one_pos le_rfl)
  exact ⟨hD00, (assertion_D_iff_E 0 0 le_rfl (by norm_num) le_rfl).mpr hD00⟩
