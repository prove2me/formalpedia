-- Prove2me | solution 1 for RefugeeCash.PDCA.pdca_symmetric_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:36:25.611733+00:00
-- url     : https://prove2.me/submissions/12ed9e16-8665-450c-aba1-992a71799098

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model

set_option autoImplicit false

namespace RefugeeCash.PDCA

/-- The algebraic identity behind the PDCA optimality: profit of the linear schedule plus the
tangent line of `π0` equals the target profit plus a quadratic correction. -/
lemma pdca_key_identity (B c kT S p pT d : ℝ) (hp : 0 < p) (hpT : 0 < pT)
    (hd : d = -B * (S * (1 - c / pT) + kT * c / pT ^ 2)) :
    (p - c) * ((kT + S * (p - pT)) * B / p) + d * (p - pT)
      = (pT - c) * (kT * B / pT) + B * c * (p - pT) ^ 2 / (p * pT) * (S - kT / pT) := by
  subst hd
  field_simp
  ring

lemma pdca_key_nonpos (B c kT S p pT : ℝ) (hB : 0 < B) (hc : 0 < c) (hp : 0 < p)
    (hpT : 0 < pT) (hkT : 0 ≤ kT) (hS : S ≤ 0) :
    B * c * (p - pT) ^ 2 / (p * pT) * (S - kT / pT) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos
  · positivity
  · have : 0 ≤ kT / pT := div_nonneg hkT hpT.le
    linarith

lemma pdca_key_neg (B c kT S p pT : ℝ) (hB : 0 < B) (hc : 0 < c) (hp : 0 < p)
    (hpT : 0 < pT) (hkT : 0 < kT) (hS : S ≤ 0) (hne : p ≠ pT) :
    B * c * (p - pT) ^ 2 / (p * pT) * (S - kT / pT) < 0 := by
  apply mul_neg_of_pos_of_neg
  · have : 0 < (p - pT) ^ 2 := by
      have : p - pT ≠ 0 := sub_ne_zero.mpr hne
      positivity
    positivity
  · have : 0 < kT / pT := div_pos hkT hpT
    linarith

/-- Tangent-line inequality for a concave function differentiable at an interior point. -/
lemma concave_tangent (f : ℝ → ℝ) (c x y : ℝ) (hf : ConcaveOn ℝ (Set.Ioi c) f)
    (hx : c < x) (hy : c < y) (hd : DifferentiableAt ℝ f x) :
    f y ≤ f x + deriv f x * (y - x) := by
  rcases lt_trichotomy y x with h | h | h
  · have := hf.le_slope_of_hasDerivAt (x := y) (y := x) hy hx h hd.hasDerivAt
    rw [slope_def_field] at this
    have hpos : 0 < x - y := sub_pos.mpr h
    rw [le_div_iff₀ hpos] at this
    nlinarith
  · subst h; simp
  · have := hf.slope_le_deriv (x := x) (y := y) hx hy h hd
    rw [slope_def_field] at this
    have hpos : 0 < y - x := sub_pos.mpr h
    rw [div_le_iff₀ hpos] at this
    nlinarith

end RefugeeCash.PDCA

open RefugeeCash.PDCA in
theorem solution (P : Params) (hP : P.Standing) (pmax p0 : ℝ)
    (hA2 : Assumption2 P pmax p0) (hconc : ConcaveOn ℝ (Set.Ioi P.c) (pi0 P))
    (pT kT : ℝ) (hpT : P.c < pT) (hpT0 : pT ≤ p0) (hkT : kT ∈ Set.Icc (0 : ℝ) 1)
    (hfeas : Pi0 P p0 ≤ retailerProfit P pT kT) :
    kPDCA P pT kT pT = kT ∧
      (∀ p, P.c < p → pdcaProfit P pT kT p ≤ pdcaProfit P pT kT pT) ∧
      (Pi0 P p0 < retailerProfit P pT kT →
        ∀ p, P.c < p → pdcaProfit P pT kT p = pdcaProfit P pT kT pT → p = pT) := by
  obtain ⟨hB, hc⟩ := hP
  obtain ⟨_, _, hDc, _, hcp0, _, _, hmax⟩ := hA2
  obtain ⟨hk0, hk1⟩ := hkT
  have hpTpos : 0 < pT := lt_trans hc hpT
  -- π0 is bounded by Π0 on (c, ∞)
  have hle0 : ∀ p, P.c < p → pi0 P p ≤ Pi0 P p0 := by
    intro p hp
    by_cases h : p = p0
    · subst h; exact le_rfl
    · exact (hmax p hp h).le
  -- differentiability of π0 on (c, ∞)
  have hdiff : ∀ x, P.c < x → DifferentiableAt ℝ (pi0 P) x := by
    intro x hx
    have hD : DifferentiableAt ℝ P.D x :=
      (hDc.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hx)
    show DifferentiableAt ℝ (fun p => (p - P.c) * P.D p) x
    fun_prop
  set d := deriv (pi0 P) pT with hd_def
  -- d ≥ 0
  have hdnn : 0 ≤ d := by
    rcases lt_or_eq_of_le hpT0 with h | h
    · have := hconc.slope_le_deriv (x := pT) (y := p0) hpT hcp0 h (hdiff pT hpT)
      rw [slope_def_field] at this
      have hnum : 0 ≤ pi0 P p0 - pi0 P pT := by
        have := hle0 pT hpT; unfold Pi0 at this; linarith
      have : 0 ≤ (pi0 P p0 - pi0 P pT) / (p0 - pT) :=
        div_nonneg hnum (sub_pos.mpr h).le
      linarith
    · have hlm : IsLocalMax (pi0 P) pT := by
        filter_upwards [Ioi_mem_nhds hpT] with p hp
        have := hle0 p hp
        unfold Pi0 at this
        rw [h]; exact this
      rw [hd_def, hlm.deriv_eq_zero]
  set S := slope P pT kT with hS_def
  have hone : 0 < 1 - P.c / pT := by
    rw [sub_pos, div_lt_one hpTpos]; exact hpT
  have hSd : d = -P.B * (S * (1 - P.c / pT) + kT * P.c / pT ^ 2) := by
    rw [hS_def]
    unfold RefugeeCash.PDCA.slope
    rw [← hd_def]
    have hcancel : (kT * P.c / pT ^ 2 + d / P.B) / (1 - P.c / pT) * (1 - P.c / pT)
        = kT * P.c / pT ^ 2 + d / P.B := div_mul_cancel₀ _ hone.ne'
    have hBd : P.B * (d / P.B) = d := by field_simp
    linear_combination (-1 : ℝ) * hBd + (-P.B) * hcancel
  have hSnp : S ≤ 0 := by
    rw [hS_def]
    unfold RefugeeCash.PDCA.slope
    rw [neg_nonpos]
    apply div_nonneg _ hone.le
    have : 0 ≤ kT * P.c / pT ^ 2 := by positivity
    have : 0 ≤ deriv (pi0 P) pT / P.B := div_nonneg hdnn hB.le
    linarith
  have hkfix : kPDCA P pT kT pT = kT := by
    simp only [kPDCA, sub_self, mul_zero, add_zero]
    rw [max_eq_left hk0, min_eq_left hk1]
  have hPhiT : pdcaProfit P pT kT pT = retailerProfit P pT kT := by
    rw [pdcaProfit, hkfix]
  -- the main bound, with an error term
  have hmain : ∀ p, P.c < p →
      pdcaProfit P pT kT p ≤ max (pi0 P p)
        (retailerProfit P pT kT +
          P.B * P.c * (p - pT) ^ 2 / (p * pT) * (S - kT / pT)) := by
    intro p hp
    have hppos : 0 < p := lt_trans hc hp
    have hw : 0 < (p - P.c) * P.B / p := by
      have : 0 < p - P.c := sub_pos.mpr hp
      positivity
    have htan := concave_tangent (pi0 P) P.c pT p hconc hpT hp (hdiff pT hpT)
    have hid := pdca_key_identity P.B P.c kT S p pT d hppos hpTpos hSd
    simp only [pdcaProfit, retailerProfit, piR, refugeeDemand] at *
    set L := kT + S * (p - pT) with hL
    have hk : kPDCA P pT kT p = min (max L 0) 1 := rfl
    rcases le_or_gt 0 L with hL0 | hL0
    · apply le_max_of_le_right
      have hkle : kPDCA P pT kT p ≤ L := by
        rw [hk, max_eq_left hL0]; exact min_le_left _ _
      have h1 : (p - P.c) * (kPDCA P pT kT p * P.B / p) ≤ (p - P.c) * (L * P.B / p) := by
        have e1 : (p - P.c) * (kPDCA P pT kT p * P.B / p)
            = kPDCA P pT kT p * ((p - P.c) * P.B / p) := by ring
        have e2 : (p - P.c) * (L * P.B / p) = L * ((p - P.c) * P.B / p) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_right hkle hw.le
      linarith
    · apply le_max_of_le_left
      have hkle : kPDCA P pT kT p ≤ 0 := by
        rw [hk, max_eq_right hL0.le]; exact min_le_left _ _
      have h1 : (p - P.c) * (kPDCA P pT kT p * P.B / p) ≤ 0 := by
        have e1 : (p - P.c) * (kPDCA P pT kT p * P.B / p)
            = kPDCA P pT kT p * ((p - P.c) * P.B / p) := by ring
        rw [e1]
        exact mul_nonpos_of_nonpos_of_nonneg hkle hw.le
      linarith
  refine ⟨hkfix, ?_, ?_⟩
  · intro p hp
    have hppos : 0 < p := lt_trans hc hp
    have h := hmain p hp
    have hE := pdca_key_nonpos P.B P.c kT S p pT hB hc hppos hpTpos hk0 hSnp
    rw [hPhiT]
    refine le_trans h (max_le ?_ ?_)
    · exact le_trans (hle0 p hp) hfeas
    · linarith
  · intro hstrict p hp heq
    have hppos : 0 < p := lt_trans hc hp
    have hkpos : 0 < kT := by
      rcases lt_or_eq_of_le hk0 with h | h
      · exact h
      · exfalso
        have : retailerProfit P pT kT = pi0 P pT := by
          rw [← h]; simp [retailerProfit, piR, refugeeDemand]
        have := hle0 pT hpT
        linarith
    by_contra hne
    have h := hmain p hp
    have hE := pdca_key_neg P.B P.c kT S p pT hB hc hppos hpTpos hkpos hSnp hne
    rw [heq, hPhiT] at h
    rcases le_max_iff.mp h with h' | h'
    · have := hle0 p hp; linarith
    · linarith
