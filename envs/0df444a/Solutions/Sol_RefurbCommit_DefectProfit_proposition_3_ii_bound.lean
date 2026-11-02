-- Prove2me | solution 1 for RefurbCommit.DefectProfit.proposition_3_ii_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:17:48.536932+00:00
-- url     : https://prove2.me/submissions/627d04e8-2c54-473d-b51a-7ff015f5817c

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

open MeasureTheory

namespace RefurbCommit.DefectProfit

lemma rc_upclosed_ge {S : Set ℝ} (hS : S ⊆ Set.Icc 0 1)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ≤ 1 → y ∈ S) {θ : ℝ} (hθ : θ ∈ S) :
    1 - (volume S).toReal ≤ θ := by
  have hsub : Set.Icc θ 1 ⊆ S := fun y hy => hup θ hθ y hy.1 hy.2
  have h1 : volume (Set.Icc θ 1) ≤ volume S := measure_mono hsub
  have hfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono hS)
  rw [Real.volume_Icc] at h1
  have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
  linarith

lemma rc_upclosed_mem {S : Set ℝ} (hS : S ⊆ Set.Icc 0 1)
    (hup : ∀ x ∈ S, ∀ y, x ≤ y → y ≤ 1 → y ∈ S) {θ : ℝ} (h1 : θ ≤ 1)
    (hθ : 1 - (volume S).toReal < θ) : θ ∈ S := by
  by_contra hn
  have hsub : S ⊆ Set.Ioc θ 1 := by
    intro x hx
    refine ⟨?_, (hS hx).2⟩
    by_contra hle; push_neg at hle
    exact hn (hup x hx θ hle h1)
  have h2 := measure_mono (μ := volume) hsub
  rw [Real.volume_Ioc] at h2
  have h3 := ENNReal.toReal_mono (by simp) h2
  rw [ENNReal.toReal_ofReal (by linarith)] at h3
  linarith

lemma buyers1_sub (P : Params) (α p1 p2 pr : ℝ) : buyers1 P α p1 p2 pr ⊆ Set.Icc 0 1 :=
  fun _ h => h.1

lemma buyers1_up (P : Params) (hP : P.Standing) (α p1 p2 pr : ℝ) :
    ∀ x ∈ buyers1 P α p1 p2 pr, ∀ y, x ≤ y → y ≤ 1 → y ∈ buyers1 P α p1 p2 pr := by
  obtain ⟨hvr, hvrn, -, -, -, -, -, hr0, hr1⟩ := hP
  intro x hx y hxy hy1
  simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U1, U2, Ur] at hx ⊢
  obtain ⟨⟨hx0, -⟩, ha, hb, hc⟩ := hx
  have k1 : 0 ≤ (1 - P.rho) * P.vn * (y - x) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have k2 : 0 ≤ (P.vn - P.rho * P.vr) * (y - x) := by
    apply mul_nonneg _ (by linarith)
    nlinarith
  have k3 : 0 ≤ P.vn * (y - x) := mul_nonneg (by linarith) (by linarith)
  refine ⟨⟨by linarith, hy1⟩, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

lemma rc_null_of_sub {s : Set ℝ} (f : ℝ → ℝ) (hf : StrictMono f) (c : ℝ)
    (hs : s ⊆ {θ | f θ = c}) : volume s = 0 := by
  apply measure_mono_null hs
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  exact hf.injective (hx.trans hy.symm)

/-- In a subgame-perfect outcome, second-period new-product sales coincide with the
commitment-demand formula at the same prices. -/
lemma q2_eq_q2C (P : Params) (hP : P.Standing) (α p1 q1 p2 pr : ℝ)
    (hq : q1 = (volume (buyers1 P α p1 p2 pr)).toReal) :
    q2 P α q1 p2 pr = q2C P α p1 p2 pr := by
  have hP' := hP
  obtain ⟨hvr, hvrn, -, -, -, -, -, hr0, hr1⟩ := hP'
  have hq0 : 0 ≤ q1 := hq ▸ ENNReal.toReal_nonneg
  unfold q2 q2C
  congr 1
  apply measure_congr
  apply ae_eq_set.2
  constructor
  · -- newBuyers2 \ buyersC2 ⊆ {1 - q1}
    apply measure_mono_null (t := {1 - q1})
    · intro θ ⟨hθ, hn⟩
      simp only [newBuyers2, buyersC2, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff] at hθ hn
      obtain ⟨⟨h0, h1⟩, hra, hrb⟩ := hθ
      have hlt : U2 P α p2 θ < U1 P α p1 θ := by
        by_contra hc; push_neg at hc
        exact hn ⟨⟨h0, by linarith⟩, hc, hra, hrb⟩
      have hmem : θ ∈ buyers1 P α p1 p2 pr := by
        simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff]
        exact ⟨⟨h0, by linarith⟩, hlt.le, by linarith, by linarith⟩
      have := rc_upclosed_ge (buyers1_sub P α p1 p2 pr) (buyers1_up P hP α p1 p2 pr) hmem
      rw [← hq] at this
      simp only [Set.mem_singleton_iff]; linarith
    · simp
  · apply rc_null_of_sub (fun θ => U1 P α p1 θ - U2 P α p2 θ) _ 0
    · intro θ ⟨hθ, hn⟩
      simp only [newBuyers2, buyersC2, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff] at hθ hn
      obtain ⟨⟨h0, h1⟩, hra, hrb, hrc⟩ := hθ
      have hgt : 1 - q1 < θ := by
        by_contra hc; push_neg at hc
        exact hn ⟨⟨h0, hc⟩, hrb, hrc⟩
      have hmem : θ ∈ buyers1 P α p1 p2 pr :=
        rc_upclosed_mem (buyers1_sub P α p1 p2 pr) (buyers1_up P hP α p1 p2 pr) h1
          (by rw [← hq]; exact hgt)
      simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff] at hmem
      simp only [Set.mem_setOf_eq]
      linarith [hmem.2.1]
    · intro x y hxy
      simp only [U1, U2]
      have : 0 < (1 - P.rho) * P.vn * (y - x) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      nlinarith

lemma qr_eq_qrC (P : Params) (hP : P.Standing) (α p1 q1 p2 pr : ℝ)
    (hq : q1 = (volume (buyers1 P α p1 p2 pr)).toReal) :
    qr P α q1 p2 pr = qrC P α p1 p2 pr := by
  have hP' := hP
  obtain ⟨hvr, hvrn, -, -, -, -, -, hr0, hr1⟩ := hP'
  have hq0 : 0 ≤ q1 := hq ▸ ENNReal.toReal_nonneg
  unfold qr qrC
  congr 1
  apply measure_congr
  apply ae_eq_set.2
  constructor
  · apply measure_mono_null (t := {1 - q1})
    · intro θ ⟨hθ, hn⟩
      simp only [refBuyers2, buyersCr, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff] at hθ hn
      obtain ⟨⟨h0, h1⟩, hra, hrb⟩ := hθ
      have hlt : Ur P α pr θ < U1 P α p1 θ := by
        by_contra hc; push_neg at hc
        exact hn ⟨⟨h0, by linarith⟩, hc, hra, hrb⟩
      have hmem : θ ∈ buyers1 P α p1 p2 pr := by
        simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff]
        exact ⟨⟨h0, by linarith⟩, by linarith, hlt.le, by linarith⟩
      have := rc_upclosed_ge (buyers1_sub P α p1 p2 pr) (buyers1_up P hP α p1 p2 pr) hmem
      rw [← hq] at this
      simp only [Set.mem_singleton_iff]; linarith
    · simp
  · apply rc_null_of_sub (fun θ => U1 P α p1 θ - Ur P α pr θ) _ 0
    · intro θ ⟨hθ, hn⟩
      simp only [refBuyers2, buyersCr, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff] at hθ hn
      obtain ⟨⟨h0, h1⟩, hra, hrb, hrc⟩ := hθ
      have hgt : 1 - q1 < θ := by
        by_contra hc; push_neg at hc
        exact hn ⟨⟨h0, hc⟩, hrb, hrc⟩
      have hmem : θ ∈ buyers1 P α p1 p2 pr :=
        rc_upclosed_mem (buyers1_sub P α p1 p2 pr) (buyers1_up P hP α p1 p2 pr) h1
          (by rw [← hq]; exact hgt)
      simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff] at hmem
      simp only [Set.mem_setOf_eq]
      linarith [hmem.2.2.1]
    · intro x y hxy
      simp only [U1, Ur]
      have h1 : 0 < P.vn - P.rho * P.vr := by nlinarith
      have : 0 < (P.vn - P.rho * P.vr) * (y - x) := mul_pos h1 (by linarith)
      nlinarith

lemma vol_toReal_le_one {S : Set ℝ} (hS : S ⊆ Set.Icc 0 1) : (volume S).toReal ≤ 1 := by
  have h := measure_mono (μ := volume) hS
  rw [Real.volume_Icc] at h
  have := ENNReal.toReal_mono (by simp) h
  simpa using this

/-- A demand term `q (p - c)` with `c ≥ 0`, `q ∈ [0,1]`, where `q > 0` forces `p ≤ B`. -/
lemma term_le (q p c B : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hp : 0 < q → p ≤ B) : q * (p - c) ≤ B := by
  rcases hq0.lt_or_eq with h | h
  · have := hp h
    by_cases hpc : p - c ≤ 0
    · nlinarith
    · push_neg at hpc
      nlinarith
  · rw [← h]; simp; exact hB

lemma pos_vol_nonempty {S : Set ℝ} (h : 0 < (volume S).toReal) : S.Nonempty := by
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty] at hn
  rw [hn] at h; simp at h

lemma objC_le (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) (p1 p2 pr : ℝ) :
    objC P α p1 p2 pr ≤ P.vn + P.rho * P.vn + P.rho * P.vr := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  have hhα : 0 ≤ P.h * α := mul_nonneg hh hα.le
  have hhkα : 0 ≤ P.h * P.kr * α := mul_nonneg (mul_nonneg hh hkr) hα.le
  have t1 : q1C P α p1 p2 pr * (p1 - (1 + α) * P.cn) ≤ P.vn := by
    apply term_le _ _ _ _ ENNReal.toReal_nonneg (vol_toReal_le_one (fun _ h => h.1))
      (by nlinarith) (by linarith)
    intro hpos
    obtain ⟨θ, hθ⟩ := pos_vol_nonempty hpos
    simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U1] at hθ
    nlinarith [hθ.2.2.2, hθ.1.2]
  have t2 : q2C P α p1 p2 pr * (p2 - (1 + α) * P.cn) ≤ P.vn := by
    apply term_le _ _ _ _ ENNReal.toReal_nonneg (vol_toReal_le_one (fun _ h => h.1))
      (by nlinarith) (by linarith)
    intro hpos
    obtain ⟨θ, hθ⟩ := pos_vol_nonempty hpos
    simp only [buyersC2, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U2] at hθ
    have := hθ.2.2.2
    have h' : 0 ≤ P.vn * θ - P.h * α - p2 := by
      by_contra hc; push_neg at hc; nlinarith
    nlinarith [hθ.1.2]
  have t3 : qrC P α p1 p2 pr * (pr - (1 + P.kr * α) * P.cr) ≤ P.vr := by
    apply term_le _ _ _ _ ENNReal.toReal_nonneg (vol_toReal_le_one (fun _ h => h.1))
      (by have : 0 ≤ P.kr * α := mul_nonneg hkr hα.le; nlinarith) (by linarith)
    intro hpos
    obtain ⟨θ, hθ⟩ := pos_vol_nonempty hpos
    simp only [buyersCr, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, Ur] at hθ
    have := hθ.2.2.2
    have h' : 0 ≤ P.vr * θ - P.h * P.kr * α - pr := by
      by_contra hc; push_neg at hc; nlinarith
    nlinarith [hθ.1.2]
  unfold objC
  have := mul_le_mul_of_nonneg_left t2 hr0.le
  have := mul_le_mul_of_nonneg_left t3 hr0.le
  nlinarith

lemma objC_bdd (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) :
    BddAbove {v | ∃ p1 p2 pr, FeasibleC P α p1 p2 pr ∧ v = objC P α p1 p2 pr} := by
  refine ⟨P.vn + P.rho * P.vn + P.rho * P.vr, ?_⟩
  rintro v ⟨p1, p2, pr, -, rfl⟩
  exact objC_le P hP α hα p1 p2 pr

lemma PiC_nonneg (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) : 0 ≤ PiC P α := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  have hP' : P.Standing := ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩
  have hhα : 0 ≤ P.h * α := mul_nonneg hh hα.le
  have hhkα : 0 ≤ P.h * P.kr * α := mul_nonneg (mul_nonneg hh hkr) hα.le
  set b : ℝ := P.vn + 1
  have e1 : buyers1 P α b b b = ∅ := by
    ext θ
    simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U1, Set.mem_empty_iff_false,
      iff_false, not_and, not_le]
    intro h0 _ _
    nlinarith [h0.1, h0.2]
  have e2 : buyersC2 P α b b b = ∅ := by
    ext θ
    simp only [buyersC2, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U2, Set.mem_empty_iff_false,
      iff_false, not_and, not_le]
    intro h0 _ _
    exact mul_neg_of_pos_of_neg hr0 (by nlinarith [h0.1, h0.2])
  have e3 : buyersCr P α b b b = ∅ := by
    ext θ
    simp only [buyersCr, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, Ur, Set.mem_empty_iff_false,
      iff_false, not_and, not_le]
    intro h0 _ _
    exact mul_neg_of_pos_of_neg hr0 (by nlinarith [h0.1, h0.2])
  have h0 : objC P α b b b = 0 := by
    simp [objC, q1C, q2C, qrC, e1, e2, e3]
  apply le_csSup (objC_bdd P hP' α hα)
  refine ⟨b, b, b, ?_, h0.symm⟩
  simp [FeasibleC, q1C, qrC, e1, e3]

theorem prop3_ii_bound (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) :
    PiStar P α ≤ PiC P α := by
  unfold PiStar
  rcases Set.eq_empty_or_nonempty
    {v | ∃ p1 q1 p2 pr, IsSPOutcome P α p1 q1 p2 pr ∧ v = totalProfit P α p1 q1 p2 pr} with h | h
  · rw [h, Real.sSup_empty]; exact PiC_nonneg P hP α hα
  apply csSup_le h
  rintro v ⟨p1, q1, p2, pr, ⟨hq, hopt⟩, rfl⟩
  have e2 := q2_eq_q2C P hP α p1 q1 p2 pr hq
  have er := qr_eq_qrC P hP α p1 q1 p2 pr hq
  have hfeas : FeasibleC P α p1 p2 pr := by
    have := hopt.1
    unfold Feasible2 at this
    unfold FeasibleC q1C
    rw [er] at this; rw [← hq]; exact this
  have hval : totalProfit P α p1 q1 p2 pr = objC P α p1 p2 pr := by
    unfold totalProfit profit2 objC q1C
    rw [e2, er, ← hq]; ring
  rw [hval]
  exact le_csSup (objC_bdd P hP α hα) ⟨p1, p2, pr, hfeas, rfl⟩


end RefurbCommit.DefectProfit

open RefurbCommit.DefectProfit in
theorem solution (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) :
    PiStar P α ≤ PiC P α := prop3_ii_bound P hP α hα
