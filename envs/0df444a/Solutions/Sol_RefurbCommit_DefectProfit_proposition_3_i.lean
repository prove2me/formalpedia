-- Prove2me | solution 1 for RefurbCommit.DefectProfit.proposition_3_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:52:47.956501+00:00
-- url     : https://prove2.me/submissions/807854fc-7df0-4030-b2c0-6364f370b1ae

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

open MeasureTheory
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false


namespace RefurbCommit.DefectProfit

lemma rc_vol_le_of_sub {S : Set ℝ} {m b : ℝ} (hmb : m ≤ b) (h : S ⊆ Set.Icc m b) :
    (volume S).toReal ≤ b - m := by
  have h2 := measure_mono (μ := volume) h
  rw [Real.volume_Icc] at h2
  have h3 := ENNReal.toReal_mono (by simp) h2
  rwa [ENNReal.toReal_ofReal (by linarith)] at h3

lemma rc_fin {S : Set ℝ} {b : ℝ} (h : S ⊆ Set.Icc 0 b) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono h)

lemma rc_union_toReal {S T : Set ℝ} {b : ℝ} (hS : S ⊆ Set.Icc 0 b) (hT : T ⊆ Set.Icc 0 b)
    (hTm : MeasurableSet T) (hn : volume (S ∩ T) = 0) :
    (volume (S ∪ T)).toReal = (volume S).toReal + (volume T).toReal := by
  have := measure_union_add_inter (μ := volume) S hTm
  rw [hn, add_zero] at this
  rw [this, ENNReal.toReal_add (rc_fin hS) (rc_fin hT)]

/-- Three stacked sets in `[0, b]`: `C` below `B` below `A`. -/
lemma rc_stack3 {b : ℝ} (hb : 0 ≤ b) (A B C : Set ℝ) (hA : A ⊆ Set.Icc 0 b)
    (hB : B ⊆ Set.Icc 0 b) (hC : C ⊆ Set.Icc 0 b)
    (cA : IsClosed A) (cB : IsClosed B) (cC : IsClosed C)
    (nAB : volume (A ∩ B) = 0) (nAC : volume (A ∩ C) = 0) (nBC : volume (B ∩ C) = 0)
    (oBA : ∀ x ∈ B, ∀ y ∈ A, x ≤ y) (oCA : ∀ x ∈ C, ∀ y ∈ A, x ≤ y)
    (oCB : ∀ x ∈ C, ∀ y ∈ B, x ≤ y) :
    (volume A).toReal + (volume B).toReal + (volume C).toReal ≤ b ∧
    (0 < (volume A).toReal → ∃ θ ∈ A, θ ≤ b - (volume A).toReal) ∧
    (0 < (volume B).toReal → ∃ θ ∈ B, θ ≤ b - (volume A).toReal - (volume B).toReal) ∧
    (0 < (volume C).toReal →
      ∃ θ ∈ C, θ ≤ b - (volume A).toReal - (volume B).toReal - (volume C).toReal) := by
  have hAB : A ∪ B ⊆ Set.Icc 0 b := Set.union_subset hA hB
  have e2 : (volume (A ∪ B)).toReal = (volume A).toReal + (volume B).toReal :=
    rc_union_toReal hA hB cB.measurableSet nAB
  have nABC : volume ((A ∪ B) ∩ C) = 0 := by
    rw [Set.union_inter_distrib_right]
    exact measure_union_null nAC nBC
  have e3 : (volume (A ∪ B ∪ C)).toReal =
      (volume A).toReal + (volume B).toReal + (volume C).toReal := by
    rw [rc_union_toReal hAB hC cC.measurableSet nABC, e2]
  have nonemp : ∀ {S : Set ℝ}, 0 < (volume S).toReal → S.Nonempty := by
    intro S h
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn] at h; simp at h
  have infmem : ∀ {S : Set ℝ}, S ⊆ Set.Icc 0 b → IsClosed S → S.Nonempty →
      sInf S ∈ S ∧ ∀ x ∈ S, sInf S ≤ x := by
    intro S hS cS hne
    have hbdd : BddBelow S := ⟨0, fun x hx => (hS hx).1⟩
    exact ⟨cS.csInf_mem hne hbdd, fun x hx => csInf_le hbdd hx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e3]
    have := rc_vol_le_of_sub hb (Set.union_subset hAB hC)
    linarith
  · intro h
    obtain ⟨hm, hle⟩ := infmem hA cA (nonemp h)
    refine ⟨sInf A, hm, ?_⟩
    have := rc_vol_le_of_sub (hA hm).2 (fun x hx => ⟨hle x hx, (hA hx).2⟩)
    linarith
  · intro h
    obtain ⟨hm, hle⟩ := infmem hB cB (nonemp h)
    refine ⟨sInf B, hm, ?_⟩
    have hsub : A ∪ B ⊆ Set.Icc (sInf B) b := by
      rintro x (hx | hx)
      · exact ⟨oBA _ hm x hx, (hA hx).2⟩
      · exact ⟨hle x hx, (hB hx).2⟩
    have := rc_vol_le_of_sub (hB hm).2 hsub
    linarith
  · intro h
    obtain ⟨hm, hle⟩ := infmem hC cC (nonemp h)
    refine ⟨sInf C, hm, ?_⟩
    have hsub : A ∪ B ∪ C ⊆ Set.Icc (sInf C) b := by
      rintro x ((hx | hx) | hx)
      · exact ⟨oCA _ hm x hx, (hA hx).2⟩
      · exact ⟨oCB _ hm x hx, (hB hx).2⟩
      · exact ⟨hle x hx, (hC hx).2⟩
    have := rc_vol_le_of_sub (hC hm).2 hsub
    linarith

lemma rc_null_of_sub {s : Set ℝ} (f : ℝ → ℝ) (hf : StrictMono f) (c : ℝ)
    (hs : s ⊆ {θ | f θ = c}) : volume s = 0 := by
  apply measure_mono_null hs
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  exact hf.injective (hx.trans hy.symm)

/-- The quantity form of the commitment objective (B.20) at the tight prices. -/
def Pq (P : Params) (α q1 q2 qr : ℝ) : ℝ :=
  q1 * (mun P α - P.vn * q1 - P.rho * P.vn * q2 - P.rho * P.vr * qr)
    + P.rho * q2 * (mun P α - P.vn * (q1 + q2) - P.vr * qr)
    + P.rho * qr * (mur P α - P.vr * (q1 + q2 + qr))

/-- The quantity form of the second-period profit (4.3) at the tight prices. -/
def P2q (P : Params) (α q1 q2 qr : ℝ) : ℝ :=
  q2 * (mun P α - P.vn * (q1 + q2) - P.vr * qr) + qr * (mur P α - P.vr * (q1 + q2 + qr))

section mono
variable (P : Params) (hP : P.Standing) (α p1 p2 pr : ℝ)
include hP

lemma sm12 : StrictMono (fun θ => U1 P α p1 θ - U2 P α p2 θ) := by
  obtain ⟨hvr, hvrn, -, -, -, -, -, hr0, hr1⟩ := hP
  intro x y hxy
  simp only [U1, U2]
  have : 0 < (1 - P.rho) * P.vn * (y - x) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  nlinarith

lemma sm1r : StrictMono (fun θ => U1 P α p1 θ - Ur P α pr θ) := by
  obtain ⟨hvr, hvrn, -, -, -, -, -, hr0, hr1⟩ := hP
  intro x y hxy
  simp only [U1, Ur]
  have h1 : 0 < P.vn - P.rho * P.vr := by nlinarith
  have : 0 < (P.vn - P.rho * P.vr) * (y - x) := mul_pos h1 (by linarith)
  nlinarith

lemma sm2r : StrictMono (fun θ => U2 P α p2 θ - Ur P α pr θ) := by
  obtain ⟨hvr, hvrn, -, -, -, -, -, hr0, hr1⟩ := hP
  intro x y hxy
  simp only [U2, Ur]
  have : 0 < P.rho * (P.vn - P.vr) * (y - x) :=
    mul_pos (mul_pos hr0 (by linarith)) (by linarith)
  nlinarith

end mono

lemma rc_closed_aux (a b : ℝ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    IsClosed {θ | θ ∈ Set.Icc a b ∧ f θ ≤ g θ} :=
  isClosed_Icc.inter (isClosed_le hf hg)

lemma closed_B1 (P : Params) (α p1 p2 pr : ℝ) : IsClosed (buyers1 P α p1 p2 pr) := by
  (try simp only [buyers1, buyersC2, buyersCr, newBuyers2, refBuyers2, U1, U2, Ur]); exact rc_closed_aux _ _ _ _ (by fun_prop) (by fun_prop)
lemma closed_C2 (P : Params) (α p1 p2 pr : ℝ) : IsClosed (buyersC2 P α p1 p2 pr) := by
  (try simp only [buyers1, buyersC2, buyersCr, newBuyers2, refBuyers2, U1, U2, Ur]); exact rc_closed_aux _ _ _ _ (by fun_prop) (by fun_prop)
lemma closed_Cr (P : Params) (α p1 p2 pr : ℝ) : IsClosed (buyersCr P α p1 p2 pr) := by
  (try simp only [buyers1, buyersC2, buyersCr, newBuyers2, refBuyers2, U1, U2, Ur]); exact rc_closed_aux _ _ _ _ (by fun_prop) (by fun_prop)
lemma closed_N2 (P : Params) (α q1 p2 pr : ℝ) : IsClosed (newBuyers2 P α q1 p2 pr) := by
  (try simp only [buyers1, buyersC2, buyersCr, newBuyers2, refBuyers2, U1, U2, Ur]); exact rc_closed_aux _ _ _ _ (by fun_prop) (by fun_prop)
lemma closed_R2 (P : Params) (α q1 p2 pr : ℝ) : IsClosed (refBuyers2 P α q1 p2 pr) := by
  (try simp only [buyers1, buyersC2, buyersCr, newBuyers2, refBuyers2, U1, U2, Ur]); exact rc_closed_aux _ _ _ _ (by fun_prop) (by fun_prop)

/-- Stack structure of the commitment demands. -/
lemma commit_stack (P : Params) (hP : P.Standing) (α p1 p2 pr : ℝ) :
    let Q1 := q1C P α p1 p2 pr
    let Q2 := q2C P α p1 p2 pr
    let QR := qrC P α p1 p2 pr
    Q1 + Q2 + QR ≤ 1 ∧
    (0 < Q1 → ∃ θ ∈ buyers1 P α p1 p2 pr, θ ≤ 1 - Q1) ∧
    (0 < Q2 → ∃ θ ∈ buyersC2 P α p1 p2 pr, θ ≤ 1 - Q1 - Q2) ∧
    (0 < QR → ∃ θ ∈ buyersCr P α p1 p2 pr, θ ≤ 1 - Q1 - Q2 - QR) := by
  intro Q1 Q2 QR
  have h12 := sm12 P hP α p1 p2
  have h1r := sm1r P hP α p1 pr
  have h2r := sm2r P hP α p2 pr
  apply rc_stack3 zero_le_one _ _ _ (fun _ h => h.1) (fun _ h => h.1) (fun _ h => h.1)
    (closed_B1 P α p1 p2 pr) (closed_C2 P α p1 p2 pr) (closed_Cr P α p1 p2 pr)
  · apply rc_null_of_sub _ h12 0
    rintro θ ⟨ha, hb⟩
    simp only [buyers1, buyersC2, Set.mem_setOf_eq, max_le_iff] at ha hb
    simp only [Set.mem_setOf_eq]; linarith [ha.2.1, hb.2.1]
  · apply rc_null_of_sub _ h1r 0
    rintro θ ⟨ha, hb⟩
    simp only [buyers1, buyersCr, Set.mem_setOf_eq, max_le_iff] at ha hb
    simp only [Set.mem_setOf_eq]; linarith [ha.2.2.1, hb.2.1]
  · apply rc_null_of_sub _ h2r 0
    rintro θ ⟨ha, hb⟩
    simp only [buyersC2, buyersCr, Set.mem_setOf_eq, max_le_iff] at ha hb
    simp only [Set.mem_setOf_eq]; linarith [ha.2.2.1, hb.2.2.1]
  · intro x hx y hy
    by_contra hc; push_neg at hc
    have := h12 hc
    simp only [buyers1, buyersC2, Set.mem_setOf_eq, max_le_iff] at hx hy
    simp only at this; linarith [hx.2.1, hy.2.1]
  · intro x hx y hy
    by_contra hc; push_neg at hc
    have := h1r hc
    simp only [buyers1, buyersCr, Set.mem_setOf_eq, max_le_iff] at hx hy
    simp only at this; linarith [hx.2.1, hy.2.2.1]
  · intro x hx y hy
    by_contra hc; push_neg at hc
    have := h2r hc
    simp only [buyersC2, buyersCr, Set.mem_setOf_eq, max_le_iff] at hx hy
    simp only at this; linarith [hx.2.2.1, hy.2.2.1]

lemma mul_le_of_pos_imp {q x y : ℝ} (hq : 0 ≤ q) (h : 0 < q → x ≤ y) : q * x ≤ q * y := by
  rcases hq.lt_or_eq with h' | h'
  · exact mul_le_mul_of_nonneg_left (h h') hq
  · rw [← h']; simp

lemma vol_nonneg' (S : Set ℝ) : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg

/-- **L1.** The commitment objective is bounded by its quantity form. -/
lemma objC_le_Pq (P : Params) (hP : P.Standing) (α p1 p2 pr : ℝ) :
    objC P α p1 p2 pr ≤ Pq P α (q1C P α p1 p2 pr) (q2C P α p1 p2 pr) (qrC P α p1 p2 pr) := by
  obtain ⟨hsum, e1, e2, er⟩ := commit_stack P hP α p1 p2 pr
  have hP' := hP
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP'
  set Q1 := q1C P α p1 p2 pr
  set Q2 := q2C P α p1 p2 pr
  set QR := qrC P α p1 p2 pr
  have hQ1 : 0 ≤ Q1 := vol_nonneg' _
  have hQ2 : 0 ≤ Q2 := vol_nonneg' _
  have hQR : 0 ≤ QR := vol_nonneg' _
  set t1 := 1 - Q1
  set t2 := 1 - Q1 - Q2
  set tr := 1 - Q1 - Q2 - QR
  set PR := P.vr * tr - P.h * P.kr * α
  set P2 := (P.vn - P.vr) * t2 + P.vr * tr - P.h * α
  set P1 := (1 - P.rho) * (P.vn * t1 - P.h * α) + P.rho * P2
  have bR : 0 < QR → pr ≤ PR := by
    intro h
    obtain ⟨θ, hθ, hle⟩ := er h
    simp only [buyersCr, Set.mem_setOf_eq, max_le_iff, Ur] at hθ
    have := hθ.2.2.2
    have h' : 0 ≤ P.vr * θ - P.h * P.kr * α - pr := by
      by_contra hc; push_neg at hc; nlinarith
    nlinarith
  have b2 : 0 < Q2 → p2 ≤ P2 := by
    intro h
    obtain ⟨θ, hθ, hle⟩ := e2 h
    simp only [buyersC2, Set.mem_setOf_eq, max_le_iff, U2, Ur] at hθ
    obtain ⟨-, -, hb, hc⟩ := hθ
    rcases hQR.lt_or_eq with hpos | hzero
    · have := bR hpos
      have h' : P.vr * θ - P.h * P.kr * α - pr ≤ P.vn * θ - P.h * α - p2 := by
        by_contra hc'; push_neg at hc'; nlinarith
      have : (P.vn - P.vr) * θ ≤ (P.vn - P.vr) * t2 :=
        mul_le_mul_of_nonneg_left hle (by linarith)
      simp only [P2, PR] at *; nlinarith
    · have h' : 0 ≤ P.vn * θ - P.h * α - p2 := by
        by_contra hc'; push_neg at hc'; nlinarith
      have htr : tr = t2 := by simp only [tr, t2]; rw [← hzero]; ring
      have : P.vn * θ ≤ P.vn * t2 := mul_le_mul_of_nonneg_left hle (by linarith)
      simp only [P2]; rw [htr]; nlinarith
  have b1 : 0 < Q1 → p1 ≤ P1 := by
    intro h
    obtain ⟨θ, hθ, hle⟩ := e1 h
    simp only [buyers1, Set.mem_setOf_eq, max_le_iff, U1, U2, Ur] at hθ
    obtain ⟨-, ha, hb, hc⟩ := hθ
    rcases hQ2.lt_or_eq with h2 | h2
    · have := b2 h2
      have : (1 - P.rho) * (P.vn * θ) ≤ (1 - P.rho) * (P.vn * t1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by linarith)) (by linarith)
      simp only [P1] at *; nlinarith
    · have ht2 : t2 = t1 := by simp only [t2, t1]; rw [← h2]; ring
      rcases hQR.lt_or_eq with hR | hR
      · have := bR hR
        have hm : (P.vn - P.rho * P.vr) * θ ≤ (P.vn - P.rho * P.vr) * t1 :=
          mul_le_mul_of_nonneg_left hle (by nlinarith)
        have : P.rho * pr ≤ P.rho * PR := mul_le_mul_of_nonneg_left this hr0.le
        simp only [P1, P2, PR] at *; rw [ht2]; nlinarith
      · have htr : tr = t1 := by simp only [tr, t1]; rw [← h2, ← hR]; ring
        have : P.vn * θ ≤ P.vn * t1 := mul_le_mul_of_nonneg_left hle (by linarith)
        simp only [P1, P2]; rw [ht2, htr]; nlinarith
  have k1 := mul_le_of_pos_imp hQ1 (fun h => sub_le_sub_right (b1 h) ((1 + α) * P.cn))
  have k2 := mul_le_of_pos_imp hQ2 (fun h => sub_le_sub_right (b2 h) ((1 + α) * P.cn))
  have kR := mul_le_of_pos_imp hQR (fun h => sub_le_sub_right (bR h) ((1 + P.kr * α) * P.cr))
  have : objC P α p1 p2 pr ≤ Q1 * (P1 - (1 + α) * P.cn) + P.rho * (Q2 * (P2 - (1 + α) * P.cn))
      + P.rho * (QR * (PR - (1 + P.kr * α) * P.cr)) := by
    unfold objC
    have := mul_le_mul_of_nonneg_left k2 hr0.le
    have := mul_le_mul_of_nonneg_left kR hr0.le
    nlinarith
  refine this.trans (le_of_eq ?_)
  simp only [Pq, mun, mur, P1, P2, PR, t1, t2, tr]; ring

/-- Stack structure of the second-period demands in the residual market `[0, 1 - q1]`. -/
lemma second_stack (P : Params) (hP : P.Standing) (α q1 p2 pr : ℝ) (hq1 : q1 ≤ 1) :
    let Q2 := q2 P α q1 p2 pr
    let QR := qr P α q1 p2 pr
    Q2 + QR ≤ 1 - q1 ∧
    (0 < Q2 → ∃ θ ∈ newBuyers2 P α q1 p2 pr, θ ≤ 1 - q1 - Q2) ∧
    (0 < QR → ∃ θ ∈ refBuyers2 P α q1 p2 pr, θ ≤ 1 - q1 - Q2 - QR) := by
  intro Q2 QR
  have h2r := sm2r P hP α p2 pr
  have := rc_stack3 (b := 1 - q1) (by linarith) ∅ (newBuyers2 P α q1 p2 pr)
    (refBuyers2 P α q1 p2 pr) (Set.empty_subset _) (fun _ h => h.1) (fun _ h => h.1)
    isClosed_empty (closed_N2 P α q1 p2 pr) (closed_R2 P α q1 p2 pr) (by simp) (by simp)
    (by
      apply rc_null_of_sub _ h2r 0
      rintro θ ⟨ha, hb⟩
      simp only [newBuyers2, refBuyers2, Set.mem_setOf_eq, max_le_iff] at ha hb
      simp only [Set.mem_setOf_eq]; linarith [ha.2.1, hb.2.1])
    (by simp) (by simp)
    (by
      intro x hx y hy
      by_contra hc; push_neg at hc
      have := h2r hc
      simp only [newBuyers2, refBuyers2, Set.mem_setOf_eq, max_le_iff] at hx hy
      simp only at this; linarith [hx.2.1, hy.2.1])
  simp only [measure_empty, ENNReal.toReal_zero, zero_add, sub_zero] at this
  exact ⟨this.1, this.2.2.1, this.2.2.2⟩

/-- **L2.** Second-period profit is bounded by its quantity form. -/
lemma profit2_le_P2q (P : Params) (hP : P.Standing) (α q1 p2 pr : ℝ) (hq1 : q1 ≤ 1) :
    profit2 P α q1 p2 pr ≤ P2q P α q1 (q2 P α q1 p2 pr) (qr P α q1 p2 pr) := by
  obtain ⟨hsum, e2, er⟩ := second_stack P hP α q1 p2 pr hq1
  have hP' := hP
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP'
  set Q2 := q2 P α q1 p2 pr
  set QR := qr P α q1 p2 pr
  have hQ2 : 0 ≤ Q2 := vol_nonneg' _
  have hQR : 0 ≤ QR := vol_nonneg' _
  set t2 := 1 - q1 - Q2
  set tr := 1 - q1 - Q2 - QR
  set PR := P.vr * tr - P.h * P.kr * α
  set P2 := (P.vn - P.vr) * t2 + P.vr * tr - P.h * α
  have bR : 0 < QR → pr ≤ PR := by
    intro h
    obtain ⟨θ, hθ, hle⟩ := er h
    simp only [refBuyers2, Set.mem_setOf_eq, max_le_iff, Ur] at hθ
    have := hθ.2.2
    have h' : 0 ≤ P.vr * θ - P.h * P.kr * α - pr := by
      by_contra hc; push_neg at hc; nlinarith
    nlinarith
  have b2 : 0 < Q2 → p2 ≤ P2 := by
    intro h
    obtain ⟨θ, hθ, hle⟩ := e2 h
    simp only [newBuyers2, Set.mem_setOf_eq, max_le_iff, U2, Ur] at hθ
    obtain ⟨-, hb, hc⟩ := hθ
    rcases hQR.lt_or_eq with hpos | hzero
    · have := bR hpos
      have h' : P.vr * θ - P.h * P.kr * α - pr ≤ P.vn * θ - P.h * α - p2 := by
        by_contra hc'; push_neg at hc'; nlinarith
      have : (P.vn - P.vr) * θ ≤ (P.vn - P.vr) * t2 :=
        mul_le_mul_of_nonneg_left hle (by linarith)
      simp only [P2, PR] at *; nlinarith
    · have h' : 0 ≤ P.vn * θ - P.h * α - p2 := by
        by_contra hc'; push_neg at hc'; nlinarith
      have htr : tr = t2 := by simp only [tr, t2]; rw [← hzero]; ring
      have : P.vn * θ ≤ P.vn * t2 := mul_le_mul_of_nonneg_left hle (by linarith)
      simp only [P2]; rw [htr]; nlinarith
  have k2 := mul_le_of_pos_imp hQ2 (fun h => sub_le_sub_right (b2 h) ((1 + α) * P.cn))
  have kR := mul_le_of_pos_imp hQR (fun h => sub_le_sub_right (bR h) ((1 + P.kr * α) * P.cr))
  have : profit2 P α q1 p2 pr ≤ Q2 * (P2 - (1 + α) * P.cn)
      + QR * (PR - (1 + P.kr * α) * P.cr) := by
    unfold profit2; linarith
  refine this.trans (le_of_eq ?_)
  simp only [P2q, mun, mur, P2, PR, t2, tr]; ring

/-! ### Tight prices -/

def tpr (P : Params) (α q1 q2 qr : ℝ) : ℝ := P.vr * (1 - q1 - q2 - qr) - P.h * P.kr * α
def tp2 (P : Params) (α q1 q2 qr : ℝ) : ℝ :=
  (P.vn - P.vr) * (1 - q1 - q2) + P.vr * (1 - q1 - q2 - qr) - P.h * α
def tp1 (P : Params) (α q1 q2 qr : ℝ) : ℝ :=
  (1 - P.rho) * (P.vn * (1 - q1) - P.h * α) + P.rho * tp2 P α q1 q2 qr

lemma Ur_tight (P : Params) (α q1 q2 qr θ : ℝ) :
    Ur P α (tpr P α q1 q2 qr) θ = P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := by
  simp only [Ur, tpr]; ring
lemma U2_tight (P : Params) (α q1 q2 qr θ : ℝ) :
    U2 P α (tp2 P α q1 q2 qr) θ = P.rho * (P.vn - P.vr) * (θ - (1 - q1 - q2))
      + P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := by
  simp only [U2, tp2]; ring
lemma U1_tight (P : Params) (α q1 q2 qr θ : ℝ) :
    U1 P α (tp1 P α q1 q2 qr) θ = (1 - P.rho) * P.vn * (θ - (1 - q1))
      + P.rho * (P.vn - P.vr) * (θ - (1 - q1 - q2))
      + P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := by
  simp only [U1, tp1, tp2]; ring

lemma tight_consts (P : Params) (hP : P.Standing) : 0 < (1 - P.rho) * P.vn ∧ 0 < P.rho * (P.vn - P.vr) ∧ 0 < P.rho * P.vr := by
  obtain ⟨hvr, hvrn, -, -, -, -, -, hr0, hr1⟩ := hP
  exact ⟨mul_pos (by linarith) (by linarith), mul_pos hr0 (by linarith), mul_pos hr0 hvr⟩

lemma vol_Icc_toReal {a b : ℝ} (h : a ≤ b) : (volume (Set.Icc a b)).toReal = b - a := by
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

section tight
variable (P : Params) (hP : P.Standing) (α q1 q2 qr : ℝ) (h1 : 0 ≤ q1) (h2 : 0 ≤ q2) (hr : 0 ≤ qr)
  (hs : q1 + q2 + qr ≤ 1)
include hP h1 h2 hr hs

lemma B1_tight : buyers1 P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr)
    = Set.Icc (1 - q1) 1 := by
  obtain ⟨ka, kb, kc⟩ := tight_consts P hP
  ext θ
  simp only [buyers1, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U1_tight, U2_tight, Ur_tight]
  constructor
  · rintro ⟨⟨-, hb⟩, hu, -, -⟩
    refine ⟨?_, hb⟩
    have : 0 ≤ (1 - P.rho) * P.vn * (θ - (1 - q1)) := by linarith
    have := (mul_nonneg_iff_of_pos_left ka).1 this
    linarith
  · rintro ⟨ha, hb⟩
    have e1 : 0 ≤ (1 - P.rho) * P.vn * (θ - (1 - q1)) := mul_nonneg ka.le (by linarith)
    have e2 : 0 ≤ P.rho * (P.vn - P.vr) * (θ - (1 - q1 - q2)) := mul_nonneg kb.le (by linarith)
    have e3 : 0 ≤ P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := mul_nonneg kc.le (by linarith)
    refine ⟨⟨by linarith, hb⟩, by linarith, by linarith, by linarith⟩

lemma C2_tight : buyersC2 P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr)
    = Set.Icc (1 - q1 - q2) (1 - q1) := by
  obtain ⟨ka, kb, kc⟩ := tight_consts P hP
  ext θ
  simp only [buyersC2, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U1_tight, U2_tight, Ur_tight]
  constructor
  · rintro ⟨-, hu, hv, -⟩
    have : 0 ≤ (1 - P.rho) * P.vn * ((1 - q1) - θ) := by linarith
    have := (mul_nonneg_iff_of_pos_left ka).1 this
    have : 0 ≤ P.rho * (P.vn - P.vr) * (θ - (1 - q1 - q2)) := by linarith
    have := (mul_nonneg_iff_of_pos_left kb).1 this
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    have e1 : 0 ≤ (1 - P.rho) * P.vn * ((1 - q1) - θ) := mul_nonneg ka.le (by linarith)
    have e2 : 0 ≤ P.rho * (P.vn - P.vr) * (θ - (1 - q1 - q2)) := mul_nonneg kb.le (by linarith)
    have e3 : 0 ≤ P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := mul_nonneg kc.le (by linarith)
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩

lemma Cr_tight : buyersCr P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr)
    = Set.Icc (1 - q1 - q2 - qr) (1 - q1 - q2) := by
  obtain ⟨ka, kb, kc⟩ := tight_consts P hP
  ext θ
  simp only [buyersCr, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U1_tight, U2_tight, Ur_tight]
  constructor
  · rintro ⟨-, -, hu, hv⟩
    have : 0 ≤ P.rho * (P.vn - P.vr) * ((1 - q1 - q2) - θ) := by linarith
    have := (mul_nonneg_iff_of_pos_left kb).1 this
    have := (mul_nonneg_iff_of_pos_left kc).1 hv
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    have e1 : 0 ≤ (1 - P.rho) * P.vn * ((1 - q1) - θ) := mul_nonneg ka.le (by linarith)
    have e2 : 0 ≤ P.rho * (P.vn - P.vr) * ((1 - q1 - q2) - θ) := mul_nonneg kb.le (by linarith)
    have e3 : 0 ≤ P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := mul_nonneg kc.le (by linarith)
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩

lemma N2_tight : newBuyers2 P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr)
    = Set.Icc (1 - q1 - q2) (1 - q1) := by
  obtain ⟨ka, kb, kc⟩ := tight_consts P hP
  ext θ
  simp only [newBuyers2, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U2_tight, Ur_tight]
  constructor
  · rintro ⟨⟨-, hb⟩, hv, -⟩
    have : 0 ≤ P.rho * (P.vn - P.vr) * (θ - (1 - q1 - q2)) := by linarith
    have := (mul_nonneg_iff_of_pos_left kb).1 this
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    have e2 : 0 ≤ P.rho * (P.vn - P.vr) * (θ - (1 - q1 - q2)) := mul_nonneg kb.le (by linarith)
    have e3 : 0 ≤ P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := mul_nonneg kc.le (by linarith)
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma R2_tight : refBuyers2 P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr)
    = Set.Icc (1 - q1 - q2 - qr) (1 - q1 - q2) := by
  obtain ⟨ka, kb, kc⟩ := tight_consts P hP
  ext θ
  simp only [refBuyers2, Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, U2_tight, Ur_tight]
  constructor
  · rintro ⟨-, hu, hv⟩
    have : 0 ≤ P.rho * (P.vn - P.vr) * ((1 - q1 - q2) - θ) := by linarith
    have := (mul_nonneg_iff_of_pos_left kb).1 this
    have := (mul_nonneg_iff_of_pos_left kc).1 hv
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    have e2 : 0 ≤ P.rho * (P.vn - P.vr) * ((1 - q1 - q2) - θ) := mul_nonneg kb.le (by linarith)
    have e3 : 0 ≤ P.rho * P.vr * (θ - (1 - q1 - q2 - qr)) := mul_nonneg kc.le (by linarith)
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **L3 (commitment).** Tight prices realize the quantities and the quantity-form profit. -/
lemma commit_tight :
    q1C P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = q1 ∧
    q2C P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = q2 ∧
    qrC P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = qr ∧
    objC P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = Pq P α q1 q2 qr := by
  have e1 : q1C P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = q1 := by
    unfold q1C; rw [B1_tight P hP α q1 q2 qr h1 h2 hr hs, vol_Icc_toReal (by linarith)]; ring
  have e2 : q2C P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = q2 := by
    unfold q2C; rw [C2_tight P hP α q1 q2 qr h1 h2 hr hs, vol_Icc_toReal (by linarith)]; ring
  have e3 : qrC P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = qr := by
    unfold qrC; rw [Cr_tight P hP α q1 q2 qr h1 h2 hr hs, vol_Icc_toReal (by linarith)]; ring
  refine ⟨e1, e2, e3, ?_⟩
  unfold objC; rw [e1, e2, e3]
  simp only [Pq, tp1, tp2, tpr, mun, mur]; ring

/-- **L3 (second period).** -/
lemma second_tight :
    (volume (buyers1 P α (tp1 P α q1 q2 qr) (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr))).toReal = q1 ∧
    DefectProfit.q2 P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = q2 ∧
    DefectProfit.qr P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = qr ∧
    profit2 P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = P2q P α q1 q2 qr ∧
    totalProfit P α (tp1 P α q1 q2 qr) q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr)
      = Pq P α q1 q2 qr := by
  have e1 := (commit_tight P hP α q1 q2 qr h1 h2 hr hs).1
  have e2 : DefectProfit.q2 P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = q2 := by
    unfold DefectProfit.q2; rw [N2_tight P hP α q1 q2 qr h1 h2 hr hs, vol_Icc_toReal (by linarith)]; ring
  have e3 : DefectProfit.qr P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = qr := by
    unfold DefectProfit.qr; rw [R2_tight P hP α q1 q2 qr h1 h2 hr hs, vol_Icc_toReal (by linarith)]; ring
  have e4 : profit2 P α q1 (tp2 P α q1 q2 qr) (tpr P α q1 q2 qr) = P2q P α q1 q2 qr := by
    unfold profit2; rw [e2, e3]; simp only [P2q, tp2, tpr, mun, mur]; ring
  refine ⟨e1, e2, e3, e4, ?_⟩
  unfold totalProfit; rw [e4]; simp only [Pq, P2q, tp1, tp2, tpr, mun, mur]; ring

end tight

end RefurbCommit.DefectProfit



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



namespace RefurbCommit.DefectProfit

def RegC (P : Params) (α q1 q2 qr : ℝ) : Prop :=
  0 ≤ q1 ∧ 0 ≤ q2 ∧ 0 ≤ qr ∧ q1 + q2 + qr ≤ 1 ∧ (1 + P.kr * α) * qr ≤ α * q1

def Reg2 (P : Params) (α q1 q2 qr : ℝ) : Prop :=
  0 ≤ q2 ∧ 0 ≤ qr ∧ q2 + qr ≤ 1 - q1 ∧ (1 + P.kr * α) * qr ≤ α * q1

def IsMax2 (P : Params) (α q1 a b : ℝ) : Prop :=
  Reg2 P α q1 a b ∧ ∀ c d, Reg2 P α q1 c d → P2q P α q1 c d ≤ P2q P α q1 a b

lemma PiC_le_of (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) (M : ℝ)
    (hM : ∀ q1 q2 qr, RegC P α q1 q2 qr → Pq P α q1 q2 qr ≤ M) : PiC P α ≤ M := by
  have h0 : RegC P α 0 0 0 := by
    refine ⟨le_refl _, le_refl _, le_refl _, by norm_num, by simp⟩
  have hne : ({v | ∃ p1 p2 pr, FeasibleC P α p1 p2 pr ∧ v = objC P α p1 p2 pr}).Nonempty := by
    obtain ⟨-, -, e3, -⟩ := commit_tight P hP α 0 0 0 le_rfl le_rfl le_rfl (by norm_num)
    obtain ⟨e1, -, -, -⟩ := commit_tight P hP α 0 0 0 le_rfl le_rfl le_rfl (by norm_num)
    refine ⟨_, tp1 P α 0 0 0, tp2 P α 0 0 0, tpr P α 0 0 0, ?_, rfl⟩
    unfold FeasibleC; rw [e1, e3]; simp
  unfold PiC
  apply csSup_le hne
  rintro v ⟨p1, p2, pr, hf, rfl⟩
  obtain ⟨hsum, -, -, -⟩ := commit_stack P hP α p1 p2 pr
  refine (objC_le_Pq P hP α p1 p2 pr).trans (hM _ _ _ ?_)
  exact ⟨vol_nonneg' _, vol_nonneg' _, vol_nonneg' _, hsum, hf⟩

lemma le_PiC_of (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) (q1 q2 qr : ℝ)
    (h : RegC P α q1 q2 qr) : Pq P α q1 q2 qr ≤ PiC P α := by
  obtain ⟨h1, h2, hr, hs, hf⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := commit_tight P hP α q1 q2 qr h1 h2 hr hs
  apply le_csSup (objC_bdd P hP α hα)
  refine ⟨tp1 P α q1 q2 qr, tp2 P α q1 q2 qr, tpr P α q1 q2 qr, ?_, e4.symm⟩
  unfold FeasibleC; rw [e1, e3]; exact hf

lemma SP_facts (P : Params) (hP : P.Standing) (α : ℝ) (p1 q1 p2 pr : ℝ)
    (h : IsSPOutcome P α p1 q1 p2 pr) :
    0 ≤ q1 ∧ q1 ≤ 1 ∧ IsMax2 P α q1 (DefectProfit.q2 P α q1 p2 pr) (DefectProfit.qr P α q1 p2 pr) ∧
      totalProfit P α p1 q1 p2 pr ≤
        Pq P α q1 (DefectProfit.q2 P α q1 p2 pr) (DefectProfit.qr P α q1 p2 pr) := by
  obtain ⟨hq, hopt⟩ := h
  have hq0 : 0 ≤ q1 := hq ▸ vol_nonneg' _
  have hq1 : q1 ≤ 1 := hq ▸ vol_toReal_le_one (fun _ h => h.1)
  have e2 := q2_eq_q2C P hP α p1 q1 p2 pr hq
  have er := qr_eq_qrC P hP α p1 q1 p2 pr hq
  obtain ⟨hsum, -, -⟩ := second_stack P hP α q1 p2 pr hq1
  refine ⟨hq0, hq1, ⟨⟨vol_nonneg' _, vol_nonneg' _, hsum, hopt.1⟩, ?_⟩, ?_⟩
  · rintro c d ⟨hc, hd, hcd, hf⟩
    obtain ⟨-, f2, f3, f4, -⟩ := second_tight P hP α q1 c d hq0 hc hd (by linarith)
    have hfe : Feasible2 P α q1 (tp2 P α q1 c d) (tpr P α q1 c d) := by
      unfold Feasible2; rw [f3]; exact hf
    have := hopt.2 _ _ hfe
    rw [f4] at this
    exact this.trans (profit2_le_P2q P hP α q1 p2 pr hq1)
  · have hval : totalProfit P α p1 q1 p2 pr = objC P α p1 p2 pr := by
      unfold totalProfit profit2 objC q1C
      rw [e2, er, ← hq]; ring
    rw [hval]
    have := objC_le_Pq P hP α p1 p2 pr
    unfold q1C at this
    rwa [← hq, ← e2, ← er] at this

lemma PiStar_set_bdd (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) :
    BddAbove {v | ∃ p1 q1 p2 pr, IsSPOutcome P α p1 q1 p2 pr ∧ v = totalProfit P α p1 q1 p2 pr} := by
  refine ⟨P.vn + P.rho * P.vn + P.rho * P.vr, ?_⟩
  rintro v ⟨p1, q1, p2, pr, ⟨hq, hopt⟩, rfl⟩
  have e2 := q2_eq_q2C P hP α p1 q1 p2 pr hq
  have er := qr_eq_qrC P hP α p1 q1 p2 pr hq
  have hval : totalProfit P α p1 q1 p2 pr = objC P α p1 p2 pr := by
    unfold totalProfit profit2 objC q1C
    rw [e2, er, ← hq]; ring
  rw [hval]; exact objC_le P hP α hα p1 p2 pr

lemma PiStar_le_of (P : Params) (hP : P.Standing) (α : ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ q1 a b, 0 ≤ q1 → q1 ≤ 1 → IsMax2 P α q1 a b → Pq P α q1 a b ≤ M) :
    PiStar P α ≤ M := by
  unfold PiStar
  rcases Set.eq_empty_or_nonempty
    {v | ∃ p1 q1 p2 pr, IsSPOutcome P α p1 q1 p2 pr ∧ v = totalProfit P α p1 q1 p2 pr} with h | h
  · rw [h, Real.sSup_empty]; exact hM0
  apply csSup_le h
  rintro v ⟨p1, q1, p2, pr, hsp, rfl⟩
  obtain ⟨h0, h1, hmax, hle⟩ := SP_facts P hP α p1 q1 p2 pr hsp
  exact hle.trans (hM _ _ _ h0 h1 hmax)

lemma le_PiStar_of (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) (q1 a b : ℝ)
    (h0 : 0 ≤ q1) (hmax : IsMax2 P α q1 a b) : Pq P α q1 a b ≤ PiStar P α := by
  obtain ⟨⟨ha, hb, hab, hf⟩, hopt⟩ := hmax
  obtain ⟨f1, f2, f3, f4, f5⟩ := second_tight P hP α q1 a b h0 ha hb (by linarith)
  apply le_csSup (PiStar_set_bdd P hP α hα)
  refine ⟨tp1 P α q1 a b, q1, tp2 P α q1 a b, tpr P α q1 a b, ⟨f1.symm, ?_, ?_⟩, f5.symm⟩
  · unfold Feasible2; rw [f3]; exact hf
  · intro p2' pr' hfe
    rw [f4]
    have hq1 : q1 ≤ 1 := by linarith
    refine (profit2_le_P2q P hP α q1 p2' pr' hq1).trans (hopt _ _ ?_)
    obtain ⟨hsum, -, -⟩ := second_stack P hP α q1 p2' pr' hq1
    exact ⟨vol_nonneg' _, vol_nonneg' _, hsum, hfe⟩

end RefurbCommit.DefectProfit



namespace RefurbCommit.DefectProfit

/-- Concave-quadratic (Taylor) form of the commitment Lagrangian around `(u, 0, w)`. -/
lemma saddle_of_kkt (P : Params) (hP : P.Standing) (α u w lam : ℝ)
    (g1 : mun P α - 2 * P.vn * u - 2 * P.rho * P.vr * w + lam * α = 0)
    (g2 : mun P α - 2 * P.vn * u - 2 * P.vr * w ≤ 0)
    (gx : P.rho * (mur P α - 2 * P.vr * u - 2 * P.vr * w) - lam * (1 + P.kr * α) = 0 ∨
      (w = 0 ∧ P.rho * (mur P α - 2 * P.vr * u - 2 * P.vr * w) - lam * (1 + P.kr * α) ≤ 0))
    (q1 q2 x : ℝ) (h2 : 0 ≤ q2) (hx : 0 ≤ x) :
    Pq P α q1 q2 x + lam * (α * q1 - (1 + P.kr * α) * x)
      ≤ Pq P α u 0 w + lam * (α * u - (1 + P.kr * α) * w) := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  have iden : Pq P α q1 q2 x + lam * (α * q1 - (1 + P.kr * α) * x)
      = Pq P α u 0 w + lam * (α * u - (1 + P.kr * α) * w)
        + (mun P α - 2 * P.vn * u - 2 * P.rho * P.vr * w + lam * α) * (q1 - u)
        + P.rho * (mun P α - 2 * P.vn * u - 2 * P.vr * w) * q2
        + (P.rho * (mur P α - 2 * P.vr * u - 2 * P.vr * w) - lam * (1 + P.kr * α)) * (x - w)
        - ((1 - P.rho) * P.vn * (q1 - u) ^ 2 + P.rho * (P.vn - P.vr) * (q1 - u + q2) ^ 2
          + P.rho * P.vr * (q1 - u + q2 + (x - w)) ^ 2) := by
    unfold Pq; ring
  rw [iden, g1]
  have hQ : 0 ≤ (1 - P.rho) * P.vn * (q1 - u) ^ 2 + P.rho * (P.vn - P.vr) * (q1 - u + q2) ^ 2
      + P.rho * P.vr * (q1 - u + q2 + (x - w)) ^ 2 := by
    have : 0 ≤ (1 - P.rho) * P.vn := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ P.rho * (P.vn - P.vr) := mul_nonneg hr0.le (by linarith)
    have : 0 ≤ P.rho * P.vr := mul_nonneg hr0.le hvr.le
    positivity
  have t2 : P.rho * (mun P α - 2 * P.vn * u - 2 * P.vr * w) * q2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr0.le g2) h2
  have t3 : (P.rho * (mur P α - 2 * P.vr * u - 2 * P.vr * w) - lam * (1 + P.kr * α)) * (x - w) ≤ 0 := by
    rcases gx with h | ⟨hw, h⟩
    · rw [h]; simp
    · subst hw; rw [sub_zero]; exact mul_nonpos_of_nonpos_of_nonneg h hx
  linarith

lemma PiC_nonpos_of (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α)
    (ha : mun P α ≤ 0) (hA : mun P α * (1 + P.kr * α) + P.rho * α * mur P α ≤ 0) :
    PiC P α ≤ 0 := by
  have hP' := hP
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP'
  have hK : 0 < 1 + P.kr * α := by nlinarith
  apply PiC_le_of P hP α hα
  rintro q1 q2 x ⟨h1, h2, hx, hs, hf⟩
  have hle : Pq P α q1 q2 x ≤ q1 * mun P α + P.rho * q2 * mun P α + P.rho * x * mur P α := by
    have : Pq P α q1 q2 x = q1 * mun P α + P.rho * q2 * mun P α + P.rho * x * mur P α
        - ((1 - P.rho) * P.vn * q1 ^ 2 + P.rho * (P.vn - P.vr) * (q1 + q2) ^ 2
          + P.rho * P.vr * (q1 + q2 + x) ^ 2) := by unfold Pq; ring
    rw [this]
    have : 0 ≤ (1 - P.rho) * P.vn := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ P.rho * (P.vn - P.vr) := mul_nonneg hr0.le (by linarith)
    have : 0 ≤ P.rho * P.vr := mul_nonneg hr0.le hvr.le
    have : 0 ≤ (1 - P.rho) * P.vn * q1 ^ 2 + P.rho * (P.vn - P.vr) * (q1 + q2) ^ 2
          + P.rho * P.vr * (q1 + q2 + x) ^ 2 := by positivity
    linarith
  refine hle.trans ?_
  have t2 : P.rho * q2 * mun P α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr0.le h2) ha
  rcases le_total 0 (mur P α) with hm | hm
  · -- K (q1 a + ρ x m) ≤ q1 (a K + ρ α m) ≤ 0
    have k1 : (1 + P.kr * α) * (P.rho * x * mur P α) ≤ P.rho * α * q1 * mur P α := by
      have := mul_le_mul_of_nonneg_right hf (mul_nonneg hr0.le hm)
      nlinarith
    have k2 : (1 + P.kr * α) * (q1 * mun P α + P.rho * x * mur P α) ≤ 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hA]
    have : q1 * mun P α + P.rho * x * mur P α ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    linarith
  · have : P.rho * x * mur P α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr0.le hx) hm
    have : q1 * mun P α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 ha
    linarith

lemma mur_le (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) : mur P α ≤ P.vr := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  unfold mur
  have : 0 ≤ (1 + P.kr * α) * P.cr := mul_nonneg (by nlinarith) hcr
  have : 0 ≤ P.h * P.kr * α := by positivity
  linarith

lemma mun_le (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) : mun P α ≤ P.vn := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  unfold mun
  have : 0 ≤ (1 + α) * P.cn := mul_nonneg (by linarith) (by linarith)
  have : 0 ≤ P.h * α := by positivity
  linarith

/-- Algebraic KKT analysis of the commitment problem in the variables `(q1, x)`. -/
lemma kkt_alg (vn vr rho cn h α a m K : ℝ) (hvr : 0 < vr) (hvrn : vr < vn) (hr0 : 0 < rho)
    (hr1 : rho < 1) (hα : 0 < α) (hcn : 0 < cn) (hh : 0 ≤ h) (hK1 : 1 ≤ K)
    (ea : a = vn - cn - α * (cn + h)) (hmle : m ≤ vr) :
    (a ≤ 0 ∧ a * K + rho * α * m ≤ 0) ∨
    ∃ u w lam, 0 ≤ lam ∧ lam < cn + h ∧ 0 ≤ u ∧ 0 ≤ w ∧ u + w ≤ 1 ∧ K * w ≤ α * u ∧
      lam * (α * u - K * w) = 0 ∧
      a - 2 * vn * u - 2 * rho * vr * w + lam * α = 0 ∧
      a - 2 * vn * u - 2 * vr * w ≤ 0 ∧
      (rho * (m - 2 * vr * u - 2 * vr * w) - lam * K = 0 ∨
        (w = 0 ∧ rho * (m - 2 * vr * u - 2 * vr * w) - lam * K ≤ 0)) := by
  have hvn : 0 < vn := by linarith
  have hK : 0 < K := by linarith
  have hD : 0 < vn - rho * vr := by nlinarith
  have hale : a ≤ vn := by rw [ea]; nlinarith
  rcases le_or_gt (m * vn) (vr * a) with hN | hN
  · -- Case N: no refurbishing
    by_cases ha : a ≤ 0
    · left
      refine ⟨ha, ?_⟩
      have : m ≤ 0 := by
        by_contra hm; push_neg at hm
        nlinarith [mul_pos hm hvn, mul_nonpos_of_nonneg_of_nonpos hvr.le ha]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr0.le hα.le) this,
        mul_nonpos_of_nonpos_of_nonneg ha hK.le]
    push_neg at ha
    right
    have hu2 : 2 * vn * (a / (2 * vn)) = a := by field_simp
    have hu0 : 0 ≤ a / (2 * vn) := by positivity
    have hu1 : a / (2 * vn) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    refine ⟨a / (2 * vn), 0, 0, le_rfl, by linarith, hu0, le_rfl, by linarith, by simp; positivity,
      by simp, by linarith, by linarith, Or.inr ⟨rfl, ?_⟩⟩
    have : m * vn ≤ vr * (2 * vn * (a / (2 * vn))) := by rw [hu2]; exact hN
    have : m ≤ 2 * vr * (a / (2 * vn)) := by nlinarith
    nlinarith
  have hD' : vn - rho * vr ≠ 0 := hD.ne'
  have e_uI : 2 * (vn - rho * vr) * ((a - rho * m) / (2 * (vn - rho * vr))) = a - rho * m := by
    field_simp
  have e_wI : 2 * vr * (vn - rho * vr) * ((m * vn - vr * a) / (2 * vr * (vn - rho * vr)))
      = m * vn - vr * a := by
    have hne : 2 * vr * (vn - rho * vr) ≠ 0 := (mul_pos (mul_pos two_pos hvr) hD).ne'
    rw [mul_comm]; exact div_mul_cancel₀ _ hne
  generalize huI : (a - rho * m) / (2 * (vn - rho * vr)) = uI at e_uI
  generalize hwI : (m * vn - vr * a) / (2 * vr * (vn - rho * vr)) = wI at e_wI
  have hwI0 : 0 < wI := by rw [← hwI]; apply div_pos (by linarith) (by positivity)
  have hsumI : 2 * vr * (uI + wI) = m := by
    have h1 : (vn - rho * vr) * (2 * vr * (uI + wI)) = (vn - rho * vr) * m := by nlinarith
    exact mul_left_cancel₀ hD.ne' h1
  have g1I : a - 2 * vn * uI - 2 * rho * vr * wI = 0 := by
    have h1 : (vn - rho * vr) * (a - 2 * vn * uI - 2 * rho * vr * wI) = 0 := by nlinarith
    exact (mul_eq_zero.1 h1).resolve_left hD.ne'
  rcases le_or_gt (K * wI) (α * uI) with hI | hI
  · -- Case I: interior refurbishing
    have huI0 : 0 ≤ uI := by
      have : 0 ≤ α * uI := le_trans (mul_nonneg hK.le hwI0.le) hI
      by_contra hc; push_neg at hc; nlinarith [mul_neg_of_pos_of_neg hα hc]
    right
    refine ⟨uI, wI, 0, le_rfl, by linarith, huI0, hwI0.le, by nlinarith, hI, by simp,
      by linarith, by nlinarith [mul_pos hvr hwI0], Or.inl (by nlinarith)⟩
  · -- Case B: all returns refurbished
    have hcond : 0 < m * (vn * K + rho * vr * α) - a * vr * (K + α) := by
      have h1 : α * vr * (2 * (vn - rho * vr) * uI) < K * (2 * vr * (vn - rho * vr) * wI) := by
        have := mul_lt_mul_of_pos_left hI (mul_pos (mul_pos two_pos hvr) hD)
        have e1 : α * vr * (2 * (vn - rho * vr) * uI) = 2 * vr * (vn - rho * vr) * (α * uI) := by ring
        have e2 : K * (2 * vr * (vn - rho * vr) * wI) = 2 * vr * (vn - rho * vr) * (K * wI) := by ring
        rw [e1, e2]; exact this
      rw [e_uI, e_wI] at h1
      have e3 : α * vr * (a - rho * m) = α * vr * a - rho * vr * α * m := by ring
      have e4 : K * (m * vn - vr * a) = m * vn * K - a * vr * K := by ring
      have e5 : m * (vn * K + rho * vr * α) - a * vr * (K + α)
          = (m * vn * K - a * vr * K) - (α * vr * a - rho * vr * α * m) := by ring
      rw [e5]; rw [e3, e4] at h1; linarith
    by_cases hApos : a * K + rho * α * m ≤ 0
    · left
      refine ⟨?_, hApos⟩
      by_contra ha; push_neg at ha
      have hm : 0 < m := by
        by_contra hm; push_neg at hm
        have : 0 < vn * K + rho * vr * α := by
          have := mul_pos hvn hK; have := mul_pos (mul_pos hr0 hvr) hα; linarith
        linarith [mul_nonpos_of_nonpos_of_nonneg hm this.le,
          mul_pos (mul_pos ha hvr) (by linarith : (0:ℝ) < K + α)]
      linarith [mul_pos (mul_pos hr0 hα) hm, mul_pos ha hK]
    push_neg at hApos
    right
    have hEpos : 0 < vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2 := by
      have := mul_pos hvn (pow_pos hK 2)
      have := mul_pos (mul_pos (mul_pos (mul_pos two_pos hr0) hvr) hα) hK
      have := mul_pos (mul_pos hr0 hvr) (pow_pos hα 2)
      linarith
    have hlam0 : 0 < rho * (m * (vn * K + rho * vr * α) - a * vr * (K + α)) /
        (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2) := div_pos (mul_pos hr0 hcond) hEpos
    have huB0 : 0 < K * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)) :=
      div_pos (mul_pos hK hApos) (by linarith)
    have hwB0 : 0 < α * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)) :=
      div_pos (mul_pos hα hApos) (by linarith)
    have g1 : a - 2 * vn * (K * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)))
        - 2 * rho * vr * (α * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)))
        + rho * (m * (vn * K + rho * vr * α) - a * vr * (K + α)) /
          (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2) * α = 0 := by
      field_simp; ring
    have gx : rho * (m - 2 * vr * (K * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)))
        - 2 * vr * (α * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2))))
        - rho * (m * (vn * K + rho * vr * α) - a * vr * (K + α)) /
          (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2) * K = 0 := by
      field_simp; ring
    have hfeas : K * (α * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)))
        = α * (K * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2))) := by
      ring
    generalize rho * (m * (vn * K + rho * vr * α) - a * vr * (K + α)) /
        (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2) = lam at hlam0 g1 gx
    generalize K * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)) = uB
      at huB0 g1 gx hfeas
    generalize α * (a * K + rho * α * m) / (2 * (vn * K ^ 2 + 2 * rho * vr * α * K + rho * vr * α ^ 2)) = wB
      at hwB0 g1 gx hfeas
    have hX : 0 ≤ m - 2 * vr * uB - 2 * vr * wB := by
      have h1 : 0 ≤ rho * (m - 2 * vr * uB - 2 * vr * wB) := by
        have : 0 ≤ lam * K := mul_nonneg hlam0.le hK.le
        linarith
      exact (mul_nonneg_iff_of_pos_left hr0).1 h1
    have hsumB : uB + wB ≤ 1 / 2 := by
      have : vr * (2 * (uB + wB)) ≤ vr * 1 := by linarith
      have := le_of_mul_le_mul_left this hvr
      linarith
    have hlam_lt : lam < cn + h := by
      by_contra hc; push_neg at hc
      have c0 : (cn + h) * α ≤ lam * α := mul_le_mul_of_nonneg_right hc hα.le
      have c1 : vn - cn ≤ 2 * vn * uB + 2 * rho * vr * wB := by
        rw [ea] at g1; linarith
      have c2 : cn ≤ rho * (m - 2 * vr * uB - 2 * vr * wB) := by
        have : (cn + h) * 1 ≤ lam * K := mul_le_mul hc hK1 zero_le_one hlam0.le
        linarith
      have c3 : cn ≤ vr - 2 * vr * uB - 2 * vr * wB := by
        have : rho * (m - 2 * vr * uB - 2 * vr * wB) ≤ 1 * (m - 2 * vr * uB - 2 * vr * wB) :=
          mul_le_mul_of_nonneg_right hr1.le hX
        linarith
      have hvw : 0 < vr * wB := mul_pos hvr hwB0
      have hvu : vr * (2 * uB) < vr * 1 := by linarith
      have hu_half : 2 * uB < 1 := lt_of_mul_lt_mul_left hvu hvr.le
      have P1 := mul_pos (by linarith : (0:ℝ) < vn - vr) (by linarith : (0:ℝ) < 1 - 2 * uB)
      have P2 := mul_pos (mul_pos (by linarith : (0:ℝ) < 1 - rho) hvr) hwB0
      linarith
    refine ⟨uB, wB, lam, hlam0.le, hlam_lt, huB0.le, hwB0.le, by linarith, hfeas.le,
      by rw [hfeas]; ring, g1, ?_, Or.inl gx⟩
    have := mul_nonneg hlam0.le hα.le
    have := mul_nonneg (sub_nonneg.2 hr1.le) (mul_nonneg hvr.le hwB0.le)
    linarith

lemma saddle_exists (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) (hV : 0 < PiC P α) :
    ∃ lam W, 0 ≤ lam ∧ lam < P.cn + P.h ∧ W ≤ PiC P α ∧
      ∀ q1 q2 x, 0 ≤ q2 → 0 ≤ x →
        Pq P α q1 q2 x + lam * (α * q1 - (1 + P.kr * α) * x) ≤ W := by
  have hP' := hP
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP'
  have hK1 : 1 ≤ 1 + P.kr * α := by have := mul_nonneg hkr hα.le; linarith
  have ea : mun P α = P.vn - P.cn - α * (P.cn + P.h) := by unfold mun; ring
  rcases kkt_alg P.vn P.vr P.rho P.cn P.h α (mun P α) (mur P α) (1 + P.kr * α) hvr hvrn hr0 hr1 hα
    (by linarith) hh hK1 ea (mur_le P hP α hα) with ⟨h1, h2⟩ | ⟨u, w, lam, hl0, hl1, hu, hw, hs, hf, hcs, g1, g2, gx⟩
  · have := PiC_nonpos_of P hP α hα h1 h2
    linarith
  refine ⟨lam, Pq P α u 0 w, hl0, hl1, le_PiC_of P hP α hα u 0 w ⟨hu, le_rfl, hw, by linarith, hf⟩, ?_⟩
  intro q1 q2 x h2 hx
  have := saddle_of_kkt P hP α u w lam g1 g2 gx q1 q2 x h2 hx
  rw [hcs, add_zero] at this
  exact this

lemma crude_bound (P : Params) (hP : P.Standing) (α' : ℝ) (hα' : 0 < α') (q1 q2 x : ℝ)
    (h1 : 0 ≤ q1) (h2 : 0 ≤ q2) (hx : 0 ≤ x) (hf : (1 + P.kr * α') * x ≤ α' * q1) :
    Pq P α' q1 q2 x ≤ (P.vn + P.vr * α') * (q1 + q2) := by
  have hP' := hP
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP'
  have hK1' : 1 ≤ 1 + P.kr * α' := by have := mul_nonneg hkr hα'.le; linarith
  have e : Pq P α' q1 q2 x = q1 * mun P α' + P.rho * q2 * mun P α' + P.rho * x * mur P α'
      - ((1 - P.rho) * P.vn * q1 ^ 2 + P.rho * (P.vn - P.vr) * (q1 + q2) ^ 2
        + P.rho * P.vr * (q1 + q2 + x) ^ 2) := by unfold Pq; ring
  have hQ : 0 ≤ (1 - P.rho) * P.vn * q1 ^ 2 + P.rho * (P.vn - P.vr) * (q1 + q2) ^ 2
        + P.rho * P.vr * (q1 + q2 + x) ^ 2 := by
    have : 0 ≤ (1 - P.rho) * P.vn := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ P.rho * (P.vn - P.vr) := mul_nonneg hr0.le (by linarith)
    have : 0 ≤ P.rho * P.vr := mul_nonneg hr0.le hvr.le
    positivity
  have ha := mun_le P hP α' hα'
  have hm := mur_le P hP α' hα'
  rw [e]
  generalize mun P α' = a at ha ⊢
  generalize mur P α' = m at hm ⊢
  have t1 : q1 * a ≤ q1 * P.vn := mul_le_mul_of_nonneg_left ha h1
  have t2 : P.rho * q2 * a ≤ q2 * P.vn := by
    rcases le_total 0 a with h | h
    · have b1 : P.rho * (q2 * a) ≤ 1 * (q2 * a) := mul_le_mul_of_nonneg_right hr1.le (mul_nonneg h2 h)
      have b2 : q2 * a ≤ q2 * P.vn := mul_le_mul_of_nonneg_left ha h2
      linarith
    · have b1 : P.rho * (q2 * a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le (mul_nonpos_of_nonneg_of_nonpos h2 h)
      have b2 : 0 ≤ q2 * P.vn := mul_nonneg h2 (by linarith)
      linarith
  have hxle : x ≤ α' * q1 := by
    have : 1 * x ≤ (1 + P.kr * α') * x := mul_le_mul_of_nonneg_right hK1' hx
    linarith
  have t3 : P.rho * x * m ≤ P.vr * α' * q1 := by
    rcases le_total 0 m with h | h
    · have a1 : P.rho * (x * m) ≤ 1 * (x * m) := mul_le_mul_of_nonneg_right hr1.le (mul_nonneg hx h)
      have a2 : x * m ≤ x * P.vr := mul_le_mul_of_nonneg_left hm hx
      have a3 : x * P.vr ≤ α' * q1 * P.vr := mul_le_mul_of_nonneg_right hxle hvr.le
      linarith
    · have a1 : P.rho * (x * m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le (mul_nonpos_of_nonneg_of_nonpos hx h)
      have a2 : 0 ≤ P.vr * α' * q1 := mul_nonneg (mul_nonneg hvr.le hα'.le) h1
      linarith
  have t4 : 0 ≤ P.vr * α' * q2 := mul_nonneg (mul_nonneg hvr.le hα'.le) h2
  linarith

lemma saddle_bound (P : Params) (hP : P.Standing) (α α' lam W : ℝ) (hl0 : 0 ≤ lam)
    (hsad : ∀ q1 q2 x, 0 ≤ q2 → 0 ≤ x → Pq P α q1 q2 x + lam * (α * q1 - (1 + P.kr * α) * x) ≤ W)
    (κ : ℝ) (hκ1 : κ ≤ P.cn + P.h - lam) (hκ2 : κ ≤ (P.cn + P.h) * P.rho) (hlt : α < α')
    (q1 q2 x : ℝ) (h1 : 0 ≤ q1) (h2 : 0 ≤ q2) (hx : 0 ≤ x) (hf : (1 + P.kr * α') * x ≤ α' * q1) :
    Pq P α' q1 q2 x ≤ W - (α' - α) * κ * (q1 + q2) := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  have iden : Pq P α q1 q2 x - Pq P α' q1 q2 x
      = (α' - α) * ((P.cn + P.h) * (q1 + P.rho * q2) + P.rho * P.kr * (P.cr + P.h) * x) := by
    unfold Pq mun mur; ring
  have hs' := hsad q1 q2 x h2 hx
  have ec : α * q1 - (1 + P.kr * α) * x
      = (α' * q1 - (1 + P.kr * α') * x) - (α' - α) * (q1 - P.kr * x) := by ring
  rw [ec] at hs'
  have hfe : 0 ≤ α' * q1 - (1 + P.kr * α') * x := by linarith
  have k1 : 0 ≤ lam * (α' * q1 - (1 + P.kr * α') * x) := mul_nonneg hl0 hfe
  have k2 : κ * (q1 + q2) ≤ (P.cn + P.h - lam) * q1 + (P.cn + P.h) * P.rho * q2 := by
    have := mul_le_mul_of_nonneg_right hκ1 h1
    have := mul_le_mul_of_nonneg_right hκ2 h2
    linarith
  have k3 : 0 ≤ P.rho * P.kr * (P.cr + P.h) * x + lam * P.kr * x := by
    have : 0 ≤ P.rho * P.kr * (P.cr + P.h) := mul_nonneg (mul_nonneg hr0.le hkr) (by linarith)
    have : 0 ≤ lam * P.kr := mul_nonneg hl0 hkr
    positivity
  have hΔ0 : 0 ≤ α' - α := by linarith
  have k4 := mul_le_mul_of_nonneg_left k2 hΔ0
  have k5 := mul_nonneg hΔ0 k3
  have e2 : lam * ((α' * q1 - (1 + P.kr * α') * x) - (α' - α) * (q1 - P.kr * x))
      = lam * (α' * q1 - (1 + P.kr * α') * x) - (α' - α) * (lam * q1) + (α' - α) * (lam * P.kr * x) := by ring
  rw [e2] at hs'
  have e3 : (α' - α) * ((P.cn + P.h) * (q1 + P.rho * q2) + P.rho * P.kr * (P.cr + P.h) * x)
      = (α' - α) * ((P.cn + P.h - lam) * q1 + (P.cn + P.h) * P.rho * q2)
        + (α' - α) * (P.rho * P.kr * (P.cr + P.h) * x + lam * P.kr * x) + (α' - α) * (lam * q1)
        - (α' - α) * (lam * P.kr * x) := by ring
  rw [e3] at iden
  have e4 : (α' - α) * (κ * (q1 + q2)) = (α' - α) * κ * (q1 + q2) := by ring
  linarith

theorem prop3_i (P : Params) (hP : P.Standing) :
    StrictAntiOn (PiC P) {α | 0 < α ∧ 0 < PiC P α} := by
  rintro α ⟨hα, hV⟩ α' ⟨hα', hV'⟩ hlt
  have hP' := hP
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP'
  obtain ⟨lam, W, hl0, hl1, hW, hsad⟩ := saddle_exists P hP α hα hV
  obtain ⟨κ, hκ1, hκ2, hκ0⟩ : ∃ κ : ℝ, κ ≤ P.cn + P.h - lam ∧ κ ≤ (P.cn + P.h) * P.rho ∧ 0 < κ :=
    ⟨min (P.cn + P.h - lam) ((P.cn + P.h) * P.rho), min_le_left _ _, min_le_right _ _,
      lt_min (by linarith) (mul_pos (by linarith) hr0)⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = α' - α := ⟨_, rfl⟩
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = P.vn + P.vr * α' := ⟨_, rfl⟩
  have hC0 : 0 < C := by have := mul_pos hvr hα'; linarith
  have hCK : 0 < C + Δ * κ := by have := mul_pos hΔ0 hκ0; linarith
  have hM : PiC P α' ≤ C * W / (C + Δ * κ) := by
    apply PiC_le_of P hP α' hα'
    rintro q1 q2 x ⟨h1, h2, hx, hs, hf⟩
    have b1 := crude_bound P hP α' hα' q1 q2 x h1 h2 hx hf
    have b2 := saddle_bound P hP α α' lam W hl0 hsad κ hκ1 hκ2 hlt q1 q2 x h1 h2 hx hf
    rw [← hC] at b1; rw [← hΔ] at b2
    rw [le_div_iff₀ hCK]
    have u1 := mul_le_mul_of_nonneg_left b1 (mul_pos hΔ0 hκ0).le
    have u2 := mul_le_mul_of_nonneg_left b2 hC0.le
    have e1 : Δ * κ * (C * (q1 + q2)) = C * (Δ * κ * (q1 + q2)) := by ring
    have e2 : C * (W - Δ * κ * (q1 + q2)) = C * W - C * (Δ * κ * (q1 + q2)) := by ring
    have e3 : Pq P α' q1 q2 x * (C + Δ * κ) = C * Pq P α' q1 q2 x + Δ * κ * Pq P α' q1 q2 x := by ring
    rw [e3]; linarith
  have hWpos : 0 < W := by
    have h0 : 0 < C * W / (C + Δ * κ) := lt_of_lt_of_le hV' hM
    rw [lt_div_iff₀ hCK, zero_mul] at h0
    exact pos_of_mul_pos_right h0 hC0.le
  have : C * W / (C + Δ * κ) < W := by
    rw [div_lt_iff₀ hCK]
    have := mul_pos (mul_pos hΔ0 hκ0) hWpos
    linarith
  linarith

end RefurbCommit.DefectProfit

open RefurbCommit.DefectProfit in
theorem solution (P : Params) (hP : P.Standing) :
    StrictAntiOn (PiC P) {α | 0 < α ∧ 0 < PiC P α} := prop3_i P hP
