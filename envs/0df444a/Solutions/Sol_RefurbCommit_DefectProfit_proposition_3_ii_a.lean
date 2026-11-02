-- Prove2me | solution 1 for RefurbCommit.DefectProfit.proposition_3_ii_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:29:21.033341+00:00
-- url     : https://prove2.me/submissions/9d59c7ef-054e-4f0e-a457-917069c9c829

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

lemma mun_nonpos_of_alphaC (P : Params) (hP : P.Standing) (α : ℝ) (h : alphaC P ≤ α) :
    mun P α ≤ 0 := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  have hpos : 0 < P.cn + P.h := by linarith
  unfold alphaC at h
  rw [div_le_iff₀ hpos] at h
  unfold mun; nlinarith

/-- With `µn ≤ 0`, the second-period optimum given `q1 = x (1 + kr α)/α` refurbishes
`max 0 (min v x)` with `v = (µr − vr q1)/(2 vr)` and sells no new units. -/
lemma isMax2_clip (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α) (hmun : mun P α ≤ 0)
    (q1 x : ℝ) (hx : 0 ≤ x) (hq : (1 + P.kr * α) * x = α * q1) (hsum : q1 + x ≤ 1) :
    IsMax2 P α q1 0 (max 0 (min ((mur P α - P.vr * q1) / (2 * P.vr)) x)) := by
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP
  have hk : 0 < 1 + P.kr * α := by nlinarith
  have hq1 : 0 ≤ q1 := by nlinarith
  set v := (mur P α - P.vr * q1) / (2 * P.vr) with hv
  have hv' : mur P α - P.vr * q1 = 2 * P.vr * v := by rw [hv]; field_simp
  set b := max 0 (min v x)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hbx : b ≤ x := max_le hx (min_le_right _ _)
  refine ⟨⟨le_rfl, hb0, by linarith, ?_⟩, ?_⟩
  · have := mul_le_mul_of_nonneg_left hbx hk.le; linarith
  rintro c d ⟨hc, hd, hcd, hf⟩
  have hdx : d ≤ x := by
    have : (1 + P.kr * α) * d ≤ (1 + P.kr * α) * x := by linarith
    exact le_of_mul_le_mul_left this hk
  have s1 : P2q P α q1 c d ≤ P2q P α q1 0 d := by
    unfold P2q
    nlinarith [mul_nonneg hc hq1, mul_nonneg hc hc, mul_nonneg hc hd, mul_nonneg hc hvr.le,
      mul_nonneg (mul_nonneg hc hd) hvr.le, mul_nonneg (mul_nonneg hc hq1) (by linarith : (0:ℝ) ≤ P.vn),
      mul_nonneg (mul_nonneg hc hc) (by linarith : (0:ℝ) ≤ P.vn)]
  refine s1.trans ?_
  have g : ∀ y, P2q P α q1 0 y = P.vr * y * (2 * v - y) := by
    intro y; unfold P2q; linear_combination y * hv'
  rw [g, g]
  rcases le_total v 0 with h0 | h0
  · have : b = 0 := by simp only [b]; exact max_eq_left (le_trans (min_le_left _ _) h0)
    rw [this]; nlinarith [mul_nonneg hvr.le hd]
  rcases le_total v x with h1 | h1
  · have : b = v := by simp only [b]; rw [min_eq_left h1, max_eq_right h0]
    rw [this]; nlinarith [mul_nonneg hvr.le (sq_nonneg (v - d))]
  · have : b = x := by simp only [b]; rw [min_eq_right h1, max_eq_right hx]
    rw [this]
    have : 0 ≤ (x - d) * (2 * v - x - d) := mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg hvr.le this]

theorem prop3_ii_a (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α)
    (hαc : alphaC P ≤ α) : PiStar P α = PiC P α := by
  apply le_antisymm (prop3_ii_bound P hP α hα)
  have hmun := mun_nonpos_of_alphaC P hP α hαc
  apply PiC_le_of P hP α hα
  rintro q1 q2 x ⟨h1, h2, hx, hs, hf⟩
  have hP' := hP
  obtain ⟨hvr, hvrn, hcr, hcrn, hkr, hkr1, hh, hr0, hr1⟩ := hP'
  have hk : 0 < 1 + P.kr * α := by nlinarith
  set q1' := (1 + P.kr * α) * x / α with hq1'
  have eq' : (1 + P.kr * α) * x = α * q1' := by rw [hq1']; field_simp
  have hq1'0 : 0 ≤ q1' := by positivity
  have hq1'le : q1' ≤ q1 := by
    have : α * q1' ≤ α * q1 := by linarith
    exact le_of_mul_le_mul_left this hα
  -- step 1: drop q2 and shrink q1
  have st1 : Pq P α q1 q2 x ≤ Pq P α q1' 0 x := by
    unfold Pq
    have hvn : 0 ≤ P.vn := by linarith
    have hd : 0 ≤ q1 - q1' := by linarith
    nlinarith [mul_nonneg h1 h2, mul_nonneg h2 h2, mul_nonneg h2 hx,
      mul_nonneg (mul_nonneg h1 h2) hvn, mul_nonneg (mul_nonneg h2 h2) hvn,
      mul_nonneg (mul_nonneg h2 hx) hvr.le, mul_nonneg hr0.le (mul_nonneg (mul_nonneg h2 hx) hvr.le),
      mul_nonneg hr0.le (mul_nonneg (mul_nonneg h1 h2) hvn),
      mul_nonneg hr0.le (mul_nonneg (mul_nonneg h2 h2) hvn),
      mul_nonneg hr0.le h2, mul_nonneg (mul_nonneg hr0.le h2) (neg_nonneg.2 hmun),
      mul_nonneg hd (neg_nonneg.2 hmun), mul_nonneg (mul_nonneg hd (add_nonneg h1 hq1'0)) hvn,
      mul_nonneg (mul_nonneg (mul_nonneg hd hx) hvr.le) hr0.le]
  -- step 2: move refurbishing to the second-period optimum
  have hsum' : q1' + x ≤ 1 := by linarith
  have hmax := isMax2_clip P hP α hα hmun q1' x hx eq' hsum'
  refine st1.trans (le_trans ?_ (le_PiStar_of P hP α hα q1' 0 _ hq1'0 hmax))
  set v := (mur P α - P.vr * q1') / (2 * P.vr) with hv
  have hv' : mur P α - P.vr * q1' = 2 * P.vr * v := by rw [hv]; field_simp
  have g : ∀ y, Pq P α q1' 0 y = q1' * (mun P α - P.vn * q1') + P.rho * P.vr * y * (2 * v - q1' - y) := by
    intro y; unfold Pq; linear_combination (P.rho * y) * hv'
  rw [g, g]
  have hc : 0 < P.rho * P.vr := mul_pos hr0 hvr
  rcases le_total v 0 with h0 | h0
  · have : max 0 (min v x) = 0 := max_eq_left (le_trans (min_le_left _ _) h0)
    rw [this]
    have : 0 ≤ x * (x + q1' - 2 * v) := mul_nonneg hx (by linarith)
    nlinarith [mul_nonneg hc.le this]
  rcases le_total v x with h1' | h1'
  · have : max 0 (min v x) = v := by rw [min_eq_left h1', max_eq_right h0]
    rw [this]
    have : 0 ≤ (x - v) * (x + v + q1' - 2 * v) := mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg hc.le this]
  · have : max 0 (min v x) = x := by rw [min_eq_right h1', max_eq_right hx]
    rw [this]

end RefurbCommit.DefectProfit

open RefurbCommit.DefectProfit in
theorem solution (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α)
    (hαc : alphaC P ≤ α) :
    PiStar P α = PiC P α := prop3_ii_a P hP α hα hαc
