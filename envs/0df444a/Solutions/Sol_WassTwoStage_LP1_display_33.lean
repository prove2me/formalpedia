-- Prove2me | solution 1 for WassTwoStage.LP1.display_33
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:06:30.814473+00:00
-- url     : https://prove2.me/submissions/dbc81072-d387-4694-8453-b3047b7ede56
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge
import Definitions.Def_WassTwoStage_LP1_Setting
import Definitions.Def_WassTwoStage_LP1_Reformulations
import Theorems.Thm_WassTwoStage_LP1_theorem_1
import Theorems.Thm_WassTwoStage_LP1_dual_norm_31
import Theorems.Thm_LP_farkas
import Theorems.Thm_LP_strong_duality_matrix

open MeasureTheory Matrix

namespace WTS6Aux

variable {M N : ℕ}

lemma weak (W : Matrix (Fin M) (Fin N) ℝ) (q : Fin N → ℝ) (b : Fin M → ℝ)
    (y : Fin N → ℝ) (p : Fin M → ℝ) (hy : b ≤ W *ᵥ y) (hp : 0 ≤ p) (hpq : Wᵀ *ᵥ p = q) :
    b ⬝ᵥ p ≤ q ⬝ᵥ y := by
  have h1 : q ⬝ᵥ y = p ⬝ᵥ (W *ᵥ y) := by
    rw [← hpq, dotProduct_mulVec, mulVec_transpose]
  rw [h1, dotProduct_comm b p]
  exact dotProduct_le_dotProduct_of_nonneg_left hy hp

lemma attain (W : Matrix (Fin M) (Fin N) ℝ) (q : Fin N → ℝ) (b : Fin M → ℝ)
    (hrec : ∃ p : Fin M → ℝ, 0 ≤ p ∧ Wᵀ *ᵥ p = q) (hf : ∃ y, b ≤ W *ᵥ y) :
    ∃ y p, b ≤ W *ᵥ y ∧ 0 ≤ p ∧ Wᵀ *ᵥ p = q ∧ q ⬝ᵥ y = b ⬝ᵥ p := by
  obtain ⟨y0, hy0⟩ := hf
  obtain ⟨p0, hp0, hpq0⟩ := hrec
  have hP : ∃ x, (-W) *ᵥ x ≤ -b := ⟨y0, by
    intro i; simp only [neg_mulVec, Pi.neg_apply, neg_le_neg_iff]; exact hy0 i⟩
  have hD : ∃ z, 0 ≤ z ∧ (-W)ᵀ *ᵥ z = -q := ⟨p0, hp0, by
    rw [transpose_neg, neg_mulVec, hpq0]⟩
  obtain ⟨x, z, hx, hz, hzq, heq, -⟩ := LP.strong_duality_matrix (-W) (-b) (-q) hP hD
  refine ⟨x, z, ?_, hz, ?_, ?_⟩
  · intro i
    have := hx i
    simp only [neg_mulVec, Pi.neg_apply, neg_le_neg_iff] at this
    exact this
  · rw [transpose_neg, neg_mulVec] at hzq
    exact neg_injective hzq
  · simp only [neg_dotProduct] at heq
    linarith

lemma unbdd (W : Matrix (Fin M) (Fin N) ℝ) (q : Fin N → ℝ) (b : Fin M → ℝ)
    (hrec : ∃ p : Fin M → ℝ, 0 ≤ p ∧ Wᵀ *ᵥ p = q) (hf : ¬ ∃ y, b ≤ W *ᵥ y) (C : ℝ) :
    ∃ p, (0 ≤ p ∧ Wᵀ *ᵥ p = q) ∧ C < b ⬝ᵥ p := by
  obtain ⟨p0, hp0, hpq0⟩ := hrec
  let a : Fin M → Module.Dual ℝ (Fin N → ℝ) := fun i =>
    -((LinearMap.proj i).comp (Matrix.mulVecLin W))
  have ha : ∀ i y, a i y = -(W *ᵥ y) i := by
    intro i y; simp [a]
  have hno : ¬ ∃ x : Fin N → ℝ, (∀ i, a i x ≤ (-b) i) ∧
      ∀ j : Fin 0, (fun _ => (0 : Module.Dual ℝ (Fin N → ℝ))) j x = (fun _ => (0:ℝ)) j := by
    rintro ⟨x, hx, -⟩
    apply hf
    refine ⟨x, fun i => ?_⟩
    have := hx i
    rw [ha] at this
    simp only [Pi.neg_apply, neg_le_neg_iff] at this
    exact this
  obtain ⟨u, z, hu, hsum, hneg⟩ := (LP.farkas a (-b) (fun _ : Fin 0 => 0) (fun _ => 0)).1 hno
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hsum
  have hz : z ⬝ᵥ (fun _ : Fin 0 => (0:ℝ)) = 0 := by simp [dotProduct]
  rw [hz, add_zero, dotProduct_neg] at hneg
  have hub : 0 < u ⬝ᵥ b := by linarith
  have hWu : Wᵀ *ᵥ u = 0 := by
    have hall : ∀ y, u ⬝ᵥ (W *ᵥ y) = 0 := by
      intro y
      have := congrArg (fun f : Module.Dual ℝ (Fin N → ℝ) => f y) hsum
      rw [LinearMap.sum_apply] at this
      simp only [LinearMap.smul_apply, ha, smul_eq_mul, LinearMap.zero_apply] at this
      simp only [dotProduct]
      have h2 : ∑ i, u i * -(W *ᵥ y) i = -∑ i, u i * (W *ᵥ y) i := by
        rw [← Finset.sum_neg_distrib]; congr 1; ext i; ring
      linarith [h2]
    have := hall (Wᵀ *ᵥ u)
    rw [dotProduct_mulVec, ← mulVec_transpose] at this
    exact dotProduct_self_eq_zero.mp this
  set t : ℝ := max 0 ((C - b ⬝ᵥ p0 + 1) / (u ⬝ᵥ b)) with ht
  have ht0 : 0 ≤ t := le_max_left _ _
  have ht1 : (C - b ⬝ᵥ p0 + 1) ≤ t * (u ⬝ᵥ b) := by
    have : (C - b ⬝ᵥ p0 + 1) / (u ⬝ᵥ b) ≤ t := le_max_right _ _
    rwa [div_le_iff₀ hub] at this
  refine ⟨p0 + t • u, ⟨?_, ?_⟩, ?_⟩
  · exact add_nonneg hp0 (smul_nonneg ht0 hu)
  · rw [mulVec_add, mulVec_smul, hWu, smul_zero, add_zero, hpq0]
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b u]
    linarith

/-- EReal LP duality under dual feasibility. -/
lemma lp_eq (W : Matrix (Fin M) (Fin N) ℝ) (q : Fin N → ℝ) (b : Fin M → ℝ)
    (hrec : ∃ p : Fin M → ℝ, 0 ≤ p ∧ Wᵀ *ᵥ p = q) :
    (⨅ (y : Fin N → ℝ) (_ : b ≤ W *ᵥ y), ((q ⬝ᵥ y : ℝ) : EReal)) =
      ⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((b ⬝ᵥ p : ℝ) : EReal) := by
  apply le_antisymm
  · by_cases hf : ∃ y, b ≤ W *ᵥ y
    · obtain ⟨y, p, hy, hp, hpq, he⟩ := attain W q b hrec hf
      refine (iInf₂_le y hy).trans ?_
      rw [he]
      exact le_iSup₂ (f := fun p (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q) => ((b ⬝ᵥ p : ℝ) : EReal)) p ⟨hp, hpq⟩
    · have : (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((b ⬝ᵥ p : ℝ) : EReal)) = ⊤ := by
        rw [EReal.eq_top_iff_forall_lt]
        intro C
        obtain ⟨p, hp, hC⟩ := unbdd W q b hrec hf C
        exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hC)
          (le_iSup₂ (f := fun p (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q) => ((b ⬝ᵥ p : ℝ) : EReal)) p hp)
      rw [this]; exact le_top
  · refine iSup₂_le fun p hp => le_iInf₂ fun y hy => ?_
    exact EReal.coe_le_coe_iff.mpr (weak W q b y p hy hp.1 hp.2)

lemma sup_le_iff' (W : Matrix (Fin M) (Fin N) ℝ) (q : Fin N → ℝ) (b : Fin M → ℝ)
    (hrec : ∃ p : Fin M → ℝ, 0 ≤ p ∧ Wᵀ *ᵥ p = q) (lam : ℝ) :
    (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((b ⬝ᵥ p : ℝ) : EReal)) ≤ (lam : EReal) ↔
      ∃ y, b ≤ W *ᵥ y ∧ q ⬝ᵥ y ≤ lam := by
  constructor
  · intro h
    by_cases hf : ∃ y, b ≤ W *ᵥ y
    · obtain ⟨y, p, hy, hp, hpq, he⟩ := attain W q b hrec hf
      refine ⟨y, hy, ?_⟩
      have := (le_iSup₂ (f := fun p (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q) => ((b ⬝ᵥ p : ℝ) : EReal))
        p ⟨hp, hpq⟩).trans h
      rw [he]; exact EReal.coe_le_coe_iff.mp this
    · obtain ⟨p, hp, hC⟩ := unbdd W q b hrec hf lam
      have := (le_iSup₂ (f := fun p (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q) => ((b ⬝ᵥ p : ℝ) : EReal))
        p hp).trans h
      exact absurd (EReal.coe_le_coe_iff.mp this) (not_le.mpr hC)
  · rintro ⟨y, hy, hle⟩
    refine iSup₂_le fun p hp => EReal.coe_le_coe_iff.mpr ?_
    exact (weak W q b y p hy hp.1 hp.2).trans hle

end WTS6Aux

namespace WTS6Aux

open WassTwoStage.LP1

lemma iSup_add_coe_le {ι : Sort*} (f : ι → EReal) (c : ℝ) (S : EReal)
    (h : ∀ j, f j + (c : EReal) ≤ S) : (⨆ j, f j) + (c : EReal) ≤ S := by
  have h1 : ∀ j, f j ≤ S + ((-c : ℝ) : EReal) := by
    intro j
    have := add_le_add_left (h j) ((-c : ℝ) : EReal)
    rwa [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] at this
  have h2 := add_le_add_left (iSup_le h1) (c : EReal)
  rwa [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h2

lemma gauge_smul {K : ℕ} (wp wm t : ℝ) (ht : 0 ≤ t) (ξ : Fin K → ℝ) :
    gauge wp wm (t • ξ) = t * gauge wp wm ξ := by
  simp only [WassTwoStage.LP1.gauge, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_max_of_nonneg _ _ ht]
  congr 1 <;> ring

lemma gauge_zero {K : ℕ} (wp wm : ℝ) : gauge wp wm (0 : Fin K → ℝ) = 0 := by
  simp [WassTwoStage.LP1.gauge]

lemma polar {K : ℕ} (wp wm lam : ℝ) (hwp : 0 < wp) (hwm : 0 < wm) (hlam : 0 ≤ lam)
    (z ζ : Fin K → ℝ) (h : dualGauge wp wm z ≤ (lam : EReal)) :
    z ⬝ᵥ ζ ≤ lam * gauge wp wm ζ := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [dotProduct, WassTwoStage.LP1.gauge]
  · rw [dual_norm_31 hK wp wm hwp hwm z, EReal.coe_le_coe_iff, Finset.sup'_le_iff] at h
    simp only [dotProduct, WassTwoStage.LP1.gauge, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    obtain ⟨h1, h2⟩ := max_le_iff.mp (h k (Finset.mem_univ _))
    rw [div_le_iff₀ hwp] at h1
    rw [div_le_iff₀ hwm] at h2
    have hm1 : lam * (wp * ζ k) ≤ lam * max (wp * ζ k) (-(wm * ζ k)) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hlam
    have hm2 : lam * (-(wm * ζ k)) ≤ lam * max (wp * ζ k) (-(wm * ζ k)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hlam
    rcases le_total 0 (ζ k) with hz | hz
    · have : z k * ζ k ≤ lam * wp * ζ k := mul_le_mul_of_nonneg_right h1 hz
      nlinarith
    · have : -z k * -ζ k ≤ lam * wm * -ζ k := mul_le_mul_of_nonneg_right h2 (by linarith)
      nlinarith

variable {K M N₁ N₂ I : ℕ}

lemma dual6_eq_33 (d : Data K M N₁ N₂ I) (hI : 0 < I)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse)
    (x : Fin N₁ → ℝ) : d.dualValue6 x = d.value33 x := by
  have hrec' : ∃ p : Fin M → ℝ, 0 ≤ p ∧ d.Wᵀ *ᵥ p = d.q := hrec
  have hdotT : ∀ (ξ : Fin K → ℝ) (p : Fin M → ℝ),
      (d.T x *ᵥ ξ) ⬝ᵥ p = ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ := by
    intro ξ p
    rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
  have hBdot : ∀ (ξ : Fin K → ℝ) (p : Fin M → ℝ),
      (d.T x *ᵥ ξ + d.h x) ⬝ᵥ p = d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ := by
    intro ξ p
    rw [add_dotProduct, hdotT, add_comm]
  have hZge : ∀ (ξ : Fin K → ℝ) (p : Fin M → ℝ), d.DualFeasible p →
      (((d.T x *ᵥ ξ + d.h x) ⬝ᵥ p : ℝ) : EReal) ≤ d.recourse x ξ := by
    intro ξ p hp
    unfold Data.recourse
    exact le_iInf₂ fun y hy => EReal.coe_le_coe_iff.mpr (weak d.W d.q _ y p hy hp.1 hp.2)
  have hZle : ∀ ξ : Fin K → ℝ, d.recourse x ξ =
      ⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p), (((d.T x *ᵥ ξ + d.h x) ⬝ᵥ p : ℝ) : EReal) := by
    intro ξ
    unfold Data.recourse
    exact lp_eq d.W d.q _ hrec'
  have hGC : ∀ lam : ℝ, 0 ≤ lam →
      (∀ p, d.DualFeasible p → dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam : EReal)) →
      ∀ i, (⨆ ξ : Fin K → ℝ,
          d.recourse x ξ - ((lam * gauge d.wp d.wm (ξ - d.ξhat i) : ℝ) : EReal)) =
        ⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
          ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal) := by
    intro lam hlam hC i
    apply le_antisymm
    · refine iSup_le fun ξ => ?_
      rw [hZle ξ, sub_eq_add_neg, ← EReal.coe_neg]
      refine iSup_add_coe_le _ _ _ fun p => iSup_add_coe_le _ _ _ fun hp => ?_
      rw [← EReal.coe_add]
      refine le_trans (EReal.coe_le_coe_iff.mpr ?_)
        (le_iSup₂ (f := fun p (_ : d.DualFeasible p) =>
          ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)) p hp)
      have hpol := polar d.wp d.wm lam hwp hwm hlam ((d.T x)ᵀ *ᵥ p) (ξ - d.ξhat i) (hC p hp)
      rw [dotProduct_sub] at hpol
      rw [hBdot]
      linarith
    · refine le_iSup_of_le (d.ξhat i) ?_
      rw [sub_self, gauge_zero, mul_zero, EReal.coe_zero, sub_zero]
      refine iSup₂_le fun p hp => ?_
      rw [← hBdot]
      exact hZge _ p hp
  have hGnC : ∀ lam : ℝ, 0 ≤ lam →
      ¬ (∀ p, d.DualFeasible p → dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam : EReal)) →
      ∀ i, (⨆ ξ : Fin K → ℝ,
          d.recourse x ξ - ((lam * gauge d.wp d.wm (ξ - d.ξhat i) : ℝ) : EReal)) = ⊤ := by
    intro lam hlam hC i
    push Not at hC
    obtain ⟨p, hp, hlt⟩ := hC
    unfold dualGauge at hlt
    obtain ⟨ξ', hlt⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hξ', hlt⟩ := lt_iSup_iff.mp hlt
    have hlt' : lam < ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ' := EReal.coe_lt_coe_iff.mp hlt
    set a := ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ' with ha
    have hδ : 0 < a - lam := by linarith
    rw [EReal.eq_top_iff_forall_lt]
    intro C
    set c0 := (d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ p with hc0
    set t : ℝ := max 0 ((C - c0 + 1) / (a - lam)) with ht
    have ht0 : 0 ≤ t := le_max_left _ _
    have ht1 : C - c0 + 1 ≤ t * (a - lam) := by
      have : (C - c0 + 1) / (a - lam) ≤ t := le_max_right _ _
      rwa [div_le_iff₀ hδ] at this
    refine lt_of_lt_of_le ?_ (le_iSup _ (d.ξhat i + t • ξ'))
    have hsub : d.ξhat i + t • ξ' - d.ξhat i = t • ξ' := by abel
    rw [hsub, gauge_smul _ _ _ ht0]
    refine lt_of_lt_of_le ?_ (EReal.sub_le_sub (hZge _ p hp) le_rfl)
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
    have hval : (d.T x *ᵥ (d.ξhat i + t • ξ') + d.h x) ⬝ᵥ p = c0 + t * a := by
      rw [hc0, ha, mulVec_add, mulVec_smul, add_right_comm, add_dotProduct, smul_dotProduct,
        hdotT ξ' p, smul_eq_mul]
    rw [hval]
    have hg : lam * (t * gauge d.wp d.wm ξ') ≤ lam * t := by
      have := mul_le_mul_of_nonneg_left hξ' ht0
      nlinarith
    nlinarith
  have hIpos : (0 : ℝ) < (I : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hI)
  unfold Data.dualValue6 Data.value33
  apply le_antisymm
  · refine le_iInf₂ fun lam hc => ?_
    refine iInf₂_le_of_le lam hc.1 (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun i _ => hGC lam hc.1 hc.2 i]
  · refine le_iInf₂ fun lam hlam => ?_
    by_cases hC : ∀ p, d.DualFeasible p → dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam : EReal)
    · refine iInf₂_le_of_le lam ⟨hlam, hC⟩ (le_of_eq ?_)
      rw [Finset.sum_congr rfl fun i _ => hGC lam hlam hC i]
    · rw [Finset.sum_congr rfl fun i _ => hGnC lam hlam hC i]
      have hsum : ∑ _i : Fin I, (⊤ : EReal) = ⊤ := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hI⟩ : Fin I))]
        apply EReal.top_add_of_ne_bot
        exact ne_bot_of_le_ne_bot (b := 0) (by simp) (Finset.sum_nonneg fun _ _ => le_top)
      rw [hsum, EReal.coe_mul_top_of_pos hIpos, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top

end WTS6Aux

open WassTwoStage.LP1 in
theorem solution {K M N₁ N₂ I : ℕ} (d : Data K M N₁ N₂ I) (hI : 0 < I) (hε : 0 < d.ε)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse)
    (x : Fin N₁ → ℝ) (hx : x ∈ d.X) :
    d.worstCase x = d.value33 x := by
  rw [(theorem_1 d hI hε.le hwp hwm hrec x hx).2 hε, WTS6Aux.dual6_eq_33 d hI hwp hwm hrec x]
