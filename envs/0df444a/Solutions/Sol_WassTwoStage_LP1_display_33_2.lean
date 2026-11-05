-- Prove2me | solution 2 for WassTwoStage.LP1.display_33
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:19:29.707124+00:00
-- url     : https://prove2.me/submissions/b303e9db-7c80-40d4-b996-059373f54ab3

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_WassTwoStage_LP1_Gauge
import Definitions.Def_WassTwoStage_LP1_Setting
import Definitions.Def_WassTwoStage_LP1_Reformulations
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
lemma coe_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) :=
  map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f s
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

namespace WTS6Meas

open MeasureTheory

section Disc

variable {E : Type*} [MeasurableSpace E]

/-- A finitely supported measure `∑ j, c j • δ_{a j}`. -/
noncomputable def disc {J : Type*} [Fintype J] (c : J → ENNReal) (a : J → E) : Measure E :=
  ∑ j, c j • Measure.dirac (a j)

lemma lintegral_disc [MeasurableSingletonClass E] {J : Type*} [Fintype J] (c : J → ENNReal)
    (a : J → E) (f : E → ENNReal) : ∫⁻ x, f x ∂(disc c a) = ∑ j, c j * f (a j) := by
  simp [disc, lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac]

lemma map_disc {F : Type*} [MeasurableSpace F] {J : Type*} [Fintype J] (c : J → ENNReal)
    (a : J → E) {g : E → F} (hg : Measurable g) : (disc c a).map g = disc c (g ∘ a) := by
  unfold disc
  rw [← Measure.mapₗ_apply_of_measurable hg, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower, Measure.mapₗ_apply_of_measurable hg,
    Measure.map_dirac' hg]
  rfl

lemma disc_univ {J : Type*} [Fintype J] (c : J → ENNReal) (a : J → E) :
    disc c a Set.univ = ∑ j, c j := by
  simp [disc]

lemma disc_isProb {J : Type*} [Fintype J] (c : J → ENNReal) (a : J → E) (h : ∑ j, c j = 1) :
    IsProbabilityMeasure (disc c a) := ⟨by rw [disc_univ, h]⟩

end Disc

lemma toENNReal_coe_real (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  simp [EReal.toENNReal]

lemma ofReal_eq_max (u : ℝ) : ENNReal.ofReal u = ENNReal.ofReal (max u 0) := by
  rcases le_total u 0 with h | h
  · simp [h, ENNReal.ofReal_of_nonpos]
  · simp [h]

section Exp

variable {E : Type*} [MeasurableSpace E]

lemma ee_mono (Q : Measure E) (f g : E → EReal) (h : ∀ x, f x ≤ g x) :
    WassersteinDRO.Duality.erealExpectation Q f ≤
      WassersteinDRO.Duality.erealExpectation Q g := by
  unfold WassersteinDRO.Duality.erealExpectation
  have h1 : ∫⁻ x, (f x).toENNReal ∂Q ≤ ∫⁻ x, (g x).toENNReal ∂Q :=
    lintegral_mono fun x => EReal.toENNReal_le_toENNReal (h x)
  have h2 : ∫⁻ x, (-(g x)).toENNReal ∂Q ≤ ∫⁻ x, (-(f x)).toENNReal ∂Q :=
    lintegral_mono fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h x))
  split_ifs with hf hg hg
  · exact le_rfl
  · exact absurd (top_le_iff.mp (hf ▸ h1)) hg
  · exact le_top
  · exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h2)

lemma ee_real_disc [MeasurableSingletonClass E] {J : Type*} [Fintype J] (c : J → ENNReal)
    (hc : ∀ j, c j ≠ ⊤) (a : J → E) (f : E → ℝ) :
    WassersteinDRO.Duality.erealExpectation (disc c a) (fun x => ((f x : ℝ) : EReal)) =
      ((∑ j, (c j).toReal * f (a j) : ℝ) : EReal) := by
  unfold WassersteinDRO.Duality.erealExpectation
  simp only [lintegral_disc, toENNReal_coe_real, ← EReal.coe_neg]
  have hfin : ∀ (u : J → ℝ), ∑ j, c j * ENNReal.ofReal (u j) ≠ ⊤ := fun u =>
    ENNReal.sum_ne_top.mpr fun j _ => ENNReal.mul_ne_top (hc j) ENNReal.ofReal_ne_top
  rw [if_neg (hfin _), ← EReal.coe_ennreal_toReal (hfin _),
    ← EReal.coe_ennreal_toReal (hfin (fun j => -f (a j))), ← EReal.coe_sub]
  congr 1
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top (hc j) ENNReal.ofReal_ne_top),
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top (hc j) ENNReal.ofReal_ne_top),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total 0 (f (a j)) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

end Exp

end WTS6Meas

namespace WTS6Meas

open MeasureTheory

lemma lintegral_emp {K I : ℕ} (ξhat : Fin I → Fin K → ℝ) (f : (Fin K → ℝ) → ENNReal) :
    ∫⁻ x, f x ∂(WassersteinDRO.Duality.empiricalDistribution ξhat) =
      (I : ENNReal)⁻¹ * ∑ i, f (ξhat i) := by
  simp [WassersteinDRO.Duality.empiricalDistribution, lintegral_smul_measure,
    lintegral_dirac]

lemma real_pw (a b c : ℝ) (h : a ≤ b + c) :
    max a 0 + max (-b) 0 ≤ max b 0 + max (-a) 0 + max c 0 := by
  have := le_max_left c 0
  have := le_max_right c 0
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [max_eq_left ha, max_eq_right (by linarith : -b ≤ 0), max_eq_left hb,
      max_eq_right (by linarith : -a ≤ 0)]; linarith
  · rw [max_eq_left ha, max_eq_left (by linarith : 0 ≤ -b), max_eq_right hb,
      max_eq_right (by linarith : -a ≤ 0)]; linarith
  · rw [max_eq_right ha, max_eq_right (by linarith : -b ≤ 0), max_eq_left hb,
      max_eq_left (by linarith : 0 ≤ -a)]; linarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -b), max_eq_right hb,
      max_eq_left (by linarith : 0 ≤ -a)]; linarith

lemma toReal_sum_ofReal {I : ℕ} (u : Fin I → ℝ) :
    ((I : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (u i)).toReal =
      (I : ℝ)⁻¹ * ∑ i, max (u i) 0 := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
  simp [ENNReal.toReal_ofReal']

lemma ub {K I : ℕ} (P : Measure (Fin K → ℝ)) [IsProbabilityMeasure P]
    (ξhat : Fin I → Fin K → ℝ) (hI : 0 < I) (wp wm ε lam : ℝ) (hε : 0 ≤ ε) (hlam : 0 ≤ lam)
    (hT : RWPI.SqrtLasso.transportCost (WassTwoStage.LP1.gaugeCost wp wm) P
      (WassersteinDRO.Duality.empiricalDistribution ξhat) ≤ ENNReal.ofReal ε)
    (z : (Fin K → ℝ) → ℝ) (hz : Measurable z)
    (hlip : ∀ ξ ξ', z ξ ≤ z ξ' + lam * WassTwoStage.LP1.gauge wp wm (ξ - ξ')) :
    WassersteinDRO.Duality.erealExpectation P (fun ξ => ((z ξ : ℝ) : EReal)) ≤
      ((ε * lam + (I : ℝ)⁻¹ * ∑ i, z (ξhat i) : ℝ) : EReal) := by
  set R : ℝ := ε * lam + (I : ℝ)⁻¹ * ∑ i, z (ξhat i) with hR
  set Ex := WassersteinDRO.Duality.erealExpectation P (fun ξ => ((z ξ : ℝ) : EReal)) with hEx
  have hzp : Measurable fun x => ENNReal.ofReal (z x) := hz.ennreal_ofReal
  have hzn : Measurable fun x => ENNReal.ofReal (-z x) := hz.neg.ennreal_ofReal
  -- the key estimate for every slack δ > 0
  have key : ∀ δ : ℝ, 0 < δ → Ex ≤ ((R + lam * δ : ℝ) : EReal) := by
    intro δ hδ
    have hlt : RWPI.SqrtLasso.transportCost (WassTwoStage.LP1.gaugeCost wp wm) P
        (WassersteinDRO.Duality.empiricalDistribution ξhat) < ENNReal.ofReal (ε + δ) := by
      rw [ENNReal.ofReal_add hε hδ.le]
      exact lt_of_le_of_lt hT (ENNReal.lt_add_right ENNReal.ofReal_ne_top
        (ENNReal.ofReal_pos.mpr hδ).ne')
    unfold RWPI.SqrtLasso.transportCost at hlt
    obtain ⟨π, hlt⟩ := iInf_lt_iff.mp hlt
    obtain ⟨⟨hπ, h1, h2⟩, hcost⟩ := iInf_lt_iff.mp hlt
    set gc : (Fin K → ℝ) × (Fin K → ℝ) → ENNReal :=
      fun w => WassTwoStage.LP1.gaugeCost wp wm w.1 w.2 with hgc
    set cost := ∫⁻ w, gc w ∂π with hcostdef
    have hcost_ne : cost ≠ ⊤ := ne_top_of_lt hcost
    have hzp1 : Measurable fun w : (Fin K → ℝ) × (Fin K → ℝ) => ENNReal.ofReal (z w.1) :=
      hzp.comp measurable_fst
    have hzp2 : Measurable fun w : (Fin K → ℝ) × (Fin K → ℝ) => ENNReal.ofReal (z w.2) :=
      hzp.comp measurable_snd
    have hzn1 : Measurable fun w : (Fin K → ℝ) × (Fin K → ℝ) => ENNReal.ofReal (-z w.1) :=
      hzn.comp measurable_fst
    -- integrals against P and P̂ as integrals against π
    have hP1 : ∀ f : (Fin K → ℝ) → ENNReal, Measurable f →
        ∫⁻ x, f x ∂P = ∫⁻ w, f w.1 ∂π := by
      intro f hf; rw [← h1, lintegral_map hf measurable_fst]
    have hP2 : ∀ f : (Fin K → ℝ) → ENNReal, Measurable f →
        ∫⁻ w, f w.2 ∂π = (I : ENNReal)⁻¹ * ∑ i, f (ξhat i) := by
      intro f hf; rw [← lintegral_emp, ← h2, lintegral_map hf measurable_snd]
    set Ap := ∫⁻ x, ENNReal.ofReal (z x) ∂P with hAp
    set An := ∫⁻ x, ENNReal.ofReal (-z x) ∂P with hAn
    set cp := (I : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (z (ξhat i)) with hcp
    set cn := (I : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (-z (ξhat i)) with hcn
    have hcp_ne : cp ≠ ⊤ := ENNReal.mul_ne_top (by simpa using hI.ne')
      (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)
    have hcn_ne : cn ≠ ⊤ := ENNReal.mul_ne_top (by simpa using hI.ne')
      (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)
    have hgc_eq : ∀ w : (Fin K → ℝ) × (Fin K → ℝ),
        ENNReal.ofReal (lam * WassTwoStage.LP1.gauge wp wm (w.1 - w.2)) =
          ENNReal.ofReal lam * gc w := by
      intro w; rw [ENNReal.ofReal_mul hlam]; rfl
    -- Ap is finite
    have hAp_le : Ap ≤ cp + ENNReal.ofReal lam * cost := by
      rw [hAp, hP1 _ hzp]
      calc ∫⁻ w, ENNReal.ofReal (z w.1) ∂π
          ≤ ∫⁻ w, (ENNReal.ofReal (z w.2) + ENNReal.ofReal lam * gc w) ∂π := by
            refine lintegral_mono fun w => ?_
            rw [← hgc_eq]
            exact (ENNReal.ofReal_le_ofReal (hlip w.1 w.2)).trans ENNReal.ofReal_add_le
        _ = cp + ENNReal.ofReal lam * cost := by
            rw [lintegral_add_left hzp2, hP2 _ hzp,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hAp_ne : Ap ≠ ⊤ := ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hcp_ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcost_ne⟩) hAp_le
    -- the balance inequality
    have hbal : Ap + cn ≤ cp + An + ENNReal.ofReal lam * cost := by
      have e1 : Ap + cn = ∫⁻ w, (ENNReal.ofReal (z w.1) + ENNReal.ofReal (-z w.2)) ∂π := by
        rw [lintegral_add_left hzp1, hP2 _ hzn, hAp, hP1 _ hzp]
      have e2 : cp + An + ENNReal.ofReal lam * cost = ∫⁻ w, (ENNReal.ofReal (z w.2) +
          (ENNReal.ofReal (-z w.1) + ENNReal.ofReal lam * gc w)) ∂π := by
        rw [lintegral_add_left hzp2, lintegral_add_left hzn1, hP2 _ hzp, hAn, hP1 _ hzn,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, add_assoc]
      rw [e1, e2]
      refine lintegral_mono fun w => ?_
      rw [← hgc_eq, ofReal_eq_max (z w.1), ofReal_eq_max (-z w.2), ofReal_eq_max (z w.2),
        ofReal_eq_max (-z w.1), ofReal_eq_max (lam * _),
        ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
        ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
        ← ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _)
          (le_max_right _ _))]
      apply ENNReal.ofReal_le_ofReal
      have := real_pw (z w.1) (z w.2) _ (hlip w.1 w.2)
      linarith
    -- conclude
    rw [hEx]
    unfold WassersteinDRO.Duality.erealExpectation
    simp only [toENNReal_coe_real, ← EReal.coe_neg]
    rw [← hAp, ← hAn, if_neg hAp_ne]
    by_cases hAn_ne : An = ⊤
    · rw [hAn_ne, EReal.coe_ennreal_top, EReal.sub_top]; exact bot_le
    · rw [← EReal.coe_ennreal_toReal hAp_ne, ← EReal.coe_ennreal_toReal hAn_ne,
        ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have hr := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hAp_ne, hcn_ne⟩)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hcp_ne, hAn_ne⟩,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcost_ne⟩)).mpr hbal
      rw [ENNReal.toReal_add hAp_ne hcn_ne, ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨hcp_ne, hAn_ne⟩) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcost_ne),
        ENNReal.toReal_add hcp_ne hAn_ne,
        show (ENNReal.ofReal lam * cost).toReal = lam * cost.toReal by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam]] at hr
      have hcostR : cost.toReal ≤ ε + δ := by
        have := (ENNReal.toReal_le_toReal hcost_ne ENNReal.ofReal_ne_top).mpr hcost.le
        rwa [ENNReal.toReal_ofReal (by linarith)] at this
      have hdiff : cp.toReal - cn.toReal = (I : ℝ)⁻¹ * ∑ i, z (ξhat i) := by
        rw [hcp, hcn, toReal_sum_ofReal, toReal_sum_ofReal, ← mul_sub,
          ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases le_total 0 (z (ξhat i)) with h | h
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      have hlc : lam * cost.toReal ≤ lam * (ε + δ) := mul_le_mul_of_nonneg_left hcostR hlam
      rw [hR]
      nlinarith
  -- let the slack go to zero
  have hEtop : Ex ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (key 1 one_pos)
  by_cases hEbot : Ex = ⊥
  · rw [hEbot]; exact bot_le
  · rw [← EReal.coe_toReal hEtop hEbot, EReal.coe_le_coe_iff]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have := key (η / (lam + 1)) (div_pos hη (by linarith))
    rw [← EReal.coe_toReal hEtop hEbot, EReal.coe_le_coe_iff] at this
    have h3 : lam * (η / (lam + 1)) ≤ η := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith

end WTS6Meas

namespace WTS6Meas

open MeasureTheory

variable {K I : ℕ}

/-- Weights of the perturbed empirical distribution: mass `α/I` moved from each sample. -/
noncomputable def cQ (I : ℕ) (α : ℝ) : Fin I × Bool → ENNReal :=
  fun j => (I : ENNReal)⁻¹ * ENNReal.ofReal (if j.2 then α else 1 - α)

/-- Atoms of the perturbed empirical distribution: `ξ̂_i + v` and `ξ̂_i`. -/
def aQ (ξhat : Fin I → Fin K → ℝ) (v : Fin K → ℝ) : Fin I × Bool → Fin K → ℝ :=
  fun j => if j.2 then ξhat j.1 + v else ξhat j.1

lemma sum_inv_I (hI : 0 < I) (u : ENNReal) : ∑ _i : Fin I, (I : ENNReal)⁻¹ * u = u := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simpa using hI.ne') (by simp), one_mul]

lemma cQ_pair (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (i : Fin I) :
    cQ I α (i, true) + cQ I α (i, false) = (I : ENNReal)⁻¹ := by
  simp only [cQ, if_true, Bool.false_eq_true, if_false]
  rw [← mul_add, ← ENNReal.ofReal_add h0 (by linarith), add_sub_cancel, ENNReal.ofReal_one,
    mul_one]

lemma sum_cQ (hI : 0 < I) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (g : Fin I × Bool → ENNReal) :
    ∑ j, cQ I α j * g j = ∑ i, (cQ I α (i, true) * g (i, true) + cQ I α (i, false) * g (i, false)) := by
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_bool, add_comm]

lemma cQ_ne_top (hI : 0 < I) (α : ℝ) (j : Fin I × Bool) : cQ I α j ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by simpa using hI.ne')) ENNReal.ofReal_ne_top

lemma emp_eq_disc (ξhat : Fin I → Fin K → ℝ) :
    WassersteinDRO.Duality.empiricalDistribution ξhat =
      disc (fun _ => (I : ENNReal)⁻¹) ξhat := by
  unfold WassersteinDRO.Duality.empiricalDistribution disc
  rw [Finset.smul_sum]

lemma disc_cQ_snd (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (ξhat : Fin I → Fin K → ℝ) :
    disc (cQ I α) (fun j => ξhat j.1) = disc (fun _ => (I : ENNReal)⁻¹) ξhat := by
  unfold disc
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, ← add_smul, cQ_pair α h0 h1 i]

lemma total_cQ (hI : 0 < I) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : ∑ j, cQ I α j = 1 := by
  rw [Fintype.sum_prod_type,
    Finset.sum_congr rfl fun i _ => by rw [Fintype.sum_bool, cQ_pair α h0 h1 i]]
  simpa using sum_inv_I hI 1

lemma ballQ (hI : 0 < I) (wp wm ε α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (ξhat : Fin I → Fin K → ℝ) (v : Fin K → ℝ)
    (hcost : α * WassTwoStage.LP1.gauge wp wm v ≤ ε) :
    IsProbabilityMeasure (disc (cQ I α) (aQ ξhat v)) ∧
      RWPI.SqrtLasso.transportCost (WassTwoStage.LP1.gaugeCost wp wm)
        (disc (cQ I α) (aQ ξhat v)) (WassersteinDRO.Duality.empiricalDistribution ξhat)
        ≤ ENNReal.ofReal ε := by
  refine ⟨disc_isProb _ _ (total_cQ hI α h0 h1), ?_⟩
  set π := disc (cQ I α) (fun j => (aQ ξhat v j, ξhat j.1)) with hπ
  have hprob : IsProbabilityMeasure π := disc_isProb _ _ (total_cQ hI α h0 h1)
  have hm1 : π.map Prod.fst = disc (cQ I α) (aQ ξhat v) := by
    rw [hπ, map_disc _ _ measurable_fst]; rfl
  have hm2 : π.map Prod.snd = WassersteinDRO.Duality.empiricalDistribution ξhat := by
    rw [hπ, map_disc _ _ measurable_snd, emp_eq_disc, ← disc_cQ_snd α h0 h1]; rfl
  refine (iInf₂_le π ⟨hprob, hm1, hm2⟩).trans ?_
  rw [hπ, lintegral_disc, sum_cQ hI α h0 h1]
  calc ∑ i, (cQ I α (i, true) * WassTwoStage.LP1.gaugeCost wp wm (aQ ξhat v (i, true)) (ξhat i)
        + cQ I α (i, false) * WassTwoStage.LP1.gaugeCost wp wm (aQ ξhat v (i, false)) (ξhat i))
      = ∑ _i : Fin I, (I : ENNReal)⁻¹ *
          ENNReal.ofReal (α * WassTwoStage.LP1.gauge wp wm v) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [cQ, aQ, WassTwoStage.LP1.gaugeCost, if_true, Bool.false_eq_true, if_false,
          add_sub_cancel_left, sub_self]
        have hg0 : WassTwoStage.LP1.gauge wp wm (0 : Fin K → ℝ) = 0 := by
          simp [WassTwoStage.LP1.gauge]
        rw [hg0, ENNReal.ofReal_zero, mul_zero, add_zero, mul_assoc, ENNReal.ofReal_mul h0]
    _ ≤ ∑ _i : Fin I, (I : ENNReal)⁻¹ * ENNReal.ofReal ε :=
        Finset.sum_le_sum fun i _ => by gcongr
    _ = ENNReal.ofReal ε := sum_inv_I hI _

lemma eeQ (hI : 0 < I) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (ξhat : Fin I → Fin K → ℝ) (v : Fin K → ℝ) (f : (Fin K → ℝ) → ℝ) :
    WassersteinDRO.Duality.erealExpectation (disc (cQ I α) (aQ ξhat v))
        (fun x => ((f x : ℝ) : EReal)) =
      ((∑ i, ((I : ℝ)⁻¹ * α * f (ξhat i + v) + (I : ℝ)⁻¹ * (1 - α) * f (ξhat i)) : ℝ) :
        EReal) := by
  rw [ee_real_disc _ (cQ_ne_top hI α) _ f]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [cQ, aQ, if_true, Bool.false_eq_true, if_false, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - α)]

end WTS6Meas

namespace WTS6Aux

open WassTwoStage.LP1 WTS6Meas

variable {K M N₁ N₂ I : ℕ}

theorem display33_direct (d : Data K M N₁ N₂ I) (hI : 0 < I) (hε : 0 < d.ε)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse)
    (x : Fin N₁ → ℝ) : d.worstCase x = d.value33 x := by
  have hrec' : ∃ p : Fin M → ℝ, 0 ≤ p ∧ d.Wᵀ *ᵥ p = d.q := hrec
  obtain ⟨p0, hp0, hpq0⟩ := hrec'
  have hdotT : ∀ (ξ : Fin K → ℝ) (p : Fin M → ℝ),
      (d.T x *ᵥ ξ) ⬝ᵥ p = ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ := by
    intro ξ p
    rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
  have hBdot : ∀ (ξ : Fin K → ℝ) (p : Fin M → ℝ),
      (d.T x *ᵥ ξ + d.h x) ⬝ᵥ p = d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ := by
    intro ξ p
    rw [add_dotProduct, hdotT, add_comm]
  set Z : (Fin K → ℝ) → EReal := fun ξ => d.recourse x ξ with hZdef
  have hZge : ∀ (ξ : Fin K → ℝ) (p : Fin M → ℝ), d.DualFeasible p →
      (((d.T x *ᵥ ξ + d.h x) ⬝ᵥ p : ℝ) : EReal) ≤ Z ξ := by
    intro ξ p hp
    simp only [hZdef]
    unfold Data.recourse
    exact le_iInf₂ fun y hy => EReal.coe_le_coe_iff.mpr (weak d.W d.q _ y p hy hp.1 hp.2)
  have hZle : ∀ ξ : Fin K → ℝ, Z ξ =
      ⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p), (((d.T x *ᵥ ξ + d.h x) ⬝ᵥ p : ℝ) : EReal) := by
    intro ξ
    simp only [hZdef]
    unfold Data.recourse
    exact lp_eq d.W d.q _ ⟨p0, hp0, hpq0⟩
  have hSZ : ∀ i, (⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
      ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)) = Z (d.ξhat i) := by
    intro i
    rw [hZle]
    simp only [hBdot]
  have hZbot : ∀ ξ, Z ξ ≠ ⊥ := fun ξ =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hZge ξ p0 ⟨hp0, hpq0⟩)
  have hIpos : (0 : ℝ) < (I : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hI)
  -- the value of (33) when some sample has infinite recourse value
  have hinf_top : (∃ i0, Z (d.ξhat i0) = ⊤) → ∀ lam : ℝ,
      ((d.ε * lam : ℝ) : EReal) + (((I : ℝ)⁻¹ : ℝ) : EReal) * ∑ i, Z (d.ξhat i) = ⊤ := by
    rintro ⟨i0, hi0⟩ lam
    have hsum : ∑ i, Z (d.ξhat i) = ⊤ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hi0]
      apply EReal.top_add_of_ne_bot
      apply ne_bot_of_le_ne_bot (b := ((∑ i ∈ Finset.univ.erase i0,
        (d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ p0 : ℝ) : EReal))
      · exact EReal.coe_ne_bot _
      · rw [coe_sum']
        exact Finset.sum_le_sum fun i _ => hZge _ p0 ⟨hp0, hpq0⟩
    rw [hsum, EReal.coe_mul_top_of_pos hIpos, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  -- measurability of the recourse function (it is lower semicontinuous)
  have hZlsc : LowerSemicontinuous Z := by
    have : Z = fun ξ => ⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
        (((d.T x *ᵥ ξ + d.h x) ⬝ᵥ p : ℝ) : EReal) := funext hZle
    rw [this]
    refine lowerSemicontinuous_iSup fun p => lowerSemicontinuous_iSup fun _ => ?_
    refine Continuous.lowerSemicontinuous (continuous_coe_real_ereal.comp ?_)
    have : (fun ξ : Fin K → ℝ => (d.T x *ᵥ ξ + d.h x) ⬝ᵥ p) =
        fun ξ => d.h x ⬝ᵥ p + ∑ k, ((d.T x)ᵀ *ᵥ p) k * ξ k := by
      funext ξ; rw [hBdot]; rfl
    rw [this]
    fun_prop
  have hZmeas : Measurable Z := hZlsc.measurable
  -- the transport-feasible distributions used for the lower bound
  have hball : ∀ (α : ℝ) (v : Fin K → ℝ), 0 ≤ α → α ≤ 1 →
      α * gauge d.wp d.wm v ≤ d.ε → disc (cQ I α) (aQ d.ξhat v) ∈ d.ball := by
    intro α v h0 h1 hc
    exact ballQ hI d.wp d.wm d.ε α h0 h1 d.ξhat v hc
  unfold Data.worstCase Data.value33
  simp only [hSZ]
  apply le_antisymm
  · ---------------- upper bound (weak duality)
    refine iSup₂_le fun P hP => le_iInf₂ fun lam hadm => ?_
    obtain ⟨hPprob, hPT⟩ := hP
    by_cases hfin : ∀ i, Z (d.ξhat i) ≠ ⊤
    · have hLip : ∀ ξ ξ', Z ξ ≤ Z ξ' + ((lam * gauge d.wp d.wm (ξ - ξ') : ℝ) : EReal) := by
        intro ξ ξ'
        rw [hZle ξ]
        refine iSup₂_le fun p hp => ?_
        have hpol := polar d.wp d.wm lam hwp hwm hadm.1 ((d.T x)ᵀ *ᵥ p) (ξ - ξ') (hadm.2 p hp)
        rw [dotProduct_sub] at hpol
        calc (((d.T x *ᵥ ξ + d.h x) ⬝ᵥ p : ℝ) : EReal)
            ≤ (((d.T x *ᵥ ξ' + d.h x) ⬝ᵥ p + lam * gauge d.wp d.wm (ξ - ξ') : ℝ) : EReal) := by
              rw [EReal.coe_le_coe_iff, hBdot, hBdot]; linarith
          _ = (((d.T x *ᵥ ξ' + d.h x) ⬝ᵥ p : ℝ) : EReal) +
                ((lam * gauge d.wp d.wm (ξ - ξ') : ℝ) : EReal) := EReal.coe_add _ _
          _ ≤ Z ξ' + ((lam * gauge d.wp d.wm (ξ - ξ') : ℝ) : EReal) :=
              add_le_add (hZge ξ' p hp) le_rfl
      have hZtop : ∀ ξ, Z ξ ≠ ⊤ := by
        intro ξ
        refine ne_top_of_le_ne_top ?_ (hLip ξ (d.ξhat ⟨0, hI⟩))
        exact EReal.add_ne_top_iff_ne_top₂ (hZbot _) (EReal.coe_ne_bot _) |>.mpr
          ⟨hfin _, EReal.coe_ne_top _⟩
      set z : (Fin K → ℝ) → ℝ := fun ξ => (Z ξ).toReal with hzdef
      have hZz : ∀ ξ, Z ξ = ((z ξ : ℝ) : EReal) := fun ξ =>
        (EReal.coe_toReal (hZtop ξ) (hZbot ξ)).symm
      have hzlip : ∀ ξ ξ', z ξ ≤ z ξ' + lam * gauge d.wp d.wm (ξ - ξ') := by
        intro ξ ξ'
        have := hLip ξ ξ'
        rw [hZz ξ, hZz ξ', ← EReal.coe_add, EReal.coe_le_coe_iff] at this
        exact this
      have hzmeas : Measurable z := hZmeas.ereal_toReal
      have hE : WassersteinDRO.Duality.erealExpectation P (fun ξ => d.recourse x ξ) =
          WassersteinDRO.Duality.erealExpectation P (fun ξ => ((z ξ : ℝ) : EReal)) := by
        congr 1; funext ξ; exact hZz ξ
      rw [hE]
      refine (ub P d.ξhat hI d.wp d.wm d.ε lam hε.le hadm.1 hPT z hzmeas hzlip).trans
        (le_of_eq ?_)
      rw [Finset.sum_congr rfl fun i _ => hZz (d.ξhat i), ← coe_sum', ← EReal.coe_mul,
        ← EReal.coe_add]
    · push Not at hfin
      rw [hinf_top hfin lam]
      exact le_top
  · ---------------- lower bound (perturbed empirical distributions)
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨C, hcC, hCv⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    suffices hQ : ∃ Q ∈ d.ball,
        (C : EReal) < WassersteinDRO.Duality.erealExpectation Q (fun ξ => d.recourse x ξ) by
      obtain ⟨Q, hQb, hlt⟩ := hQ
      exact hcC.trans (hlt.trans_le (le_iSup₂ (f := fun (P : Measure (Fin K → ℝ))
        (_ : P ∈ d.ball) => WassersteinDRO.Duality.erealExpectation P
          (fun ξ => d.recourse x ξ)) Q hQb))
    by_cases hfin : ∀ i, Z (d.ξhat i) ≠ ⊤
    · -- optimal dual solutions at the samples
      have hfeas : ∀ i, ∃ y, d.T x *ᵥ d.ξhat i + d.h x ≤ d.W *ᵥ y := by
        intro i
        by_contra hno
        push Not at hno
        apply hfin i
        simp only [hZdef]
        unfold Data.recourse
        exact iInf₂_eq_top.mpr fun y hy => absurd hy (hno y)
      have hat : ∀ i, ∃ y p, d.T x *ᵥ d.ξhat i + d.h x ≤ d.W *ᵥ y ∧ 0 ≤ p ∧
          d.Wᵀ *ᵥ p = d.q ∧ d.q ⬝ᵥ y = (d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ p := fun i =>
        attain d.W d.q _ ⟨p0, hp0, hpq0⟩ (hfeas i)
      choose ys ps hys hps hpqs heqs using hat
      set r : Fin I → ℝ := fun i => (d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ ps i with hr
      have hZr : ∀ i, Z (d.ξhat i) = ((r i : ℝ) : EReal) := by
        intro i
        apply le_antisymm
        · simp only [hZdef, hr]
          unfold Data.recourse
          rw [← heqs i]
          exact iInf₂_le (ys i) (hys i)
        · exact hZge _ (ps i) ⟨hps i, hpqs i⟩
      set avg : ℝ := (I : ℝ)⁻¹ * ∑ i, r i with havg
      -- a finite lower envelope of the recourse function
      let fF : (Fin M → ℝ) → (Fin K → ℝ) → ℝ := fun p ξ =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : Option (Fin I) => (d.T x *ᵥ ξ + d.h x) ⬝ᵥ (j.elim p ps))
      have hfle : ∀ p, d.DualFeasible p → ∀ ξ, ((fF p ξ : ℝ) : EReal) ≤ Z ξ := by
        intro p hp ξ
        obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun j : Option (Fin I) => (d.T x *ᵥ ξ + d.h x) ⬝ᵥ (j.elim p ps))
        simp only [fF]
        rw [hj]
        cases j with
        | none => exact hZge ξ p hp
        | some i => exact hZge ξ (ps i) ⟨hps i, hpqs i⟩
      have hfge_i : ∀ p ξ i, (d.T x *ᵥ ξ + d.h x) ⬝ᵥ ps i ≤ fF p ξ := fun p ξ i =>
        Finset.le_sup' (fun j : Option (Fin I) => (d.T x *ᵥ ξ + d.h x) ⬝ᵥ (j.elim p ps))
          (Finset.mem_univ (some i))
      have hfge_p : ∀ p ξ, (d.T x *ᵥ ξ + d.h x) ⬝ᵥ p ≤ fF p ξ := fun p ξ =>
        Finset.le_sup' (fun j : Option (Fin I) => (d.T x *ᵥ ξ + d.h x) ⬝ᵥ (j.elim p ps))
          (Finset.mem_univ none)
      -- expectation lower bound for the perturbed distributions
      have hEQ : ∀ (α : ℝ) (v : Fin K → ℝ) (p : Fin M → ℝ), 0 ≤ α → α ≤ 1 →
          d.DualFeasible p →
          ((∑ i, ((I : ℝ)⁻¹ * α * fF p (d.ξhat i + v) + (I : ℝ)⁻¹ * (1 - α) * fF p (d.ξhat i))
            : ℝ) : EReal) ≤ WassersteinDRO.Duality.erealExpectation (disc (cQ I α) (aQ d.ξhat v))
              (fun ξ => d.recourse x ξ) := by
        intro α v p h0 h1 hp
        rw [← eeQ hI α h0 h1 d.ξhat v (fF p)]
        exact ee_mono _ _ _ (hfle p hp)
      by_cases hCa : C < avg
      · refine ⟨_, hball 0 0 le_rfl zero_le_one (by simp; exact hε.le), ?_⟩
        refine lt_of_lt_of_le ?_ (hEQ 0 0 p0 le_rfl zero_le_one ⟨hp0, hpq0⟩)
        rw [EReal.coe_lt_coe_iff]
        have : avg ≤ ∑ i, ((I : ℝ)⁻¹ * 0 * fF p0 (d.ξhat i + 0) +
            (I : ℝ)⁻¹ * (1 - 0) * fF p0 (d.ξhat i)) := by
          rw [havg, Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          have := hfge_i p0 (d.ξhat i) i
          simp only [mul_zero, zero_mul, zero_add, sub_zero, mul_one]
          exact mul_le_mul_of_nonneg_left this hIpos.le
        linarith
      · push Not at hCa
        set lam0 : ℝ := (C - avg) / d.ε with hlam0
        have hlam0nn : 0 ≤ lam0 := div_nonneg (by linarith) hε.le
        have hCeq : d.ε * lam0 + avg = C := by
          rw [hlam0]; field_simp; ring
        -- lam0 is not admissible in (33)
        have hnadm : ¬ ∀ p, d.DualFeasible p →
            dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam0 : EReal) := by
          intro hadm
          have := iInf₂_le (f := fun (lam : ℝ) (_ : 0 ≤ lam ∧ ∀ p, d.DualFeasible p →
              dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam : EReal)) =>
            ((d.ε * lam : ℝ) : EReal) + (((I : ℝ)⁻¹ : ℝ) : EReal) * ∑ i, Z (d.ξhat i))
            lam0 ⟨hlam0nn, hadm⟩
          have hterm : ((d.ε * lam0 : ℝ) : EReal) + (((I : ℝ)⁻¹ : ℝ) : EReal) *
              ∑ i, Z (d.ξhat i) = (C : EReal) := by
            rw [Finset.sum_congr rfl fun i _ => hZr i, ← coe_sum', ← EReal.coe_mul,
              ← EReal.coe_add, ← havg, hCeq]
          exact absurd (hCv.trans_le (this.trans hterm.le)) (lt_irrefl _)
        push Not at hnadm
        obtain ⟨p, hp, hlt⟩ := hnadm
        unfold dualGauge at hlt
        obtain ⟨ξ', hlt⟩ := lt_iSup_iff.mp hlt
        obtain ⟨hξ', hlt⟩ := lt_iSup_iff.mp hlt
        have hlt' : lam0 < ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ' := EReal.coe_lt_coe_iff.mp hlt
        set a := ((d.T x)ᵀ *ᵥ p) ⬝ᵥ ξ' with ha
        set Bp : ℝ := (I : ℝ)⁻¹ * ∑ i, (d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ p with hBp
        set D : ℝ := |avg - Bp| + 1 with hD
        have hDpos : 0 < D := by positivity
        set α : ℝ := min (1 / 2) (d.ε * (a - lam0) / (2 * D)) with hα
        have hgap : 0 < d.ε * (a - lam0) := mul_pos hε (by linarith)
        have hαpos : 0 < α := lt_min (by norm_num) (div_pos hgap (by positivity))
        have hα1 : α ≤ 1 := (min_le_left _ _).trans (by norm_num)
        have hαD : α * (2 * D) ≤ d.ε * (a - lam0) := by
          have := min_le_right (1 / 2 : ℝ) (d.ε * (a - lam0) / (2 * D))
          rwa [← hα, le_div_iff₀ (by positivity)] at this
        set t : ℝ := d.ε / α with ht
        have ht0 : 0 ≤ t := div_nonneg hε.le hαpos.le
        have hαt : α * t = d.ε := by rw [ht]; field_simp
        have hcostv : α * gauge d.wp d.wm (t • ξ') ≤ d.ε := by
          rw [gauge_smul _ _ _ ht0, ← mul_assoc, hαt]
          nlinarith
        refine ⟨_, hball α (t • ξ') hαpos.le hα1 hcostv, ?_⟩
        refine lt_of_lt_of_le ?_ (hEQ α (t • ξ') p hαpos.le hα1 hp)
        rw [EReal.coe_lt_coe_iff]
        have hshift : ∀ i, (d.T x *ᵥ (d.ξhat i + t • ξ') + d.h x) ⬝ᵥ p =
            (d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ p + t * a := by
          intro i
          rw [ha, mulVec_add, mulVec_smul, add_right_comm, add_dotProduct, smul_dotProduct,
            hdotT ξ' p, smul_eq_mul]
        have hlow : ∀ i, (I : ℝ)⁻¹ * α * ((d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ p + t * a) +
            (I : ℝ)⁻¹ * (1 - α) * r i ≤ (I : ℝ)⁻¹ * α * fF p (d.ξhat i + t • ξ') +
              (I : ℝ)⁻¹ * (1 - α) * fF p (d.ξhat i) := by
          intro i
          have e1 := hfge_p p (d.ξhat i + t • ξ')
          rw [hshift i] at e1
          have e2 := hfge_i p (d.ξhat i) i
          have hIa : 0 ≤ (I : ℝ)⁻¹ * α := mul_nonneg hIpos.le hαpos.le
          have hIb : 0 ≤ (I : ℝ)⁻¹ * (1 - α) := mul_nonneg hIpos.le (by linarith)
          exact add_le_add (mul_le_mul_of_nonneg_left e1 hIa) (mul_le_mul_of_nonneg_left e2 hIb)
        have hsumlow := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlow i
        have hsumeq : ∑ i, ((I : ℝ)⁻¹ * α * ((d.T x *ᵥ d.ξhat i + d.h x) ⬝ᵥ p + t * a) +
            (I : ℝ)⁻¹ * (1 - α) * r i) = α * Bp + α * t * a + (1 - α) * avg := by
          rw [Finset.sum_add_distrib, hBp, havg]
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          try ring
        rw [hsumeq, hαt] at hsumlow
        have habs : α * (avg - Bp) ≤ α * D := by
          apply mul_le_mul_of_nonneg_left _ hαpos.le
          rw [hD]; linarith [le_abs_self (avg - Bp)]
        have : C < α * Bp + d.ε * a + (1 - α) * avg := by
          rw [← hCeq]; nlinarith
        linarith
    · -- some sample has infinite recourse value: the empirical distribution itself
      push Not at hfin
      obtain ⟨i0, hi0⟩ := hfin
      refine ⟨_, hball 0 0 le_rfl zero_le_one (by simp; exact hε.le), ?_⟩
      have htop : WassersteinDRO.Duality.erealExpectation (disc (cQ I 0) (aQ d.ξhat 0))
          (fun ξ => d.recourse x ξ) = ⊤ := by
        unfold WassersteinDRO.Duality.erealExpectation
        rw [if_pos]
        rw [lintegral_disc, eq_top_iff]
        refine le_trans ?_ (Finset.single_le_sum (f := fun j => cQ I 0 j *
          (d.recourse x (aQ d.ξhat 0 j)).toENNReal) (fun _ _ => bot_le)
          (Finset.mem_univ (i0, false)))
        simp only [cQ, aQ, Bool.false_eq_true, if_false, sub_zero, ENNReal.ofReal_one, mul_one]
        have : d.recourse x (d.ξhat i0) = ⊤ := hi0
        rw [this, EReal.toENNReal_top, ENNReal.mul_top (by simp)]
      rw [htop]
      exact EReal.coe_lt_top C

end WTS6Aux

open WassTwoStage.LP1 in
theorem solution {K M N₁ N₂ I : ℕ} (d : Data K M N₁ N₂ I) (hI : 0 < I) (hε : 0 < d.ε)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse)
    (x : Fin N₁ → ℝ) (hx : x ∈ d.X) :
    d.worstCase x = d.value33 x :=
  WTS6Aux.display33_direct d hI hε hwp hwm hrec x
