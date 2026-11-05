-- Prove2me | solution 1 for WassTwoStage.LP1.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:03:30.799375+00:00
-- url     : https://prove2.me/submissions/f217c92e-4668-49e6-b636-8fa954098f4f

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge
import Definitions.Def_WassTwoStage_LP1_Setting
import Definitions.Def_WassTwoStage_LP1_Reformulations
import Theorems.Thm_WassTwoStage_LP1_display_33
import Theorems.Thm_WassTwoStage_LP1_constraint_decomposition
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

lemma coe_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) :=
  map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f s

variable {K M N₁ N₂ I : ℕ}

lemma value33_eq_lp32 (d : Data K M N₁ N₂ I) (hI : 0 < I)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse)
    (x : Fin N₁ → ℝ) : d.value33 x = d.lp32 x := by
  have hrec' : ∃ p : Fin M → ℝ, 0 ≤ p ∧ d.Wᵀ *ᵥ p = d.q := hrec
  set B : Fin I → Fin M → ℝ := fun i => d.T x *ᵥ d.ξhat i + d.h x with hB
  have hBdot : ∀ i p, B i ⬝ᵥ p = d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i := by
    intro i p
    simp only [hB, add_dotProduct]
    rw [add_comm]; congr 1; rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
  -- the λ-constraint of (33) via the decomposition
  have decomp : ∀ lam : ℝ, 0 ≤ lam →
      ((∀ p, d.DualFeasible p → dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam : EReal)) ↔
        ∀ k : Fin K, ∃ phi psi : Fin N₂ → ℝ,
          d.q ⬝ᵥ phi ≤ lam ∧ d.q ⬝ᵥ psi ≤ lam ∧
          (1 / d.wp) • (d.T x *ᵥ Pi.single k 1) ≤ d.W *ᵥ phi ∧
          -((1 / d.wm) • (d.T x *ᵥ Pi.single k 1)) ≤ d.W *ᵥ psi) := by
    intro lam hlam
    obtain ⟨e1, e2⟩ := constraint_decomposition (d.T x) d.W d.q d.wp d.wm lam hwp hwm hlam hrec'
    refine Iff.trans ?_ (e1.trans e2)
    exact ⟨fun h p hp hpq => h p ⟨hp, hpq⟩, fun h p hp => h p hp.1 hp.2⟩
  have hIpos : (0 : ℝ) < (I : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hI)
  obtain ⟨p0, hp0, hpq0⟩ := hrec'
  have hSge : ∀ i, (((B i ⬝ᵥ p0 : ℝ)) : EReal) ≤
      ⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
        ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal) := by
    intro i
    rw [hBdot]
    exact le_iSup₂ (f := fun p (_ : d.DualFeasible p) =>
      ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)) p0 ⟨hp0, hpq0⟩
  by_cases hall : ∀ i, ∃ y, B i ≤ d.W *ᵥ y
  · have hat : ∀ i, ∃ y p, B i ≤ d.W *ᵥ y ∧ 0 ≤ p ∧ d.Wᵀ *ᵥ p = d.q ∧
        d.q ⬝ᵥ y = B i ⬝ᵥ p := fun i => attain d.W d.q (B i) ⟨p0, hp0, hpq0⟩ (hall i)
    choose ys ps hys hps hpqs heqs using hat
    have hS : ∀ i, (⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
        ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)) = ((d.q ⬝ᵥ ys i : ℝ) : EReal) := by
      intro i
      apply le_antisymm
      · refine iSup₂_le fun p hp => EReal.coe_le_coe_iff.mpr ?_
        rw [← hBdot]
        exact weak d.W d.q (B i) (ys i) p (hys i) hp.1 hp.2
      · rw [heqs i, hBdot]
        exact le_iSup₂ (f := fun p (_ : d.DualFeasible p) =>
          ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)) (ps i) ⟨hps i, hpqs i⟩
    have hterm : ∀ lam : ℝ, ((d.ε * lam : ℝ) : EReal) + (((I : ℝ)⁻¹ : ℝ) : EReal) *
        ∑ i, (⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
          ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)) =
        ((d.ε * lam + (I : ℝ)⁻¹ * ∑ i, d.q ⬝ᵥ ys i : ℝ) : EReal) := by
      intro lam
      rw [Finset.sum_congr rfl (fun i _ => hS i), ← coe_sum', ← EReal.coe_mul, ← EReal.coe_add]
    unfold Data.value33 Data.lp32
    simp only [hterm]
    apply le_antisymm
    · refine le_iInf fun lam => le_iInf fun y => le_iInf fun phi => le_iInf fun psi =>
        le_iInf fun hF => ?_
      have hc : 0 ≤ lam ∧ ∀ p, d.DualFeasible p →
          dualGauge d.wp d.wm ((d.T x)ᵀ *ᵥ p) ≤ (lam : EReal) :=
        ⟨hF.1, (decomp lam hF.1).2 fun k => ⟨phi k, psi k, hF.2.2 k⟩⟩
      refine (iInf₂_le lam hc).trans (EReal.coe_le_coe_iff.mpr ?_)
      have hle : ∀ i, d.q ⬝ᵥ ys i ≤ d.q ⬝ᵥ y i := by
        intro i
        rw [heqs i]
        exact weak d.W d.q (B i) (y i) (ps i) (hF.2.1 i) (hps i) (hpqs i)
      rw [one_div]
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
      nlinarith
    · refine le_iInf₂ fun lam hc => ?_
      have := (decomp lam hc.1).1 hc.2
      choose phi psi hpp using this
      refine iInf_le_of_le lam (iInf_le_of_le ys (iInf_le_of_le phi (iInf_le_of_le psi
        (iInf_le_of_le ⟨hc.1, hys, hpp⟩ ?_))))
      rw [one_div]
  · push Not at hall
    obtain ⟨i0, hi0⟩ := hall
    have hlp : d.lp32 x = ⊤ := by
      unfold Data.lp32
      refine eq_top_iff.mpr (le_iInf fun lam => le_iInf fun y => le_iInf fun phi =>
        le_iInf fun psi => le_iInf fun hF => ?_)
      exact absurd (hF.2.1 i0) (hi0 (y i0))
    rw [hlp]
    unfold Data.value33
    refine eq_top_iff.mpr (le_iInf₂ fun lam _ => ?_)
    have hS0 : (⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
        ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i0 : ℝ) : EReal)) = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro C
      have hnf : ¬ ∃ y, B i0 ≤ d.W *ᵥ y := fun ⟨y, hy⟩ => hi0 y hy
      obtain ⟨p, hp, hC⟩ := unbdd d.W d.q (B i0) ⟨p0, hp0, hpq0⟩ hnf C
      rw [hBdot] at hC
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hC)
        (le_iSup₂ (f := fun p (_ : d.DualFeasible p) =>
          ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i0 : ℝ) : EReal)) p hp)
    have hsum : ∑ i, (⨆ (p : Fin M → ℝ) (_ : d.DualFeasible p),
        ((d.h x ⬝ᵥ p + ((d.T x)ᵀ *ᵥ p) ⬝ᵥ d.ξhat i : ℝ) : EReal)) = ⊤ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hS0]
      apply EReal.top_add_of_ne_bot
      apply ne_bot_of_le_ne_bot (b := ((∑ i ∈ Finset.univ.erase i0, B i ⬝ᵥ p0 : ℝ) : EReal))
      · exact EReal.coe_ne_bot _
      · rw [coe_sum']
        exact Finset.sum_le_sum fun i _ => hSge i
    rw [hsum, EReal.coe_mul_top_of_pos hIpos, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]

lemma coe_add_iInf {ι : Sort*} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + ⨅ j, f j = ⨅ j, ((c : EReal) + f j) := by
  apply le_antisymm
  · exact le_iInf fun j => add_le_add_right (iInf_le f j) _
  · have h : ∀ j, ((-c : ℝ) : EReal) + ⨅ j, ((c : EReal) + f j) ≤ f j := by
      intro j
      calc ((-c : ℝ) : EReal) + ⨅ j, ((c : EReal) + f j)
          ≤ ((-c : ℝ) : EReal) + ((c : EReal) + f j) := add_le_add_right (iInf_le _ j) _
        _ = f j := by
          rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
    have h2 := add_le_add_right (le_iInf h) (c : EReal)
    rwa [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add] at h2

end WTS6Aux

open WassTwoStage.LP1 in
theorem solution {K M N₁ N₂ I : ℕ} (d : Data K M N₁ N₂ I) (hI : 0 < I) (hε : 0 < d.ε)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse) :
    (∀ x ∈ d.X, d.worstCase x = d.lp32 x) ∧ d.value1 = d.value32 := by
  have hpt : ∀ x ∈ d.X, d.worstCase x = d.lp32 x := by
    intro x hx
    rw [display_33 d hI hε hwp hwm hrec x hx, WTS6Aux.value33_eq_lp32 d hI hwp hwm hrec x]
  refine ⟨hpt, ?_⟩
  unfold Data.value1 Data.value32
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun lam => le_iInf fun y => le_iInf fun phi =>
      le_iInf fun psi => le_iInf fun hF => ?_
    refine (iInf₂_le x hF.1).trans ?_
    rw [hpt x hF.1]
    have hle : d.lp32 x ≤ ((d.ε * lam + (1 / (I:ℝ)) * ∑ i, d.q ⬝ᵥ y i : ℝ) : EReal) := by
      unfold Data.lp32
      exact iInf_le_of_le lam (iInf_le_of_le y (iInf_le_of_le phi (iInf_le_of_le psi
        (iInf_le_of_le hF.2 le_rfl))))
    refine (add_le_add_right hle _).trans ?_
    rw [← EReal.coe_add, add_assoc]
  · refine le_iInf₂ fun x hx => ?_
    rw [hpt x hx]
    unfold Data.lp32
    simp only [WTS6Aux.coe_add_iInf]
    refine le_iInf fun lam => le_iInf fun y => le_iInf fun phi => le_iInf fun psi =>
      le_iInf fun hF => ?_
    refine iInf_le_of_le x (iInf_le_of_le lam (iInf_le_of_le y (iInf_le_of_le phi
      (iInf_le_of_le psi (iInf_le_of_le ⟨hx, hF⟩ ?_)))))
    rw [← EReal.coe_add, add_assoc]
