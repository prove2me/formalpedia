-- Prove2me | solution 1 for WassTwoStage.LP1.constraint_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:00:35.155812+00:00
-- url     : https://prove2.me/submissions/e00eba2c-702c-40bf-82a3-1f78504c964d

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge
import Theorems.Thm_WassTwoStage_LP1_dual_norm_31
import Theorems.Thm_LP_farkas
import Theorems.Thm_LP_strong_duality_matrix

open Matrix

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

open WassTwoStage.LP1 in
theorem solution {K M N₂ : ℕ} (T : Matrix (Fin M) (Fin K) ℝ)
    (W : Matrix (Fin M) (Fin N₂) ℝ) (q : Fin N₂ → ℝ) (wp wm lam : ℝ)
    (hwp : 0 < wp) (hwm : 0 < wm) (hlam : 0 ≤ lam)
    (hrec : ∃ p : Fin M → ℝ, 0 ≤ p ∧ Wᵀ *ᵥ p = q) :
    ((∀ p : Fin M → ℝ, 0 ≤ p → Wᵀ *ᵥ p = q → dualGauge wp wm (Tᵀ *ᵥ p) ≤ (lam : EReal)) ↔
      ∀ k : Fin K,
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), (((Tᵀ *ᵥ p) k / wp : ℝ) : EReal))
            ≤ (lam : EReal) ∧
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((-(Tᵀ *ᵥ p) k / wm : ℝ) : EReal))
            ≤ (lam : EReal)) ∧
    ((∀ k : Fin K,
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), (((Tᵀ *ᵥ p) k / wp : ℝ) : EReal))
            ≤ (lam : EReal) ∧
        (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((-(Tᵀ *ᵥ p) k / wm : ℝ) : EReal))
            ≤ (lam : EReal)) ↔
      ∀ k : Fin K, ∃ phi psi : Fin N₂ → ℝ,
        q ⬝ᵥ phi ≤ lam ∧ q ⬝ᵥ psi ≤ lam ∧
        (1 / wp) • (T *ᵥ Pi.single k 1) ≤ W *ᵥ phi ∧
        -((1 / wm) • (T *ᵥ Pi.single k 1)) ≤ W *ᵥ psi) := by
  have hcol : ∀ (k : Fin K) (p : Fin M → ℝ), (T *ᵥ Pi.single k 1) ⬝ᵥ p = (Tᵀ *ᵥ p) k := by
    intro k p
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_single_one]
  have h1 : ∀ (k : Fin K) (p : Fin M → ℝ),
      ((1 / wp) • (T *ᵥ Pi.single k 1)) ⬝ᵥ p = (Tᵀ *ᵥ p) k / wp := by
    intro k p; rw [smul_dotProduct, hcol, smul_eq_mul]; ring
  have h2 : ∀ (k : Fin K) (p : Fin M → ℝ),
      (-((1 / wm) • (T *ᵥ Pi.single k 1))) ⬝ᵥ p = -(Tᵀ *ᵥ p) k / wm := by
    intro k p; rw [neg_dotProduct, smul_dotProduct, hcol, smul_eq_mul]; ring
  constructor
  · rcases Nat.eq_zero_or_pos K with rfl | hK
    · constructor
      · intro _ k; exact k.elim0
      · intro _ p _ _
        unfold dualGauge
        refine iSup₂_le fun ξ _ => ?_
        have : (Tᵀ *ᵥ p) ⬝ᵥ ξ = 0 := by simp [dotProduct]
        rw [this]; exact_mod_cast hlam
    · have hdn := fun z => WassTwoStage.LP1.dual_norm_31 hK wp wm hwp hwm z
      constructor
      · intro H k
        constructor
        · refine iSup₂_le fun p hp => ?_
          have := H p hp.1 hp.2
          rw [hdn, EReal.coe_le_coe_iff, Finset.sup'_le_iff] at this
          exact EReal.coe_le_coe_iff.mpr (le_of_max_le_left (this k (Finset.mem_univ _)))
        · refine iSup₂_le fun p hp => ?_
          have := H p hp.1 hp.2
          rw [hdn, EReal.coe_le_coe_iff, Finset.sup'_le_iff] at this
          exact EReal.coe_le_coe_iff.mpr (le_of_max_le_right (this k (Finset.mem_univ _)))
      · intro H p hp hpq
        rw [hdn, EReal.coe_le_coe_iff, Finset.sup'_le_iff]
        intro k _
        obtain ⟨Ha, Hb⟩ := H k
        have ha := (le_iSup₂ (f := fun p (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q) =>
          (((Tᵀ *ᵥ p) k / wp : ℝ) : EReal)) p ⟨hp, hpq⟩).trans Ha
        have hb := (le_iSup₂ (f := fun p (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q) =>
          ((-(Tᵀ *ᵥ p) k / wm : ℝ) : EReal)) p ⟨hp, hpq⟩).trans Hb
        exact max_le (EReal.coe_le_coe_iff.mp ha) (EReal.coe_le_coe_iff.mp hb)
  · refine forall_congr' fun k => ?_
    have e1 : (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), (((Tᵀ *ᵥ p) k / wp : ℝ) : EReal))
        = ⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q),
          ((((1 / wp) • (T *ᵥ Pi.single k 1)) ⬝ᵥ p : ℝ) : EReal) := by
      simp only [h1]
    have e2 : (⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q), ((-(Tᵀ *ᵥ p) k / wm : ℝ) : EReal))
        = ⨆ (p : Fin M → ℝ) (_ : 0 ≤ p ∧ Wᵀ *ᵥ p = q),
          (((-((1 / wm) • (T *ᵥ Pi.single k 1))) ⬝ᵥ p : ℝ) : EReal) := by
      simp only [h2]
    rw [e1, e2, WTS6Aux.sup_le_iff' W q _ hrec, WTS6Aux.sup_le_iff' W q _ hrec]
    constructor
    · rintro ⟨⟨φ, hφ1, hφ2⟩, ⟨ψ, hψ1, hψ2⟩⟩
      exact ⟨φ, ψ, hφ2, hψ2, hφ1, hψ1⟩
    · rintro ⟨φ, ψ, a1, a2, a3, a4⟩
      exact ⟨⟨φ, a3, a1⟩, ⟨ψ, a4, a2⟩⟩
