-- Prove2me | solution 1 for QMA2ClassicalSep.Main.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:00:28.082642+00:00
-- url     : https://prove2.me/submissions/db23610a-e3ee-4293-bd8f-54390437d56c

import Definitions.Def_QMA2ClassicalSep_Main_HardDist

namespace QMA2ClassicalSep.Main

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

set_option autoImplicit false

private lemma signedU_unitary {k ℓ : ℕ} (inst : SignedInstance k ℓ) (p : PIdx k) :
    (inst.U p)ᴴ * inst.U p = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, SignedInstance.U]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (inst.perm p i)]
    · by_cases h : inst.bit p i <;> simp [SignedInstance.sgn, h]
    · intro b _ hbi
      simp [hbi]
    · simp
  · simp only [Matrix.one_apply, hij, if_false]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x = inst.perm p i
    · subst x
      simp [hij]
    · simp [hxi]

private lemma hp_factor {k ℓ : ℕ} (inst : SignedInstance k ℓ) (p : PIdx k) :
    inst.Hp p = (1 / 4 : ℂ) • ((1 - inst.U p)ᴴ * (1 - inst.U p)) := by
  rw [SignedInstance.Hp, SignedInstance.Gam, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    signedU_unitary]
  module

private lemma hp_posSemidef {k ℓ : ℕ} (inst : SignedInstance k ℓ) (p : PIdx k) :
    (inst.Hp p).PosSemidef := by
  rw [hp_factor]
  exact Matrix.PosSemidef.smul
    (Matrix.posSemidef_conjTranspose_mul_self (1 - inst.U p))
    (a := (1 / 4 : ℂ)) (by norm_num [Complex.nonneg_iff])

private lemma ham_posSemidef {k ℓ : ℕ} (inst : SignedInstance k ℓ) :
    inst.Ham.PosSemidef := by
  unfold SignedInstance.Ham
  apply Matrix.PosSemidef.smul (a := (1 / (2 ^ k : ℂ))) _
    (by norm_num [Complex.nonneg_iff])
  classical
  induction (Finset.univ : Finset (PIdx k)) using Finset.induction with
  | empty => simp [Matrix.PosSemidef.zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hp_posSemidef inst a).add ih

private lemma ham_expect_nonneg {k ℓ : ℕ} (inst : SignedInstance k ℓ) (ψ : Vtx ℓ → ℂ) :
    0 ≤ expect inst.Ham ψ :=
  (Complex.nonneg_iff.mp ((ham_posSemidef inst).dotProduct_mulVec_nonneg ψ)).1

private lemma ham_expect_zero_of_fixed {k ℓ : ℕ} (inst : SignedInstance k ℓ)
    (ψ : Vtx ℓ → ℂ) (hfix : ∀ p, (inst.U p).mulVec ψ = ψ) :
    expect inst.Ham ψ = 0 := by
  have hpzero (p : PIdx k) : (inst.Hp p).mulVec ψ = 0 := by
    rw [hp_factor, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, hfix]
    simp
  unfold expect
  rw [SignedInstance.Ham, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp [hpzero]

private lemma unit_normSq (u : ℤˣ) : Complex.normSq (((u : ℤ) : ℂ)) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

private lemma signVec_isUnit {ℓ : ℕ} (h : Coord ℓ → ℤˣ) :
    IsUnit' (fun x => ((h x : ℤ) : ℂ) / (Real.sqrt ((2 : ℝ) ^ ℓ) : ℂ)) := by
  have hr : (Real.sqrt ((2 : ℝ) ^ ℓ)) ^ 2 = (2 : ℝ) ^ ℓ := by
    rw [Real.sq_sqrt (by positivity)]
  unfold IsUnit'
  simp_rw [Complex.normSq_div, unit_normSq, Complex.normSq_ofReal]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  simp only [nsmul_eq_mul]
  rw [show Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt ((2 : ℝ) ^ ℓ) = (2 : ℝ) ^ ℓ by
    nlinarith [hr]]
  field_simp
  norm_num

private lemma chi_cases {k : ℕ} (hA hB : SignFn k) (x : HVtx k) :
    chi hA hB x = 1 ∨ chi hA hB x = -1 := by
  rcases Int.units_eq_one_or (hA x.1) with ha | ha <;>
    rcases Int.units_eq_one_or (hB x.2) with hb | hb <;>
    simp [chi, ha, hb]

private lemma yes_sgn {k : ℕ} (ω : YESParam k) (p : PIdx k) (x : HVtx k) :
    (yesInst ω).sgn p x =
      (((chi ω.2.1 ω.2.2 x * chi ω.2.1 ω.2.2 (ω.1 p x) : ℤ) : ℂ)) := by
  rcases chi_cases ω.2.1 ω.2.2 x with hx | hx <;>
    rcases chi_cases ω.2.1 ω.2.2 (ω.1 p x) with hy | hy <;>
    simp [SignedInstance.sgn, yesInst, hx, hy]

private lemma yes_U_fix {k : ℕ} (ω : YESParam k) (p : PIdx k) :
    ((yesInst ω).U p).mulVec (prodVec
        (fun a => ((ω.2.1 a : ℤ) : ℂ) / (Real.sqrt ((2 : ℝ) ^ (3 * k)) : ℂ))
        (fun b => ((ω.2.2 b : ℤ) : ℂ) / (Real.sqrt ((2 : ℝ) ^ (3 * k)) : ℂ))) =
    prodVec
      (fun a => ((ω.2.1 a : ℤ) : ℂ) / (Real.sqrt ((2 : ℝ) ^ (3 * k)) : ℂ))
      (fun b => ((ω.2.2 b : ℤ) : ℂ) / (Real.sqrt ((2 : ℝ) ^ (3 * k)) : ℂ)) := by
  classical
  let r : ℂ := (Real.sqrt ((2 : ℝ) ^ (3 * k)) : ℂ)
  let ψ : HVtx k → ℂ := prodVec
    (fun a => ((ω.2.1 a : ℤ) : ℂ) / r)
    (fun b => ((ω.2.2 b : ℤ) : ℂ) / r)
  have hψ (x : HVtx k) : ψ x = ((chi ω.2.1 ω.2.2 x : ℤ) : ℂ) / (r * r) := by
    simp [ψ, prodVec, r, chi]
    ring
  have hstep (x : HVtx k) : (yesInst ω).sgn p x * ψ x = ψ (ω.1 p x) := by
    rw [yes_sgn, hψ, hψ]
    have hx : chi ω.2.1 ω.2.2 x * chi ω.2.1 ω.2.2 x = 1 := by
      rcases chi_cases ω.2.1 ω.2.2 x with h | h <;> rw [h] <;> norm_num
    push_cast
    calc
      ((chi ω.2.1 ω.2.2 x : ℂ) * (chi ω.2.1 ω.2.2 (ω.1 p x) : ℂ)) *
          ((chi ω.2.1 ω.2.2 x : ℂ) / (r * r)) =
          (((chi ω.2.1 ω.2.2 x * chi ω.2.1 ω.2.2 x : ℤ) : ℂ) *
            (chi ω.2.1 ω.2.2 (ω.1 p x) : ℂ)) / (r * r) := by push_cast; ring
      _ = (chi ω.2.1 ω.2.2 (ω.1 p x) : ℂ) / (r * r) := by rw [hx]; norm_num
  funext y
  change ∑ x, (yesInst ω).U p y x * ψ x = ψ y
  rw [Finset.sum_eq_single ((ω.1 p).symm y)]
  · simp only [SignedInstance.U]
    have heq : y = (yesInst ω).perm p ((ω.1 p).symm y) :=
      ((ω.1 p).apply_symm_apply y).symm
    rw [if_pos heq, hstep]
    simp
  · intro b _ hb
    have hy : y ≠ (yesInst ω).perm p b := by
      intro hy
      have hc := congrArg (ω.1 p).symm hy
      simp only [yesInst, Equiv.symm_apply_apply] at hc
      exact hb hc.symm
    simp [SignedInstance.U, hy]
  · simp

end QMA2ClassicalSep.Main

open QMA2ClassicalSep.Main

theorem solution (k : ℕ) (hk : 2 ≤ k) (ω : YESParam k) :
    lamSep (yesInst ω).Ham = 0 := by
  let α : Coord (3 * k) → ℂ := fun a =>
    ((ω.2.1 a : ℤ) : ℂ) / (Real.sqrt ((2 : ℝ) ^ (3 * k)) : ℂ)
  let β : Coord (3 * k) → ℂ := fun b =>
    ((ω.2.2 b : ℤ) : ℂ) / (Real.sqrt ((2 : ℝ) ^ (3 * k)) : ℂ)
  have hα : IsUnit' α := signVec_isUnit ω.2.1
  have hβ : IsUnit' β := signVec_isUnit ω.2.2
  have hzero : expect (yesInst ω).Ham (prodVec α β) = 0 := by
    apply ham_expect_zero_of_fixed
    intro p
    exact yes_U_fix ω p
  have hnonneg : ∀ e ∈ {e | ∃ α β : Coord (3 * k) → ℂ,
      IsUnit' α ∧ IsUnit' β ∧ e = expect (yesInst ω).Ham (prodVec α β)}, 0 ≤ e := by
    rintro e ⟨a, b, ha, hb, rfl⟩
    exact ham_expect_nonneg (yesInst ω) (prodVec a b)
  have hmem : (0 : ℝ) ∈ {e | ∃ α β : Coord (3 * k) → ℂ,
      IsUnit' α ∧ IsUnit' β ∧ e = expect (yesInst ω).Ham (prodVec α β)} :=
    ⟨α, β, hα, hβ, hzero.symm⟩
  exact le_antisymm (csInf_le ⟨0, hnonneg⟩ hmem) (le_csInf ⟨0, hmem⟩ hnonneg)
