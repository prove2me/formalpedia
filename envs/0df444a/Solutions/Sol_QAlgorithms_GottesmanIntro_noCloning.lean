-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.noCloning
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:56:47.220675+00:00
-- url     : https://prove2.me/submissions/98f04684-44fd-4698-aa01-634b2974e2dc

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open QAlgorithms
open scoped ComplexConjugate Matrix

private noncomputable def twoState {ι : Type*} [DecidableEq ι]
    (i j : ι) (c : ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun k => if k = i then (3 / 5 : ℂ) else if k = j then c else 0)

private lemma twoState_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c : ℂ) (hc : ‖c‖ ^ 2 = 16 / 25) :
    IsState (twoState i j c) := by
  have hsq : ‖twoState i j c‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ k, ‖twoState i j c k‖ ^ 2 =
          ∑ k : ι, ((if k = i then (9 / 25 : ℝ) else 0) +
            (if k = j then (16 / 25 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hi : k = i
        · subst k
          norm_num [twoState, hij]
        · by_cases hj : k = j
          · subst k
            simp [twoState, hij.symm, hc]
          · simp [twoState, hi, hj]
      _ = 1 := by simp [Finset.sum_add_distrib]; norm_num
  unfold IsState
  nlinarith [norm_nonneg (twoState i j c)]

private lemma channel_add_smul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) (A B : Matrix ι ι ℂ) (r s : ℂ) :
    Φ (r • A + s • B) = r • Φ A + s • Φ B := by
  obtain ⟨m, E, _, hE⟩ := hΦ
  simp only [hE, krausApply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Finset.sum_add_distrib, ← Finset.smul_sum]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι)
    (Φ : Superop ι (ι × ι)) (hΦ : IsChannel Φ) :
    ¬ ∀ ψ : EuclideanSpace ℂ ι, IsState ψ → Φ (pureDensity ψ) = pureDensity (tensorVec ψ ψ) := by
  classical
  have hn : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let _ := hn
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let p := twoState i j (4 / 5)
  let m := twoState i j (-4 / 5)
  have hp : IsState p := twoState_unit i j hij _ (by norm_num)
  have hm : IsState m := twoState_unit i j hij _ (by norm_num)
  intro hclone
  have hi := hclone (ket i) (by simp [IsState, ket])
  have hj := hclone (ket j) (by simp [IsState, ket])
  have hmix : pureDensity p + pureDensity m =
      (18 / 25 : ℂ) • pureDensity (ket i) + (32 / 25 : ℂ) • pureDensity (ket j) := by
    ext x y
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      by_cases hyi : y = i <;> by_cases hyj : y = j <;>
      simp_all [pureDensity, p, m, twoState, ket, map_ofNat]
    <;> norm_num
  have hlin : Φ (pureDensity p) + Φ (pureDensity m) =
      (18 / 25 : ℂ) • Φ (pureDensity (ket i)) +
      (32 / 25 : ℂ) • Φ (pureDensity (ket j)) := by
    calc
      Φ (pureDensity p) + Φ (pureDensity m) = Φ (pureDensity p + pureDensity m) := by
        simpa only [one_smul] using
          (channel_add_smul Φ hΦ (pureDensity p) (pureDensity m) 1 1).symm
      _ = _ := by rw [hmix, channel_add_smul Φ hΦ]
  rw [hclone p hp, hclone m hm, hi, hj] at hlin
  have he := congrArg (fun M => M (i,j) (i,j)) hlin
  norm_num [pureDensity, tensorVec, p, m, twoState, ket,
    PiLp.single_apply, hij, hij.symm] at he
