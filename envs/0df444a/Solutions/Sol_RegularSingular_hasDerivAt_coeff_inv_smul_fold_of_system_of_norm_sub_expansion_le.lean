-- Prove2me | solution 1 for RegularSingular.hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c669bb03-1986-57a1-bea7-eb8ca9248179

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Group.Bounded
import Theorems.Thm_RegularSingular_hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
import Theorems.Thm_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le

set_option autoImplicit false

open Set

namespace RegularSingular
p2m_export "RegularSingular" "hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le norm_sum_shifted_sub_sum_reindexed_le"
namespace FoldAux
p2m_open "RegularSingular"

noncomputable def MopL {R : ℕ} (M : Matrix (Fin R) (Fin R) ℂ) : (Fin R → ℂ) →L[ℂ] (Fin R → ℂ) :=
  ContinuousLinearMap.pi fun a => ∑ b, M a b • ContinuousLinearMap.proj b

theorem MopL_apply {R : ℕ} (M : Matrix (Fin R) (Fin R) ℂ) (v : Fin R → ℂ) :
    MopL M v = Matrix.mulVec M v := by
  ext a; simp [MopL, Matrix.mulVec, dotProduct]

noncomputable def Lop {R d d₂ : ℕ} (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (y z : ℝ) :
    (Fin R → ℂ) →L[ℂ] (Fin R → ℂ) :=
  ∑ a' : Fin (d₂ + 1), ((y : ℂ) ^ (a' : ℕ)) • MopL (Mc a') +
    ∑ k : Fin d, ∑ a' : Fin (d₂ + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a' : ℕ)) • A k a'

theorem rhs_eq_Lop {R d d₂ : ℕ} (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (y z : ℝ) (v : Fin R → ℂ) :
    ((fun a => ∑ b, (∑ a' : Fin (d₂ + 1), (y : ℂ) ^ (a' : ℕ) * Mc a' a b) • v b) +
        ∑ k : Fin d, ∑ a' : Fin (d₂ + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a' : ℕ)) • A k a' v)
      = Lop Mc A y z v := by
  simp only [Lop, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, MopL_apply]
  congr 1
  ext a
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a' _ => ?_
  ring

theorem cpow_add_natCast (x : ℂ) (k : ℕ) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (x + (k : ℕ)) = (y : ℂ) ^ (k : ℕ) * (y : ℂ) ^ x := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_add _ _ hy', Complex.cpow_natCast, mul_comm]

theorem Lop_apply_eq_sum {R d d₂ : ℕ} (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (y z : ℝ) (v : Fin R → ℂ) :
    Lop Mc A y z v = ∑ a' : Fin (d₂ + 1), ((y : ℂ) ^ (a' : ℕ)) •
      (Matrix.mulVec (Mc a') v + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a' v) := by
  simp only [Lop, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, MopL_apply, smul_add, Finset.smul_sum, smul_smul,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun k _ => ?_
  ring_nf

theorem Lop_expansion {R d d₂ n J : ℕ} (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (e : Fin n → ℂ)
    (y z : ℝ) (hy : 0 < y) (v : Fin n → Fin J → (Fin R → ℂ)) :
    Lop Mc A y z (∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v i j) =
      ∑ a' : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J,
        ((y : ℂ) ^ (e i + (a' : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
          (Matrix.mulVec (Mc a') (v i j) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a' (v i j)) := by
  rw [map_sum]
  simp_rw [map_sum, map_smul, Lop_apply_eq_sum, Finset.smul_sum, smul_smul, cpow_add_natCast _ _ y hy]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a' _ => ?_
  congr 1
  ring

theorem norm_Lop_le {R d d₂ : ℕ} (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (y z : ℝ)
    (hy : y ∈ Ioc (0:ℝ) 1) (hz : z ∈ Ioc (0:ℝ) 2) :
    ‖Lop Mc A y z‖ ≤ ∑ a' : Fin (d₂ + 1), ‖MopL (Mc a')‖ +
      ∑ k : Fin d, ∑ a' : Fin (d₂ + 1), (2:ℝ) ^ ((k : ℕ) + 1) * ‖A k a'‖ := by
  have hy1 : ‖(y : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy.1]; exact hy.2
  have hz2 : ‖(z : ℂ)‖ ≤ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz.1]; exact hz.2
  unfold Lop
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    rw [norm_smul, norm_pow]
    calc ‖(y:ℂ)‖ ^ (a' : ℕ) * ‖MopL (Mc a')‖ ≤ 1 * ‖MopL (Mc a')‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hy1) (norm_nonneg _)
      _ = ‖MopL (Mc a')‖ := one_mul _
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    rw [norm_smul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖(z:ℂ)‖ ^ ((k:ℕ) + 1) ≤ (2:ℝ) ^ ((k:ℕ) + 1) := pow_le_pow_left₀ (norm_nonneg _) hz2 _
    have h2 : ‖(y:ℂ)‖ ^ (a' : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) hy1
    calc ‖(z:ℂ)‖ ^ ((k:ℕ) + 1) * ‖(y:ℂ)‖ ^ (a' : ℕ) * ‖A k a'‖ ≤ (2:ℝ) ^ ((k:ℕ) + 1) * 1 * ‖A k a'‖ := by
          gcongr
      _ = (2:ℝ) ^ ((k:ℕ) + 1) * ‖A k a'‖ := by ring

noncomputable def fold {R d d₂ n J : ℕ} (e : Fin n → ℂ) (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (C : Fin n → Fin J → ℝ → (Fin R → ℂ)) (i : Fin n) (j : Fin J) (z : ℝ) : Fin R → ℂ :=
  ∑ a : Fin (d₂ + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
    Matrix.mulVec (Mc a) (C i' j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i' j z) else 0

theorem continuousOn_fold {R d d₂ n J : ℕ} (e : Fin n → ℂ) (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (C : Fin n → Fin J → ℝ → (Fin R → ℂ)) (s : Set ℝ) (hC : ∀ i j, ContinuousOn (C i j) s)
    (i : Fin n) (j : Fin J) : ContinuousOn (fold e Mc A C i j) s := by
  unfold fold
  refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun i' _ => ?_
  split_ifs with h
  · refine ContinuousOn.add ?_ ?_
    · have : (fun z => Matrix.mulVec (Mc a) (C i' j z)) = fun z => MopL (Mc a) (C i' j z) := by
        funext z; rw [MopL_apply]
      rw [this]
      exact (MopL (Mc a)).continuous.comp_continuousOn (hC i' j)
    · refine continuousOn_finsetSum _ fun k _ => ?_
      exact ((Complex.continuous_ofReal.pow _).continuousOn).fun_smul ((A k a).continuous.comp_continuousOn (hC i' j))
  · exact continuousOn_const

theorem norm_el_shift_nonneg (x : ℂ) (l : ℕ) (y : ℝ) : 0 ≤ ‖(y : ℂ) ^ x * ((Real.log y : ℝ) : ℂ) ^ l‖ :=
  norm_nonneg _

theorem expFz_bound {R d d₂ n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hcl : ∀ (i : Fin n) (m : ℕ), (e i + m).re ≤ ρ → ∃ i', e i' = e i + m)
    (hgap : ∀ (i : Fin n) (m : ℕ), ρ < (e i + m).re → ρ + 2 * δ ≤ (e i + m).re)
    (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (F Fz : ℝ → ℝ → (Fin R → ℂ))
    (hsys : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt (fun z => F y z) (Fz y z) z ∧
      (z : ℂ) • Fz y z = (fun a => ∑ b, (∑ a' : Fin (d₂ + 1), (y : ℂ) ^ (a' : ℕ) * Mc a' a b) • F y z b) +
        ∑ k : Fin d, ∑ a' : Fin (d₂ + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a' : ℕ)) • A k a' (F y z))
    (C : Fin n → Fin J → ℝ → (Fin R → ℂ)) (hC : ∀ i j, ContinuousOn (C i j) (Set.Ioc 0 2))
    (hexp : ∀ z₀ ∈ Set.Ioc (0 : ℝ) 2, ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F y z - ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • C i j z‖ ≤
          K * y ^ (ρ + δ))
    (z₀ : ℝ) (hz₀ : z₀ ∈ Set.Ioc (0 : ℝ) 2) :
    ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε → ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖Fz y z - ∑ p : Fin n × Fin J, ((y : ℂ) ^ e p.1 * ((Real.log y : ℝ) : ℂ) ^ ((p.2 : Fin J) : ℕ)) •
          ((z : ℂ)⁻¹ • fold e Mc A C p.1 p.2 z)‖ ≤ K * y ^ (ρ + δ) := by
  classical
  obtain ⟨K, ε, hε, hK⟩ := hexp z₀ hz₀

  have hIcc : Icc (z₀ / 2) 2 ⊆ Ioc (0:ℝ) 2 := fun z hz => ⟨by linarith [hz.1, hz₀.1], hz.2⟩
  have hBij : ∀ i j, ∃ B, ∀ z ∈ Icc (z₀ / 2) 2, ‖C i j z‖ ≤ B := fun i j =>
    isCompact_Icc.exists_bound_of_continuousOn ((hC i j).mono hIcc)
  choose Bf hBf using hBij
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ i j, ∀ z ∈ Icc (z₀ / 2) 2, ‖C i j z‖ ≤ B := by
    refine ⟨∑ i, ∑ j, |Bf i j|, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _,
      fun i j z hz => ?_⟩
    calc ‖C i j z‖ ≤ |Bf i j| := (hBf i j z hz).trans (le_abs_self _)
      _ ≤ ∑ j', |Bf i j'| := Finset.single_le_sum (f := fun j' => |Bf i j'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', |Bf i' j'| := Finset.single_le_sum (f := fun i' => ∑ j', |Bf i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

  set W : ℝ := ∑ a : Fin (d₂ + 1), (‖MopL (Mc a)‖ + ∑ k : Fin d, (2:ℝ) ^ ((k:ℕ) + 1) * ‖A k a‖) with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun a _ => add_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _))
  set Λ : ℝ := ∑ a' : Fin (d₂ + 1), ‖MopL (Mc a')‖ +
      ∑ k : Fin d, ∑ a' : Fin (d₂ + 1), (2:ℝ) ^ ((k : ℕ) + 1) * ‖A k a'‖ with hΛ
  have hΛ0 : 0 ≤ Λ := add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _))
  set C5 : ℝ := (((d₂ : ℝ) + 1) * n * (W * B) * ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) with hC5
  refine ⟨(2 / z₀) * (C5 + Λ * |K|), min ε (z₀ / 2), lt_min hε (by linarith [hz₀.1]), ?_⟩
  intro z hz hzz y hy
  have hzε : |z - z₀| < ε := hzz.trans_le (min_le_left _ _)
  have hzI : z ∈ Icc (z₀ / 2) 2 := by
    constructor
    · have := (abs_lt.1 (hzz.trans_le (min_le_right _ _))).1; linarith
    · exact hz.2
  have hz0 : 0 < z := hz.1
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz0.ne'

  obtain ⟨hderz, hsz⟩ := hsys y hy z hz
  have hFz : Fz y z = (z : ℂ)⁻¹ • Lop Mc A y z (F y z) := by
    rw [← rhs_eq_Lop, ← hsz, inv_smul_smul₀ hzC]
  set P : Fin R → ℂ := ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • C i j z
    with hP
  have hRm : ‖F y z - P‖ ≤ K * y ^ (ρ + δ) := hK z hz hzε y hy

  have hw : ∀ a i j, ‖Matrix.mulVec (Mc a) (C i j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i j z)‖
      ≤ W * B := by
    intro a i j
    have hCB := hB i j z hzI
    have h1 : ‖Matrix.mulVec (Mc a) (C i j z)‖ ≤ ‖MopL (Mc a)‖ * B := by
      rw [← MopL_apply]; exact (MopL (Mc a)).le_opNorm_of_le hCB
    have h2 : ∀ k : Fin d, ‖((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i j z)‖ ≤ (2:ℝ) ^ ((k:ℕ)+1) * ‖A k a‖ * B := by
      intro k
      rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0, mul_assoc]
      exact mul_le_mul (pow_le_pow_left₀ hz0.le hz.2 _) ((A k a).le_opNorm_of_le hCB) (norm_nonneg _)
        (pow_nonneg (by norm_num) _)
    calc _ ≤ ‖Matrix.mulVec (Mc a) (C i j z)‖ + ∑ k : Fin d, ‖((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i j z)‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ ‖MopL (Mc a)‖ * B + ∑ k : Fin d, (2:ℝ) ^ ((k:ℕ)+1) * ‖A k a‖ * B :=
          add_le_add h1 (Finset.sum_le_sum fun k _ => h2 k)
      _ = (‖MopL (Mc a)‖ + ∑ k : Fin d, (2:ℝ) ^ ((k:ℕ) + 1) * ‖A k a‖) * B := by
          rw [add_mul, Finset.sum_mul]
      _ ≤ W * B := by
          refine mul_le_mul_of_nonneg_right ?_ hB0
          exact Finset.single_le_sum (f := fun a => ‖MopL (Mc a)‖ + ∑ k : Fin d, (2:ℝ) ^ ((k:ℕ) + 1) * ‖A k a‖)
            (fun a _ => add_nonneg (norm_nonneg _)
              (Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)))
            (Finset.mem_univ a)
  have hfold := RegularSingular.norm_sum_shifted_sub_sum_reindexed_le e he ρ δ hδ hcl hgap d₂
    (fun a i j => Matrix.mulVec (Mc a) (C i j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i j z))
    (W * B) hw y hy

  have hfold_eq : (∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
      (∑ a : Fin (d₂ + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then
        Matrix.mulVec (Mc a) (C i j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i j z) else 0))
      = ∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • fold e Mc A C i' j z := by
    rfl
  rw [hfold_eq] at hfold
  have hLopP : Lop Mc A y z P = ∑ a' : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J,
        ((y : ℂ) ^ (e i + (a' : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
          (Matrix.mulVec (Mc a') (C i j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a' (C i j z)) :=
    Lop_expansion Mc A e y z hy.1 (fun i j => C i j z)

  have hsum : ∑ p : Fin n × Fin J, ((y : ℂ) ^ e p.1 * ((Real.log y : ℝ) : ℂ) ^ ((p.2 : Fin J) : ℕ)) •
      ((z : ℂ)⁻¹ • fold e Mc A C p.1 p.2 z)
      = (z : ℂ)⁻¹ • ∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
          fold e Mc A C i' j z := by
    rw [Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  rw [hsum, hFz, ← smul_sub, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0]

  have hsplit : Lop Mc A y z (F y z) - ∑ i' : Fin n, ∑ j : Fin J,
      ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • fold e Mc A C i' j z
      = (Lop Mc A y z P - ∑ i' : Fin n, ∑ j : Fin J,
          ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • fold e Mc A C i' j z) + Lop Mc A y z (F y z - P) := by
    rw [map_sub]; abel
  rw [hsplit]
  have hnorm : ‖(Lop Mc A y z P - ∑ i' : Fin n, ∑ j : Fin J,
          ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • fold e Mc A C i' j z) + Lop Mc A y z (F y z - P)‖
      ≤ (C5 + Λ * |K|) * y ^ (ρ + δ) := by
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ?_ ?_
    · rw [hLopP]; exact hfold
    · calc ‖Lop Mc A y z (F y z - P)‖ ≤ ‖Lop Mc A y z‖ * ‖F y z - P‖ := (Lop Mc A y z).le_opNorm _
        _ ≤ Λ * (|K| * y ^ (ρ + δ)) := by
            refine mul_le_mul (norm_Lop_le Mc A y z hy hz) ?_ (norm_nonneg _) hΛ0
            exact hRm.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hy.1.le _))
        _ = Λ * |K| * y ^ (ρ + δ) := by ring
  have hQ0 : 0 ≤ (C5 + Λ * |K|) * y ^ (ρ + δ) := (norm_nonneg _).trans hnorm
  have hinvz : z⁻¹ ≤ 2 / z₀ := by
    rw [div_eq_mul_inv, ← one_div]
    have : z₀ / 2 ≤ z := hzI.1
    rw [show (2:ℝ) * z₀⁻¹ = (z₀ / 2)⁻¹ by rw [inv_div]; ring]
    exact (one_div z).symm ▸ inv_anti₀ (by linarith [hz₀.1]) this
  calc z⁻¹ * ‖_‖ ≤ z⁻¹ * ((C5 + Λ * |K|) * y ^ (ρ + δ)) := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hz0.le)
    _ ≤ (2 / z₀) * ((C5 + Λ * |K|) * y ^ (ρ + δ)) := mul_le_mul_of_nonneg_right hinvz hQ0
    _ = 2 / z₀ * (C5 + Λ * |K|) * y ^ (ρ + δ) := by ring

end RegularSingular.FoldAux

open RegularSingular.FoldAux in
theorem solution
    {n J R d d₂ : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ (i : Fin n) (m : ℕ), (e i + m).re ≤ ρ → ∃ i', e i' = e i + m)
    (hgap : ∀ (i : Fin n) (m : ℕ), ρ < (e i + m).re → ρ + 2 * δ ≤ (e i + m).re)
    (Mc : Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (F Fz : ℝ → ℝ → (Fin R → ℂ))
    (hsys : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt (fun z => F y z) (Fz y z) z ∧
      (z : ℂ) • Fz y z = (fun a => ∑ b, (∑ a' : Fin (d₂ + 1), (y : ℂ) ^ (a' : ℕ) * Mc a' a b) • F y z b) +
        ∑ k : Fin d, ∑ a' : Fin (d₂ + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a' : ℕ)) • A k a' (F y z))
    (C : Fin n → Fin J → ℝ → (Fin R → ℂ)) (hC : ∀ i j, ContinuousOn (C i j) (Set.Ioc 0 2))
    (hexp : ∀ z₀ ∈ Set.Ioc (0 : ℝ) 2, ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F y z - ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • C i j z‖ ≤
          K * y ^ (ρ + δ)) :
    ∀ (i : Fin n) (j : Fin J), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      HasDerivAt (C i j)
        ((z : ℂ)⁻¹ • ∑ a : Fin (d₂ + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
          Matrix.mulVec (Mc a) (C i' j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a (C i' j z)
        else 0) z := by
  classical

  have hFzeq : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2,
      Fz y z = (z : ℂ)⁻¹ • Lop Mc A y z (F y z) := by
    intro y hy z hz
    have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz.1.ne'
    rw [← rhs_eq_Lop, ← (hsys y hy z hz).2, inv_smul_smul₀ hzC]
  have hFc : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ContinuousOn (fun z => F y z) (Set.Ioc 0 2) :=
    fun y hy z hz => (hsys y hy z hz).1.continuousAt.continuousWithinAt
  have hFz : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ContinuousOn (fun z => Fz y z) (Set.Ioc 0 2) := by
    intro y hy
    have hform : ContinuousOn (fun z : ℝ => (z : ℂ)⁻¹ • Lop Mc A y z (F y z)) (Set.Ioc 0 2) := by
      refine ContinuousOn.fun_smul (f := fun z : ℝ => (z : ℂ)⁻¹) (g := fun z => Lop Mc A y z (F y z)) ?_ ?_
      · exact (Complex.continuous_ofReal.continuousOn).inv₀ fun z hz => by exact_mod_cast hz.1.ne'
      · have : (fun z : ℝ => Lop Mc A y z (F y z)) = fun z => ∑ a' : Fin (d₂ + 1), ((y : ℂ) ^ (a' : ℕ)) •
            (MopL (Mc a') (F y z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A k a' (F y z)) := by
          funext z; rw [Lop_apply_eq_sum]; simp only [MopL_apply]
        rw [this]
        refine continuousOn_finsetSum _ fun a' _ => ContinuousOn.fun_const_smul ?_ _
        refine ((MopL (Mc a')).continuous.comp_continuousOn (hFc y hy)).add ?_
        refine continuousOn_finsetSum _ fun k _ => ?_
        exact ((Complex.continuous_ofReal.pow _).continuousOn).fun_smul ((A k a').continuous.comp_continuousOn (hFc y hy))
    exact hform.congr fun z hz => hFzeq y hy z hz
  have hinjP : Function.Injective (fun p : Fin n × Fin J => (e p.1, ((p.2 : Fin J) : ℕ))) := by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    have hi : i₁ = i₂ := he h₁
    have hj : j₁ = j₂ := Fin.ext h₂
    subst hi hj
    rfl
  have hθP : ∀ p : Fin n × Fin J, (e p.1).re < ρ + δ := fun p => by linarith [hre p.1]
  have hg : ∀ p : Fin n × Fin J, ContinuousOn (fun z : ℝ => ((z : ℝ) : ℂ)⁻¹ • fold e Mc A C p.1 p.2 z) (Set.Ioc 0 2) := by
    intro p
    refine ContinuousOn.fun_smul ?_ (continuousOn_fold e Mc A C _ hC p.1 p.2)
    exact (Complex.continuous_ofReal.continuousOn).inv₀ fun z hz => by exact_mod_cast hz.1.ne'
  have hexpF : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∃ K : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y z - ∑ p : Fin n × Fin J, ((y : ℂ) ^ e p.1 * ((Real.log y : ℝ) : ℂ) ^ ((p.2 : Fin J) : ℕ)) •
        C p.1 p.2 z‖ ≤ K * y ^ (ρ + δ) := by
    intro z hz
    obtain ⟨K, ε, hε, hK⟩ := hexp z hz
    refine ⟨K, fun y hy => ?_⟩
    rw [Fintype.sum_prod_type]
    exact hK z hz (by simp [hε]) y hy
  have hexpFz := fun z₀ (hz₀ : z₀ ∈ Set.Ioc (0:ℝ) 2) =>
    expFz_bound e he ρ δ hδ hcl hgap Mc A F Fz hsys C hC hexp z₀ hz₀
  have key := RegularSingular.hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
    (ι := Fin n × Fin J) R (fun p => e p.1) (fun p => ((p.2 : Fin J) : ℕ)) hinjP (ρ + δ) hθP F Fz
    (fun p (z : ℝ) => C p.1 p.2 z) (fun p (z : ℝ) => ((z : ℝ) : ℂ)⁻¹ • fold e Mc A C p.1 p.2 z)
    (fun y hy z hz => (hsys y hy z hz).1) hFz hg hexpF hexpFz
  intro i j z hz
  exact key (i, j) z hz

end S_RegularSingular_hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le
end P2MW
export P2MW.S_RegularSingular_hasDerivAt_coeff_inv_smul_fold_of_system_of_norm_sub_expansion_le (solution)
