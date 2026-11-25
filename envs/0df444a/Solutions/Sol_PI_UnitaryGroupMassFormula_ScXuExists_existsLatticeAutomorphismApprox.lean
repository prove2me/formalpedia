-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.existsLatticeAutomorphismApprox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:54.964687+00:00
-- url     : https://prove2.me/submissions/cfcaeb24-c35e-418a-97a3-4530e22c3f58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_v_small
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_v_add_small
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_v_neg_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_good_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_inv_memO_of_v
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_leg
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_ne_zero_of_v
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_add_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_add_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_smul_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_smul_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_sub_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_sub_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_sum_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_sum_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_smem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
section Main
variable {K : Type} [Field K] (O : ValuationSubring K)
private theorem valuationSubring_valuation_le_one_of_mem {K : Type} [Field K] (O : ValuationSubring K) {x : K}
    (hx : x ∈ O) : O.valuation x ≤ 1 := by
  first
  | exact (O.valuation_le_one_iff x).mpr hx
  | exact O.valuation_le_one ⟨x, hx⟩
  | exact (ValuationSubring.valuation_le_one_iff O x).2 hx
end Main
private theorem sub_vecMul_field {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : (x - y) ᵥ* M = x ᵥ* M - y ᵥ* M := by
  first
  | exact Matrix.sub_vecMul M x y
  | (funext j; simp [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib])
private theorem add_vecMul_field {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : (x + y) ᵥ* M = x ᵥ* M + y ᵥ* M := by
  first
  | exact Matrix.add_vecMul M x y
  | (funext j; simp [Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib])
private theorem smul_vecMul_field {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (c : K) (x : Fin n → K) : (c • x) ᵥ* M = c • (x ᵥ* M) := by
  first
  | exact Matrix.vecMul_smul M c x
  | (funext j; simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc])
private theorem exists_mem_sum_smul_eq_smul_of_divisible {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ}
    (M : Submodule O (Fin n → K)) (g : K) (f f' : Fin r → K) (v v' : Fin r → Fin n → K)
    (hv : ∀ i, v i ∈ M) (hv' : ∀ i, v' i ∈ M)
    (hf : ∀ i, ∃ s ∈ O, f i = g * s) (hf' : ∀ i, ∃ s ∈ O, f' i = g * s) :
    ∃ w ∈ M, ∑ i, (f i • v i + f' i • v' i) = g • w := by
  choose s hs hse using hf
  choose s' hs' hse' using hf'
  refine ⟨∑ i, (s i • v i + s' i • v' i),
    M.sum_mem fun i _ => M.add_mem (smem O (hs i) (hv i))
      (smem O (hs' i) (hv' i)), ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hse i, hse' i, smul_add, mul_smul, mul_smul]
private theorem exists_pr_orthogonal_left_sub_smul_mem {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (Λ1 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
    (g : K) (hg : g ∈ O)
    (hpair : ∀ i j, pr P (α i) (a j) = 0 ∧ pr P (α' i) (a' j) = 0 ∧
      pr P (α i) (a' j) = (if i = j then 1 else 0) ∧ pr P (α' i) (a j) = (if i = j then 1 else 0))
    (ha : ∀ i, a i ∈ Λ1) (ha' : ∀ i, a' i ∈ Λ1) {u0 : Fin n → K} (hu0 : u0 ∈ Λ1)
    (h1 : ∀ i, ∃ s ∈ O, pr P (α i) u0 = g * s) (h2 : ∀ i, ∃ s ∈ O, pr P (α' i) u0 = g * s) :
    ∃ u1 ∈ Λ1, (∀ j, pr P (α j) u1 = 0 ∧ pr P (α' j) u1 = 0) ∧
      ∃ w ∈ Λ1, u1 = u0 - g • w := by
  have e1 : ∀ i j, pr P (α i) (a j) = 0 := fun i j => (hpair i j).1
  have e2 : ∀ i j, pr P (α' i) (a' j) = 0 := fun i j => (hpair i j).2.1
  have e3 : ∀ i j, pr P (α i) (a' j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.1
  have e4 : ∀ i j, pr P (α' i) (a j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.2
  obtain ⟨w, hw, hS⟩ := exists_mem_sum_smul_eq_smul_of_divisible O Λ1 g (fun i => pr P (α i) u0)
    (fun i => pr P (α' i) u0) a' a ha' ha h1 h2
  refine ⟨u0 - g • w, Λ1.sub_mem hu0 (smem O hg hw), fun j => ?_, w, hw, rfl⟩
  rw [← hS]
  constructor
  · simp [pr_sub_right, pr_sum_right, pr_add_right, pr_smul_right, e1, e2, e3, e4]
  · simp [pr_sub_right, pr_sum_right, pr_add_right, pr_smul_right, e1, e2, e3, e4]
private theorem exists_pr_orthogonal_right_sub_smul_mem {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
    (g : K) (hg : g ∈ O)
    (hpair : ∀ i j, pr P (α i) (a j) = 0 ∧ pr P (α' i) (a' j) = 0 ∧
      pr P (α i) (a' j) = (if i = j then 1 else 0) ∧ pr P (α' i) (a j) = (if i = j then 1 else 0))
    (hα : ∀ i, α i ∈ Λ2) (hα' : ∀ i, α' i ∈ Λ2) {φ0 : Fin n → K} (hφ0 : φ0 ∈ Λ2)
    (h3 : ∀ i, ∃ s ∈ O, pr P φ0 (a i) = g * s) (h4 : ∀ i, ∃ s ∈ O, pr P φ0 (a' i) = g * s) :
    ∃ φ1 ∈ Λ2, (∀ j, pr P φ1 (a j) = 0 ∧ pr P φ1 (a' j) = 0) ∧
      ∃ w ∈ Λ2, φ1 = φ0 - g • w := by
  have e1 : ∀ i j, pr P (α i) (a j) = 0 := fun i j => (hpair i j).1
  have e2 : ∀ i j, pr P (α' i) (a' j) = 0 := fun i j => (hpair i j).2.1
  have e3 : ∀ i j, pr P (α i) (a' j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.1
  have e4 : ∀ i j, pr P (α' i) (a j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.2
  obtain ⟨w, hw, hS⟩ := exists_mem_sum_smul_eq_smul_of_divisible O Λ2 g (fun i => pr P φ0 (a i))
    (fun i => pr P φ0 (a' i)) α' α hα' hα h3 h4
  refine ⟨φ0 - g • w, Λ2.sub_mem hφ0 (smem O hg hw), fun j => ?_, w, hw, rfl⟩
  rw [← hS]
  constructor
  · simp [pr_sub_left, pr_sum_left, pr_add_left, pr_smul_left, e1, e2, e3, e4]
  · simp [pr_sub_left, pr_sum_left, pr_add_left, pr_smul_left, e1, e2, e3, e4]
private theorem exists_isAdmissible_of_chain_lemma_8 {K : Type} [Field K] {O : ValuationSubring K} {n r : ℕ}
    {P : Matrix (Fin n) (Fin n) K} {Λ1 Λ2 : Submodule O (Fin n → K)} {a a' α α' : Fin r → Fin n → K}
    (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) {up φp um φm uq φq : Fin n → K}
    (hp : Pair O P Λ1 Λ2 a a' α α' up φp) (hm : Pair O P Λ1 Λ2 a a' α α' um φm)
    (hq : Pair O P Λ1 Λ2 a a' α α' uq φq)
    (hcp : O.valuation (pr P φp up) = 1) (hcm : O.valuation (pr P φm um) = 1)
    (hcq : O.valuation (pr P φq uq) = 1)
    (hd1 : O.valuation (pr P φp um) = 1) (hd2 : O.valuation (pr P φm uq) = 1) :
    ∃ T : GL (Fin n) K, Good O P Λ1 Λ2 a a' α α' T ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ up = uq ∧
      (φq ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = (pr P φq uq / pr P φp up) • (φp ᵥ* P) := by
  obtain ⟨T1, hT1, hT1u, hT1φ⟩ := leg hP hp hm hcp hcm hd1
  obtain ⟨T2, hT2, hT2u, hT2φ⟩ := leg hP hm hq hcm hcq hd2
  have hm0 : pr P φm um ≠ 0 := ne_zero_of_v O hcm
  have hp0 : pr P φp up ≠ 0 := ne_zero_of_v O hcp
  have hcoe : ((T2 * T1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (T2 : Matrix (Fin n) (Fin n) K) * (T1 : Matrix (Fin n) (Fin n) K) := by
    first
    | exact Units.val_mul T2 T1
    | rfl
    | simp
  refine ⟨T2 * T1, good_mul _ _ _ _ _ _ _ _ hT2 hT1, ?_, ?_⟩
  · rw [hcoe, ← Matrix.mulVec_mulVec, hT1u, hT2u]
  · rw [hcoe, ← Matrix.vecMul_vecMul, hT2φ, smul_vecMul_field, hT1φ, smul_smul]
    congr 1
    first
    | rw [div_mul_div_comm, mul_comm (pr P φm um) (pr P φp up), mul_div_mul_right _ _ hm0]
    | (field_simp; try ring)
end PI.UnitaryGroupMassFormula.ScXuExists
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution : LocLin := by
  unfold LocLin
  intro K _ O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t hg hginv hP hfam hpair hu hφ hu0 hφ0 horth ht htg
    hφu hcong hc0
  obtain ⟨st, hst, hts⟩ := htg
  obtain ⟨s0, hs0, hs0e⟩ := hc0
  have hvg : O.valuation g < 1 := lt_of_le_of_ne (valuationSubring_valuation_le_one_of_mem O hg)
    (fun h => hginv (inv_memO_of_v O h))
  obtain ⟨u1, hu1, hu1o, w1, hw1, hu1e⟩ := exists_pr_orthogonal_left_sub_smul_mem O P Λ1 a a' α α' g hg hpair
    (fun i => (hfam i).1) (fun i => (hfam i).2.1) hu0 (fun i => (hcong i).1) (fun i => (hcong i).2.1)
  obtain ⟨φ1, hφ1, hφ1o, w2, hw2, hφ1e⟩ := exists_pr_orthogonal_right_sub_smul_mem O P Λ2 a a' α α' g hg hpair
    (fun i => (hfam i).2.2.1) (fun i => (hfam i).2.2.2) hφ0 (fun i => (hcong i).2.2.1)
    (fun i => (hcong i).2.2.2)
  have hp1 : Pair O P Λ1 Λ2 a a' α α' u1 φ1 := by
    unfold Pair
    exact ⟨hu1, hφ1, hu1o, hφ1o⟩
  have hq : Pair O P Λ1 Λ2 a a' α α' u φ := by
    unfold Pair
    exact ⟨hu, hφ, fun i => ⟨(horth i).1, (horth i).2.1⟩, fun i => ⟨(horth i).2.2.1, (horth i).2.2.2⟩⟩
  have hk : s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1 ∈ O :=
    add_mem (sub_mem (sub_mem hs0 (hP φ0 hφ0 w1 hw1)) (hP w2 hw2 u0 hu0)) (mul_mem hg (hP w2 hw2 w1 hw1))
  have hBe : pr P φ1 u1 =
      -1 + g * (s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1) := by
    rw [hφ1e, hu1e]
    simp only [pr_sub_left, pr_sub_right, pr_smul_left, pr_smul_right]
    linear_combination hs0e
  have hB : O.valuation (pr P φ1 u1) = 1 := by
    rw [hBe]
    exact v_add_small O (v_neg_one O) (v_small O hvg hk)
  have hAe : pr P φ u = -1 + g * (-st) := by
    rw [hφu]
    linear_combination -hts
  have hA : O.valuation (pr P φ u) = 1 := by
    rw [hAe]
    exact v_add_small O (v_neg_one O) (v_small O hvg (neg_mem hst))
  have hmid : ∃ um φm, Pair O P Λ1 Λ2 a a' α α' um φm ∧
      O.valuation (pr P φm um) = 1 ∧ O.valuation (pr P φ1 um) = 1 ∧
      O.valuation (pr P φm u) = 1 := by
    rcases (valuationSubring_valuation_le_one_of_mem O (hP φ1 hφ1 u hu)).lt_or_eq with hx | hx
    · rcases (valuationSubring_valuation_le_one_of_mem O (hP φ hφ u1 hu1)).lt_or_eq with hy | hy
      · refine ⟨u + u1, φ, ?_, ?_, ?_, hA⟩
        · unfold Pair
          refine ⟨Λ1.add_mem hu hu1, hφ, fun i => ⟨?_, ?_⟩,
            fun i => ⟨(horth i).2.2.1, (horth i).2.2.2⟩⟩
          · rw [pr_add_right, (horth i).1, (hu1o i).1, add_zero]
          · rw [pr_add_right, (horth i).2.1, (hu1o i).2, add_zero]
        · rw [pr_add_right]
          exact v_add_small O hA hy
        · rw [pr_add_right, add_comm]
          exact v_add_small O hB hx
      · refine ⟨u1, φ, ?_, hy, hB, hA⟩
        unfold Pair
        exact ⟨hu1, hφ, hu1o, fun i => ⟨(horth i).2.2.1, (horth i).2.2.2⟩⟩
    · exact ⟨u, φ, hq, hA, hx, hA⟩
  obtain ⟨um, φm, hm, hcm, hd1, hd2⟩ := hmid
  obtain ⟨T, hT, hTu, hTφ⟩ := exists_isAdmissible_of_chain_lemma_8 hP hp1 hm hq hB hcm hA hd1 hd2
  have hB0 : pr P φ1 u1 ≠ 0 := ne_zero_of_v O hB
  obtain ⟨kc, hkc, hc⟩ : ∃ kc ∈ O, pr P φ u / pr P φ1 u1 = 1 + g * kc := by
    refine ⟨(-st - (s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1)) *
      (pr P φ1 u1)⁻¹, mul_mem (sub_mem (neg_mem hst) hk) (inv_memO_of_v O hB), ?_⟩
    rw [div_eq_iff hB0]
    have hinv : (pr P φ1 u1)⁻¹ * pr P φ1 u1 = 1 := inv_mul_cancel₀ hB0
    linear_combination hAe - hBe +
      g * (st + (s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1)) * hinv
  have hTinv : ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u1 := by
    rw [← hTu, Matrix.mulVec_mulVec]
    first
    | simp
    | rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hφ0e : φ0 = φ1 + g • w2 := by
    rw [hφ1e]
    abel
  unfold Good at hT
  obtain ⟨h1, h2, h3⟩ := hT
  refine ⟨T, h1, h2, h3, ⟨-w1, Λ1.neg_mem hw1, ?_⟩,
    ⟨kc • φ1 - w2, Λ2.sub_mem (smem O hkc hφ1) hw2, ?_⟩⟩
  · rw [hTinv, hu1e, smul_neg]
    abel
  · rw [hTφ, hc, hφ0e, add_vecMul_field, sub_vecMul_field, smul_vecMul_field, smul_vecMul_field]
    first
    | module
    | (simp only [add_smul, one_smul, smul_sub, mul_smul]; abel)
end PI.UnitaryGroupMassFormula.ScXuExists
