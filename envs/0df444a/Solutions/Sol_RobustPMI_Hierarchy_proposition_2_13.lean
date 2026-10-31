-- Prove2me | solution 1 for RobustPMI.Hierarchy.proposition_2_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:59:52.34781+00:00
-- url     : https://prove2.me/submissions/19267e92-0108-4fa5-909f-3ba98b24fb96

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.P213aux
open MvPolynomial Matrix RobustPMI.Hierarchy

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma Hs_eq_of_subset (v : (σ →₀ ℕ) → ℝ) (h : MvPolynomial σ ℝ) (B : Finset (σ →₀ ℕ))
    (hB : h.support ⊆ B) : Hs v h = ∑ α ∈ B, coeff α h * v α := by
  unfold Hs
  refine Finset.sum_subset hB ?_
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]

lemma Hs_add (v : (σ →₀ ℕ) → ℝ) (p q : MvPolynomial σ ℝ) : Hs v (p + q) = Hs v p + Hs v q := by
  classical
  set B := p.support ∪ q.support ∪ (p + q).support
  rw [Hs_eq_of_subset v (p + q) B Finset.subset_union_right,
    Hs_eq_of_subset v p B (fun x hx => by simp [B, hx]),
    Hs_eq_of_subset v q B (fun x hx => by simp [B, hx]), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add]; ring

lemma Hs_zero (v : (σ →₀ ℕ) → ℝ) : Hs v 0 = 0 := by simp [Hs]

lemma Hs_sum {κ : Type*} (v : (σ →₀ ℕ) → ℝ) (s : Finset κ) (p : κ → MvPolynomial σ ℝ) :
    Hs v (∑ i ∈ s, p i) = ∑ i ∈ s, Hs v (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Hs_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Hs_add, ih]

lemma Hs_monomial (v : (σ →₀ ℕ) → ℝ) (β : σ →₀ ℕ) (c : ℝ) : Hs v (monomial β c) = c * v β := by
  rw [Hs_eq_of_subset v _ {β} (support_monomial_subset), Finset.sum_singleton, coeff_monomial,
    if_pos rfl]

lemma Hs_monomial_mul (v : (σ →₀ ℕ) → ℝ) (β : σ →₀ ℕ) (c : ℝ) (g : MvPolynomial σ ℝ) :
    Hs v (monomial β c * g) = c * Hs (fun γ => v (β + γ)) g := by
  conv_lhs => rw [g.as_sum]
  rw [Finset.mul_sum, Hs_sum]
  rw [show Hs (fun γ => v (β + γ)) g = ∑ γ ∈ g.support, coeff γ g * v (β + γ) from rfl,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [monomial_mul, Hs_monomial]; ring

lemma Hs_mul (v : (σ →₀ ℕ) → ℝ) (p g : MvPolynomial σ ℝ) (B : Finset (σ →₀ ℕ))
    (hB : p.support ⊆ B) :
    Hs v (p * g) = ∑ β ∈ B, coeff β p * Hs (fun γ => v (β + γ)) g := by
  conv_lhs => rw [p.as_sum]
  rw [Finset.sum_mul, Hs_sum]
  rw [← Finset.sum_subset hB (f := fun β => coeff β p * Hs (fun γ => v (β + γ)) g)
    (fun β _ hβ => by rw [notMem_support_iff.mp hβ, zero_mul])]
  exact Finset.sum_congr rfl fun β _ => Hs_monomial_mul v β _ g

lemma support_subset_monos (p : MvPolynomial σ ℝ) (d : ℕ) (hp : p.totalDegree ≤ d) :
    p.support ⊆ monos (σ := σ) d := by
  intro α hα
  unfold monos
  rw [Finset.mem_filter, Finset.mem_Iic]
  have hdeg : α.degree ≤ d := le_trans (le_totalDegree hα) hp
  refine ⟨fun i => ?_, hdeg⟩
  simpa using le_trans (Finsupp.le_degree i α) hdeg

lemma riesz_entry {ι : Type*} [Fintype ι] (S : MatSeq σ ι) (F : Matrix ι ι (MvPolynomial σ ℝ)) :
    riesz S F = ∑ i, ∑ j, Hs (fun α => S α j i) (F i j) := by
  classical
  unfold riesz
  simp only [trace, diag, mul_apply, coeffMat, map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Hs_eq_of_subset _ _ (suppMat F)]
  exact fun α hα => Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, hα⟩

lemma part1 {n m : ℕ} (S : MatSeq (Fin n) (Fin m)) (d l : ℕ)
    (T : Matrix (Fin l) (Fin m) (MvPolynomial (Fin n) ℝ)) (hT : ∀ i j, (T i j).totalDegree ≤ d)
    (hM : (momentMat d S).PosSemidef) : 0 ≤ riesz S (Tᵀ * T) := by
  classical
  set B := monos (σ := Fin n) d
  have hB : ∀ r i, (T r i).support ⊆ B := fun r i => support_subset_monos _ d (hT r i)
  rw [riesz_entry]
  simp only [mul_apply, transpose_apply, Hs_sum]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun r _ => ?_
  have E : ∑ i, ∑ j, Hs (fun α => S α j i) (T r i * T r j) =
      ∑ β ∈ B, ∑ i, ∑ β' ∈ B, ∑ j, coeff β (T r i) * (S (β' + β) j i * coeff β' (T r j)) := by
    simp only [fun i j => Hs_mul (fun α => S α j i) (T r i) (T r j) B (hB r i)]
    simp only [fun i j β => Hs_eq_of_subset (fun γ => S (β + γ) j i) (T r j) B (hB r j)]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β' _ => Finset.sum_congr rfl fun j _ => ?_
    rw [add_comm β β']; ring
  rw [E]
  have hq := (posSemidef_iff_dotProduct_mulVec.1 hM.transpose).2
    (fun p : B × Fin m => coeff p.1.1 (T r p.2))
  simp only [dotProduct, mulVec, star_trivial, transpose_apply, momentMat, of_apply,
    Fintype.sum_prod_type, Finset.mul_sum] at hq
  rw [← Finset.sum_coe_sort B]
  refine le_of_le_of_eq hq (Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun i _ => ?_)
  rw [← Finset.sum_coe_sort B]

lemma pairM_TT_apply {n m q l : ℕ} (T : Matrix (Fin l) (Fin m × Fin q) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (j k : Fin m) :
    pairM (Tᵀ * T) G j k = ∑ r, ∑ a', ∑ a, T r (k, a') * (T r (j, a) * G a' a) := by
  simp only [pairM, trBlocks, of_apply, mul_apply, transpose_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- now: ∑ a, ∑ a', ∑ r, T r (k,a') * T r (j,a) * G a' a
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a' _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun a _ => by ring

lemma part2 {n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (S : MatSeq (Fin n) (Fin m)) (d l : ℕ)
    (T : Matrix (Fin l) (Fin m × Fin q) (MvPolynomial (Fin n) ℝ))
    (hT : ∀ i j, (T i j).totalDegree ≤ d)
    (hL : (locMat d G S).PosSemidef) : 0 ≤ riesz S (pairM (Tᵀ * T) G) := by
  classical
  set B := monos (σ := Fin n) d
  have hB : ∀ r i, (T r i).support ⊆ B := fun r i => support_subset_monos _ d (hT r i)
  rw [riesz_entry]
  simp only [pairM_TT_apply, Hs_sum]
  -- [j, k, r, a', a] → [r, j, k, a', a]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun r _ => ?_
  simp only [fun j k a' a => Hs_mul (fun α => S α k j) (T r (k, a')) (T r (j, a) * G a' a) B
    (hB r (k, a')), fun j k a' a β => Hs_mul (fun γ => S (β + γ) k j) (T r (j, a)) (G a' a) B
    (hB r (j, a)), Finset.mul_sum]
  -- [j, k, a', a, β, β'] → [β, k, a', β', j, a]
  conv_rhs => enter [2, j, 2, k, 2, a']; rw [Finset.sum_comm]
  conv_rhs => enter [2, j, 2, k]; rw [Finset.sum_comm]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_rhs => enter [2, β]; rw [Finset.sum_comm]
  conv_rhs => enter [2, β, 2, k]; rw [Finset.sum_comm]
  conv_rhs => enter [2, β, 2, k, 2, a', 2, j]; rw [Finset.sum_comm]
  conv_rhs => enter [2, β, 2, k, 2, a']; rw [Finset.sum_comm]
  have hq := (posSemidef_iff_dotProduct_mulVec.1 hL).2
    (fun p : B × (Fin m × Fin q) => coeff p.1.1 (T r p.2))
  simp only [dotProduct, mulVec, star_trivial, locMat, of_apply,
    Fintype.sum_prod_type, Finset.mul_sum] at hq
  rw [← Finset.sum_coe_sort B]
  refine le_of_le_of_eq hq (Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun a' _ => ?_)
  rw [← Finset.sum_coe_sort B]
  refine Finset.sum_congr rfl fun β' _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => ?_
  rw [Hs_eq_of_subset _ (G a' a) (suppMat G)
    (fun γ hγ => Finset.mem_biUnion.2 ⟨(a', a), Finset.mem_univ _, hγ⟩), Finset.mul_sum,
    Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [add_assoc]; ring

end RobustPMI.Hierarchy.P213aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.P213aux Matrix in
theorem solution {n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (S : MatSeq (Fin n) (Fin m)) :
    (∀ (d l : ℕ) (T : Matrix (Fin l) (Fin m) (MvPolynomial (Fin n) ℝ)),
      (∀ i j, (T i j).totalDegree ≤ d) → (momentMat d S).PosSemidef → 0 ≤ riesz S (Tᵀ * T)) ∧
    (∀ (d l : ℕ) (T : Matrix (Fin l) (Fin m × Fin q) (MvPolynomial (Fin n) ℝ)),
      (∀ i j, (T i j).totalDegree ≤ d) → (locMat d G S).PosSemidef →
        0 ≤ riesz S (pairM (Tᵀ * T) G)) :=
  ⟨fun d l T hT hM => part1 S d l T hT hM, fun d l T hT hL => part2 G S d l T hT hL⟩
