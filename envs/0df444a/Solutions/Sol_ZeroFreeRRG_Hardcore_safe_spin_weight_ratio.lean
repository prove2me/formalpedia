-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.safe_spin_weight_ratio
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:18:20.809288+00:00
-- url     : https://prove2.me/submissions/4c27f581-54f5-4e16-a8b9-1b5059da9bcd

import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_edge_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_has_safe_spin
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_interaction_symmetric
import Theorems.Thm_ZeroFreeRRG_Hardcore_finite_factor_ratio_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_changed_factors_product_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_incident_edge_reps_card_le_degree
import Mathlib
set_option autoImplicit false
open AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) (d : ℕ) :
    ∃ (a₀ : m.Spin) (K : ℝ), 0 < K ∧
      ∀ (n : ℕ) (M : Matching n d) (σ : Fin n → m.Spin) (v : Fin n),
        weight m t M σ ≤ K * weight m t M (Function.update σ v a₀) := by
  classical
  have hπ := (model_pi_positive_simplex m hm t ht).1
  have hJ : ∀ a b, 0 ≤ m.M t a b := by
    intro a b
    exact div_nonneg (model_edge_nonnegative m hm t ht a b) (le_of_lt (mul_pos (hπ a) (hπ b)))
  obtain ⟨a₀, ha₀⟩ := model_has_safe_spin m hm t ht
  obtain ⟨C,hC,hπrat,hJrat⟩ := finite_factor_ratio_bound (m.pi t) (m.M t) hπ
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  refine ⟨a₀,C^(d+1),pow_pos (lt_of_lt_of_le zero_lt_one hC) _,?_⟩
  intro n M σ v
  let σ' := Function.update σ v a₀
  let E := (edgeReps M).filter (fun x => x.1=v ∨ (M.1 x).1=v)
  have hv : (∏ u, m.pi t (σ u)) ≤ C * ∏ u, m.pi t (σ' u) := by
    have h := changed_factors_product_bound (Finset.univ : Finset (Fin n)) {v}
      (fun u => m.pi t (σ u)) (fun u => m.pi t (σ' u)) C
      (by intro u hu; exact le_of_lt (hπ _))
      (by intro u hu huv; exact hπrat _ _)
      (by
        intro u hu huv
        have huv' : u ≠ v := by simpa using huv
        simp [σ', huv'])
    have hF : (Finset.univ : Finset (Fin n)).filter (· ∈ ({v} : Finset (Fin n))) = {v} := Finset.filter_univ_mem _
    rw [hF, Finset.card_singleton, pow_one] at h
    exact h
  have he : (∏ x ∈ edgeReps M, m.M t (σ x.1) (σ (M.1 x).1)) ≤
      C ^ E.card * ∏ x ∈ edgeReps M, m.M t (σ' x.1) (σ' (M.1 x).1) := by
    have h := changed_factors_product_bound (edgeReps M) E
      (fun x => m.M t (σ x.1) (σ (M.1 x).1))
      (fun x => m.M t (σ' x.1) (σ' (M.1 x).1)) C
      (by intro x hx; exact hJ _ _)
      (by
        intro x hx hxE
        have hx' := (Finset.mem_filter.mp hxE).2
        apply hJrat
        rcases hx' with hleft | hright
        · simpa [σ', hleft] using ha₀ (σ' (M.1 x).1)
        · rw [model_interaction_symmetric m t]
          simpa [σ', hright] using ha₀ (σ' x.1))
      (by
        intro x hx hxE
        have hh : ¬ (x.1=v ∨ (M.1 x).1=v) := by simpa [E, hx] using hxE
        simp only [not_or] at hh
        simp [σ',hh.1,hh.2])
    have hF : (edgeReps M).filter (· ∈ E) = E := by
      rw [Finset.filter_mem_eq_inter]
      exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hF] at h
    exact h
  have hcard : E.card ≤ d := incident_edge_reps_card_le_degree d n M v
  have hpow : C ^ E.card ≤ C ^ d := pow_le_pow_right₀ hC hcard
  have hV0 : 0 ≤ ∏ u, m.pi t (σ' u) := Finset.prod_nonneg (by intro i hi; exact le_of_lt (hπ _))
  have hE0 : 0 ≤ ∏ x ∈ edgeReps M, m.M t (σ' x.1) (σ' (M.1 x).1) :=
    Finset.prod_nonneg (by intro x hx; exact hJ _ _)
  have hEold0 : 0 ≤ ∏ x ∈ edgeReps M, m.M t (σ x.1) (σ (M.1 x).1) :=
    Finset.prod_nonneg (by intro x hx; exact hJ _ _)
  unfold weight
  calc
    (∏ u, m.pi t (σ u)) * (∏ x ∈ edgeReps M, m.M t (σ x.1) (σ (M.1 x).1)) ≤
        (C * ∏ u, m.pi t (σ' u)) *
          (C ^ E.card * ∏ x ∈ edgeReps M, m.M t (σ' x.1) (σ' (M.1 x).1)) :=
      mul_le_mul hv he hEold0 (mul_nonneg hC0 hV0)
    _ ≤ (C * ∏ u, m.pi t (σ' u)) *
          (C ^ d * ∏ x ∈ edgeReps M, m.M t (σ' x.1) (σ' (M.1 x).1)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hE0) (mul_nonneg hC0 hV0)
    _ = C ^ (d+1) * ((∏ u, m.pi t (σ' u)) *
          ∏ x ∈ edgeReps M, m.M t (σ' x.1) (σ' (M.1 x).1)) := by rw [pow_succ]; ring
