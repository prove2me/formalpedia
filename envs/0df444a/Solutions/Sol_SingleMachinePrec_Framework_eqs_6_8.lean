-- Prove2me | solution 1 for SingleMachinePrec.Framework.eqs_6_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:10:57.617177+00:00
-- url     : https://prove2.me/submissions/c11e2407-2093-4e74-bd1a-50a1fd1d899a

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP



namespace SingleMachinePrec.Framework

open Classical

section eqs
variable {N : Type*} [Fintype N] [DecidableEq N]

theorem eq_vw_nonneg (S : Instance N) (u : IncPair S.P) : 0 ≤ vertexWeight S u :=
  mul_nonneg (S.p_nonneg _) (S.w_nonneg _)

theorem eq_weight_nonneg (S : Instance N) (C : Finset (IncPair S.P)) : 0 ≤ weight S C :=
  Finset.sum_nonneg (fun u _ => eq_vw_nonneg S u)

theorem eq_weight_rounded (S : Instance N) (x : IncPair S.P → ℝ) (L : LinearExtension S.P) :
    weight S (roundedCover x L) =
      weight S (levelSet x 1) + (weight S (levelSet x (1 / 2)) - weight S (reversedHalf x L)) := by
  unfold roundedCover weight
  have hd : Disjoint (levelSet x 1) (levelSet x (1 / 2) \ reversedHalf x L) := by
    rw [Finset.disjoint_left]
    intro u hu hu2
    have h1 : x u = 1 := by simpa [levelSet] using hu
    have h2 : x u = 1 / 2 := by
      have := (Finset.mem_sdiff.1 hu2).1
      simpa [levelSet] using this
    rw [h1] at h2; norm_num at h2
  rw [Finset.sum_union hd]
  have hs : reversedHalf x L ⊆ levelSet x (1 / 2) := Finset.filter_subset _ _
  have := Finset.sum_sdiff (f := vertexWeight S) hs
  linarith

theorem eq_sum_rev (S : Instance N) (k t : ℕ) (L : Fin t → LinearExtension S.P)
    (hL : IsKFoldRealizer S.P k t L) (x : IncPair S.P → ℝ) :
    (k : ℝ) * weight S (levelSet x (1 / 2)) ≤ ∑ i, weight S (reversedHalf x (L i)) := by
  unfold weight reversedHalf
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hc : (k : ℝ) ≤ ((Finset.univ.filter (fun i => (L i).Reverses u)).card : ℝ) := by
    exact_mod_cast (hL.2 u)
  have : ∑ i, (if (L i).Reverses u then vertexWeight S u else 0) =
      ((Finset.univ.filter (fun i => (L i).Reverses u)).card : ℝ) * vertexWeight S u := by
    rw [← Finset.sum_filter]
    simp
  rw [this]
  exact mul_le_mul_of_nonneg_right hc (eq_vw_nonneg S u)

theorem eq_csLP_value (S : Instance N) (x : IncPair S.P → ℝ) (hhalf : IsHalfIntegral x) :
    csLPValue S x = weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2)) := by
  unfold csLPValue weight levelSet
  rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rcases hhalf u with h | h | h <;> rw [h] <;> norm_num <;> ring

theorem eq_lp_le_opt (S : Instance N) (x : IncPair S.P → ℝ) (hx : IsCSLPOptimal S x)
    (hhalf : IsHalfIntegral x) :
    weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2)) ≤ OPT S := by
  rw [← eq_csLP_value S x hhalf]
  unfold OPT
  obtain ⟨C, hC, hCeq⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.univ.filter
      (fun C : Finset (IncPair S.P) => (vertexCoverGraph S.P).IsVertexCover (C : Set _)))
    ⟨Finset.univ, by simp [SimpleGraph.isVertexCover_univ]⟩ (weight S)
  rw [hCeq]
  have hcov : (vertexCoverGraph S.P).IsVertexCover (C : Set _) := (Finset.mem_filter.1 hC).2
  have hfeas : IsCSLPFeasible S (fun u => if u ∈ C then 1 else 0) := by
    refine ⟨fun u => ?_, fun u v huv => ?_⟩
    · by_cases h : u ∈ C <;> simp [h]
    · rcases hcov huv with h | h
      · have : u ∈ C := h
        by_cases hv : v ∈ C <;> simp [this, hv]
      · have : v ∈ C := h
        by_cases hu : u ∈ C <;> simp [this, hu]
  have := hx.2 _ hfeas
  refine this.trans (le_of_eq ?_)
  unfold csLPValue weight
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

theorem eq_two_k_le_t (S : Instance N) (hP : ¬ IsLinearOrder N S.P) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L) : 2 * k ≤ t := by
  have hex : ∃ a b, ¬ S.P a b ∧ ¬ S.P b a := by
    by_contra hcon
    push_neg at hcon
    apply hP
    haveI := S.isPartialOrder
    exact { total := fun a b => by
              by_contra hh
              push_neg at hh
              obtain ⟨h1, h2⟩ := hh
              exact h2 (hcon a b h1) }
  obtain ⟨a, b, hab, hba⟩ := hex
  let u : IncPair S.P := ⟨(a, b), ⟨hab, hba⟩⟩
  let u' : IncPair S.P := ⟨(b, a), ⟨hba, hab⟩⟩
  have h1 := hL.2 u
  have h2 := hL.2 u'
  have hdisj : Disjoint (Finset.univ.filter (fun i => (L i).Reverses u))
      (Finset.univ.filter (fun i => (L i).Reverses u')) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    have e1 := (Finset.mem_filter.1 hi).2
    have e2 := (Finset.mem_filter.1 hi').2
    haveI := (L i).isLinearOrder
    obtain ⟨e1, e1'⟩ := e1
    obtain ⟨e2, e2'⟩ := e2
    simp only [u, u'] at e1 e1' e2 e2'
    exact e1' (antisymm_of (L i).le e1 e2)
  have := Finset.card_le_univ (Finset.univ.filter (fun i => (L i).Reverses u) ∪
      Finset.univ.filter (fun i => (L i).Reverses u'))
  rw [Finset.card_union_of_disjoint hdisj] at this
  simp at this
  omega

theorem eqs_6_8_core (S : Instance N)
    (hP : ¬ IsLinearOrder N S.P) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) (hx : IsCSLPOptimal S x) (hhalf : IsHalfIntegral x) :
    (1 / (t : ℝ)) * ∑ i, weight S (roundedCover x (L i)) ≤
        weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ∧
      weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ≤
        2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ∧
      2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ≤
        (2 - 2 / ((t : ℝ) / k)) * OPT S := by
  have ht : 0 < t := hL.1
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have h2k : (2 * k : ℝ) ≤ t := by exact_mod_cast eq_two_k_le_t S hP k t L hL
  have hc : (k : ℝ) / t ≤ 1 / 2 := by
    rw [div_le_iff₀ htR]; linarith
  have hc0 : (0 : ℝ) ≤ (k : ℝ) / t := by positivity
  have hW1 := eq_weight_nonneg S (levelSet x 1)
  have hWh := eq_weight_nonneg S (levelSet x (1 / 2))
  have hrev := eq_sum_rev S k t L hL x
  have hsum : ∑ i, weight S (roundedCover x (L i)) =
      t * (weight S (levelSet x 1) + weight S (levelSet x (1 / 2))) -
        ∑ i, weight S (reversedHalf x (L i)) := by
    simp_rw [eq_weight_rounded]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
    ring
  have hopt := eq_lp_le_opt S x hx hhalf
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum]
    have : (1 / (t : ℝ)) * (t * (weight S (levelSet x 1) + weight S (levelSet x (1 / 2))) -
        ∑ i, weight S (reversedHalf x (L i))) =
        weight S (levelSet x 1) + weight S (levelSet x (1 / 2)) -
          (1 / (t : ℝ)) * ∑ i, weight S (reversedHalf x (L i)) := by
      field_simp
    rw [this]
    have h3 : (k : ℝ) / t * weight S (levelSet x (1 / 2)) ≤
        (1 / (t : ℝ)) * ∑ i, weight S (reversedHalf x (L i)) := by
      have := mul_le_mul_of_nonneg_left hrev (by positivity : (0 : ℝ) ≤ 1 / (t : ℝ))
      calc (k : ℝ) / t * weight S (levelSet x (1 / 2))
          = 1 / (t : ℝ) * ((k : ℝ) * weight S (levelSet x (1 / 2))) := by ring
        _ ≤ _ := this
    nlinarith
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * ((k : ℝ) / t)) hW1]
  · have e : 2 / ((t : ℝ) / k) = 2 * ((k : ℝ) / t) := by
      rw [div_div_eq_mul_div]; ring
    rw [e]
    have : 2 * (1 - (k : ℝ) / t) = 2 - 2 * ((k : ℝ) / t) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hopt (by linarith)

end eqs

end SingleMachinePrec.Framework

open SingleMachinePrec.Framework


theorem solution {N : Type*} [Fintype N] [DecidableEq N] (S : Instance N)
    (hP : ¬ IsLinearOrder N S.P) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) (hx : IsCSLPOptimal S x) (hhalf : IsHalfIntegral x) :
    (1 / (t : ℝ)) * ∑ i, weight S (roundedCover x (L i)) ≤
        weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ∧
      weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ≤
        2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ∧
      2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ≤
        (2 - 2 / ((t : ℝ) / k)) * OPT S := by
  exact eqs_6_8_core S hP k t L hL x hx hhalf
