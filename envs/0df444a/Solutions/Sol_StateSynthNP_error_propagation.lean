-- Prove2me | solution 1 for StateSynthNP.error_propagation
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T06:40:20.281842+00:00
-- url     : https://prove2.me/submissions/9ddfe071-822e-4698-8cb6-9eaca0e17f5a

import Mathlib

set_option autoImplicit false

namespace StateSynthNP

lemma ep_part2 {ι : Type} [Fintype ι] (k : ℕ)
    (U V : Fin k → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))
    (hU : ∀ i, U i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))
    (hV : ∀ i, V i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))
    (v w : EuclideanSpace ℂ ι) :
    ‖((List.ofFn U).reverse.prod) v - ((List.ofFn V).reverse.prod) w‖ ≤
      ‖v - w‖ + (∑ i, ‖U i - V i‖) * ‖w‖ := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 := ih (fun i => U i.castSucc) (fun i => V i.castSucc) (fun i => hU _) (fun i => hV _)
    rw [List.ofFn_succ', List.ofFn_succ', List.concat_eq_append, List.concat_eq_append,
      List.reverse_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.prod_cons]
    rw [Fin.sum_univ_castSucc]
    set P := (List.ofFn fun i : Fin n => U i.castSucc).reverse.prod
    set Q := (List.ofFn fun i : Fin n => V i.castSucc).reverse.prod
    have hQ : Q ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := by
      apply Submonoid.list_prod_mem
      intro x hx
      simp only [List.mem_reverse, List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hV _
    have e1 : ‖(U (Fin.last n)) (P v - Q w)‖ = ‖P v - Q w‖ :=
      ContinuousLinearMap.norm_map_of_mem_unitary (hU _) _
    have e2 : ‖Q w‖ = ‖w‖ := ContinuousLinearMap.norm_map_of_mem_unitary hQ _
    have e3 : ‖(U (Fin.last n) - V (Fin.last n)) (Q w)‖ ≤ ‖U (Fin.last n) - V (Fin.last n)‖ * ‖w‖ := by
      rw [← e2]; exact ContinuousLinearMap.le_opNorm _ _
    have : (U (Fin.last n)) (P v) - (V (Fin.last n)) (Q w)
        = (U (Fin.last n)) (P v - Q w) + (U (Fin.last n) - V (Fin.last n)) (Q w) := by
      simp [map_sub, sub_apply]
    simp only [ContinuousLinearMap.mul_apply]
    rw [this]
    calc _ ≤ ‖(U (Fin.last n)) (P v - Q w)‖ + ‖(U (Fin.last n) - V (Fin.last n)) (Q w)‖ :=
          norm_add_le _ _
      _ ≤ _ := by rw [e1]; nlinarith

theorem error_propagation {ι : Type} [Fintype ι] :
    (∀ (a b : EuclideanSpace ℂ ι) (η : ℝ), (∀ i, ‖a i - b i‖ ≤ η * ‖b i‖) → ‖a - b‖ ≤ η * ‖b‖) ∧
    (∀ (k : ℕ) (U V : Fin k → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)),
      (∀ i, U i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) →
      (∀ i, V i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) →
      ∀ v w : EuclideanSpace ℂ ι,
        ‖((List.ofFn U).reverse.prod) v - ((List.ofFn V).reverse.prod) w‖ ≤
          ‖v - w‖ + (∑ i, ‖U i - V i‖) * ‖w‖) ∧
    (∀ (u v : EuclideanSpace ℂ ι) (δ : ℝ), ‖u‖ = 1 → ‖v‖ = 1 → ‖u - v‖ ≤ δ →
      1 - δ ^ 2 ≤ ‖inner ℂ u v‖ ^ 2) := by
  refine ⟨?_, fun k U V hU hV v w => ep_part2 k U V hU hV v w, ?_⟩
  · intro a b η h
    have hη : 0 ≤ η ∨ b = 0 := by
      by_cases hb : b = 0
      · exact Or.inr hb
      · left
        by_contra hneg
        push_neg at hneg
        apply hb
        ext i
        have := h i
        have h0 : 0 ≤ ‖b i‖ := norm_nonneg _
        have : ‖b i‖ = 0 := by nlinarith [norm_nonneg (a i - b i)]
        simpa using this
    rcases hη with hη | hb
    · have hsq : ‖a - b‖ ^ 2 ≤ (η * ‖b‖) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have := h i
        simp only [PiLp.sub_apply]
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq
    · subst hb
      have := h
      have ha : a = 0 := by
        ext i
        have := h i
        simp at this
        simpa using this
      subst ha; simp
  · intro u v δ hu hv h
    have hδ : 0 ≤ δ := le_trans (norm_nonneg _) h
    have hs : ‖u - v‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [norm_sub_sq (𝕜 := ℂ), hu, hv] at hs
    have hs' : 1 ^ 2 - 2 * (inner ℂ u v).re + 1 ^ 2 ≤ δ ^ 2 := by simpa using hs
    have hre : (inner ℂ u v).re ≤ ‖inner ℂ u v‖ := Complex.re_le_norm _
    have hn := norm_nonneg (inner ℂ u v)
    by_cases hd : δ ^ 2 ≤ 2
    · have : 1 - δ ^ 2 / 2 ≤ ‖inner ℂ u v‖ := by nlinarith
      have h2 := pow_le_pow_left₀ (by linarith) this 2
      nlinarith [sq_nonneg (δ ^ 2)]
    · nlinarith [sq_nonneg ‖inner ℂ u v‖]

end StateSynthNP

theorem solution {ι : Type} [Fintype ι] :
    (∀ (a b : EuclideanSpace ℂ ι) (η : ℝ), (∀ i, ‖a i - b i‖ ≤ η * ‖b i‖) → ‖a - b‖ ≤ η * ‖b‖) ∧
    (∀ (k : ℕ) (U V : Fin k → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)),
      (∀ i, U i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) →
      (∀ i, V i ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) →
      ∀ v w : EuclideanSpace ℂ ι,
        ‖((List.ofFn U).reverse.prod) v - ((List.ofFn V).reverse.prod) w‖ ≤
          ‖v - w‖ + (∑ i, ‖U i - V i‖) * ‖w‖) ∧
    (∀ (u v : EuclideanSpace ℂ ι) (δ : ℝ), ‖u‖ = 1 → ‖v‖ = 1 → ‖u - v‖ ≤ δ →
      1 - δ ^ 2 ≤ ‖inner ℂ u v‖ ^ 2) := StateSynthNP.error_propagation
