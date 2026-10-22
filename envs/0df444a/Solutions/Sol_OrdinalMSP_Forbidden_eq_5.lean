-- Prove2me | solution 1 for OrdinalMSP.Forbidden.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:12:08.723703+00:00
-- url     : https://prove2.me/submissions/3d7b4ae1-3a76-49f9-aecb-35a972fa223c

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting
import Theorems.Thm_OrdinalMSP_Forbidden_conditional_product_bound

open OrdinalMSP.Forbidden

namespace OMSPeq5

variable {R : Type*} [Fintype R] [DecidableEq R]

lemma mem_arrived (σ : ArrivalOrder R) (t : ℕ) (x : R) :
    x ∈ arrived σ t ↔ ((σ.symm x : ℕ) < t) := by
  unfold arrived
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa using hi
  · intro h
    exact ⟨σ.symm x, by simpa using h, by simp⟩

lemma card_arrived (σ : ArrivalOrder R) (t : ℕ) (ht : t ≤ Fintype.card R) :
    (arrived σ t).card = t := by
  unfold arrived
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_filter_val_lt]
  omega

/-- All positions are equally likely for `r`: `n · #{σ : σ⁻¹ r = i} = n!`. -/
lemma card_pos_eq (r : R) (i : Fin (Fintype.card R)) :
    (Fintype.card R) * (Finset.univ.filter (fun σ : ArrivalOrder R => σ.symm r = i)).card =
      (Fintype.card R).factorial := by
  have heq : ∀ i i' : Fin (Fintype.card R),
      (Finset.univ.filter (fun σ : ArrivalOrder R => σ.symm r = i)).card =
      (Finset.univ.filter (fun σ : ArrivalOrder R => σ.symm r = i')).card := by
    intro i i'
    refine Finset.card_nbij' (fun σ => (Equiv.swap i i').trans σ)
      (fun σ => (Equiv.swap i i').trans σ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
      simp [Equiv.symm_trans_apply, hσ]
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
      simp [Equiv.symm_trans_apply, hσ]
    · intro σ _; ext j; simp
    · intro σ _; ext j; simp
  have htot : (Finset.univ : Finset (ArrivalOrder R)).card =
      ∑ j : Fin (Fintype.card R),
        (Finset.univ.filter (fun σ : ArrivalOrder R => σ.symm r = j)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : ArrivalOrder R => σ.symm r)
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  rw [Finset.sum_congr rfl (fun j _ => heq j i), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_equiv (Fintype.equivFin R).symm,
    Fintype.card_fin] at htot
  exact htot.symm

end OMSPeq5

open OMSPeq5 in
theorem solution {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (k : ℕ) (ALG : ArrivalOrder R → ℕ → Finset R)
    (hALG : HasForbiddenSets M k ALG) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : R) (hr : r ∈ opt M Finset.univ) :
    ∑ s ∈ Finset.range (Fintype.card R + 1),
        ((Fintype.card R).choose s : ℝ) * p ^ s * (1 - p) ^ (Fintype.card R - s) *
          ((1 / (Fintype.card R : ℝ)) *
            ∑ t ∈ Finset.Icc (s + 1) (Fintype.card R),
              ∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ)))
      ≤ selProb ALG p r := by
  unfold selProb
  set n := Fintype.card R with hn
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.mpr ⟨r⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  apply Finset.sum_le_sum
  intro s hs
  apply mul_le_mul_of_nonneg_left _ (by
    have : 0 ≤ 1 - p := by linarith
    positivity)
  set A := Finset.univ.filter (fun σ : ArrivalOrder R => r ∈ ALG σ s) with hA
  -- D t = #{σ : position of r is t-1}
  have hD : ∀ t ∈ Finset.Icc (s + 1) n,
      (n : ℝ) * ((Finset.univ.filter (fun σ : ArrivalOrder R => (σ.symm r : ℕ) = t - 1)).card : ℝ)
        = n.factorial := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hlt : t - 1 < n := by omega
    have := card_pos_eq r (⟨t - 1, hlt⟩ : Fin n)
    have hc : (Finset.univ.filter (fun σ : ArrivalOrder R => (σ.symm r : ℕ) = t - 1)) =
        Finset.univ.filter (fun σ : ArrivalOrder R => σ.symm r = ⟨t - 1, hlt⟩) := by
      apply Finset.filter_congr; intro σ _
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    rw [hc]; exact_mod_cast this
  -- per-t bound
  have hT : ∀ t ∈ Finset.Icc (s + 1) n,
      (∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ))) *
        ((Finset.univ.filter (fun σ : ArrivalOrder R => (σ.symm r : ℕ) = t - 1)).card : ℝ) ≤
      ((Finset.univ.filter (fun σ : ArrivalOrder R =>
          (σ.symm r : ℕ) = t - 1 ∧ r ∈ ALG σ s)).card : ℝ) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hP : (∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ))) =
        ∏ j ∈ Finset.Ico (s + 1) t, max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_Ico] at hj
      have : (j : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        linarith
      rw [sub_div, div_self this]
    rw [hP]
    set P := ∏ j ∈ Finset.Ico (s + 1) t, max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ))
    have hmapsY : ∀ B : Finset (ArrivalOrder R),
        ((B : Set (ArrivalOrder R))).MapsTo (fun σ => arrived σ t)
          ((Finset.univ.powersetCard t : Finset (Finset R)) : Set (Finset R)) := by
      intro B σ _
      simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact card_arrived σ t ht.2
    rw [Finset.card_eq_sum_card_fiberwise (hmapsY _),
      Finset.card_eq_sum_card_fiberwise (hmapsY _)]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Y hY
    rw [Finset.mem_powersetCard] at hY
    rw [Finset.filter_filter, Finset.filter_filter]
    by_cases hrY : r ∈ Y
    · have := conditional_product_bound M hE k ALG hALG r hr s t ht.1 ht.2 Y hY.2 hrY
      have e : Finset.univ.filter (fun σ : ArrivalOrder R =>
          ((σ.symm r : ℕ) = t - 1 ∧ r ∈ ALG σ s) ∧ arrived σ t = Y) =
          Finset.univ.filter (fun σ : ArrivalOrder R =>
          ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y) ∧ r ∈ ALG σ s) :=
        Finset.filter_congr (fun σ _ => by tauto)
      rw [e]; exact this
    · have hempty : Finset.univ.filter (fun σ : ArrivalOrder R =>
          (σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y) = ∅ := by
        apply Finset.filter_false_of_mem
        rintro σ _ ⟨h1, h2⟩
        apply hrY
        rw [← h2, mem_arrived]; omega
      rw [hempty]; simp
  -- sum over t
  have hsumA : ∑ t ∈ Finset.Icc (s + 1) n,
      ((Finset.univ.filter (fun σ : ArrivalOrder R =>
          (σ.symm r : ℕ) = t - 1 ∧ r ∈ ALG σ s)).card : ℝ) ≤ (A.card : ℝ) := by
    have hsub : A.filter (fun σ => (σ.symm r : ℕ) + 1 ∈ Finset.Icc (s + 1) n) ⊆ A :=
      Finset.filter_subset _ _
    have h1 := Finset.card_eq_sum_card_fiberwise
      (s := A.filter (fun σ => (σ.symm r : ℕ) + 1 ∈ Finset.Icc (s + 1) n))
      (t := Finset.Icc (s + 1) n) (f := fun σ => (σ.symm r : ℕ) + 1)
      (fun σ hσ => (Finset.mem_filter.1 hσ).2)
    have h2 : ∀ t ∈ Finset.Icc (s + 1) n,
        (A.filter (fun σ => (σ.symm r : ℕ) + 1 ∈ Finset.Icc (s + 1) n)).filter
          (fun σ => (σ.symm r : ℕ) + 1 = t) =
        Finset.univ.filter (fun σ : ArrivalOrder R => (σ.symm r : ℕ) = t - 1 ∧ r ∈ ALG σ s) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      ext σ
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨by omega, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2, by omega, by omega⟩, by omega⟩
    rw [Finset.sum_congr rfl (fun t ht => by rw [h2 t ht])] at h1
    have h3 := Finset.card_le_card hsub
    rw [h1] at h3
    exact_mod_cast h3
  -- combine
  have : (1 / (n : ℝ)) * ∑ t ∈ Finset.Icc (s + 1) n,
      ∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ)) =
      (∑ t ∈ Finset.Icc (s + 1) n,
        (∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ))) *
        ((Finset.univ.filter (fun σ : ArrivalOrder R => (σ.symm r : ℕ) = t - 1)).card : ℝ)) /
          (n.factorial : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t ht
    have := hD t ht
    field_simp
    rw [← this]; ring
  rw [this]
  apply div_le_div_of_nonneg_right _ hfac.le
  exact (Finset.sum_le_sum hT).trans hsumA
