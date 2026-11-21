-- Prove2me | solution 1 for ProdMomentConc.expect_Lk_le
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:02:24.013187+00:00
-- url     : https://prove2.me/submissions/975620ef-66fe-40c4-bb3c-b9e06ebf69fd

import Mathlib
import Definitions.Def_ProdMomentConc_edgeCount
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_Lk

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

private lemma integral_uniformOn_finset_real
    {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (A : Finset α) (hA : A.Nonempty) (f : α → ℝ) :
    (∫ x, f x ∂(uniformOn (A : Set α))) =
      (∑ x ∈ A, f x) / (A.card : ℝ) := by
  classical
  have hmeasure (x : α) :
      ((uniformOn (A : Set α)) {x}).toReal =
        if x ∈ A then (A.card : ℝ)⁻¹ else 0 := by
    rw [show ({x} : Set α) = (({x} : Finset α) : Set α) by
      ext y
      simp]
    rw [uniformOn_apply_finset, Finset.inter_singleton]
    by_cases hx : x ∈ A
    · simp [hx, ENNReal.toReal_div, ENNReal.toReal_natCast, div_eq_mul_inv]
    · simp [hx]
  haveI : IsProbabilityMeasure (uniformOn (A : Set α)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  rw [integral_fintype (f := f) (μ := uniformOn (A : Set α)) Integrable.of_finite]
  simp only [measureReal_def, hmeasure, smul_eq_mul, ite_mul, zero_mul]
  have hsum :
      (∑ x : α, if x ∈ A then (A.card : ℝ)⁻¹ * f x else 0) =
        ∑ x ∈ A, (A.card : ℝ)⁻¹ * f x := by
    let g : α → ℝ := fun x =>
      if x ∈ A then (A.card : ℝ)⁻¹ * f x else 0
    have hsub : (∑ x ∈ A, g x) = ∑ x ∈ Finset.univ, g x := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro x _hx hxA
      simp [g, hxA]
    calc
      _ = ∑ x ∈ Finset.univ, g x := by rfl
      _ = ∑ x ∈ A, g x := hsub.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [g, hx]
  rw [hsum, ← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

private lemma card_filter_powersetCard_succ (n k : ℕ) (i : Fin (n + 1)) :
    (((Finset.univ : Finset (Fin (n + 1))).powersetCard (k + 1)).filter
      (fun S => i ∈ S)).card = n.choose k := by
  classical
  let U : Finset (Fin (n + 1)) := Finset.univ.erase i
  have hiU : i ∉ U := by
    simp [U]
  have h_avoid {T : Finset (Fin (n + 1))}
      (hT : T ∈ U.powersetCard k) : i ∉ T := by
    intro hiT
    have hsub := (Finset.mem_powersetCard.mp hT).1
    exact hiU (hsub hiT)
  have hfilter :
      ((Finset.univ : Finset (Fin (n + 1))).powersetCard (k + 1)).filter
          (fun S => i ∈ S) =
        (U.powersetCard k).image (fun T => insert i T) := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_filter.mp hS with ⟨hSpow, hiS⟩
      have hcardS : S.card = k + 1 :=
        (Finset.mem_powersetCard.mp hSpow).2
      refine Finset.mem_image.mpr ⟨S.erase i, ?_, ?_⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro x hx
          have hx' := Finset.mem_erase.mp hx
          simp only [U, Finset.mem_erase, Finset.mem_univ, and_true]
          exact hx'.1
        · rw [Finset.card_erase_of_mem hiS, hcardS]
          simp
      · exact Finset.insert_erase hiS
    · intro hS
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      have hT' := Finset.mem_powersetCard.mp hT
      have hiT : i ∉ T := h_avoid hT
      refine Finset.mem_filter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hiT, hT'.2]
  have hinj :
      Set.InjOn (fun T : Finset (Fin (n + 1)) => insert i T)
        (U.powersetCard k : Set (Finset (Fin (n + 1)))) := by
    intro T hT V hV hEq
    have hiT : i ∉ T := h_avoid (by simpa using hT)
    have hiV : i ∉ V := h_avoid (by simpa using hV)
    have h := congrArg (fun W : Finset (Fin (n + 1)) => W.erase i) hEq
    simpa [hiT, hiV] using h
  rw [hfilter]
  calc
    ((U.powersetCard k).image (fun T => insert i T)).card =
        (U.powersetCard k).card := Finset.card_image_iff.mpr hinj
    _ = U.card.choose k := by rw [Finset.card_powersetCard]
    _ = n.choose k := by simp [U]

theorem _root_.solution {m n : ℕ} (P : Fin n → Finset (Fin m)) (k : ℕ) (hkn : k ≤ n) :
    ∫ S, (Lk P S : ℝ) ∂(kSubsetLaw n k) ≤ dR P * (k : ℝ) := by
  classical
  cases k with
  | zero =>
      have hlaw : kSubsetLaw n 0 =
          uniformOn ((({∅} : Finset (Finset (Fin n))) :
            Set (Finset (Fin n)))) := by
        unfold kSubsetLaw
        apply congrArg uniformOn
        ext S
        simp
      rw [hlaw, integral_uniformOn_finset_real
        ({∅} : Finset (Finset (Fin n))) (by simp)
        (fun S => (Lk P S : ℝ))]
      simp [Lk]
  | succ k =>
      cases n with
      | zero => omega
      | succ n =>
          let A : Finset (Finset (Fin (n + 1))) :=
            Finset.univ.powersetCard (k + 1)
          have hAcard : A.card = (n + 1).choose (k + 1) := by
            simp [A, Finset.card_powersetCard]
          have hCnat : 0 < (n + 1).choose (k + 1) :=
            Nat.choose_pos hkn
          have hApos : 0 < A.card := by
            simpa [hAcard] using hCnat
          have hA : A.Nonempty := Finset.card_pos.mp hApos
          have hlaw : kSubsetLaw (n + 1) (k + 1) =
              uniformOn (A : Set (Finset (Fin (n + 1)))) := by
            unfold kSubsetLaw
            apply congrArg uniformOn
            ext S
            simp [A, Finset.mem_powersetCard]
          have hcount (i : Fin (n + 1)) :
              (A.filter (fun S => i ∈ S)).card = n.choose k := by
            simpa [A] using card_filter_powersetCard_succ n k i
          let d : Fin (n + 1) → ℝ := fun i => (P i).card
          have hpoint (S : Finset (Fin (n + 1))) :
              (Lk P S : ℝ) ≤ ∑ i ∈ S, d i := by
            simp only [Lk, d]
            exact_mod_cast (Finset.card_biUnion_le (s := S) (t := P))
          have hinner (S : Finset (Fin (n + 1))) :
              (∑ i ∈ S, d i) =
                ∑ i : Fin (n + 1), if i ∈ S then d i else 0 := by
            let g : Fin (n + 1) → ℝ := fun i => if i ∈ S then d i else 0
            have hsub : (∑ i ∈ S, g i) = ∑ i ∈ Finset.univ, g i := by
              apply Finset.sum_subset (Finset.subset_univ S)
              intro i _hi hiS
              simp [g, hiS]
            calc
              (∑ i ∈ S, d i) = ∑ i ∈ S, g i := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [g, hi]
              _ = ∑ i ∈ Finset.univ, g i := hsub
              _ = _ := by rfl
          have hterm (i : Fin (n + 1)) :
              (∑ S ∈ A, if i ∈ S then d i else 0) =
                (n.choose k : ℝ) * d i := by
            calc
              (∑ S ∈ A, if i ∈ S then d i else 0) =
                  ∑ S ∈ A.filter (fun S => i ∈ S), d i := by
                    rw [Finset.sum_filter]
              _ = (n.choose k : ℝ) * d i := by
                    simp [hcount i, nsmul_eq_mul]
          have hdouble :
              (∑ S ∈ A, ∑ i ∈ S, d i) =
                (n.choose k : ℝ) * (edgeCount P : ℝ) := by
            calc
              (∑ S ∈ A, ∑ i ∈ S, d i) =
                  ∑ S ∈ A, ∑ i : Fin (n + 1),
                    if i ∈ S then d i else 0 := by
                apply Finset.sum_congr rfl
                intro S _hS
                exact hinner S
              _ = ∑ i : Fin (n + 1), ∑ S ∈ A,
                    if i ∈ S then d i else 0 := by
                exact Finset.sum_comm
              _ = ∑ i : Fin (n + 1), (n.choose k : ℝ) * d i := by
                apply Finset.sum_congr rfl
                intro i _hi
                exact hterm i
              _ = (n.choose k : ℝ) * ∑ i : Fin (n + 1), d i := by
                rw [Finset.mul_sum]
              _ = (n.choose k : ℝ) * (edgeCount P : ℝ) := by
                simp only [d, edgeCount, Nat.cast_sum]
          have hsumub :
              (∑ S ∈ A, (Lk P S : ℝ)) ≤
                (n.choose k : ℝ) * (edgeCount P : ℝ) := by
            calc
              (∑ S ∈ A, (Lk P S : ℝ)) ≤
                  ∑ S ∈ A, ∑ i ∈ S, d i := by
                exact Finset.sum_le_sum fun S _hS => hpoint S
              _ = (n.choose k : ℝ) * (edgeCount P : ℝ) := hdouble
          have hC : ((((n + 1).choose (k + 1) : ℕ) : ℝ)) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hCnat)
          have hN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
            positivity
          have hchoose :
              (((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ)) =
                ((((n + 1).choose (k + 1) : ℕ) : ℝ) *
                  ((k + 1 : ℕ) : ℝ)) := by
            exact_mod_cast (Nat.add_one_mul_choose_eq n k)
          rw [hlaw, integral_uniformOn_finset_real A hA
            (fun S => (Lk P S : ℝ))]
          calc
            (∑ S ∈ A, (Lk P S : ℝ)) / (A.card : ℝ) ≤
                ((n.choose k : ℝ) * (edgeCount P : ℝ)) / (A.card : ℝ) :=
              div_le_div_of_nonneg_right hsumub (by positivity)
            _ = dR P * ((k + 1 : ℕ) : ℝ) := by
              rw [dR, hAcard, div_mul_eq_mul_div₀]
              rw [div_eq_div_iff hC hN]
              linear_combination (edgeCount P : ℝ) * hchoose

end ProdMomentConc
