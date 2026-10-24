-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.chernoff_over_S
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T00:04:36.73499+00:00
-- url     : https://prove2.me/submissions/eb758cbe-65ba-44b0-8537-4a45a8e1a189

import Mathlib
import Theorems.Thm_ObfImpossibility_PseudoOracle_chernoff_count_T

open ObfImpossibility.PseudoOracle Filter
open scoped BigOperators

namespace WentaoSampleConcentration

private noncomputable def val (b : Bool) : ℝ := if b then 1 else 0

private lemma average_sum {α : Type} (U : Finset α) (f : α → Bool) :
    avg U f = (∑ x ∈ U, val (f x)) / U.card := by
  unfold avg
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

private lemma average_not {α : Type} (U : Finset α) (hU : 0 < U.card) (f : α → Bool) :
    avg U (fun x => !f x) = 1 - avg U f := by
  have hb (b : Bool) : val (!b) = 1 - val b := by cases b <;> simp [val]
  rw [average_sum, average_sum]
  simp_rw [hb, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hn : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.ne'
  field_simp

private lemma two_sided {α : Type} [DecidableEq α] (U : Finset α) (hU : 0 < U.card)
    (f : α → Bool) (m : ℕ) (hm : 0 < m) (ε : ℝ) (c : ℝ)
    (hup : ∀ g : α → Bool,
      (((U.powersetCard m).filter fun T => ε < avg T g - avg U g).card : ℝ) ≤
        Real.exp (-(c * (m : ℝ) * ε ^ 2)) * (U.card.choose m : ℝ)) :
    (((U.powersetCard m).filter fun T => ε < |avg T f - avg U f|).card : ℝ) ≤
      2 * Real.exp (-(c * (m : ℝ) * ε ^ 2)) * (U.card.choose m : ℝ) := by
  classical
  have hs : ((U.powersetCard m).filter fun T => ε < |avg T f - avg U f|) ⊆
      ((U.powersetCard m).filter fun T => ε < avg T f - avg U f) ∪
      ((U.powersetCard m).filter fun T => ε < avg T (fun x => !f x) - avg U (fun x => !f x)) := by
    intro T hT
    obtain ⟨hTP, hbad⟩ := Finset.mem_filter.mp hT
    have hcard : T.card = m := (Finset.mem_powersetCard.mp hTP).2
    rcases lt_abs.mp hbad with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hTP, h⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hTP, ?_⟩
      rw [average_not T (by omega) f, average_not U hU f]
      linarith
  calc
    _ ≤ (((((U.powersetCard m).filter fun T => ε < avg T f - avg U f) ∪
        ((U.powersetCard m).filter fun T => ε < avg T (fun x => !f x) -
          avg U (fun x => !f x))).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_le_card hs
    _ ≤ _ := by
      have hc := Finset.card_union_le
        ((U.powersetCard m).filter fun T => ε < avg T f - avg U f)
        ((U.powersetCard m).filter fun T => ε < avg T (fun x => !f x) - avg U (fun x => !f x))
      have hc' :
          (((((U.powersetCard m).filter fun T => ε < avg T f - avg U f) ∪
            ((U.powersetCard m).filter fun T => ε < avg T (fun x => !f x) - avg U (fun x => !f x))).card : ℕ) : ℝ) ≤
          (((U.powersetCard m).filter fun T => ε < avg T f - avg U f).card : ℝ) +
          (((U.powersetCard m).filter fun T => ε < avg T (fun x => !f x) - avg U (fun x => !f x)).card : ℝ) :=
        by exact_mod_cast hc
      linarith [hup f, hup (fun x => !f x)]

end WentaoSampleConcentration

open WentaoSampleConcentration in
theorem solution :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ K L : ℕ, K₀ ≤ K →
      ∀ (D : Fin L → QTree K L) (G : Fin K ↪ Fin L),
        1 - Real.exp (-(c * ((K : ℝ) ^ (1 - 5 * δ) * ((K : ℝ) ^ (-δ)) ^ 2))) ≤
            ((((Finset.univ : Finset (Fin K)).powersetCard ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊).filter
                fun S => |avg S (fun x => (D (G x)).run G) - prX D G| ≤
                  1 / (4 * (K : ℝ) ^ δ)).card : ℝ) /
              ((K.choose ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ : ℕ) : ℝ) ∧
          (3 / 4 : ℝ) <
            ((((Finset.univ : Finset (Fin K)).powersetCard ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊).filter
                fun S => |avg S (fun x => (D (G x)).run G) - prX D G| ≤
                  1 / (4 * (K : ℝ) ^ δ)).card : ℝ) /
              ((K.choose ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ : ℕ) : ℝ) := by
  classical
  intro δ hδ hδ1
  obtain ⟨d, hd, htail⟩ := chernoff_count_T
  let c := d / 64
  have hc : 0 < c := by dsimp [c]; positivity
  have hα : 0 < 1 - 5 * δ := by linarith
  have hβ : 0 < 1 - 7 * δ := by linarith
  have evA : ∀ᶠ K : ℕ in atTop, (2 : ℝ) ≤ (K : ℝ) ^ (1 - 5 * δ) :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have evH : ∀ᶠ K : ℕ in atTop, (3 / c : ℝ) ≤ (K : ℝ) ^ (1 - 7 * δ) :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (3 / c)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (evA.and (evH.and (eventually_ge_atTop 1)))
  refine ⟨c, hc, N, ?_⟩
  intro K L hK D G
  obtain ⟨hA2, hH3, hK1⟩ := hN K hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hKr1 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  let A := (K : ℝ) ^ (1 - 5 * δ)
  let H := A * ((K : ℝ) ^ (-δ)) ^ 2
  let m := ⌊A⌋₊
  let ε := 1 / (4 * (K : ℝ) ^ δ)
  let f : Fin K → Bool := fun x => (D (G x)).run G
  let P := (Finset.univ : Finset (Fin K)).powersetCard m
  let C : ℝ := K.choose m
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hHpow : H = (K : ℝ) ^ (1 - 7 * δ) := by
    dsimp [H, A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKr.le, ← Real.rpow_add hKr]
    congr 1 <;> ring
  have hmlo : A / 2 ≤ (m : ℝ) := by
    have hfloor := Nat.lt_floor_add_one A
    dsimp [m]
    dsimp [A] at *
    linarith
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := by dsimp [A] at hmlo; linarith
    exact_mod_cast this
  have hmK : m ≤ K := by
    have hfloor : (m : ℝ) ≤ A := Nat.floor_le (by dsimp [A]; positivity)
    have hAK : A ≤ K := by
      dsimp [A]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hKr1 (show 1 - 5 * δ ≤ 1 by linarith)
    exact_mod_cast hfloor.trans hAK
  have hC : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos hmK
  have hbad := two_sided (Finset.univ : Finset (Fin K)) (by simpa using (show 0 < K by omega))
    f m hm0 ε d (fun g => by simpa using htail Finset.univ g m ε hε)
  have hrate : 2 * (c * H) ≤ d * m * ε ^ 2 := by
    have heq : d * (A / 2) * ε ^ 2 = 2 * (c * H) := by
      dsimp [c, H, ε]
      rw [Real.rpow_neg hKr.le]
      field_simp
      <;> ring
    rw [← heq]
    gcongr
  have hcH : 3 ≤ c * H := by
    rw [hHpow]
    exact (div_le_iff₀ hc).mp hH3 |>.trans_eq (mul_comm _ _)
  have htwotail : 2 * Real.exp (-(d * m * ε ^ 2)) ≤ Real.exp (-(c * H)) := by
    have hlarge : 2 ≤ Real.exp (c * H) := by linarith [Real.add_one_le_exp (c * H)]
    have hsub : Real.exp (-(d * m * ε ^ 2)) ≤
        Real.exp (-(c * H)) / Real.exp (c * H) := by
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      linarith
    calc
      _ ≤ 2 * (Real.exp (-(c * H)) / Real.exp (c * H)) :=
        mul_le_mul_of_nonneg_left hsub (by norm_num)
      _ ≤ _ := by
        rw [mul_div_assoc', div_le_iff₀ (Real.exp_pos _)]
        nlinarith [mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (-(c * H))).le]
  simp only [Finset.card_univ, Fintype.card_fin] at hbad
  have hbad' : ((P.filter fun S => ε < |avg S f - avg Finset.univ f|).card : ℝ) ≤
      Real.exp (-(c * H)) * C :=
    hbad.trans (mul_le_mul_of_nonneg_right htwotail hC.le)
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun S => |avg S f - avg Finset.univ f| ≤ ε)
  simp only [not_le] at hsplit
  have hP : P.card = K.choose m := by simp [P]
  rw [hP] at hsplit
  have hs : ((P.filter fun S => |avg S f - avg Finset.univ f| ≤ ε).card : ℝ) +
      ((P.filter fun S => ε < |avg S f - avg Finset.univ f|).card : ℝ) = C := by
    dsimp only [C]
    exact_mod_cast hsplit
  have hgood : 1 - Real.exp (-(c * H)) ≤
      ((P.filter fun S => |avg S f - avg Finset.univ f| ≤ ε).card : ℝ) / C := by
    rw [le_div_iff₀ hC]
    nlinarith
  have hsmall : Real.exp (-(c * H)) < 1 / 4 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_lt_one_div_of_lt (by norm_num)
    have hstrict := Real.add_one_lt_exp (by linarith : c * H ≠ 0)
    linarith
  refine ⟨hgood, ?_⟩
  change (3 / 4 : ℝ) < ((P.filter fun S => |avg S f - avg Finset.univ f| ≤ ε).card : ℝ) / C
  linarith
