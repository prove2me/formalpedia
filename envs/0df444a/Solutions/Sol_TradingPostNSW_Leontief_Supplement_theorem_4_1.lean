-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:25.806248+00:00
-- url     : https://prove2.me/submissions/f86e98a9-d046-4bee-8f1b-d95c1334085f

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (hI : LinStanding I)
    (hpc : PerfectCompetition I) (b : Fin n → Fin m → ℝ) (hb : IsPNEU I (linU I) 0 b)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSWU I (linU I) y ≤ 2 * NSWU I (linU I) (tpAlloc 0 b) := by
      classical
      have hB : ∀ i, 0 < I.B i := fun i => lt_of_lt_of_le zero_lt_one (hI.one_le_B i)
      have hbn : ∀ i j, 0 ≤ b i j := fun i j => (hb.1 i).1 j |>.1
      have halloc : ∀ (a : Fin n → Fin m → ℝ), (∀ i j, 0 ≤ a i j) →
          ∀ i j, 0 ≤ tpAlloc 0 a i j := by
        intro a ha i j
        have he : ∀ k, effBid 0 a k j = a k j := fun k => if_pos (ha k j)
        simp only [tpAlloc, he]
        split_ifs
        · exact div_nonneg (ha i j) (Finset.sum_nonneg fun k _ => ha k j)
        · exact le_rfl
      have hyn : ∀ i j, 0 ≤ y i j := hy.1
      have hyle : ∀ i j, y i j ≤ 1 := by
        intro i j
        rw [← hy.2 j]
        exact Finset.single_le_sum (fun k _ => hyn k j) (Finset.mem_univ i)
      let p : Fin m → ℝ := fun j => ∑ k, b k j
      have hpn : ∀ j, 0 ≤ p j := fun j => Finset.sum_nonneg fun k _ => hbn k j
      let C : Fin n → ℝ := fun i => ∑ j, p j * y i j
      have hCn : ∀ i, 0 ≤ C i := fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hpn j) (hyn i j)
      let U : Fin n → ℝ := fun i => linU I i (tpAlloc 0 b i)
      let V : Fin n → ℝ := fun i => linU I i (y i)
      have hUn : ∀ i, 0 ≤ U i := fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hI.v_nonneg i j) (halloc b hbn i j)
      have hVn : ∀ i, 0 ≤ V i := fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hI.v_nonneg i j) (hyn i j)
      have hmain : ∀ i, I.B i * V i ≤ (I.B i + C i) * U i := by
        intro i
        have haux : ∀ t : ℝ, 0 < t → I.B i * V i ≤ (I.B i + C i + (m : ℝ) * t) * U i := by
          intro t ht
          let q : Fin m → ℝ := fun j => p j * y i j + t
          have hq : ∀ j, 0 < q j := fun j => add_pos_of_nonneg_of_pos (mul_nonneg (hpn j) (hyn i j)) ht
          let S : ℝ := ∑ j, q j
          have hm : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hI.pos_m
          have hS : 0 < S := Finset.sum_pos (fun j _ => hq j) Finset.univ_nonempty
          have hSeq : S = C i + (m : ℝ) * t := by
            simp [S, q, C, Finset.sum_add_distrib]
          let d : Fin m → ℝ := fun j => I.B i * q j / S
          have hd : ∀ j, 0 < d j := fun j => div_pos (mul_pos (hB i) (hq j)) hS
          have hds : ∑ j, d j = I.B i := by
            simp only [d, ← Finset.sum_div, ← Finset.mul_sum]
            exact mul_div_cancel_right₀ (I.B i) (ne_of_gt hS)
          have hdstr : Strategy I i d := by
            refine ⟨fun j => ⟨(hd j).le, ?_⟩, hds⟩
            rw [← hds]
            exact Finset.single_le_sum (fun k _ => (hd k).le) (Finset.mem_univ j)
          let a := Function.update b i d
          have han : ∀ k j, 0 ≤ a k j := by
            intro k j
            by_cases hk : k = i
            · subst k
              simpa [a] using (hd j).le
            · simpa [a, Function.update_of_ne hk] using hbn k j
          have hai : ∀ j, a i j = d j := fun j => by simp [a]
          have hden : ∀ j, 0 < ∑ k, a k j := by
            intro j
            exact lt_of_lt_of_le (by simpa [hai] using hd j)
              (Finset.single_le_sum (fun k _ => han k j) (Finset.mem_univ i))
          have hdenle : ∀ j, ∑ k, a k j ≤ d j + p j := by
            intro j
            calc
              ∑ k, a k j ≤ ∑ k, ((if k = i then d j else 0) + b k j) := by
                apply Finset.sum_le_sum
                intro k hk
                by_cases hki : k = i
                · subst k
                  simpa [hai] using (le_add_of_nonneg_right (hbn i j) : d j ≤ d j + b i j)
                · simp [a, hki]
              _ = d j + p j := by simp [Finset.sum_add_distrib, p]
          have hcoord : ∀ j, I.B i * y i j ≤ (I.B i + S) * tpAlloc 0 a i j := by
            intro j
            have he : ∀ k, effBid 0 a k j = a k j := fun k => if_pos (han k j)
            have hx : tpAlloc 0 a i j = d j / ∑ k, a k j := by
              simp only [tpAlloc, he, hai, if_pos (hd j)]
            rw [hx, ← mul_div_assoc]
            apply (le_div_iff₀ (hden j)).2
            have hid : S * d j = I.B i * (p j * y i j + t) := by
              dsimp [d, q]
              field_simp
            have hprod : I.B i * y i j * (∑ k, a k j) ≤ I.B i * y i j * (d j + p j) :=
              mul_le_mul_of_nonneg_left (hdenle j) (mul_nonneg (hB i).le (hyn i j))
            have hrest : 0 ≤ I.B i * d j * (1 - y i j) :=
              mul_nonneg (mul_nonneg (hB i).le (hd j).le) (sub_nonneg.mpr (hyle i j))
            have hbt : 0 ≤ I.B i * t := mul_nonneg (hB i).le ht.le
            nlinarith
          have hsum : I.B i * V i ≤ (I.B i + S) * linU I i (tpAlloc 0 a i) := by
            dsimp [V, linU]
            simp only [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro j hj
            have := mul_le_mul_of_nonneg_left (hcoord j) (hI.v_nonneg i j)
            nlinarith
          have hne : linU I i (tpAlloc 0 a i) ≤ U i := hb.2 i d hdstr
          calc
            I.B i * V i ≤ (I.B i + S) * linU I i (tpAlloc 0 a i) := hsum
            _ ≤ (I.B i + S) * U i := mul_le_mul_of_nonneg_left hne (add_nonneg (hB i).le hS.le)
            _ = (I.B i + C i + (m : ℝ) * t) * U i := by rw [hSeq]; ring
        by_cases hu : U i = 0
        · simpa [hu] using haux 1 zero_lt_one
        · have hup : 0 < U i := lt_of_le_of_ne (hUn i) (Ne.symm hu)
          apply le_of_forall_pos_le_add
          intro ε hε
          have hmp : 0 < (m : ℝ) := Nat.cast_pos.mpr hI.pos_m
          have hh := haux (ε / ((m : ℝ) * U i)) (div_pos hε (mul_pos hmp hup))
          have heq : (I.B i + C i + (m : ℝ) * (ε / ((m : ℝ) * U i))) * U i =
              (I.B i + C i) * U i + ε := by
            field_simp
          rwa [heq] at hh
      have hn : Nonempty (Fin n) := by
        obtain ⟨i, k, hik, hi, hk⟩ := hpc ⟨0, hI.pos_m⟩
        exact ⟨i⟩
      let T : ℝ := totalBudget I
      have hT : 0 < T := Finset.sum_pos (fun i _ => hB i) Finset.univ_nonempty
      have hCsum : ∑ i, C i = T := by
        dsimp [C]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hy.2, mul_one]
        dsimp [p, T, totalBudget]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (hb.1 i).2
      let z : Fin n → ℝ := fun i => (I.B i + C i) / I.B i
      have hzn : ∀ i, 0 ≤ z i := fun i => div_nonneg (add_nonneg (hB i).le (hCn i)) (hB i).le
      have hVz : ∀ i, V i ≤ z i * U i := by
        intro i
        dsimp [z]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (hB i)).2
        nlinarith [hmain i]
      have hZsum : ∑ i, I.B i * z i = 2 * T := by
        calc
          ∑ i, I.B i * z i = ∑ i, (I.B i + C i) := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [z]
            field_simp [ne_of_gt (hB i)]
          _ = 2 * T := by rw [Finset.sum_add_distrib, hCsum]; change T + T = 2 * T; ring
      have hgm : (∏ i, z i ^ I.B i) ^ (1 / T) ≤ 2 := by
        have hh := Real.geom_mean_le_arith_mean Finset.univ I.B z
          (fun i _ => (hB i).le) hT (fun i _ => hzn i)
        change (∏ i, z i ^ I.B i) ^ T⁻¹ ≤ (∑ i, I.B i * z i) / T at hh
        simpa [one_div, hZsum, ne_of_gt hT] using hh
      have hprod : (∏ i, V i ^ I.B i) ≤
          (∏ i, z i ^ I.B i) * (∏ i, U i ^ I.B i) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_le_prod
        · intro i hi
          exact Real.rpow_nonneg (hVn i) _
        · intro i hi
          rw [← Real.mul_rpow (hzn i) (hUn i)]
          exact Real.rpow_le_rpow (hVn i) (hVz i) (hB i).le
      change (∏ i, V i ^ I.B i) ^ (1 / T) ≤ 2 * (∏ i, U i ^ I.B i) ^ (1 / T)
      calc
        (∏ i, V i ^ I.B i) ^ (1 / T) ≤
            ((∏ i, z i ^ I.B i) * (∏ i, U i ^ I.B i)) ^ (1 / T) :=
          Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hVn i) _)) hprod (by positivity)
        _ = (∏ i, z i ^ I.B i) ^ (1 / T) * (∏ i, U i ^ I.B i) ^ (1 / T) :=
          Real.mul_rpow (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hzn i) _))
            (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hUn i) _))
        _ ≤ 2 * (∏ i, U i ^ I.B i) ^ (1 / T) :=
          mul_le_mul_of_nonneg_right hgm (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hUn i) _)) _)
