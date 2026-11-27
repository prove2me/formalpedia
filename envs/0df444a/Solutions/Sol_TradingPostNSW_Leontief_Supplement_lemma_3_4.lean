-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:32.375381+00:00
-- url     : https://prove2.me/submissions/61dc6359-9aa7-4842-b8ca-92fd16e268b3

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (hI : GenStanding I)
    (r : Fin n → Fin m → ℝ) (hr : ∀ k j, 0 ≤ r k j) (i : Fin n) (r' : Fin m → ℝ)
    (hr' : ∀ j, 0 ≤ r' j) (hother : ∀ k, k ≠ i → ∃ j, 0 < r k j)
    (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) (p' : Fin m → ℝ) (x' : Fin n → Fin m → ℝ)
    (hE : IsMarketEq I.B (linRep r) (orthant m) p x)
    (hE' : IsMarketEq I.B (linRep (Function.update r i r')) (orthant m) p' x') :
    ∑ j ∈ Finset.univ.filter (fun j => p j < p' j), p' j ≤
      I.B i + ∑ j ∈ Finset.univ.filter (fun j => p j < p' j), p j := by
        have exch : ∀ (s : Fin n → Fin m → ℝ) (q : Fin m → ℝ) (z : Fin n → Fin m → ℝ),
            IsMarketEq I.B (linRep s) (orthant m) q z → ∀ k a b, 0 < z k a →
              s k b * q a ≤ s k a * q b := by
          intro s q z hEq k a b hza
          have hqb := hEq.p_nonneg b
          have hqa := hEq.p_nonneg a
          set c := z k a / (q b + 1) with hc
          have hcpos : 0 < c := div_pos hza (by linarith)
          have hcle : c * q b ≤ z k a := by
            rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
          let y : Fin m → ℝ := fun j => z k j + c * (q a * (if j = b then 1 else 0)
            - q b * (if j = a then 1 else 0))
          have hy : y ∈ orthant m := by
            intro j
            simp only [y]
            have hz := hEq.x_nonneg k j
            by_cases hja : j = a
            · subst hja
              by_cases hjb : j = b
              · subst hjb; simp; exact hz
              · simp [hjb]; nlinarith
            · by_cases hjb : j = b
              · subst hjb; simp [hja]; nlinarith [mul_nonneg hcpos.le hqa]
              · simp [hja, hjb]; exact hz
          have hsum : ∀ f : Fin m → ℝ, ∑ j, f j * y j = ∑ j, f j * z k j + c * (q a * f b - q b * f a) := by
            intro f
            simp only [y, mul_add, Finset.sum_add_distrib]
            congr 1
            have : ∀ j, f j * (c * (q a * (if j = b then 1 else 0) - q b * (if j = a then 1 else 0)))
                = c * q a * (if j = b then f j else 0) - c * q b * (if j = a then f j else 0) := by
              intro j; split_ifs <;> ring
            simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
              Finset.mem_univ, if_true]
            ring
          have hbud : ∑ j, q j * z k j = I.B k := by
            rw [← hEq.budget k]; exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
          have hopt := hEq.opt k y hy (by rw [hsum q, hbud]; nlinarith)
          simp only [linRep] at hopt
          rw [hsum (s k)] at hopt
          have : c * (q a * s k b - q b * s k a) ≤ 0 := by linarith
          have : q a * s k b - q b * s k a ≤ 0 := by
            by_contra h; have h := lt_of_not_ge h; nlinarith
          linarith
        set S := Finset.univ.filter (fun j => p j < p' j) with hS
        have hmemS : ∀ j, j ∈ S ↔ p j < p' j := by intro j; simp [hS]
        -- LHS rewrite
        have hL : ∑ j ∈ S, p' j = ∑ k, ∑ j ∈ S, x' k j * p' j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          have hpos : 0 < p' j := lt_of_le_of_lt (hE.p_nonneg j) ((hmemS j).1 hj)
          rw [← Finset.sum_mul, hE'.sold j hpos, one_mul]
        have hR : ∑ k, ∑ j ∈ S, x k j * p j ≤ ∑ j ∈ S, p j := by
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [← Finset.sum_mul]
          have := hE.supply j
          have := hE.p_nonneg j
          nlinarith
        have hT : ∀ k, ∑ j ∈ S, x' k j * p' j ≤ ∑ j ∈ S, x k j * p j + (if k = i then I.B i else 0) := by
          intro k
          have hTnn : 0 ≤ ∑ j ∈ S, x k j * p j :=
            Finset.sum_nonneg (fun j _ => mul_nonneg (hE.x_nonneg k j) (hE.p_nonneg j))
          have hT'le : ∑ j ∈ S, x' k j * p' j ≤ I.B k := by
            rw [← hE'.budget k]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => mul_nonneg (hE'.x_nonneg k j) (hE'.p_nonneg j))
          by_cases hki : k = i
          · subst hki; simp; linarith
          · simp only [hki, if_false, add_zero]
            by_cases hall : ∀ j ∈ S, x' k j = 0
            · rw [Finset.sum_eq_zero (fun j hj => by rw [hall j hj, zero_mul])]; exact hTnn
            · simp only [not_forall] at hall
              obtain ⟨j, hjS, hxj⟩ := hall
              change ¬ x' k j = 0 at hxj
              have hxj' : 0 < x' k j := lt_of_le_of_ne (hE'.x_nonneg k j) (Ne.symm hxj)
              have hpj := (hmemS j).1 hjS
              have hp'j : 0 < p' j := lt_of_le_of_lt (hE.p_nonneg j) hpj
              have hupd : Function.update r i r' k = r k := Function.update_of_ne hki _ _
              have ex' := exch _ _ _ hE' k j
              rw [hupd] at ex'
              have hrkj : 0 < r k j := by
                obtain ⟨g, hg⟩ := hother k hki
                by_contra hneg
                have h0 : r k j = 0 := le_antisymm (not_lt.1 hneg) (hr k j)
                have := ex' g hxj'
                rw [h0, zero_mul] at this
                nlinarith
              have hout : ∀ l, l ∉ S → x k l * p l = 0 := by
                intro l hl
                have hl' : p' l ≤ p l := not_lt.1 (fun h => hl ((hmemS l).2 h))
                by_contra hne
                have hxl : 0 < x k l := lt_of_le_of_ne (hE.x_nonneg k l)
                  (fun h => hne (by rw [← h, zero_mul]))
                have hpl : 0 < p l := lt_of_le_of_ne (hE.p_nonneg l)
                  (fun h => hne (by rw [← h, mul_zero]))
                have e1 := exch _ _ _ hE k l j hxl
                have e2 := ex' l hxj'
                have hrl := hr k l
                rcases hrl.lt_or_eq with hrl | hrl
                · have : r k l * p' j ≤ r k l * p j := by nlinarith
                  have : p' j ≤ p j := le_of_mul_le_mul_left this hrl
                  linarith
                · rw [← hrl] at e1; nlinarith
              have : ∑ j ∈ S, x k j * p j = I.B k := by
                rw [← hE.budget k, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => p j < p' j)]
                rw [← hS]
                rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun j => ¬ p j < p' j))
                  (fun l hl => hout l (by simp at hl; rw [hmemS]; exact not_lt.2 hl)), add_zero]
              linarith
        calc ∑ j ∈ S, p' j = ∑ k, ∑ j ∈ S, x' k j * p' j := hL
          _ ≤ ∑ k, (∑ j ∈ S, x k j * p j + (if k = i then I.B i else 0)) := Finset.sum_le_sum (fun k _ => hT k)
          _ = ∑ k, ∑ j ∈ S, x k j * p j + I.B i := by
              rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
          _ ≤ I.B i + ∑ j ∈ S, p j := by linarith
