-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.proposition_L_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:43:08.384195+00:00
-- url     : https://prove2.me/submissions/33e613af-38e1-4ed6-a8ca-23c5ffad2c5b

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 2 ≤ n) (S : Finset ℝ) (f : ℝ → ℝ)
    (hTypes : ValidTypes (fun _ : Fin n => S) (fun _ => f))
    (hReg : Regular (fun _ : Fin n => S) (fun _ => f)) (delta : ℝ) (hdelta : 0 < delta)
    (a : Profile (fun _ : Fin n => S) → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence (fun _ : Fin n => f)
      (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (xstar (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (fun θ => differenceA (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta θ)) a b) :
    ∀ c ∈ S, b ⟨0,by omega⟩ c + b ⟨n-1,by omega⟩ c +
      2 * (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val ∧ i.val < n-1), b i c) = 0 := by
        classical
        intro c hc
        obtain ⟨_, _, hfpos, _⟩ := hTypes
        have hfc : 0 < f c := hfpos ⟨0, by omega⟩ c hc
        let θ : Profile (fun _ : Fin n => S) := fun _ => ⟨c, hc⟩
        have hvv : vvec (fun _ : Fin n => S) (fun _ => f) θ =
            fun _ => virtualCost (fun _ : Fin n => S) (fun _ => f) ⟨0, by omega⟩ c := by
          funext i; rfl
        have hQ : activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta θ = Finset.univ := by
          unfold activeSet hotQ
          rw [hvv]
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, sub_self]
          intro j
          exact mul_nonneg hdelta.le (abs_nonneg _)
        have hD : ∀ i : Fin n, ∑ j, differenceA (Finset.univ : Finset (Fin n)) i j = 0 := by
          intro i
          unfold differenceA
          split_ifs with h
          · simp [Finset.sum_sub_distrib]
          · simp
        have hP : ∀ j : Fin n, probOthers (fun _ : Fin n => f) j θ = f c ^ (n-1) := by
          intro j
          unfold probOthers
          simp [θ, Finset.prod_const, Finset.card_erase_of_mem]
        have hn1 : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have hnpos : (0:ℝ) < (n:ℝ) - 1 := by
          have : (2:ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hloc : ∀ i j : Fin n, j.val = i.val + 1 → |equiLoc n j - equiLoc n i| = 1 / ((n:ℝ) - 1) := by
          intro i j hij
          unfold equiLoc
          rw [hn1, hij]
          push_cast
          rw [← sub_div, show ((i.val:ℝ) + 1 - i.val) = 1 by ring, abs_of_pos (by positivity)]
        have hloc' : ∀ i j : Fin n, j.val = i.val + 1 → |equiLoc n i - equiLoc n j| = 1 / ((n:ℝ) - 1) := by
          intro i j hij
          rw [abs_sub_comm]; exact hloc i j hij
        have hx : ∀ j : Fin n, xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j =
            (if 0 < j.val then 1 / (2 * ((n:ℝ) - 1)) else 0) +
              (if j.val < n - 1 then 1 / (2 * ((n:ℝ) - 1)) else 0) := by
          intro j
          have hQ' : hotQ (equiLoc n) delta (vvec (fun _ : Fin n => S) (fun _ => f) θ) = Finset.univ := hQ
          unfold xstar hotDemand
          rw [hQ', if_pos (Finset.mem_univ _)]
          congr 1
          · by_cases h0 : 0 < j.val
            · have hne : ((Finset.univ : Finset (Fin n)).filter (· < j)).Nonempty :=
                ⟨⟨j.val - 1, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val]; omega⟩
              rw [dif_pos hne, if_pos h0]
              have hm1 := Finset.max'_mem _ hne
              have hm2 : (⟨j.val - 1, by omega⟩ : Fin n) ≤ _ :=
                Finset.le_max' ((Finset.univ : Finset (Fin n)).filter (· < j)) ⟨j.val - 1, by omega⟩ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val]; omega)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm1
              rw [Fin.lt_iff_val_lt_val] at hm1
              simp only [Fin.le_iff_val_le_val, Fin.val_mk] at hm2
              rw [hvv, hloc _ j (by omega)]
              field_simp
              ring
            · have hne : ¬ ((Finset.univ : Finset (Fin n)).filter (· < j)).Nonempty := by
                rintro ⟨k, hk⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hk; omega
              rw [dif_neg hne, if_neg h0]
              unfold equiLoc
              have : j.val = 0 := by omega
              simp [this]
          · by_cases h0 : j.val < n - 1
            · have hne : ((Finset.univ : Finset (Fin n)).filter (j < ·)).Nonempty :=
                ⟨⟨j.val + 1, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val]; omega⟩
              rw [dif_pos hne, if_pos h0]
              have hm1 := Finset.min'_mem _ hne
              have hm2 : _ ≤ (⟨j.val + 1, by omega⟩ : Fin n) :=
                Finset.min'_le ((Finset.univ : Finset (Fin n)).filter (j < ·)) ⟨j.val + 1, by omega⟩ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val]; omega)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm1
              rw [Fin.lt_iff_val_lt_val] at hm1
              simp only [Fin.le_iff_val_le_val, Fin.val_mk] at hm2
              rw [hvv, hloc j _ (by omega)]
              field_simp
              ring
            · have hne : ¬ ((Finset.univ : Finset (Fin n)).filter (j < ·)).Nonempty := by
                rintro ⟨k, hk⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hk; omega
              rw [dif_neg hne, if_neg h0]
              unfold equiLoc
              have : j.val = n - 1 := by omega
              rw [this, div_self (by rw [hn1]; exact hnpos.ne')]
              simp
        have key : ∀ j : Fin n,
            (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ReducedRow Finset.univ i),
                a θ i * differenceA Finset.univ i j) +
              b j c * f c ^ (n-1) * ((if 0 < j.val then 1 / (2 * ((n:ℝ) - 1)) else 0) +
                (if j.val < n - 1 then 1 / (2 * ((n:ℝ) - 1)) else 0)) = 0 := by
          intro j
          have h := hDep θ j (by rw [hQ]; exact Finset.mem_univ _)
          rw [← hP j, ← hx j]
          simp only [hQ] at h
          exact h
        have hsum := Finset.sum_eq_zero (s := Finset.univ) (fun j _ => key j)
        rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
        have h1 : ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ReducedRow Finset.univ i),
            ∑ j, a θ i * differenceA Finset.univ i j = 0 :=
          Finset.sum_eq_zero (fun i _ => by rw [← Finset.mul_sum, hD, mul_zero])
        rw [h1, zero_add] at hsum
        set H : ℝ := 1 / (2 * ((n:ℝ) - 1)) with hH
        have hHpos : 0 < H := by rw [hH]; positivity
        have hPpos : 0 < f c ^ (n-1) := pow_pos hfc _
        have hpt : ∀ j : Fin n, b j c * f c ^ (n-1) * ((if 0 < j.val then H else 0) +
                (if j.val < n - 1 then H else 0)) =
            f c ^ (n-1) * H * ((if j = ⟨0, by omega⟩ then b j c else 0) +
              (if j = ⟨n-1, by omega⟩ then b j c else 0) +
              2 * (if 0 < j.val ∧ j.val < n-1 then b j c else 0)) := by
          intro j
          simp only [Fin.ext_iff]
          split_ifs <;> first | (exfalso; omega) | ring
        rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum,
          ← Finset.sum_filter] at hsum
        simp only [Finset.mem_univ, if_true] at hsum
        rcases mul_eq_zero.mp hsum with h | h
        · exact absurd h (mul_pos hPpos hHpos).ne'
        · exact h
