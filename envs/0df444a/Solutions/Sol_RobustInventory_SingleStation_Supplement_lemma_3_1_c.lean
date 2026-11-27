-- Prove2me | solution 1 for RobustInventory.SingleStation.Supplement.lemma_3_1_c
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:18.13486+00:00
-- url     : https://prove2.me/submissions/7947e277-a3d1-48b8-96f0-524aa0acec19

import Definitions.Def_RobustInventory_SingleStation_Supplement_Thresholds

open RobustInventory
open RobustInventory.SingleStation
open RobustInventory.SingleStation.Supplement

/-- Lemma 3.1(c), p. 154, for a nonnegative demand sequence `w` and `K > 0`: if `t_1 < … < t_J`
are the ordering times of an optimal solution of the nominal problem, then some optimal solution
orders exactly at these times, and at each `t_j` its stock is `s_j` of (16) before the order and
`S_j` of (15) after it. -/
theorem solution (M : Model) (hK : 0 < M.K) (w : ℕ → ℝ) (hw : ∀ k < M.T, 0 ≤ w k)
    (u : ℕ → ℝ) (hu : M.IsNominalOptimal w u)
    (J : ℕ) (t : ℕ → ℕ) (ht : IsOrderingTimes M.T u J t) :
    ∃ v : ℕ → ℝ, M.IsNominalOptimal w v ∧ IsOrderingTimes M.T v J t ∧
      ∀ j ∈ Finset.Icc 1 J,
        stockBefore M w v (t j) = lowerThreshold M w J t j ∧
        stockBefore M w v (t j) + v (t j) = upperThreshold M w J t j := by
          set_option maxHeartbeats 1600000 in
            classical
            have hp : 0 < M.p := lt_trans M.hc M.hpc
            have hhp : 0 < M.h + M.p := by linarith [M.hh]
            let W : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, w i
            have hW : ∀ {a b : ℕ}, a ≤ b → b ≤ M.T → W a ≤ W b := by
              intro a b hab hb
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
              intro i hi _
              exact hw i (lt_of_lt_of_le (Finset.mem_range.mp hi) hb)
            have hRlower : ∀ x y : ℝ, x ≤ y → -(M.p * (y-x)) ≤ M.R y - M.R x := by
              intro x y hxy
              unfold Model.R
              have hh : max (M.h*x) (-(M.p*x)) ≤ max (M.h*y) (-(M.p*y)) + M.p*(y-x) := by
                apply max_le
                · nlinarith [le_max_left (M.h*y) (-(M.p*y)), M.hh]
                · nlinarith [le_max_right (M.h*y) (-(M.p*y))]
              linarith
            have hRupper : ∀ x y : ℝ, x ≤ y → M.R y - M.R x ≤ M.h * (y-x) := by
              intro x y hxy
              unfold Model.R
              apply sub_le_iff_le_add.mpr
              apply max_le
              · nlinarith [le_max_left (M.h*x) (-(M.p*x))]
              · nlinarith [le_max_right (M.h*x) (-(M.p*x))]
            have hRpos : ∀ x : ℝ, 0 ≤ x → M.R x = M.h*x := by
              intro x hx
              exact max_eq_left (by nlinarith [M.hh])
            have hRneg : ∀ x : ℝ, x ≤ 0 → M.R x = -(M.p*x) := by
              intro x hx
              exact max_eq_right (by nlinarith [M.hh])
            have htmono : ∀ {i j : ℕ}, 1 ≤ i → i ≤ j → j ≤ J+1 → t i ≤ t j := by
              intro i j hi hij hj
              induction j, hij using Nat.le_induction with
              | base => exact le_rfl
              | succ j hij ih =>
                exact ih (by omega) |>.trans (ht.2.1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).le
            have htbound : ∀ j ∈ Finset.Icc 1 J, t j < M.T := by
              intro j hj
              have hj' := Finset.mem_Icc.mp hj
              have hb := htmono (i:=j+1) (j:=J+1) (by omega) (by omega) (by omega)
              rw [ht.1] at hb
              exact lt_of_lt_of_le (ht.2.1 j hj) hb
            have htstrict : ∀ {i j : ℕ}, 1 ≤ i → i < j → j ≤ J+1 → t i < t j := by
              intro i j hi hij hj
              exact lt_of_lt_of_le (ht.2.1 i (Finset.mem_Icc.mpr ⟨hi, by omega⟩))
                (htmono (by omega) (by omega) hj)
            have hprefix : ∀ f : ℕ → ℝ, ∀ a k : ℕ, a ≤ k →
                (∑ i ∈ Finset.range k, f i) = (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.Ico a k, f i := by
              intro f a k hak
              exact (Finset.sum_range_add_sum_Ico f hak).symm
            have hS : ∀ j ∈ Finset.Icc 1 J,
                upperThreshold M w J t j = W (t j + floorIndex M J t j + 1) - W (t j) := by
              intro j hj
              have hh := Finset.sum_range_add w (t j) (floorIndex M J t j + 1)
              change _ = (∑ i ∈ Finset.range (t j + floorIndex M J t j + 1), w i) - _
              rw [show t j + floorIndex M J t j + 1 = t j + (floorIndex M J t j + 1) by omega]
              unfold upperThreshold
              linarith
            have hcycle : ∀ j ∈ Finset.Icc 1 J,
                let a := t j
                let b := t (j+1)
                let S := upperThreshold M w J t j
                let γ : ℝ := if j = J then M.c else 0
                let F : ℝ → ℝ := fun x => γ*x + ∑ k ∈ Finset.Ico a b, M.R (x-(W (k+1)-W a))
                (∀ x y, x ≤ y → y ≤ S → F y ≤ F x) ∧
                (∀ x y, S ≤ x → x ≤ y → F x ≤ F y) := by
              intro j hj
              dsimp only
              let a := t j
              let b := t (j+1)
              let L := b-a
              let I := floorIndex M J t j
              let γ : ℝ := if j = J then M.c else 0
              let S := upperThreshold M w J t j
              have hab : a < b := ht.2.1 j hj
              have hb : b ≤ M.T := by
                have hh := htmono (i:=j+1) (j:=J+1) (by have := Finset.mem_Icc.mp hj; omega) (by have := Finset.mem_Icc.mp hj; omega) le_rfl
                simpa [b, ht.1] using hh
              have hL : 1 ≤ L := by dsimp [L]; omega
              have hγ : 0 ≤ γ := by dsimp [γ]; split_ifs <;> linarith [M.hc]
              have hγc : γ ≤ M.c := by dsimp [γ]; split_ifs <;> linarith [M.hc]
              have hnum : 0 ≤ M.p*(L:ℝ)-γ := by
                have : (1:ℝ) ≤ L := by exact_mod_cast hL
                nlinarith [M.hpc]
              have hIfloor : I = ⌊(M.p*(L:ℝ)-γ)/(M.h+M.p)⌋₊ := rfl
              have hIlo : (M.h+M.p)*(I:ℝ) ≤ M.p*(L:ℝ)-γ := by
                have hh := Nat.floor_le (div_nonneg hnum hhp.le)
                rw [← hIfloor] at hh
                have hh' := (le_div_iff₀ hhp).mp hh
                nlinarith
              have hIhi : M.p*(L:ℝ)-γ < (M.h+M.p)*((I:ℝ)+1) := by
                have hh := Nat.lt_floor_add_one ((M.p*(L:ℝ)-γ)/(M.h+M.p))
                rw [← hIfloor] at hh
                have hh' := (div_lt_iff₀ hhp).mp hh
                nlinarith
              have hIL : I ≤ L := by
                have hh : (I:ℝ) ≤ L := by nlinarith [mul_nonneg M.hh (Nat.cast_nonneg I)]
                exact_mod_cast hh
              have hqT : a+I+1 ≤ M.T := by
                by_cases he : j = J
                · have hγ' : γ = M.c := by simp [γ, he]
                  have hIL' : I < L := by
                    have : (I:ℝ) < L := by nlinarith [mul_nonneg M.hh (Nat.cast_nonneg I), M.hc]
                    exact_mod_cast this
                  omega
                · have hh := htbound (j+1) (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Icc.mp hj; omega, by have := Finset.mem_Icc.mp hj; omega⟩)
                  dsimp [b, L] at *
                  omega
              have hS' : S = W (a+I+1)-W a := hS j hj
              let n := min (I+1) L
              have hnL : n ≤ L := min_le_right _ _
              have hnI : n ≤ I+1 := min_le_left _ _
              have hleft : γ + M.h*(I:ℝ)-M.p*((L-I:ℕ):ℝ) ≤ 0 := by
                rw [Nat.cast_sub hIL]
                nlinarith
              have hright : 0 ≤ γ + M.h*(n:ℝ)-M.p*((L-n:ℕ):ℝ) := by
                rw [Nat.cast_sub hnL]
                by_cases hi : I < L
                · have hn : n = I+1 := min_eq_left (by omega)
                  rw [hn, Nat.cast_add, Nat.cast_one]
                  nlinarith
                · have hn : n = L := min_eq_right (by omega)
                  rw [hn]
                  nlinarith [mul_nonneg M.hh (Nat.cast_nonneg L)]
              constructor
              · intro x y hxy hyS
                change y ≤ S at hyS
                have hsum1 : (∑ k ∈ Finset.Ico a (a+I), (M.R (y-(W (k+1)-W a))-M.R (x-(W (k+1)-W a)))) ≤ (I:ℝ)*(M.h*(y-x)) := by
                  calc
                    _ ≤ ∑ k ∈ Finset.Ico a (a+I), M.h*(y-x) := by
                      apply Finset.sum_le_sum
                      intro k hk
                      have hh := hRupper (x-(W (k+1)-W a)) (y-(W (k+1)-W a)) (by linarith)
                      nlinarith only [hh]
                    _ = _ := by simp
                have hsum2 : (∑ k ∈ Finset.Ico (a+I) b, (M.R (y-(W (k+1)-W a))-M.R (x-(W (k+1)-W a)))) = ((L-I:ℕ):ℝ)*(-(M.p*(y-x))) := by
                  calc
                    _ = ∑ k ∈ Finset.Ico (a+I) b, -(M.p*(y-x)) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      have hk' := Finset.mem_Ico.mp hk
                      have hq := hW (a:=a+I+1) (b:=k+1) (by omega) (by omega)
                      rw [hRneg _ (by rw [hS'] at hyS; linarith), hRneg _ (by rw [hS'] at hyS; linarith)]
                      ring
                    _ = _ := by simp [L, show b-(a+I) = b-a-I by omega]
                have hsplit := Finset.sum_Ico_consecutive
                  (fun k => M.R (y-(W (k+1)-W a))-M.R (x-(W (k+1)-W a)))
                  (show a ≤ a+I by omega) (show a+I ≤ b by dsimp [L] at hIL; omega)
                rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsplit
                simp only [Finset.sum_sub_distrib] at hsum1 hsum2
                dsimp [a, b] at hsum1 hsum2 hsplit
                have hc := mul_nonpos_of_nonpos_of_nonneg hleft (sub_nonneg.mpr hxy)
                dsimp [γ] at hc
                nlinarith only [hsum1, hsum2, hsplit, hc]
              · intro x y hSx hxy
                change S ≤ x at hSx
                have hsum1 : (∑ k ∈ Finset.Ico a (a+n), (M.R (y-(W (k+1)-W a))-M.R (x-(W (k+1)-W a)))) = (n:ℝ)*(M.h*(y-x)) := by
                  calc
                    _ = ∑ k ∈ Finset.Ico a (a+n), M.h*(y-x) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      have hk' := Finset.mem_Ico.mp hk
                      have hq := hW (a:=k+1) (b:=a+I+1) (by omega) hqT
                      rw [hRpos _ (by rw [hS'] at hSx; linarith), hRpos _ (by rw [hS'] at hSx; linarith)]
                      ring
                    _ = _ := by simp
                have hsum2 : ((L-n:ℕ):ℝ)*(-(M.p*(y-x))) ≤ (∑ k ∈ Finset.Ico (a+n) b, (M.R (y-(W (k+1)-W a))-M.R (x-(W (k+1)-W a)))) := by
                  calc
                    _ = ∑ k ∈ Finset.Ico (a+n) b, -(M.p*(y-x)) := by simp [L, show b-(a+n) = b-a-n by omega]
                    _ ≤ _ := by
                      apply Finset.sum_le_sum
                      intro k hk
                      have hh := hRlower (x-(W (k+1)-W a)) (y-(W (k+1)-W a)) (by linarith)
                      nlinarith only [hh]
                have hsplit := Finset.sum_Ico_consecutive
                  (fun k => M.R (y-(W (k+1)-W a))-M.R (x-(W (k+1)-W a)))
                  (show a ≤ a+n by omega) (show a+n ≤ b by dsimp [L] at hnL; omega)
                rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsplit
                simp only [Finset.sum_sub_distrib] at hsum1 hsum2
                dsimp [a, b] at hsum1 hsum2 hsplit
                have hc := mul_nonneg hright (sub_nonneg.mpr hxy)
                dsimp [γ] at hc
                nlinarith only [hsum1, hsum2, hsplit, hc]
            have hzero : ∀ (f : ℕ → ℝ), (∀ k < M.T, 0 ≤ f k) → IsOrderingTimes M.T f J t →
                ∀ j ∈ Finset.Icc 1 J, ∀ k, t j < k → k < t (j+1) → f k = 0 := by
              intro f hf hft j hj k hak hkb
              have hb : t (j+1) ≤ M.T := by
                have hh := htmono (i:=j+1) (j:=J+1) (by have := Finset.mem_Icc.mp hj; omega) (by have := Finset.mem_Icc.mp hj; omega) le_rfl
                simpa [ht.1] using hh
              by_contra hn
              have hkT : k < M.T := by omega
              have hkpos : 0 < f k := lt_of_le_of_ne (hf k hkT) (Ne.symm hn)
              obtain ⟨i, hi, hik⟩ := (hft.2.2 k).mp ⟨hkT, hkpos⟩
              have hi' := Finset.mem_Icc.mp hi
              have hj' := Finset.mem_Icc.mp hj
              by_cases hij : i ≤ j
              · have hh := htmono hi'.1 hij (by omega)
                omega
              · have hh := htmono (i:=j+1) (j:=i) (by omega) (by omega) (by omega)
                omega
            have hpath : ∀ (f : ℕ → ℝ) (a b : ℕ), a < b →
                (∀ k, a < k → k < b → f k = 0) →
                stockBefore M w f b = stockBefore M w f a + f a - (W b-W a) := by
              intro f a b hab hz
              have hsum : (∑ i ∈ Finset.Ico a b, f i) = f a := by
                apply Finset.sum_eq_single a
                · intro i hi hia
                  have hi' := Finset.mem_Ico.mp hi
                  exact hz i (by omega) hi'.2
                · intro ha
                  exact False.elim (ha (Finset.mem_Ico.mpr ⟨le_rfl, hab⟩))
              have hsumw : (∑ i ∈ Finset.Ico a b, w i) = W b-W a := Finset.sum_Ico_eq_sub w hab.le
              unfold stockBefore
              rw [hprefix (fun i => f i-w i) a b hab.le]
              simp only [Finset.sum_sub_distrib]
              rw [hsum, hsumw]
              ring
            have hstockcycle : ∀ (f : ℕ → ℝ), (∀ k < M.T, 0 ≤ f k) → IsOrderingTimes M.T f J t →
                ∀ j ∈ Finset.Icc 1 J, ∀ k ∈ Finset.Ico (t j) (t (j+1)),
                M.stock w f k = stockBefore M w f (t j) + f (t j) - (W (k+1)-W (t j)) := by
              intro f hf hft j hj k hk
              have hk' := Finset.mem_Ico.mp hk
              exact hpath f (t j) (k+1) (by omega) (fun i hi hik => hzero f hf hft j hj i hi (by omega))
            let edit : (ℕ → ℝ) → ℕ → ℕ → ℝ → ℕ → ℝ :=
              fun f a b d k => f k + (if k=a then d else 0) - (if k=b then d else 0)
            have heditstock : ∀ (f : ℕ → ℝ) (a b : ℕ) (d : ℝ) (k : ℕ),
                M.stock w (edit f a b d) k = M.stock w f k + (if a ≤ k then d else 0) - (if b ≤ k then d else 0) := by
              intro f a b d k
              unfold Model.stock
              have hh : (∑ i ∈ Finset.range (k+1), (edit f a b d i-w i)) =
                  (∑ i ∈ Finset.range (k+1), (f i-w i)) + (if a ≤ k then d else 0) - (if b ≤ k then d else 0) := by
                simp only [edit, show ∀ i, f i + (if i=a then d else 0) - (if i=b then d else 0) - w i =
                  (f i-w i) + (if i=a then d else 0) - (if i=b then d else 0) by intro i; ring,
                  Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_add_one_iff]
              rw [hh]
              ring
            have heditbefore : ∀ (f : ℕ → ℝ) (a b : ℕ) (d : ℝ) (k : ℕ), k ≤ a → a < b →
                stockBefore M w (edit f a b d) k = stockBefore M w f k := by
              intro f a b d k hka hab
              unfold stockBefore
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              have hi' := Finset.mem_range.mp hi
              simp [edit, show i ≠ a by omega, show i ≠ b by omega]
            have heditcost : ∀ (f : ℕ → ℝ) (a b : ℕ) (d : ℝ), a < b → b ≤ M.T →
                M.nominalCost w (edit f a b d) = M.nominalCost w f +
                (M.C (f a+d)-M.C (f a)) + (if b < M.T then M.C (f b-d)-M.C (f b) else 0) +
                ∑ k ∈ Finset.Ico a b, (M.R (M.stock w f k+d)-M.R (M.stock w f k)) := by
              intro f a b d hab hb
              have haT : a < M.T := by omega
              have heach : ∀ k ∈ Finset.range M.T,
                  M.C (edit f a b d k) + M.R (M.stock w (edit f a b d) k) =
                  (M.C (f k)+M.R (M.stock w f k)) +
                  (if k=a then M.C (f a+d)-M.C (f a) else 0) +
                  (if k=b then M.C (f b-d)-M.C (f b) else 0) +
                  (if k ∈ Finset.Ico a b then M.R (M.stock w f k+d)-M.R (M.stock w f k) else 0) := by
                intro k hk
                rw [heditstock]
                by_cases hka : k=a
                · subst k
                  simp [edit, ne_of_lt hab, hab, show ¬ b ≤ a by omega]
                  <;> ring
                · by_cases hkb : k=b
                  · subst k
                    simp [edit, hka, hab.le]
                    <;> ring
                  · by_cases hkI : k ∈ Finset.Ico a b
                    · have hkI' := Finset.mem_Ico.mp hkI
                      simp [edit, hka, hkb, hkI, hkI'.1, show ¬ b ≤ k by omega]
                      <;> ring
                    · have heq : (if a ≤ k then d else 0) - (if b ≤ k then d else 0) = 0 := by
                        simp only [Finset.mem_Ico] at hkI
                        split_ifs <;> (try omega) <;> ring
                      have heq' : M.stock w f k + (if a ≤ k then d else 0) - (if b ≤ k then d else 0) = M.stock w f k := by linarith
                      simp [edit, hka, hkb, hkI, heq']
              unfold Model.nominalCost
              rw [Finset.sum_congr rfl heach]
              simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, if_pos haT, Finset.sum_ite_mem]
              have hinter : Finset.range M.T ∩ Finset.Ico a b = Finset.Ico a b := by
                apply Finset.inter_eq_right.mpr
                intro k hk
                exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hb)
              rw [hinter]
            have hCnonneg : ∀ q : ℝ, 0 ≤ q → M.C q = M.K + M.c*q - (if q=0 then M.K else 0) := by
              intro q hq
              by_cases hq0 : q=0
              · simp [Model.C, hq0]
              · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
                simp [Model.C, hq0, hqpos]
            have hlocal : ∀ j ∈ Finset.Icc 1 J, ∀ f : ℕ → ℝ,
                M.IsNominalOptimal w f → IsOrderingTimes M.T f J t →
                ∃ g : ℕ → ℝ, M.IsNominalOptimal w g ∧ IsOrderingTimes M.T g J t ∧
                  stockBefore M w g (t j) + g (t j) = upperThreshold M w J t j ∧
                  (∀ k < t j, g k=f k) ∧
                  (∀ k ≤ t j, stockBefore M w g k = stockBefore M w f k) ∧
                  floorIndex M J t j < intervalLength t j := by
              intro j hj f hf hft
              let a := t j
              let b := t (j+1)
              let y := stockBefore M w f a + f a
              let S := upperThreshold M w J t j
              let γ : ℝ := if j=J then M.c else 0
              let H : ℝ → ℝ := fun x => ∑ k ∈ Finset.Ico a b, M.R (x-(W (k+1)-W a))
              let F : ℝ → ℝ := fun x => γ*x + H x
              have hab : a < b := ht.2.1 j hj
              have haT : a < M.T := htbound j hj
              have hj' := Finset.mem_Icc.mp hj
              have hb : b ≤ M.T := by
                have hh := htmono (i:=j+1) (j:=J+1) (by omega) (by omega) le_rfl
                simpa [ht.1, b] using hh
              have hbiff : b < M.T ↔ j ≠ J := by
                constructor
                · intro hh he
                  subst j
                  simpa [b, ht.1] using hh
                · intro hh
                  exact htbound (j+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
              have hfa : 0 < f a := ((hft.2.2 a).mpr ⟨j,hj,rfl⟩).2
              have hfb : b < M.T → 0 < f b := by
                intro hbT
                exact ((hft.2.2 b).mpr ⟨j+1, Finset.mem_Icc.mpr ⟨by omega, by have := hbiff.mp hbT; omega⟩,rfl⟩).2
              have hgood : ∀ d : ℝ, 0 ≤ f a+d → (b < M.T → 0 ≤ f b-d) → F (y+d) ≤ F y →
                  0 < f a+d ∧ (b < M.T → 0 < f b-d) ∧
                  M.IsNominalOptimal w (edit f a b d) ∧ IsOrderingTimes M.T (edit f a b d) J t := by
                intro d hqa hqb hF
                let A : ℝ := if f a+d=0 then M.K else 0
                let B : ℝ := if b < M.T ∧ f b-d=0 then M.K else 0
                have hA : 0 ≤ A := by dsimp [A]; split_ifs <;> linarith
                have hB : 0 ≤ B := by dsimp [B]; split_ifs <;> linarith
                have hfeas : ∀ k < M.T, 0 ≤ edit f a b d k := by
                  intro k hk
                  by_cases hka : k=a
                  · subst k
                    simpa [edit, ne_of_lt hab] using hqa
                  · by_cases hkb : k=b
                    · subst k
                      simpa [edit, hka] using hqb hk
                    · simpa [edit, hka, hkb] using hf.1 k hk
                have hRsum : (∑ k ∈ Finset.Ico a b, (M.R (M.stock w f k+d)-M.R (M.stock w f k))) = H (y+d)-H y := by
                  dsimp [H]
                  rw [← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [hstockcycle f hf.1 hft j hj k hk]
                  change M.R (y-(W (k+1)-W a)+d)-M.R (y-(W (k+1)-W a)) = _
                  rw [show y-(W (k+1)-W a)+d = (y+d)-(W (k+1)-W a) by ring]
                have hcost := heditcost f a b d hab hb
                rw [hRsum] at hcost
                have hcostle : M.nominalCost w (edit f a b d) ≤ M.nominalCost w f - A-B := by
                  have hca : M.C (f a) = M.K+M.c*f a := by simp [Model.C, hfa]
                  rw [hca, hCnonneg _ hqa] at hcost
                  by_cases hbT : b < M.T
                  · have hcb : M.C (f b) = M.K+M.c*f b := by simp [Model.C, hfb hbT]
                    rw [if_pos hbT, hcb, hCnonneg _ (hqb hbT)] at hcost
                    have hγ : γ=0 := by simp [γ, hbiff.mp hbT]
                    change γ*(y+d)+H (y+d) ≤ γ*y+H y at hF
                    rw [hγ] at hF
                    dsimp [A, B]
                    simp only [hbT, true_and]
                    nlinarith only [hcost, hF]
                  · rw [if_neg hbT] at hcost
                    have hjJ : j=J := by simpa only [not_not] using (not_congr hbiff).mp hbT
                    have hγ : γ=M.c := by simp [γ,hjJ]
                    change γ*(y+d)+H (y+d) ≤ γ*y+H y at hF
                    rw [hγ] at hF
                    dsimp [A, B]
                    simp only [hbT, false_and, if_false, sub_zero]
                    nlinarith only [hcost, hF]
                have hopt := hf.2 (edit f a b d) hfeas
                have hqaPos : 0 < f a+d := by
                  by_contra hn
                  have hq0 : f a+d=0 := by linarith
                  have hAK : A=M.K := by simp [A,hq0]
                  linarith
                have hqbPos : b < M.T → 0 < f b-d := by
                  intro hbT
                  by_contra hn
                  have hq0 : f b-d=0 := by linarith [hqb hbT]
                  have hBK : B=M.K := by simp [B,hbT,hq0]
                  linarith
                have hnewopt : M.IsNominalOptimal w (edit f a b d) := by
                  refine ⟨hfeas, fun g hg => ?_⟩
                  exact (hcostle.trans (by linarith)).trans (hf.2 g hg)
                have hsup : ∀ k < M.T, (0 < edit f a b d k ↔ 0 < f k) := by
                  intro k hk
                  by_cases hka : k=a
                  · subst k
                    simp [edit, ne_of_lt hab, hqaPos, hfa]
                  · by_cases hkb : k=b
                    · subst k
                      simp [edit, hka, hqbPos hk, hfb hk]
                    · simp [edit,hka,hkb]
                have hnewt : IsOrderingTimes M.T (edit f a b d) J t := by
                  refine ⟨hft.1, hft.2.1, fun k => ?_⟩
                  constructor
                  · rintro ⟨hk, hpos⟩
                    exact (hft.2.2 k).mp ⟨hk, (hsup k hk).mp hpos⟩
                  · intro hk
                    obtain ⟨hkT,hpos⟩ := (hft.2.2 k).mpr hk
                    exact ⟨hkT,(hsup k hkT).mpr hpos⟩
                exact ⟨hqaPos,hqbPos,hnewopt,hnewt⟩
              have hIstrict : floorIndex M J t j < intervalLength t j := by
                by_contra hn
                let L := intervalLength t j
                let I := floorIndex M J t j
                have hLI : L ≤ I := Nat.le_of_not_gt hn
                have hL : 1 ≤ L := by dsimp [L, intervalLength]; change 1 ≤ b-a; omega
                have hγnonneg : 0 ≤ γ := by dsimp [γ]; split_ifs <;> linarith [M.hc]
                have hγc : γ ≤ M.c := by dsimp [γ]; split_ifs <;> linarith [M.hc]
                have hLreal : (1:ℝ) ≤ L := by exact_mod_cast hL
                have hLIreal : (L:ℝ) ≤ I := by exact_mod_cast hLI
                have hnum : 0 ≤ M.p*(L:ℝ)-γ := by nlinarith [M.hpc]
                have hlo : (M.h+M.p)*(I:ℝ) ≤ M.p*(L:ℝ)-γ := by
                  have hh := Nat.floor_le (div_nonneg hnum hhp.le)
                  change (I:ℝ) ≤ (M.p*(L:ℝ)-γ)/(M.h+M.p) at hh
                  have hh' := (le_div_iff₀ hhp).mp hh
                  nlinarith
                have hLIprod := mul_le_mul_of_nonneg_left hLIreal hhp.le
                have hhzero : M.h=0 := by nlinarith [M.hh]
                have hjne : j ≠ J := by
                  intro he
                  have hγeq : γ=M.c := by simp [γ,he]
                  rw [hγeq,hhzero] at hlo
                  nlinarith [M.hc]
                have hbT : b < M.T := hbiff.mpr hjne
                have hF : F (y+f b) ≤ F y := by
                  have hγeq : γ=0 := by simp [γ,hjne]
                  dsimp [F]
                  rw [hγeq]
                  simp only [zero_mul, zero_add]
                  dsimp [H]
                  apply Finset.sum_le_sum
                  intro k hk
                  have hh := hRupper (y-(W (k+1)-W a)) (y+f b-(W (k+1)-W a)) (by linarith [hfb hbT])
                  rw [hhzero] at hh
                  nlinarith only [hh]
                have hh := (hgood (f b) (by linarith [hfb hbT]) (by intro; linarith) hF).2.1 hbT
                linarith
              have hmono := hcycle j hj
              change (∀ x y, x ≤ y → y ≤ S → F y ≤ F x) ∧ (∀ x y, S ≤ x → x ≤ y → F x ≤ F y) at hmono
              have hlower : stockBefore M w f a < S := by
                by_contra hn
                have hpre : S ≤ stockBefore M w f a := le_of_not_gt hn
                have hy : y-f a = stockBefore M w f a := by dsimp [y]; ring
                have hF : F (y+(-f a)) ≤ F y := by
                  rw [show y+(-f a)=stockBefore M w f a by dsimp [y]; ring]
                  exact hmono.2 _ _ hpre (by dsimp [y]; linarith)
                have hh := (hgood (-f a) (by linarith) (by intro hbT; linarith [hfb hbT]) hF).1
                linarith
              have hupper : b < M.T → S < y+f b := by
                intro hbT
                by_contra hn
                have hSy : y+f b ≤ S := le_of_not_gt hn
                have hh := (hgood (f b) (by linarith [hfb hbT]) (by intro; linarith)
                  (hmono.1 _ _ (by linarith [hfb hbT]) hSy)).2.1 hbT
                linarith
              let d := S-y
              have hF : F (y+d) ≤ F y := by
                have hyd : y+d=S := by dsimp [d]; ring
                rw [hyd]
                by_cases hyS : y ≤ S
                · exact hmono.1 _ _ hyS le_rfl
                · exact hmono.2 _ _ le_rfl (le_of_not_ge hyS)
              have hg := hgood d (by dsimp [d,y]; linarith) (by intro hbT; dsimp [d]; linarith [hupper hbT]) hF
              refine ⟨edit f a b d, hg.2.2.1, hg.2.2.2, ?_, ?_, ?_, hIstrict⟩
              · change stockBefore M w (edit f a b d) a + edit f a b d a = S
                rw [heditbefore f a b d a le_rfl hab]
                simp only [edit, if_true, if_neg (ne_of_lt hab), sub_zero]
                dsimp [d,y,S,a]
                ring
              · intro k hk
                simp [edit, show k ≠ a by omega, show k ≠ b by omega]
              · intro k hk
                exact heditbefore f a b d k hk hab
            have hindex : ∀ j ∈ Finset.Icc 1 J, floorIndex M J t j < intervalLength t j := by
              intro j hj
              obtain ⟨g, hg, hgt, hpost, hsame, hbefore, hidx⟩ := hlocal j hj u hu ht
              exact hidx
            have hbuild : ∀ n : ℕ, n ≤ J → ∃ f : ℕ → ℝ,
                M.IsNominalOptimal w f ∧ IsOrderingTimes M.T f J t ∧
                ∀ i ∈ Finset.Icc 1 n, stockBefore M w f (t i) + f (t i) = upperThreshold M w J t i := by
              intro n
              induction n with
              | zero =>
                intro hn
                refine ⟨u,hu,ht,?_⟩
                intro i hi
                have := Finset.mem_Icc.mp hi
                omega
              | succ n ih =>
                intro hn
                obtain ⟨f,hf,hft,hposts⟩ := ih (by omega)
                obtain ⟨g,hg,hgt,hpost,hsame,hbefore,hidx⟩ :=
                  hlocal (n+1) (Finset.mem_Icc.mpr ⟨by omega,hn⟩) f hf hft
                refine ⟨g,hg,hgt,?_⟩
                intro i hi
                have hi' := Finset.mem_Icc.mp hi
                by_cases he : i=n+1
                · simpa [he] using hpost
                · have hti : t i < t (n+1) := htstrict hi'.1 (by omega) (by omega)
                  rw [hbefore (t i) hti.le, hsame (t i) hti]
                  exact hposts i (Finset.mem_Icc.mpr ⟨hi'.1,by omega⟩)
            obtain ⟨v,hv,hvt,hposts⟩ := hbuild J le_rfl
            refine ⟨v,hv,hvt,?_⟩
            intro j hj
            refine ⟨?_,hposts j hj⟩
            by_cases hj1 : j=1
            · subst j
              have hsum : (∑ i ∈ Finset.range (t 1), v i) = 0 := by
                apply Finset.sum_eq_zero
                intro i hi
                have hi' := Finset.mem_range.mp hi
                have hiT : i < M.T := lt_trans hi' (htbound 1 hj)
                by_contra hn
                have hipos : 0 < v i := lt_of_le_of_ne (hv.1 i hiT) (Ne.symm hn)
                obtain ⟨q,hq,hqi⟩ := (hvt.2.2 i).mp ⟨hiT,hipos⟩
                have hq' := Finset.mem_Icc.mp hq
                have hh := htmono (i:=1) (j:=q) le_rfl hq'.1 (by omega)
                omega
              simp only [lowerThreshold, if_true, stockBefore, Finset.sum_sub_distrib, hsum, zero_sub]
              ring
            · have hj' := Finset.mem_Icc.mp hj
              have hjprev : j-1 ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
              have hjadd : j-1+1=j := by omega
              have hab : t (j-1) < t j := by simpa [hjadd] using ht.2.1 (j-1) hjprev
              have hpath' := hpath v (t (j-1)) (t j) hab (fun k hk hkj =>
                hzero v hv.1 hvt (j-1) hjprev k hk (by simpa [hjadd] using hkj))
              rw [hposts (j-1) hjprev] at hpath'
              rw [hpath', lowerThreshold, if_neg hj1]
              let a := t (j-1)
              let L := intervalLength t (j-1)
              let I := floorIndex M J t (j-1)
              have hIL : I+1 ≤ L := hindex (j-1) hjprev
              have hSsum := Finset.sum_range_add_sum_Ico (fun i => w (a+i)) hIL
              have hfull : (∑ i ∈ Finset.range L, w (a+i)) = W (t j)-W a := by
                have hh := Finset.sum_Ico_eq_sum_range w a (t j)
                rw [Finset.sum_Ico_eq_sub w hab.le] at hh
                simpa only [L, intervalLength, hjadd, a] using hh.symm
              change (∑ i ∈ Finset.range (I+1), w (a+i)) - (W (t j)-W a) =
                -∑ i ∈ Finset.Ico (I+1) L, w (a+i)
              rw [← hfull]
              linarith
