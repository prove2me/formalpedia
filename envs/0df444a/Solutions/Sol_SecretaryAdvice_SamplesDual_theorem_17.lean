-- Prove2me | solution 1 for SecretaryAdvice.SamplesDual.theorem_17
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T08:41:15.054175+00:00
-- url     : https://prove2.me/submissions/8864fb6b-656a-4f0b-b5c0-9d5b42081834

-- Licensed under Apache 2.0. Full sampled-secretary greedy dual closed form.
import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

open Finset


open Finset

namespace SamplesDualProof

noncomputable def riseProd (x : ℝ) (r : ℕ) : ℝ := ∏ a ∈ Finset.range r, (x+a)

@[simp] lemma riseProd_zero (x : ℝ) : riseProd x 0 = 1 := by simp [riseProd]

lemma riseProd_succ_right (x : ℝ) (r : ℕ) :
    riseProd x (r+1) = riseProd x r * (x+r) := by
  exact Finset.prod_range_succ _ _

lemma riseProd_succ_left (x : ℝ) (r : ℕ) :
    riseProd x (r+1) = x * riseProd (x+1) r := by
  unfold riseProd
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  ring

lemma riseProd_shift (x : ℝ) (r : ℕ) :
    riseProd (x+1) r - riseProd x r = r * riseProd (x+1) (r-1) := by
  cases r with
  | zero => simp
  | succ r =>
    rw [riseProd_succ_right, riseProd_succ_left]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

lemma riseProd_sub_one (x : ℝ) (r : ℕ) :
    riseProd (x-1) r = riseProd x r - r * riseProd x (r-1) := by
  have hh := riseProd_shift (x-1) r
  rw [sub_add_cancel] at hh
  linarith

lemma riseProd_Icc (x : ℝ) (a b : ℕ) :
    (∏ t ∈ Finset.Icc a b, (x+t)) = riseProd (x+a) (b+1-a) := by
  have he : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, Finset.prod_Ico_eq_prod_range]
  unfold riseProd
  apply Finset.prod_congr rfl
  intro t _
  push_cast
  ring

lemma riseProd_at_zero {r : ℕ} (hr : 0 < r) : riseProd 0 r = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [riseProd_succ_left, zero_mul]

lemma choose_cast_step (m j : ℕ) :
    ((m.choose (j+1) : ℕ) : ℝ) * (j+1) = (m.choose j : ℝ) * (m-j : ℕ) := by
  exact_mod_cast Nat.choose_succ_right_eq m j

end SamplesDualProof


open Finset

namespace SamplesDualProof

noncomputable def keyPoly (m : ℕ) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, ((m.choose (j+1) : ℝ)/(j+1)) *
    riseProd x (j+1) * riseProd y (m-(j+1))

lemma product_difference_term (c x y : ℝ) (j q : ℕ) :
    c/(j+1) * riseProd x (j+1) * riseProd y q -
      c/(j+1) * riseProd (x-1) (j+1) * riseProd (y+1) q =
    c * riseProd x j * riseProd (y+1) q -
      c/(j+1) * q * riseProd x (j+1) * riseProd (y+1) (q-1) := by
  have he : riseProd y q = riseProd (y+1) q - q * riseProd (y+1) (q-1) := by
    have hh := riseProd_shift y q
    linarith
  rw [he, riseProd_sub_one]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hj : (j : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

lemma keyPoly_difference (m : ℕ) (x y : ℝ) :
    keyPoly (m+1) x y - keyPoly (m+1) (x-1) (y+1) =
      (m+1) * riseProd (y+1) m -
      ∑ j ∈ Finset.range m, ((m+1).choose (j+2) : ℝ)/(j+1) *
        riseProd x (j+1) * riseProd (y+1) (m-(j+1)) := by
  unfold keyPoly
  rw [← Finset.sum_sub_distrib]
  simp_rw [product_difference_term]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ' (fun j =>
    ((m+1).choose (j+1) : ℝ) * riseProd x j * riseProd (y+1) (m+1-(j+1)))]
  rw [Finset.sum_range_succ (fun j =>
    ((m+1).choose (j+1) : ℝ)/(j+1) * (m+1-(j+1) : ℕ) *
      riseProd x (j+1) * riseProd (y+1) (m+1-(j+1)-1))]
  simp only [Nat.add_sub_add_right, Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul,
    add_zero, Nat.zero_add, Nat.choose_one_right, riseProd_zero, mul_one]
  have he : ∀ j ∈ Finset.range m,
      ((m+1).choose (j+1+1) : ℝ) * riseProd x (j+1) * riseProd (y+1) (m-(j+1)) -
      ((m+1).choose (j+1) : ℝ)/(j+1) * (m-j : ℕ) *
        riseProd x (j+1) * riseProd (y+1) (m-j-1) =
      -(((m+1).choose (j+2) : ℝ)/(j+1) * riseProd x (j+1) * riseProd (y+1) (m-(j+1))) := by
    intro j hj
    have hn : m-j-1 = m-(j+1) := by omega
    rw [hn]
    have hc := choose_cast_step (m+1) (j+1)
    simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one] at hc
    have hjn : (j : ℝ)+1 ≠ 0 := by positivity
    have ha : j+1+1=j+2 := by omega
    rw [ha]
    field_simp
    linear_combination (riseProd x (j+1) * riseProd (y+1) (m-(j+1))) * hc
  have hs := Finset.sum_congr rfl he
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  linarith

end SamplesDualProof


open Finset

namespace SamplesDualProof

lemma reverse_hockey_stick {n i j : ℕ} (hin : i < n) (hj : 1 ≤ j) :
    (∑ z ∈ Finset.Icc (i+1) (n-1), (n-z).choose j) = (n-i).choose (j+1) := by
  have hreindex : (∑ z ∈ Finset.Icc (i+1) (n-1), (n-z).choose j) =
      ∑ r ∈ Finset.Icc 1 (n-i-1), r.choose j := by
    apply Finset.sum_nbij (fun z => n-z)
    · intro z hz
      simp only [Finset.mem_Icc] at hz ⊢
      omega
    · intro z hz w hw he
      have hz' := Finset.mem_Icc.mp hz
      have hw' := Finset.mem_Icc.mp hw
      change n-z = n-w at he
      omega
    · intro r hr
      have hr' := Finset.mem_Icc.mp hr
      refine ⟨n-r, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · change n-(n-r)=r
        omega
    · intro z _
      rfl
  rw [hreindex]
  have hsub : Finset.Icc j (n-i-1) ⊆ Finset.Icc 1 (n-i-1) := by
    intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  rw [← Finset.sum_subset hsub]
  · rw [Nat.sum_Icc_choose]
    congr 1
    omega
  · intro r hr hnot
    apply Nat.choose_eq_zero_of_lt
    simp only [Finset.mem_Icc, not_and] at hr hnot
    omega

lemma triangular_choose_sum {n i : ℕ} (hin : i < n) (f : ℕ → ℝ) :
    (∑ z ∈ Finset.Icc (i+1) (n-1), ∑ j ∈ Finset.Icc 1 (n-z),
      ((n-z).choose j : ℝ) * f j) =
    ∑ j ∈ Finset.Icc 1 (n-i-1), ((n-i).choose (j+1) : ℝ) * f j := by
  calc
    _ = ∑ z ∈ Finset.Icc (i+1) (n-1), ∑ j ∈ Finset.Icc 1 (n-i-1),
        ((n-z).choose j : ℝ) * f j := by
      apply Finset.sum_congr rfl
      intro z hz
      have hsub : Finset.Icc 1 (n-z) ⊆ Finset.Icc 1 (n-i-1) := by
        intro j hj
        simp only [Finset.mem_Icc] at hz hj ⊢
        omega
      apply Finset.sum_subset hsub
      intro j hj hnot
      have hlt : n-z < j := by
        simp only [Finset.mem_Icc, not_and] at hj hnot
        omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
    _ = ∑ j ∈ Finset.Icc 1 (n-i-1), ∑ z ∈ Finset.Icc (i+1) (n-1),
        ((n-z).choose j : ℝ) * f j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast reverse_hockey_stick hin (Finset.mem_Icc.mp hj).1

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

lemma sum_Icc_one_eq_range (m : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 m, f j) = ∑ j ∈ Finset.range m, f (j+1) := by
  have he : Finset.Icc 1 m = Finset.Ico 1 (m+1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  omega

lemma native_keyPoly {n i : ℕ} (hi : 1 ≤ i) (_hin : i < n) (k s : ℕ) :
    keyRHS n k i s = keyPoly (n-i) ((k:ℝ)-s+1) ((s:ℝ)+i) := by
  unfold keyRHS keyPoly
  rw [sum_Icc_one_eq_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [riseProd_Icc, riseProd_Icc]
  have hlen : n-(j+1)-1+1-i = n-i-(j+1) := by omega
  simp only [Nat.add_sub_cancel, Nat.cast_one, Nat.cast_add, hlen]
  ring

lemma native_T_normal {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (k s : ℕ) :
    T n k i s = (n-i : ℕ) * riseProd ((s:ℝ)+i+1) (n-i-1) -
      ∑ j ∈ Finset.range (n-i-1), ((n-i).choose (j+2) : ℝ)/(j+1) *
        riseProd ((k:ℝ)-s+1) (j+1) * riseProd ((s:ℝ)+i+1) (n-i-1-(j+1)) := by
  have hs := triangular_choose_sum hin (fun j => (1/(j:ℝ)) *
    (∏ ℓ ∈ Finset.Icc 1 j, ((k:ℝ)-s+ℓ)) *
    (∏ t ∈ Finset.Icc (i+1) (n-j-1), ((s:ℝ)+t)))
  unfold T
  simp only [mul_assoc] at hs
  simp only [mul_assoc]
  rw [hs]
  rw [riseProd_Icc, sum_Icc_one_eq_range]
  have hn : n-1+1-(i+1)=n-i-1 := by omega
  rw [hn, Nat.cast_sub hin.le]
  simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [riseProd_Icc, riseProd_Icc]
  have hlen : n-(j+1)-1+1-(i+1)=n-i-1-(j+1) := by omega
  simp only [Nat.add_sub_cancel, Nat.cast_one, Nat.cast_add, hlen, ← add_assoc]
  ring

lemma native_key_difference {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (k s : ℕ) :
    keyRHS n k i s - keyRHS n k i (s+1) = T n k i s := by
  rw [native_keyPoly hi hin, native_keyPoly hi hin, native_T_normal hi hin]
  have hm : n-i=(n-i-1)+1 := by omega
  have hdiff := keyPoly_difference (n-i-1) ((k:ℝ)-s+1) ((s:ℝ)+i)
  rw [← hm] at hdiff
  simp only [Nat.cast_add, Nat.cast_one]
  have hx : (k:ℝ)-(s+1)+1 = ((k:ℝ)-s+1)-1 := by ring
  have hy : (s:ℝ)+1+i = ((s:ℝ)+i)+1 := by ring
  rw [hx, hy]
  have hcast : (n-i : ℕ) = (n-i-1)+1 := hm
  have hreal : ((n-i : ℕ) : ℝ) = (n-i-1 : ℕ)+1 := by exact_mod_cast hcast
  rw [← hreal] at hdiff
  exact hdiff

lemma native_key_terminal {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (k : ℕ) :
    keyRHS n k i (k+1) = 0 := by
  rw [native_keyPoly hi hin]
  have he : (k:ℝ)-(k+1)+1=0 := by ring
  simp only [Nat.cast_add, Nat.cast_one, he, keyPoly]
  apply Finset.sum_eq_zero
  intro j _
  rw [riseProd_at_zero (by omega : 0 < j+1), mul_zero, zero_mul]

end SamplesDualProof


open Finset SecretaryAdvice.SamplesDual

namespace SamplesDualProof

lemma key_sum_identity {n k i s : ℕ} (hi : 1 ≤ i) (hin : i < n) (hs : s ≤ k) :
    (∑ s' ∈ Finset.Icc s k, T n k i s') = keyRHS n k i s := by
  have ht := Finset.sum_Icc_sub hs (fun j => keyRHS n k i j)
  have he : (∑ j ∈ Finset.Icc s k, T n k i j) =
      -(∑ j ∈ Finset.Icc s k, (keyRHS n k i (j+1) - keyRHS n k i j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← native_key_difference hi hin]
    ring
  rw [he, ht, native_key_terminal hi hin, zero_sub, neg_neg]

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

lemma greedy_eq_max_of_positive_future {S : Type*} [Fintype S]
    (n : ℕ) (a : ℕ → S → ℝ) (c : ℕ → S → ℕ → S → ℝ)
    (F : ℕ → S → ℝ)
    (ha : ∀ s, 0 ≤ a n s)
    (hbase : ∀ s, F n s = a n s)
    (hrec : ∀ i, 1 ≤ i → i < n → ∀ s,
      F i s = a i s - ∑ j ∈ (Ioc i n).attach, ∑ s', F j.1 s' * c j.1 s' i s)
    (hc : ∀ i j s s', 1 ≤ i → i < j → j ≤ n → 0 ≤ c j s' i s)
    (hfuture : ∀ i j s s', 1 ≤ i → i < j → j ≤ n →
      0 < F i s → c j s' i s ≠ 0 → 0 < F j s') :
    ∀ i, 1 ≤ i → i ≤ n → ∀ s, greedyDual n a c i s = max 0 (F i s) := by
  intro i hi hin
  generalize he : n - i = d
  induction d using Nat.strong_induction_on generalizing i with
  | h d ih =>
    intro s
    by_cases hlt : i < n
    · rw [greedyDual, if_pos hlt]
      have hreplace :
          (∑ j ∈ (Ioc i n).attach, ∑ s', greedyDual n a c j.1 s' * c j.1 s' i s) =
          ∑ j ∈ (Ioc i n).attach, ∑ s', max 0 (F j.1 s') * c j.1 s' i s := by
        apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intro s' _
        have hj := mem_Ioc.mp j.2
        rw [ih (n - j.1) (by omega) j.1 (by omega) hj.2 rfl]
      rw [hreplace]
      by_cases hp : 0 < F i s
      · congr 1
        rw [hrec i hi hlt s]
        congr 1
        apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intro s' _
        by_cases hz : c j.1 s' i s = 0
        · simp [hz]
        · have hj := mem_Ioc.mp j.2
          rw [max_eq_right (le_of_lt (hfuture i j.1 s s' hi hj.1 hj.2 hp hz))]
      · rw [max_eq_left (le_of_not_gt hp)]
        apply max_eq_left
        have hsum :
            (∑ j ∈ (Ioc i n).attach, ∑ s', F j.1 s' * c j.1 s' i s) ≤
            ∑ j ∈ (Ioc i n).attach, ∑ s', max 0 (F j.1 s') * c j.1 s' i s := by
          apply sum_le_sum
          intro j _
          apply sum_le_sum
          intro s' _
          have hj := mem_Ioc.mp j.2
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hc i j.1 s s' hi hj.1 hj.2)
        have hr := hrec i hi hlt s
        linarith
    · have hie : i = n := by omega
      subst i
      rw [greedyDual, if_neg (lt_irrefl n), hbase, max_eq_right (ha s)]

lemma coeffA_pos {n k s : ℕ} (_hn : 1 ≤ n) : 0 < coeffA n k s := by
  unfold coeffA
  apply mul_pos
  · positivity
  · apply prod_pos
    intro t ht
    have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
    have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    exact div_pos (by positivity) (by positivity)

lemma coeffC_nonneg (s' i s : ℕ) : 0 ≤ coeffC s' i s := by
  unfold coeffC
  split_ifs
  · positivity
  · rfl

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

noncomputable def deficitTerm (n k s j : ℕ) : ℝ :=
  (1 / (j : ℝ)) * (∏ l ∈ Icc 1 j, ((k : ℝ) - s + l)) /
    (∏ t ∈ Icc (n - j) (n - 1), ((s : ℝ) + t))

noncomputable def deficit (n k i s : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (n - i), ((n - i).choose j : ℝ) * deficitTerm n k s j

lemma deficitTerm_nonneg {n k s j : ℕ} (hs : s ≤ k) :
    0 ≤ deficitTerm n k s j := by
  unfold deficitTerm
  apply div_nonneg
  · apply mul_nonneg (by positivity)
    apply prod_nonneg
    intro l _
    have : (s : ℝ) ≤ k := by exact_mod_cast hs
    positivity
  · positivity

lemma deficitTerm_antitone_signal {n k s s' j : ℕ}
    (hss : s ≤ s') (hs' : s' ≤ k) (hj : j < n) :
    deficitTerm n k s' j ≤ deficitTerm n k s j := by
  have hs : s ≤ k := hss.trans hs'
  have hcast : (s : ℝ) ≤ s' := by exact_mod_cast hss
  have hk : (s' : ℝ) ≤ k := by exact_mod_cast hs'
  have hnum :
      (∏ l ∈ Icc 1 j, ((k : ℝ) - s' + l)) ≤
      ∏ l ∈ Icc 1 j, ((k : ℝ) - s + l) := by
    apply prod_le_prod
    · intro l _; positivity
    · intro l _; linarith
  have hden :
      (∏ t ∈ Icc (n - j) (n - 1), ((s : ℝ) + t)) ≤
      ∏ t ∈ Icc (n - j) (n - 1), ((s' : ℝ) + t) := by
    apply prod_le_prod
    · intro t _; positivity
    · intro t _; linarith
  have hdpos : 0 < ∏ t ∈ Icc (n - j) (n - 1), ((s : ℝ) + t) := by
    apply prod_pos
    intro t ht
    have ht0 : 0 < t := by have := (mem_Icc.mp ht).1; omega
    have : (0 : ℝ) < t := by exact_mod_cast ht0
    positivity
  unfold deficitTerm
  apply div_le_div₀
  · apply mul_nonneg (by positivity)
    apply prod_nonneg
    intro l _
    have : (s : ℝ) ≤ k := by exact_mod_cast hs
    positivity
  · exact mul_le_mul_of_nonneg_left hnum (by positivity)
  · exact hdpos
  · exact hden

lemma deficit_antitone_round {n k i z s : ℕ} (hiz : i ≤ z) (hs : s ≤ k) :
    deficit n k z s ≤ deficit n k i s := by
  unfold deficit
  calc
    _ ≤ ∑ j ∈ Icc 1 (n-z), ((n-i).choose j : ℝ) * deficitTerm n k s j := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (deficitTerm_nonneg hs)
      exact_mod_cast Nat.choose_le_choose j (Nat.sub_le_sub_left hiz n)
    _ ≤ _ := ?_
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [mem_Icc] at hj ⊢
    exact ⟨hj.1, hj.2.trans (Nat.sub_le_sub_left hiz n)⟩
  · intro j _ _
    exact mul_nonneg (by positivity) (deficitTerm_nonneg hs)

lemma deficit_antitone_signal {n k i s s' : ℕ} (hi : 1 ≤ i)
    (hss : s ≤ s') (hs' : s' ≤ k) :
    deficit n k i s' ≤ deficit n k i s := by
  unfold deficit
  apply sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left (deficitTerm_antitone_signal hss hs' ?_) (by positivity)
  have := mem_Icc.mp hj
  omega

lemma positive_future_of_normalized_deficit
    (n k : ℕ) (F : ℕ → ℕ → ℝ)
    (hA : ∀ s, 0 < coeffA n k s)
    (hF : ∀ i s, 1 ≤ i → i ≤ n → s ≤ k →
      F i s = coeffA n k s * (1 - deficit n k i s))
    {i z s s' : ℕ} (hi : 1 ≤ i) (hiz : i ≤ z) (hzn : z ≤ n)
    (hss : s ≤ s') (hs' : s' ≤ k) (hp : 0 < F i s) : 0 < F z s' := by
  have hin : i ≤ n := hiz.trans hzn
  have hs : s ≤ k := hss.trans hs'
  rw [hF i s hi hin hs] at hp
  have hd : deficit n k i s < 1 := by
    have := (mul_pos_iff_of_pos_left (hA s)).mp hp
    linarith
  have hds : deficit n k z s' ≤ deficit n k i s :=
    (deficit_antitone_signal (by omega) hss hs').trans (deficit_antitone_round hiz hs)
  rw [hF z s' (by omega) hzn hs']
  exact mul_pos (hA s') (by linarith)

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

lemma prod_Icc_split_real (f : ℕ → ℝ) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (∏ t ∈ Icc a (c - 1), f t) =
      (∏ t ∈ Icc a (b - 1), f t) * ∏ t ∈ Icc b (c - 1), f t := by
  have h1 : Icc a (c-1) = Ico a c := by ext t; simp only [mem_Icc, mem_Ico]; omega
  have h2 : Icc a (b-1) = Ico a b := by ext t; simp only [mem_Icc, mem_Ico]; omega
  have h3 : Icc b (c-1) = Ico b c := by ext t; simp only [mem_Icc, mem_Ico]; omega
  rw [h1, h2, h3]
  exact (prod_Ico_consecutive f hab hbc).symm

lemma shifted_prod_eq {n i j s : ℕ} (hi : 1 ≤ i) (_hj : j ≤ n-i) :
    (∏ l ∈ Icc 1 (n-i-j), ((s : ℝ)+i-1+l)) =
    ∏ t ∈ Icc i (n-j-1), ((s : ℝ)+t) := by
  have hleft : Icc 1 (n-i-j) = Ico 1 (n-i-j+1) := by
    ext t; simp only [mem_Icc, mem_Ico]; omega
  have hright : Icc i (n-j-1) = Ico i (n-j) := by
    ext t; simp only [mem_Icc, mem_Ico]; omega
  rw [hleft, hright, prod_Ico_eq_prod_range, prod_Ico_eq_prod_range]
  have hlen : n-j-i = n-i-j := by omega
  simp only [Nat.add_sub_cancel, hlen]
  apply prod_congr rfl
  intro t _
  push_cast
  ring

lemma denominator_prod_pos (k a b : ℕ) :
    0 < ∏ t ∈ Icc a b, ((k : ℝ)+t+1) := by
  apply prod_pos
  intro t _
  positivity

lemma numerator_prod_pos (s a b : ℕ) (ha : 1 ≤ a) :
    0 < ∏ t ∈ Icc a b, ((s : ℝ)+t) := by
  apply prod_pos
  intro t ht
  have : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < a) (mem_Icc.mp ht).1)
  positivity

lemma inner_eq_deficit {n k i s : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    innerFormula n k i s = coeffA n k s * (1 - deficit n k i s) := by
  have hn : 1 ≤ n := hi.trans hin
  have hP := prod_Icc_split_real (fun t => (s : ℝ)+t) hi hin hi hn
  have hD := prod_Icc_split_real (fun t => (k : ℝ)+t+1) hi hin hi hn
  have hprefix := ne_of_gt (numerator_prod_pos s 1 (i-1) (by omega))
  have htail := ne_of_gt (numerator_prod_pos s i (n-1) hi)
  have hden := ne_of_gt (denominator_prod_pos k i (n-1))
  have hdenpre := ne_of_gt (denominator_prod_pos k 1 (i-1))
  have hsum :
      (∑ j ∈ Icc 1 (n-i), ((n-i).choose j : ℝ) * (1/(j:ℝ)) *
        (∏ l ∈ Icc 1 j, ((k:ℝ)-s+l)) *
        (∏ l ∈ Icc 1 (n-i-j), ((s:ℝ)+i-1+l))) =
      (∏ t ∈ Icc i (n-1), ((s:ℝ)+t)) * deficit n k i s := by
    unfold deficit
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjn := (mem_Icc.mp hj).2
    rw [shifted_prod_eq hi hjn]
    have hsplit := prod_Icc_split_real (fun t => (s:ℝ)+t)
      (show i ≤ n-j by omega) (show n-j ≤ n by omega) (show 1 ≤ n-j by omega) hn
    have hd := ne_of_gt (numerator_prod_pos s (n-j) (n-1) (by omega))
    unfold deficitTerm
    rw [hsplit]
    field_simp
  unfold innerFormula coeffA
  simp only [prod_div_distrib]
  rw [hsum, hP, hD]
  field_simp

lemma unclippedFormula_eq_deficit {n k i s : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    unclippedFormula n k i s = coeffA n k s * (1 - deficit n k i s) := by
  unfold unclippedFormula
  split_ifs with h
  · subst i
    simp [deficit]
  · exact inner_eq_deficit hi hin

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

noncomputable def commonFactor (n k i s : ℕ) : ℝ :=
  (1 / ((k : ℝ)+1)) *
    (∏ t ∈ Icc 1 (i-1), ((s : ℝ)+t)) /
    (∏ t ∈ Icc 1 (n-1), ((k : ℝ)+t+1))

lemma keyRHS_eq_inner_sum {n k i s : ℕ} (hi : 1 ≤ i) :
    keyRHS n k i s =
      ∑ j ∈ Icc 1 (n-i), ((n-i).choose j : ℝ) * (1/(j:ℝ)) *
        (∏ l ∈ Icc 1 j, ((k:ℝ)-s+l)) *
        (∏ l ∈ Icc 1 (n-i-j), ((s:ℝ)+i-1+l)) := by
  unfold keyRHS
  apply sum_congr rfl
  intro j hj
  rw [shifted_prod_eq hi (mem_Icc.mp hj).2]

lemma unclippedFormula_eq_common {n k i s : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    unclippedFormula n k i s = commonFactor n k i s *
      ((∏ t ∈ Icc i (n-1), ((s:ℝ)+t)) - keyRHS n k i s) := by
  have hn : 1 ≤ n := hi.trans hin
  unfold unclippedFormula
  split_ifs with he
  · subst i
    have hempty : Icc n (n-1) = ∅ := by exact Icc_eq_empty_of_lt (by omega)
    simp [commonFactor, keyRHS, hempty, coeffA, prod_div_distrib]
    ring
  · rw [keyRHS_eq_inner_sum hi]
    unfold innerFormula commonFactor
    simp only [prod_div_distrib]
    rw [prod_Icc_split_real (fun t => (k:ℝ)+t+1) hi hin hi hn]
    have h1 := ne_of_gt (denominator_prod_pos k 1 (i-1))
    have h2 := ne_of_gt (denominator_prod_pos k i (n-1))
    field_simp

lemma coeffC_eq_ratio {s' i s : ℕ} (hi : 1 ≤ i) (hss : s ≤ s') :
    coeffC s' i s = (∏ t ∈ Icc 1 (i-1), ((s:ℝ)+t)) /
      (∏ t ∈ Icc 1 i, ((s':ℝ)+t)) := by
  unfold coeffC
  rw [if_pos hss, prod_div_distrib]
  have hshift : (∏ t ∈ Icc 1 (i-1), ((s':ℝ)+t+1)) =
      ∏ t ∈ Icc 2 i, ((s':ℝ)+t) := by
    convert shifted_prod_eq (n := i+1) (i := 2) (j := 0) (s := s') (by omega) (by omega) using 1 <;>
      try congr 1 <;> try omega
    funext t
    norm_num
    ring
  have hsplit := prod_Icc_split_real (fun t => (s':ℝ)+t)
    (show 1 ≤ 2 by omega) (show 2 ≤ i+1 by omega) (by omega) (by omega)
  simp only [Nat.add_sub_cancel, show (2:ℕ)-1=1 by omega, Icc_self, prod_singleton] at hsplit
  rw [hshift, hsplit]
  norm_num only [Nat.cast_one]
  have h1 : (s' : ℝ)+1 ≠ 0 := by positivity
  have h2 := ne_of_gt (numerator_prod_pos s' 2 i (by omega))
  field_simp

lemma common_mul_coeffC {n k i z s s' : ℕ}
    (hi : 1 ≤ i) (hiz : i < z) (hss : s ≤ s') :
    commonFactor n k z s' * coeffC s' i s =
      commonFactor n k i s * ∏ t ∈ Icc (i+1) (z-1), ((s':ℝ)+t) := by
  rw [coeffC_eq_ratio hi hss]
  unfold commonFactor
  have hsplit := prod_Icc_split_real (fun t => (s':ℝ)+t)
    (show 1 ≤ i+1 by omega) (show i+1 ≤ z by omega) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hsplit
  rw [hsplit]
  have hP := ne_of_gt (numerator_prod_pos s' 1 i (by omega))
  have hD := ne_of_gt (denominator_prod_pos k 1 (n-1))
  field_simp

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

lemma coeffA_eq_common {n k i s : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    coeffA n k s = commonFactor n k i s * ∏ t ∈ Icc i (n-1), ((s:ℝ)+t) := by
  unfold coeffA commonFactor
  rw [prod_div_distrib, prod_Icc_split_real (fun t => (s:ℝ)+t) hi hin hi (hi.trans hin)]
  ring

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

noncomputable def futureKernel (n k i z s : ℕ) : ℝ :=
  (∏ t ∈ Icc (i+1) (n-1), ((s:ℝ)+t)) -
    ∑ j ∈ Icc 1 (n-z), ((n-z).choose j : ℝ) * (1/(j:ℝ)) *
      (∏ l ∈ Icc 1 j, ((k:ℝ)-s+l)) *
      (∏ t ∈ Icc (i+1) (n-j-1), ((s:ℝ)+t))

lemma formula_mul_coeff {n k i z s s' : ℕ}
    (hi : 1 ≤ i) (hiz : i < z) (hzn : z ≤ n) (hss : s ≤ s') :
    unclippedFormula n k z s' * coeffC s' i s =
      commonFactor n k i s * futureKernel n k i z s' := by
  rw [unclippedFormula_eq_common (by omega) hzn]
  rw [mul_right_comm, common_mul_coeffC hi hiz hss]
  have hp := prod_Icc_split_real (fun t => (s':ℝ)+t)
    (show i+1 ≤ z by omega) hzn (show 1 ≤ z by omega) (show 1 ≤ n by omega)
  have hk : (∏ t ∈ Icc (i+1) (z-1), ((s':ℝ)+t)) * keyRHS n k z s' =
      ∑ j ∈ Icc 1 (n-z), ((n-z).choose j : ℝ) * (1/(j:ℝ)) *
        (∏ l ∈ Icc 1 j, ((k:ℝ)-s'+l)) *
        (∏ t ∈ Icc (i+1) (n-j-1), ((s':ℝ)+t)) := by
    unfold keyRHS
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjn := (mem_Icc.mp hj).2
    have hsplit := prod_Icc_split_real (fun t => (s':ℝ)+t)
      (show i+1 ≤ z by omega) (show z ≤ n-j by omega) (show 1 ≤ z by omega) (show 1 ≤ n-j by omega)
    rw [hsplit]
    ring
  unfold futureKernel
  rw [hp, ← hk]
  ring

lemma futureKernel_sum {n k i s : ℕ} (hi : i < n) :
    (∑ z ∈ Ioc i n, futureKernel n k i z s) = T n k i s := by
  unfold futureKernel T
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.card_Ioc]
  have hcast : ((n-i:ℕ):ℝ) = (n:ℝ)-i := by exact_mod_cast Nat.cast_sub (Nat.le_of_lt hi)
  rw [hcast]
  congr 1
  have hset : Ioc i n = Icc (i+1) n := by ext z; simp only [mem_Ioc, mem_Icc]; omega
  rw [hset]
  have hn : n-1+1=n := by omega
  conv_lhs => rw [← hn]
  rw [sum_Icc_succ_top (by omega)]
  simp only [hn, Nat.sub_self, Icc_eq_empty_of_lt (by omega : (0:ℕ)<1), sum_empty, add_zero]

lemma sum_fin_ge (k s : ℕ) (f : ℕ → ℝ) :
    (∑ r : Fin (k+1), if s ≤ r.1 then f r.1 else 0) = ∑ r ∈ Icc s k, f r := by
  rw [show (∑ r : Fin (k+1), if s ≤ r.1 then f r.1 else 0) =
      ∑ r ∈ range (k+1), if s ≤ r then f r else 0 from
    Fin.sum_univ_eq_sum_range (fun r => if s ≤ r then f r else 0) (k+1)]
  rw [← sum_filter]
  congr 1
  ext r
  simp only [mem_filter, mem_range, mem_Icc]
  omega

lemma formula_future_sum {n k i : ℕ} (hi : 1 ≤ i) (hin : i < n) (s : Fin (k+1)) :
    (∑ z ∈ (Ioc i n).attach, ∑ s' : Fin (k+1),
      unclippedFormula n k z.1 s' * coeffC s' i s) =
      commonFactor n k i s * ∑ s' ∈ Icc s.1 k, T n k i s' := by
  rw [sum_comm]
  have hinner : ∀ s' : Fin (k+1),
      (∑ z ∈ (Ioc i n).attach, unclippedFormula n k z.1 s' * coeffC s' i s) =
      if s.1 ≤ s'.1 then commonFactor n k i s * T n k i s' else 0 := by
    intro s'
    split_ifs with hss
    · calc
        _ = ∑ z ∈ (Ioc i n).attach, commonFactor n k i s * futureKernel n k i z.1 s' := by
          apply sum_congr rfl
          intro z _
          exact formula_mul_coeff hi (mem_Ioc.mp z.2).1 (mem_Ioc.mp z.2).2 hss
        _ = commonFactor n k i s * ∑ z ∈ Ioc i n, futureKernel n k i z s' := by
          rw [← mul_sum]
          exact congrArg (fun q => commonFactor n k i s * q) ((Ioc i n).sum_attach (fun z => futureKernel n k i z s'))
        _ = _ := by rw [futureKernel_sum hin]
    · simp [coeffC, hss]
  simp_rw [hinner]
  rw [sum_fin_ge k s.1 (fun r => commonFactor n k i s * T n k i r), ← mul_sum]

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

lemma formula_recurrence {n k i : ℕ} (hi : 1 ≤ i) (hin : i < n) (s : Fin (k+1)) :
    unclippedFormula n k i s = coeffA n k s -
      ∑ z ∈ (Ioc i n).attach, ∑ s' : Fin (k+1),
        unclippedFormula n k z.1 s' * coeffC s' i s := by
  rw [formula_future_sum hi hin s, key_sum_identity hi hin (show s.1 ≤ k by omega),
    unclippedFormula_eq_common hi (Nat.le_of_lt hin), coeffA_eq_common hi (Nat.le_of_lt hin)]
  ring

lemma samplesUnclipped_eq_formula (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (s : Fin (k+1)) : samplesUnclipped n k i s = unclippedFormula n k i s := by
  generalize he : n-i=d
  induction d using Nat.strong_induction_on generalizing i s with
  | h d ih =>
    unfold samplesUnclipped
    rw [unclippedDual]
    by_cases hlt : i < n
    · rw [if_pos hlt, formula_recurrence hi hlt s]
      congr 1
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro s' _
      have hj := mem_Ioc.mp j.2
      change samplesUnclipped n k j.1 s' * _ = _
      rw [ih (n-j.1) (by omega) j.1 (by omega) hj.2 s' rfl]
    · have hie : i=n := by omega
      subst i
      simp [unclippedFormula]

end SamplesDualProof


open Finset
open SecretaryAdvice.SamplesDual

namespace SamplesDualProof

lemma samples_greedy_formula (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Fin (k+1)) :
    samplesGreedy n k i s = explicitFormula n k i s := by
  have hn : 1 ≤ n := hi.trans hin
  have h := greedy_eq_max_of_positive_future n
    (fun _ (s : Fin (k+1)) => coeffA n k s)
    (fun _ (s' : Fin (k+1)) i (s : Fin (k+1)) => coeffC s' i s)
    (fun i (s : Fin (k+1)) => unclippedFormula n k i s)
    (fun s => le_of_lt (coeffA_pos hn))
    (fun s => by simp [unclippedFormula])
    (fun i hi hin s => formula_recurrence hi hin s)
    (fun i j s s' _ _ _ => coeffC_nonneg s' i s)
    (fun i j s s' hi hij hjn hp hc => ?_) i hi hin s
  · change samplesGreedy n k i s = _ at h
    rw [h]
    unfold explicitFormula unclippedFormula
    split_ifs with he
    · exact max_eq_right (le_of_lt (coeffA_pos hn))
    · rfl
  · have hss : s.1 ≤ s'.1 := by
      by_contra hss
      exact hc (by simp [coeffC, hss])
    exact positive_future_of_normalized_deficit n k (unclippedFormula n k)
      (fun _ => coeffA_pos hn)
      (fun _ _ hi hin _ => unclippedFormula_eq_deficit hi hin)
      hi (Nat.le_of_lt hij) hjn hss (by omega) hp

end SamplesDualProof

namespace SecretaryAdvice.SamplesDual

theorem samples_complete (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Fin (k + 1)) :
    samplesGreedy n k i s = explicitFormula n k i s := by
  exact SamplesDualProof.samples_greedy_formula n k i hi hin s

end SecretaryAdvice.SamplesDual


open Finset

namespace SecretaryAdvice.SamplesDual

/-- Theorem 17, p. 17: the greedy dual solution (8) with the samples coefficients of §5 is
`u(n,s) = 1/(k+1)·∏_{t=1}^{n−1} (s+t)/(k+t+1)` and, for `i < n`,
`u(i,s) = max {0, innerFormula n k i s}`, for every round `1 ≤ i ≤ n` and signal `s ∈ {0,…,k}`. -/
theorem theorem_17 (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Fin (k + 1)) :
    samplesGreedy n k i s = explicitFormula n k i s := by
  exact samples_complete n k i hi hin s

end SecretaryAdvice.SamplesDual

open SecretaryAdvice.SamplesDual

theorem solution (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Fin (k + 1)) :
    samplesGreedy n k i s = explicitFormula n k i s := SecretaryAdvice.SamplesDual.theorem_17 n k i hi hin s
