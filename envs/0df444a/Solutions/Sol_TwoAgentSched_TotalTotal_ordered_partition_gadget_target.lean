-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.ordered_partition_gadget_target
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:59:30.926914+00:00
-- url     : https://prove2.me/submissions/bd87ebb7-50d9-4e3c-858b-ef4e8d1d6eb6

import Definitions.Def_TwoAgentSched_TotalTotal_Construction
import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_OrderedPartitionGadget
import Theorems.Thm_TwoAgentSched_TotalTotal_theorem_9_2_equivalence
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Two copies of every base-four tag below position `n` fit below `4^n`. -/
lemma two_tag_sum_lt_power (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, 4 ^ k) < 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 < 4 ^ n := by positivity
    omega

/-- Equality of packed high/low components uniquely determines both components. -/
lemma high_low_unique (K a b r s : ℕ) (hr : r < K) (hs : s < K)
    (h : K * a + r = K * b + s) : r = s ∧ a = b := by
  have hk : 0 < K := by omega
  have hrs : r = s := by
    have hm := congrArg (fun x : ℕ => x % K) h
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using hm
  have hmul : K * a = K * b := by omega
  exact ⟨hrs, Nat.eq_of_mul_eq_mul_left hk hmul⟩

/-- If base-four digits in `{0,1,2}` encode the all-ones word, every digit is one. -/
lemma tags_no_carry (digits : List ℕ) (hbound : ∀ d ∈ digits, d ≤ 2)
    (hvalue : Nat.ofDigits 4 digits = Nat.ofDigits 4 (List.replicate digits.length 1)) :
    digits = List.replicate digits.length 1 := by
  apply Nat.ofDigits_inj_of_len_eq (b := 4) (by decide)
  · simp
  · intro d hd
    have := hbound d hd
    omega
  · intro d hd
    simp only [List.mem_replicate] at hd
    omega
  · exact hvalue

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Number of selected tagged elements in a pair, always one of 0, 1, or 2. -/
noncomputable def selectedDigit {n : ℕ} (S : Finset (Fin n × Bool)) (i : Fin n) : ℕ :=
  (if (i, false) ∈ S then 1 else 0) + (if (i, true) ∈ S then 1 else 0)

lemma selectedDigit_le_two {n : ℕ} (S : Finset (Fin n × Bool)) (i : Fin n) :
    selectedDigit S i ≤ 2 := by
  classical
  unfold selectedDigit
  split_ifs <;> omega

/-- A selected-pair digit word with the all-ones base-four value selects one per pair. -/
lemma selectedDigit_eq_one {n : ℕ} (S : Finset (Fin n × Bool))
    (hvalue : Nat.ofDigits 4 (List.ofFn (selectedDigit S)) =
      Nat.ofDigits 4 (List.ofFn (fun _ : Fin n => 1))) :
    ∀ i, selectedDigit S i = 1 := by
  have hlist : List.ofFn (selectedDigit S) = List.ofFn (fun _ : Fin n => 1) := by
    apply Nat.ofDigits_inj_of_len_eq (b := 4) (by decide)
    · simp
    · intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      have := selectedDigit_le_two S i
      omega
    · intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      omega
    · exact hvalue
  have hfun := List.ofFn_injective hlist
  intro i
  exact congrFun hfun i

lemma selectedDigit_eq_one_iff {n : ℕ} (S : Finset (Fin n × Bool)) (i : Fin n) :
    selectedDigit S i = 1 ↔
      (((i, false) ∈ S ∧ (i, true) ∉ S) ∨ ((i, false) ∉ S ∧ (i, true) ∈ S)) := by
  classical
  unfold selectedDigit
  by_cases h0 : (i, false) ∈ S <;> by_cases h1 : (i, true) ∈ S <;> simp [h0, h1]

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Equality of selected tag weight with the one-per-pair tag weight forces every digit to one. -/
lemma selectedDigit_eq_one_of_tag_sum {n : ℕ} (S : Finset (Fin n × Bool))
    (h : (∑ i : Fin n, 4 ^ i.val * selectedDigit S i) = ∑ i : Fin n, 4 ^ i.val) :
    ∀ i, selectedDigit S i = 1 := by
  apply selectedDigit_eq_one S
  have h' : (∑ i : Fin n, 4 ^ i.val * selectedDigit S i) =
      ∑ i : Fin n, 4 ^ i.val * 1 := by simpa using h
  simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn,
    List.length_ofFn, Fin.val_cast, mul_comm, List.sum_ofFn] using! h'

lemma exactly_one_of_each_pair {n : ℕ} (S : Finset (Fin n × Bool))
    (h : (∑ i : Fin n, 4 ^ i.val * selectedDigit S i) = ∑ i : Fin n, 4 ^ i.val) :
    ∀ i, (((i, false) ∈ S ∧ (i, true) ∉ S) ∨
      ((i, false) ∉ S ∧ (i, true) ∈ S)) := by
  intro i
  exact (selectedDigit_eq_one_iff S i).mp (selectedDigit_eq_one_of_tag_sum S h i)

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Equal packed partition sums force equal high parts and one copy of the total tag weight. -/
lemma packed_partition_forces_tags (K wA wB tagA tagB tags : ℕ)
    (hA : tagA ≤ 2 * tags) (hB : tagB ≤ 2 * tags) (hK : 2 * tags < K)
    (htotal : tagA + tagB = 2 * tags)
    (heq : K * wA + tagA = K * wB + tagB) :
    tagA = tags ∧ tagB = tags ∧ wA = wB := by
  have hparts := high_low_unique K wA wB tagA tagB (by omega) (by omega) heq
  omega

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- The tag sum of a selected subset, grouped by pair. -/
lemma selected_tag_sum {n : ℕ} (S : Finset (Fin n × Bool)) :
    (∑ x ∈ S, 4 ^ x.1.val) = ∑ i : Fin n, 4 ^ i.val * selectedDigit S i := by
  classical
  calc
    (∑ x ∈ S, 4 ^ x.1.val) = ∑ x : Fin n × Bool, if x ∈ S then 4 ^ x.1.val else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp
    _ = ∑ i : Fin n, 4 ^ i.val * selectedDigit S i := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      unfold selectedDigit
      split_ifs <;> simp <;> omega

/-- The total weight of the two tags at each index is less than the scale. -/
lemma total_tag_sum_lt_scale (n : ℕ) :
    2 * (∑ i : Fin n, 4 ^ i.val) < 4 ^ n := by
  simpa only [Fin.sum_univ_eq_sum_range] using two_tag_sum_lt_power n

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- One member of each pair carries its source weight in a high base-four block. -/
def gadgetWeight {n : ℕ} (w : Fin n → ℕ) (x : Fin n × Bool) : ℕ :=
  4 ^ n * (if x.2 then w x.1 else 0) + 4 ^ x.1.val

lemma gadget_subset_sum {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n × Bool)) :
    (∑ x ∈ S, gadgetWeight w x) =
      4 ^ n * (∑ x ∈ S, if x.2 then w x.1 else 0) + ∑ x ∈ S, 4 ^ x.1.val := by
  simp [gadgetWeight, Finset.sum_add_distrib, Finset.mul_sum]

lemma total_pair_tags (n : ℕ) :
    (∑ x : Fin n × Bool, 4 ^ x.1.val) = 2 * ∑ i : Fin n, 4 ^ i.val := by
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_bool, two_mul, Finset.sum_add_distrib]

/-- A balanced gadget partition chooses exactly one member of each pair and balances high weights. -/
lemma balanced_gadget_forces_pairs {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n × Bool))
    (heq : (∑ x ∈ S, gadgetWeight w x) = ∑ x ∈ Sᶜ, gadgetWeight w x) :
    (∀ i, (((i, false) ∈ S ∧ (i, true) ∉ S) ∨
      ((i, false) ∉ S ∧ (i, true) ∈ S))) ∧
    (∑ x ∈ S, if x.2 then w x.1 else 0) =
      ∑ x ∈ Sᶜ, if x.2 then w x.1 else 0 := by
  classical
  let tags : ℕ := ∑ i : Fin n, 4 ^ i.val
  let low : Finset (Fin n × Bool) → ℕ := fun T => ∑ x ∈ T, 4 ^ x.1.val
  let high : Finset (Fin n × Bool) → ℕ := fun T => ∑ x ∈ T, if x.2 then w x.1 else 0
  have htotal : low S + low Sᶜ = 2 * tags := by
    dsimp [low, tags]
    rw [Finset.sum_add_sum_compl]
    exact total_pair_tags n
  have hscale : 2 * tags < 4 ^ n := by
    simpa [tags] using total_tag_sum_lt_scale n
  have heq' : 4 ^ n * high S + low S = 4 ^ n * high Sᶜ + low Sᶜ := by
    simpa only [gadget_subset_sum, low, high] using heq
  have hparts := packed_partition_forces_tags (4 ^ n) (high S) (high Sᶜ) (low S) (low Sᶜ) tags
    (by omega) (by omega) hscale htotal heq'
  have htag : (∑ i : Fin n, 4 ^ i.val * selectedDigit S i) = ∑ i : Fin n, 4 ^ i.val := by
    rw [← selected_tag_sum S]
    simpa [low, tags] using hparts.1
  exact ⟨exactly_one_of_each_pair S htag, hparts.2.2⟩

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Original indices whose weight-carrying member is selected. -/
noncomputable def chosenTrue {n : ℕ} (S : Finset (Fin n × Bool)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => (i, true) ∈ S

lemma chosenTrue_compl {n : ℕ} (S : Finset (Fin n × Bool)) :
    chosenTrue Sᶜ = (chosenTrue S)ᶜ := by
  classical
  ext i
  simp [chosenTrue]

lemma selected_high_sum {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n × Bool)) :
    (∑ x ∈ S, if x.2 then w x.1 else 0) = ∑ i ∈ chosenTrue S, w i := by
  classical
  calc
    (∑ x ∈ S, if x.2 then w x.1 else 0) =
        ∑ x : Fin n × Bool, if x ∈ S then (if x.2 then w x.1 else 0) else 0 := by
      have hfilter : Finset.univ.filter (fun x : Fin n × Bool => x ∈ S) = S := by
        ext x
        simp
      calc
        (∑ x ∈ S, if x.2 then w x.1 else 0) =
            ∑ x ∈ Finset.univ.filter (fun x : Fin n × Bool => x ∈ S),
              if x.2 then w x.1 else 0 := by rw [hfilter]
        _ = _ := by rw [Finset.sum_filter]
    _ = ∑ i : Fin n, if (i, true) ∈ S then w i else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      by_cases hi : (i, true) ∈ S <;> simp [hi]
    _ = ∑ i ∈ chosenTrue S, w i := by
      simp [chosenTrue, Finset.sum_filter]

/-- Any balanced gadget subset yields equal sums of the source weights. -/
lemma balanced_gadget_implies_equal_sums {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n × Bool))
    (heq : (∑ x ∈ S, gadgetWeight w x) = ∑ x ∈ Sᶜ, gadgetWeight w x) :
    (∑ i ∈ chosenTrue S, w i) = ∑ i ∈ (chosenTrue S)ᶜ, w i := by
  have hw := (balanced_gadget_forces_pairs w S heq).2
  rw [selected_high_sum, selected_high_sum, chosenTrue_compl] at hw
  exact hw

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/- Reindexing adapted from the checked `fs_hget` helper in
   `Ref_TwoAgentSched_TotalTotal_theorem_9_2_equivalence.lean`. -/
lemma ofFn_sum_reindex {n : ℕ} (w : Fin n → ℕ) (hlen : (List.ofFn w).length = n)
    (A : Finset (Fin (List.ofFn w).length)) :
    ∑ i ∈ A, (List.ofFn w).get i =
      ∑ h : Fin n, if (Fin.cast hlen.symm h) ∈ A then w h else 0 := by
  classical
  have h0 : ∑ i ∈ A, (List.ofFn w).get i = ∑ i, if i ∈ A then (List.ofFn w).get i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  rw [h0]
  refine Fintype.sum_equiv (finCongr hlen) _ _ (fun i => ?_)
  have e : Fin.cast hlen.symm (finCongr hlen i) = i := by ext; simp
  simp only [e, List.get_ofFn]
  rfl

/-- A balanced gadget subset induces a `PartitionYes` witness for the input list. -/
lemma balanced_gadget_implies_partition {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n × Bool))
    (heq : (∑ x ∈ S, gadgetWeight w x) = ∑ x ∈ Sᶜ, gadgetWeight w x) :
    ProjSchedTW.Complexity.PartitionYes (List.ofFn w) := by
  classical
  have hlen : (List.ofFn w).length = n := List.length_ofFn
  let A : Finset (Fin (List.ofFn w).length) :=
    Finset.univ.filter (fun i => Fin.cast hlen i ∈ chosenTrue S)
  have hA : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ A) = chosenTrue S := by
    ext i
    simp [A]
  have hAc : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ Aᶜ) = (chosenTrue S)ᶜ := by
    ext i
    simp [A]
  refine ⟨A, ?_⟩
  rw [ofFn_sum_reindex w hlen A, ofFn_sum_reindex w hlen Aᶜ]
  rw [← Finset.sum_filter, ← Finset.sum_filter, hA, hAc]
  exact balanced_gadget_implies_equal_sums w S heq

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Select the weight-carrying member exactly for source indices in `A`. -/
noncomputable def gadgetChoice {n : ℕ} (A : Finset (Fin n)) : Finset (Fin n × Bool) := by
  classical
  exact Finset.univ.filter fun x => if x.2 then x.1 ∈ A else x.1 ∉ A

lemma gadgetChoice_compl {n : ℕ} (A : Finset (Fin n)) :
    gadgetChoice Aᶜ = (gadgetChoice A)ᶜ := by
  classical
  ext ⟨i, b⟩
  cases b <;> simp [gadgetChoice]

lemma chosenTrue_gadgetChoice {n : ℕ} (A : Finset (Fin n)) :
    chosenTrue (gadgetChoice A) = A := by
  classical
  ext i
  simp [chosenTrue, gadgetChoice]

lemma gadgetChoice_tags {n : ℕ} (A : Finset (Fin n)) :
    (∑ x ∈ gadgetChoice A, 4 ^ x.1.val) = ∑ i : Fin n, 4 ^ i.val := by
  classical
  rw [selected_tag_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : selectedDigit (gadgetChoice A) i = 1 := by
    by_cases hi : i ∈ A <;> simp [selectedDigit, gadgetChoice, hi]
  simp [h]

/-- A balanced source partition gives a balanced selection of gadget weights. -/
lemma gadgetChoice_balanced {n : ℕ} (w : Fin n → ℕ) (A : Finset (Fin n))
    (h : (∑ i ∈ A, w i) = ∑ i ∈ Aᶜ, w i) :
    (∑ x ∈ gadgetChoice A, gadgetWeight w x) =
      ∑ x ∈ (gadgetChoice A)ᶜ, gadgetWeight w x := by
  classical
  have htag := gadgetChoice_tags A
  have htagC : (∑ x ∈ (gadgetChoice A)ᶜ, 4 ^ x.1.val) = ∑ i : Fin n, 4 ^ i.val := by
    rw [← gadgetChoice_compl]
    exact gadgetChoice_tags Aᶜ
  simp only [gadget_subset_sum, selected_high_sum, chosenTrue_compl,
    chosenTrue_gadgetChoice, htag, htagC, h]

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- The paired base-four gadget preserves the source `PartitionYes` predicate. -/
theorem gadget_partition_iff {n : ℕ} (w : Fin n → ℕ) :
    ProjSchedTW.Complexity.PartitionYes (List.ofFn w) ↔
      ∃ S : Finset (Fin n × Bool),
        (∑ x ∈ S, gadgetWeight w x) = ∑ x ∈ Sᶜ, gadgetWeight w x := by
  classical
  constructor
  · rintro ⟨A, hA⟩
    have hlen : (List.ofFn w).length = n := List.length_ofFn
    rw [ofFn_sum_reindex w hlen A, ofFn_sum_reindex w hlen Aᶜ] at hA
    let C : Finset (Fin n) := Finset.univ.filter (fun i => Fin.cast hlen.symm i ∈ A)
    have hf : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ A) = C := rfl
    have hfc : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ Aᶜ) = Cᶜ := by
      ext i
      simp [C]
    rw [← Finset.sum_filter, ← Finset.sum_filter, hf, hfc] at hA
    exact ⟨gadgetChoice C, gadgetChoice_balanced w C hA⟩
  · rintro ⟨S, hS⟩
    exact balanced_gadget_implies_partition w S hS

end TwoAgentSched.TotalTotal.StrictPartition


namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Add the same high-block offset to both members of every pair. -/
def offsetGadgetWeight {n : ℕ} (w off : Fin n → ℕ) (x : Fin n × Bool) : ℕ :=
  gadgetWeight w x + 4 ^ n * off x.1

/-- Summing any index-only weight over selected pair members groups by the
    number of selected members at each index. -/
lemma selected_index_sum {n : ℕ} (v : Fin n → ℕ) (S : Finset (Fin n × Bool)) :
    (∑ x ∈ S, v x.1) = ∑ i : Fin n, v i * selectedDigit S i := by
  classical
  calc
    (∑ x ∈ S, v x.1) = ∑ x : Fin n × Bool, if x ∈ S then v x.1 else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp
    _ = ∑ i : Fin n, v i * selectedDigit S i := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      unfold selectedDigit
      split_ifs <;> simp <;> omega

/-- If each pair is split, equal index offsets contribute equally to both sides. -/
lemma split_pair_offset_sums {n : ℕ} (off : Fin n → ℕ) (S : Finset (Fin n × Bool))
    (hpair : ∀ i, (((i, false) ∈ S ∧ (i, true) ∉ S) ∨
      ((i, false) ∉ S ∧ (i, true) ∈ S))) :
    (∑ x ∈ S, off x.1) = ∑ x ∈ Sᶜ, off x.1 := by
  classical
  have hS : ∀ i, selectedDigit S i = 1 := fun i => (selectedDigit_eq_one_iff S i).2 (hpair i)
  have hC : ∀ i, selectedDigit Sᶜ i = 1 := by
    intro i
    apply (selectedDigit_eq_one_iff Sᶜ i).2
    obtain h | h := hpair i <;> simp_all
  simp only [selected_index_sum, hS, hC, mul_one]

/-- A common multiple-of-scale offset on each pair preserves precisely the
    balanced subsets of the original gadget. -/
theorem offset_gadget_balance_iff {n : ℕ} (w off : Fin n → ℕ) (S : Finset (Fin n × Bool)) :
    ((∑ x ∈ S, offsetGadgetWeight w off x) = ∑ x ∈ Sᶜ, offsetGadgetWeight w off x) ↔
      ((∑ x ∈ S, gadgetWeight w x) = ∑ x ∈ Sᶜ, gadgetWeight w x) := by
  classical
  have hsum (T : Finset (Fin n × Bool)) :
      (∑ x ∈ T, offsetGadgetWeight w off x) =
        (∑ x ∈ T, gadgetWeight w x) + 4 ^ n * (∑ x ∈ T, off x.1) := by
    simp [offsetGadgetWeight, Finset.sum_add_distrib, Finset.mul_sum]
  constructor
  · intro heq
    let tags : ℕ := ∑ i : Fin n, 4 ^ i.val
    let low : Finset (Fin n × Bool) → ℕ := fun T => ∑ x ∈ T, 4 ^ x.1.val
    let high : Finset (Fin n × Bool) → ℕ := fun T =>
      (∑ x ∈ T, if x.2 then w x.1 else 0) + ∑ x ∈ T, off x.1
    have htotal : low S + low Sᶜ = 2 * tags := by
      dsimp [low, tags]
      rw [Finset.sum_add_sum_compl]
      exact total_pair_tags n
    have hscale : 2 * tags < 4 ^ n := by
      simpa [tags] using total_tag_sum_lt_scale n
    have heq' : 4 ^ n * high S + low S = 4 ^ n * high Sᶜ + low Sᶜ := by
      rw [hsum, hsum, gadget_subset_sum, gadget_subset_sum] at heq
      dsimp [high, low]
      nlinarith [heq]
    have hparts := packed_partition_forces_tags (4 ^ n) (high S) (high Sᶜ) (low S) (low Sᶜ) tags
      (by omega) (by omega) hscale htotal heq'
    have htag : (∑ i : Fin n, 4 ^ i.val * selectedDigit S i) = ∑ i : Fin n, 4 ^ i.val := by
      rw [← selected_tag_sum S]
      simpa [low, tags] using hparts.1
    have hpair := exactly_one_of_each_pair S htag
    have hoff := split_pair_offset_sums off S hpair
    rw [hsum, hsum, hoff] at heq
    omega
  · intro heq
    have hpair := (balanced_gadget_forces_pairs w S heq).1
    have hoff := split_pair_offset_sums off S hpair
    rw [hsum, hsum, heq, hoff]

/-- Adding common high offsets does not alter PARTITION feasibility. -/
theorem offset_gadget_partition_iff {n : ℕ} (w off : Fin n → ℕ) :
    ProjSchedTW.Complexity.PartitionYes (List.ofFn w) ↔
      ∃ S : Finset (Fin n × Bool),
        (∑ x ∈ S, offsetGadgetWeight w off x) = ∑ x ∈ Sᶜ, offsetGadgetWeight w off x := by
  rw [gadget_partition_iff]
  constructor <;> rintro ⟨S, hS⟩
  · exact ⟨S, (offset_gadget_balance_iff w off S).2 hS⟩
  · exact ⟨S, (offset_gadget_balance_iff w off S).1 hS⟩

end TwoAgentSched.TotalTotal.StrictPartition


set_option autoImplicit false

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- The two members of a positive-weight pair occur in the required order. -/
theorem orderedPair_within {n : ℕ} (w : Fin n → ℕ) (N : ℕ) (i : Fin n)
    (hw : 0 < w i) : orderedPairWeight w N i false < orderedPairWeight w N i true := by
  have hK : 0 < 4 ^ n := by positivity
  have hh : 2 ^ (N + i.val) < 2 ^ (N + i.val) + w i := by omega
  have hm := Nat.mul_lt_mul_of_pos_left hh hK
  unfold orderedPairWeight
  simp only [Bool.false_eq_true, if_false, if_true, add_zero]
  omega

/-- If every weight fits in N bits, the larger member of an earlier pair is
    strictly smaller than either member of every later pair. -/
theorem orderedPair_across {n : ℕ} (w : Fin n → ℕ) (N : ℕ)
    (hw : ∀ i, w i < 2 ^ N) (i j : Fin n) (hij : i < j) (b c : Bool) :
    orderedPairWeight w N i b < orderedPairWeight w N j c := by
  let K : ℕ := 4 ^ n
  let hi : ℕ := 2 ^ (N + i.val) + if b then w i else 0
  let hj : ℕ := 2 ^ (N + j.val) + if c then w j else 0
  have hK : 0 < K := by dsimp [K]; positivity
  have htag : 4 ^ i.val < K := by
    dsimp [K]
    exact Nat.pow_lt_pow_right (by decide) i.isLt
  have hw' : (if b then w i else 0) < 2 ^ N := by
    cases b <;> simp [hw i]
  have hp : 2 ^ N ≤ 2 ^ (N + i.val) := Nat.pow_le_pow_right (by decide) (by omega)
  have hjpow : 2 ^ (N + i.val + 1) ≤ 2 ^ (N + j.val) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hdbl : 2 ^ (N + i.val + 1) = 2 * 2 ^ (N + i.val) := by rw [pow_succ]; ring
  have hhi : hi + 1 ≤ hj := by
    dsimp [hi, hj]
    omega
  have hmul : K * (hi + 1) ≤ K * hj := Nat.mul_le_mul_left K hhi
  have hlt : K * hi + 4 ^ i.val < K * (hi + 1) := by
    calc
      K * hi + 4 ^ i.val < K * hi + K := Nat.add_lt_add_left htag _
      _ = K * (hi + 1) := by simp [Nat.mul_add]
  have hh : K * hi + 4 ^ i.val < K * hj + 4 ^ j.val :=
    lt_of_lt_of_le hlt (le_trans hmul (Nat.le_add_right _ _))
  change 2 * (K * hi + 4 ^ i.val) < 2 * (K * hj + 4 ^ j.val)
  omega


/-- The explicit pair-by-pair enumeration is strictly increasing, without a
    sorting operation. -/
theorem orderedEnum_strict {n : ℕ} (w : Fin n → ℕ) (N : ℕ)
    (hpos : ∀ i, 0 < w i) (hbound : ∀ i, w i < 2 ^ N) : StrictMono (orderedEnum w N) := by
  intro a b hab
  have hab' : a.val < b.val := hab
  have hle : a.val / 2 ≤ b.val / 2 := by omega
  by_cases hidx : a.val / 2 = b.val / 2
  · have ha : a.val % 2 = 0 := by omega
    have hb : b.val % 2 = 1 := by omega
    have he : orderedIndex a = orderedIndex b := Fin.ext hidx
    simpa [orderedEnum, orderedIsHeavy, ha, hb, he] using
      orderedPair_within w N (orderedIndex b) (hpos (orderedIndex b))
  · have hlt : orderedIndex a < orderedIndex b := by
      change a.val / 2 < b.val / 2
      omega
    exact orderedPair_across w N hbound (orderedIndex a) (orderedIndex b) hlt
      (orderedIsHeavy a) (orderedIsHeavy b)

/-- Every emitted gadget weight is even. -/
theorem orderedEnum_even {n : ℕ} (w : Fin n → ℕ) (N : ℕ) (t : Fin (2 * n)) :
    Even (orderedEnum w N t) := by
  exact even_two_mul _


end TwoAgentSched.TotalTotal.StrictPartition


namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Reindexing a balanced finite subset along an equivalence preserves both sums. -/
lemma balance_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (w : β → ℕ) (A : Finset α)
    (hA : (∑ i ∈ A, w (e i)) = ∑ i ∈ Aᶜ, w (e i)) :
    (∑ j ∈ A.map e.toEmbedding, w j) = ∑ j ∈ (A.map e.toEmbedding)ᶜ, w j := by
  classical
  have hcompl : (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by
    ext y
    simp only [Finset.mem_compl, Finset.mem_map_equiv]
  rw [hcompl]
  simpa only [Finset.sum_map, Equiv.coe_toEmbedding] using hA

/-- Finite partition feasibility is invariant under any bijective reindexing. -/
lemma balance_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (w : β → ℕ) :
    (∃ A : Finset α, (∑ i ∈ A, w (e i)) = ∑ i ∈ Aᶜ, w (e i)) ↔
      ∃ B : Finset β, (∑ j ∈ B, w j) = ∑ j ∈ Bᶜ, w j := by
  classical
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.map e.toEmbedding, balance_map e w A hA⟩
  · rintro ⟨B, hB⟩
    have hB' : (∑ j ∈ B, (fun i : α => w (e i)) (e.symm j)) =
        ∑ j ∈ Bᶜ, (fun i : α => w (e i)) (e.symm j) := by
      simpa using hB
    exact ⟨B.map e.symm.toEmbedding, balance_map e.symm (fun i : α => w (e i)) B hB'⟩

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- `PartitionYes` on `List.ofFn` is exactly balanced partitioning of the original finite index type. -/
lemma partitionYes_ofFn_iff {n : ℕ} (w : Fin n → ℕ) :
    ProjSchedTW.Complexity.PartitionYes (List.ofFn w) ↔
      ∃ A : Finset (Fin n), (∑ i ∈ A, w i) = ∑ i ∈ Aᶜ, w i := by
  classical
  have hlen : (List.ofFn w).length = n := List.length_ofFn
  constructor
  · rintro ⟨A, hA⟩
    rw [ofFn_sum_reindex w hlen A, ofFn_sum_reindex w hlen Aᶜ] at hA
    let C : Finset (Fin n) := Finset.univ.filter (fun i => Fin.cast hlen.symm i ∈ A)
    have hf : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ A) = C := rfl
    have hfc : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ Aᶜ) = Cᶜ := by
      ext i
      simp [C]
    rw [← Finset.sum_filter, ← Finset.sum_filter, hf, hfc] at hA
    exact ⟨C, hA⟩
  · rintro ⟨C, hC⟩
    let A : Finset (Fin (List.ofFn w).length) :=
      Finset.univ.filter (fun i => Fin.cast hlen i ∈ C)
    have hA : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ A) = C := by
      ext i
      simp [A]
    have hAc : Finset.univ.filter (fun i : Fin n => Fin.cast hlen.symm i ∈ Aᶜ) = Cᶜ := by
      ext i
      simp [A]
    refine ⟨A, ?_⟩
    rw [ofFn_sum_reindex w hlen A, ofFn_sum_reindex w hlen Aᶜ]
    rw [← Finset.sum_filter, ← Finset.sum_filter, hA, hAc]
    exact hC

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Multiplying every source weight by two preserves equality of partition sums. -/
lemma double_balance_iff {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℕ) (A : Finset α) :
    (∑ i ∈ A, 2 * w i) = (∑ i ∈ Aᶜ, 2 * w i) ↔
      (∑ i ∈ A, w i) = ∑ i ∈ Aᶜ, w i := by
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  omega

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Adjacent positions enumerate every input-index/side pair exactly once. -/
def orderedEquiv {n : ℕ} : Fin (2 * n) ≃ Fin n × Bool where
  toFun t := (orderedIndex t, orderedIsHeavy t)
  invFun x := ⟨2 * x.1.val + (if x.2 then 1 else 0), by cases x.2 <;> simp <;> omega⟩
  left_inv t := by
    apply Fin.ext
    by_cases ht : t.val % 2 = 1 <;> simp [orderedIndex, orderedIsHeavy, ht] <;> omega
  right_inv x := by
    rcases x with ⟨i, b⟩
    apply Prod.ext
    · apply Fin.ext
      cases b <;> simp [orderedIndex] <;> omega
    · cases b <;> simp [orderedIsHeavy] <;> omega

lemma orderedEnum_eq_offset {n : ℕ} (w : Fin n → ℕ) (N : ℕ) (t : Fin (2 * n)) :
    orderedEnum w N t = 2 * offsetGadgetWeight w (fun i => 2 ^ (N + i.val)) (orderedEquiv t) := by
  change 2 * (4 ^ n * (2 ^ (N + (orderedIndex t).val) +
      if orderedIsHeavy t then w (orderedIndex t) else 0) + 4 ^ (orderedIndex t).val) =
    2 * ((4 ^ n * (if orderedIsHeavy t then w (orderedIndex t) else 0) +
      4 ^ (orderedIndex t).val) + 4 ^ n * 2 ^ (N + (orderedIndex t).val))
  ring

/-- Directly ordered, even gadget weights preserve the original PARTITION
    instance, with no sorting or reindexing algorithm needed. -/
theorem orderedEnum_partition_iff {n : ℕ} (w : Fin n → ℕ) (N : ℕ) :
    ProjSchedTW.Complexity.PartitionYes (List.ofFn w) ↔
      ProjSchedTW.Complexity.PartitionYes (List.ofFn (orderedEnum w N)) := by
  classical
  let off : Fin n → ℕ := fun i => 2 ^ (N + i.val)
  have hs : (∃ A : Finset (Fin (2 * n)),
          (∑ i ∈ A, orderedEnum w N i) = ∑ i ∈ Aᶜ, orderedEnum w N i) ↔
      ∃ B : Finset (Fin n × Bool),
        (∑ x ∈ B, 2 * offsetGadgetWeight w off x) =
          ∑ x ∈ Bᶜ, 2 * offsetGadgetWeight w off x := by
    have he := balance_equiv orderedEquiv (fun x => 2 * offsetGadgetWeight w off x)
    have hpe : ∀ i, orderedEnum w N i = 2 * offsetGadgetWeight w off (orderedEquiv i) :=
      fun i => orderedEnum_eq_offset w N i
    simp only [← hpe] at he
    exact he
  have hd : (∃ B : Finset (Fin n × Bool),
          (∑ x ∈ B, 2 * offsetGadgetWeight w off x) =
            ∑ x ∈ Bᶜ, 2 * offsetGadgetWeight w off x) ↔
      ∃ B : Finset (Fin n × Bool),
        (∑ x ∈ B, offsetGadgetWeight w off x) = ∑ x ∈ Bᶜ, offsetGadgetWeight w off x := by
    constructor <;> rintro ⟨B, hB⟩
    · exact ⟨B, (double_balance_iff (offsetGadgetWeight w off) B).mp hB⟩
    · exact ⟨B, (double_balance_iff (offsetGadgetWeight w off) B).mpr hB⟩
  exact (offset_gadget_partition_iff w off).trans
    (hd.symm.trans (hs.symm.trans (partitionYes_ofFn_iff (orderedEnum w N)).symm))

end TwoAgentSched.TotalTotal.StrictPartition

namespace TwoAgentSched.TotalTotal.StrictPartition

/-- Every directly ordered gadget weight has binary size linear in the
    input bit bound and the number of original weights. -/
theorem orderedPair_bits_bound {n : ℕ} (w : Fin n → ℕ) (N : ℕ)
    (hw : ∀ i, w i < 2 ^ N) (i : Fin n) (b : Bool) :
    (orderedPairWeight w N i b).bits.length ≤ N + 3 * n + 2 := by
  let K : ℕ := 4 ^ n
  let hi : ℕ := 2 ^ (N + i.val) + if b then w i else 0
  have htag : 4 ^ i.val < K := by
    dsimp [K]
    exact Nat.pow_lt_pow_right (by decide) i.isLt
  have hw' : (if b then w i else 0) < 2 ^ N := by
    cases b <;> simp [hw i]
  have hp : 2 ^ N ≤ 2 ^ (N + i.val) := Nat.pow_le_pow_right (by decide) (by omega)
  have hdbl : 2 ^ (N + i.val + 1) = 2 * 2 ^ (N + i.val) := by rw [pow_succ]; ring
  have hhi : hi + 1 ≤ 2 ^ (N + i.val + 1) := by dsimp [hi]; omega
  have hmul : K * (hi + 1) ≤ K * 2 ^ (N + i.val + 1) := Nat.mul_le_mul_left K hhi
  have hlt : K * hi + 4 ^ i.val < K * (hi + 1) := by
    calc
      K * hi + 4 ^ i.val < K * hi + K := Nat.add_lt_add_left htag _
      _ = K * (hi + 1) := by simp [Nat.mul_add]
  have hbase : K * hi + 4 ^ i.val < K * 2 ^ (N + i.val + 1) := lt_of_lt_of_le hlt hmul
  have hfour : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have hpow : 2 * K * 2 ^ (N + i.val + 1) = 2 ^ (N + 2 * n + i.val + 2) := by
    dsimp [K]
    rw [hfour]
    simp only [pow_add, pow_one]
    ring
  have hbig : 2 ^ (N + 2 * n + i.val + 2) ≤ 2 ^ (N + 3 * n + 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hvalue : orderedPairWeight w N i b < 2 ^ (N + 3 * n + 2) := by
    have h := Nat.mul_lt_mul_of_pos_left hbase (by decide : 0 < 2)
    rw [← Nat.mul_assoc, hpow] at h
    exact lt_of_lt_of_le h hbig
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.2 hvalue


end TwoAgentSched.TotalTotal.StrictPartition


namespace TwoAgentSched.TotalTotal

/-- If the input processing times are all even, the reduction's real threshold
    is the cast of a natural number. -/
lemma thresholdQ_integral {k : ℕ} (p : Fin k → ℕ) (he : ∀ i, Even (p i)) :
    ∃ q : ℕ, thresholdQ p = (q : ℝ) := by
  choose q hq using he
  let m : ℕ := ∑ i, q i
  have hm : bigP p = m + m := by
    unfold bigP m
    simp_rw [hq]
    rw [Finset.sum_add_distrib]
  refine ⟨3 * m + 2 * weightedSum p, ?_⟩
  unfold thresholdQ
  rw [hm]
  push_cast
  ring

end TwoAgentSched.TotalTotal


open ProjSchedTW.Complexity

/-- Read the binary digits of the first separator-terminated code.  This is a
    mathematical decoder, not yet a stack or Turing-machine program. -/
private def readFirstBits : List BSym → List Bool
  | .zero :: rest => false :: readFirstBits rest
  | .one :: rest => true :: readFirstBits rest
  | _ => []

private theorem readFirstBits_digits (digits : List Bool) (tail : List BSym) :
    readFirstBits ((digits.map fun b ↦ if b then BSym.one else BSym.zero) ++ BSym.sep :: tail) =
      digits := by
  induction digits with
  | nil => rfl
  | cons b digits ih =>
    cases b <;> simp [readFirstBits, ih]

private theorem readFirstBits_encNat (n : ℕ) (tail : List BSym) :
    readFirstBits (encNat n ++ tail) = n.bits := by
  simpa [encNat, List.append_assoc] using readFirstBits_digits n.bits tail

private theorem encNat_not_nil (n : ℕ) : encNat n ≠ [] := by
  simp [encNat]

/-- Canonical binary natural-number codes are uniquely decodable from the front,
    even in the presence of arbitrary trailing input. -/
theorem tensor_encNat_prefix_unique (m n : ℕ) (s t : List BSym)
    (h : encNat m ++ s = encNat n ++ t) : m = n ∧ s = t := by
  have hb : m.bits = n.bits := by
    have he := congrArg readFirstBits h
    simpa only [readFirstBits_encNat] using he
  have hmn : m = n := by
    apply Nat.eq_of_testBit_eq
    intro i
    simpa only [Nat.testBit_eq_inth] using congrArg (fun bs : List Bool ↦ bs.getI i) hb
  subst n
  exact ⟨rfl, (List.append_right_inj (encNat m)).mp h⟩

/-- A canonical sequence of separator-terminated natural-number codes uniquely
    determines the encoded natural-number list. -/
theorem tensor_encNats_injective : Function.Injective encNats := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h' : encNat y ++ encNats ys = [] := by simpa [encNats] using h.symm
      exact False.elim (encNat_not_nil y (List.append_eq_nil_iff.mp h').1)
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have h' : encNat x ++ encNats xs = [] := by simpa [encNats] using h
      exact False.elim (encNat_not_nil x (List.append_eq_nil_iff.mp h').1)
    | cons y ys =>
      have h' : encNat x ++ encNats xs = encNat y ++ encNats ys := by
        simpa [encNats] using h
      obtain ⟨hxy, htail⟩ := tensor_encNat_prefix_unique x y (encNats xs) (encNats ys) h'
      have hxs : xs = ys := ih htail
      simp [hxy, hxs]


namespace TwoAgentSched.TotalTotal

/-- The job counts, job lengths and bounds in a code list determine its instance. -/
lemma codeList_injective (I J : Instance) (a b c d : ℕ)
    (h : I.codeList a b = J.codeList c d) : I = J ∧ a = c ∧ b = d := by
  cases I with
  | mk na nb pa pb =>
    cases J with
    | mk na' nb' pa' pb' =>
      simp only [Instance.codeList, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨hna, hnb, hrest⟩ := h
      subst na'
      subst nb'
      have hpa : List.ofFn pa = List.ofFn pa' := by
        have ht := congrArg (List.take na) hrest
        simpa [List.take_append] using ht
      have hpaf : pa = pa' := List.ofFn_injective hpa
      subst pa'
      have hrest' : List.ofFn pb ++ [a, b] = List.ofFn pb' ++ [c, d] := by
        have ht : List.ofFn pa ++ (List.ofFn pb ++ [a, b]) =
            List.ofFn pa ++ (List.ofFn pb' ++ [c, d]) := by
          simpa only [List.append_assoc] using hrest
        exact List.append_cancel_left ht
      have hpb : List.ofFn pb = List.ofFn pb' := by
        have ht := congrArg (List.take nb) hrest'
        simpa [List.take_append] using ht
      have hpbf : pb = pb' := List.ofFn_injective hpb
      subst pb'
      have hab : [a, b] = [c, d] := List.append_cancel_left hrest'
      simp only [List.cons.injEq, and_true] at hab
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨rfl, rfl, rfl⟩

end TwoAgentSched.TotalTotal

namespace TwoAgentSched.TotalTotal

open CookPvsNP ProjSchedTW.Complexity

/-- A canonical code is in the recognition language exactly when its encoded
    instance satisfies its encoded bounds. -/
theorem targetLang_encoded_iff (I : Instance) (a b : ℕ) :
    encNats (I.codeList a b) ∈ targetLang ↔ I.RecYes a b := by
  constructor
  · rintro ⟨J, c, d, hJ, hcode⟩
    have hc := tensor_encNats_injective hcode
    obtain ⟨rfl, rfl, rfl⟩ := codeList_injective I J a b c d hc
    exact hJ
  · intro h
    exact ⟨I, a, b, h, rfl⟩

end TwoAgentSched.TotalTotal



open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal
open TwoAgentSched.TotalTotal.StrictPartition

/-- The direct pair-by-pair gadget is ordered, even, compactly encoded, and
    preserves the exact scheduling target-language answer. -/
theorem solution {n : ℕ} (w : Fin n → ℕ) (N : ℕ)
    (hpos : ∀ i, 0 < w i) (hbound : ∀ i, w i < 2 ^ N) :
    ∃ q : ℕ, StrictMono (orderedEnum w N) ∧
      (∀ t, Even (orderedEnum w N t) ∧ (orderedEnum w N t).bits.length ≤ N + 3 * n + 2) ∧
      thresholdQ (orderedEnum w N) = (q : ℝ) ∧
      (PartitionYes (List.ofFn w) ↔
        encNats ((construction (orderedEnum w N)).codeList q q) ∈ targetLang) := by
  have hm := orderedEnum_strict w N hpos hbound
  have he : ∀ t, Even (orderedEnum w N t) := orderedEnum_even w N
  obtain ⟨q, hq⟩ := thresholdQ_integral (orderedEnum w N) he
  refine ⟨q, hm, ?_, hq, ?_⟩
  · intro t
    exact ⟨he t, orderedPair_bits_bound w N hbound (orderedIndex t) (orderedIsHeavy t)⟩
  · have hth : (bigT (orderedEnum w N) : ℝ) / 2 = thresholdQ (orderedEnum w N) := by
      unfold bigT thresholdQ
      push_cast
      ring
    have hrec := theorem_9_2_equivalence (orderedEnum w N) hm
    rw [hth, hq] at hrec
    exact (orderedEnum_partition_iff w N).trans
      (hrec.trans (targetLang_encoded_iff (construction (orderedEnum w N)) q q).symm)

#print axioms solution
