-- Prove2me | solution 1 for blockColor_polychrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:07.953645+00:00
-- url     : https://prove2.me/submissions/42525d00-5560-4b73-a289-59582bd02367

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


section
open Finset Pointwise
section BlockColorInfra
private lemma checkLinearPolychrom_spec {offsets : List ℕ} {L : List (Fin 3)}
    (hcheck : checkLinearPolychrom offsets L = true)
    {i : ℕ} (hi : i + offsets.foldr max 0 < L.length) (c : Fin 3) :
    ∃ s ∈ offsets, L[i + s]? = some c := by
  simp only [checkLinearPolychrom, List.all_eq_true, List.mem_range, List.any_eq_true,
    beq_iff_eq] at hcheck
  exact hcheck i (by omega) c (by grind)
private lemma add_mod_of_lt {i s r : ℕ} (h : i % r + s < r) : (i + s) % r = i % r + s := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : s < r), Nat.mod_eq_of_lt h]
private lemma add_mod_sub {i s r : ℕ} (hge : r ≤ i % r + s) (hlt : i % r + s < 2 * r) :
    (i + s) % r = i % r + s - r := by
  have h1 := Nat.mod_add_div i r
  have key : i + s = (i % r + s - r) + (i / r + 1) * r := by
    grind [Nat.sub_add_cancel hge, mul_comm r (i / r)]
  conv_lhs => rw [key]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)
private lemma add_lt_of_mod_add_lt {i s r n : ℕ}
    (hi : i < r * n) (h : i % r + s < r) :
    i + s < r * n := by
  have h1 := Nat.mod_add_div i r
  have : i / r + 1 ≤ n := Nat.div_lt_of_lt_mul hi
  grind [Nat.mul_le_mul_left r this]
private lemma mod_eq_sub {n M : ℕ} (hge : M ≤ n) (hlt : n - M < M) : n % M = n - M := by
  conv_lhs => rw [← Nat.sub_add_cancel hge]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
private lemma ge_mul_of_mod_add_ge {i s r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hi_lo : r * (n - 1) ≤ i) (hge : r ≤ i % r + s) :
    r * n ≤ i + s := by
  have := Nat.mod_add_div i r
  have : n - 1 ≤ i / r := by rw [Nat.le_div_iff_mul_le hr]; grind
  have : n ≤ i / r + 1 := by omega
  grind [Nat.mul_le_mul_left r this]
private lemma bcv_eq_A (A B : List (Fin 3)) (h : ℕ)
    (XY : List (Fin 3)) (js p idx : ℕ)
    (hp : p < A.length * h)
    (hmod : p % A.length = idx) (hidx : idx < A.length)
    (hxy : XY[js]? = A[idx]?) :
    XY[js]? = some (blockColorVal A B h p) := by
  simp only [hxy, blockColorVal, if_pos hp, hmod, List.getElem?_eq_getElem hidx, Option.getD_some]
private lemma bcv_eq_B (A B : List (Fin 3)) (h : ℕ)
    (XY : List (Fin 3)) (js p idx : ℕ)
    (hp : ¬(p < A.length * h))
    (hmod : (p - A.length * h) % B.length = idx) (hidx : idx < B.length)
    (hxy : XY[js]? = B[idx]?) :
    XY[js]? = some (blockColorVal A B h p) := by
  simp only [hxy, blockColorVal, if_neg hp, hmod, List.getElem?_eq_getElem hidx, Option.getD_some]
private lemma sub_region_eq {i s r h : ℕ} (hr : 0 < r)
    (hi_lo : r * (h - 1) ≤ i) (hi_hi : i < r * h)
    (hjs_ge : r ≤ i % r + s) :
    i + s - r * h = i % r + s - r := by
  have hdiv := Nat.mod_add_div i r
  have hle : h - 1 ≤ i / r := by rw [Nat.le_div_iff_mul_le hr]; grind
  have hlt : i / r < h := Nat.div_lt_of_lt_mul (by grind)
  have hh : 1 ≤ h := by omega
  have hQr : r * h = r * (i / r) + r := by grind [Nat.sub_add_cancel]
  grind
private lemma case_no_wrap_AA (A B : List (Fin 3)) (offsets : List ℕ) (h k m i : ℕ)
    (hA : 0 < A.length)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hAA : checkLinearPolychrom offsets (A ++ A) = true)
    (hm : A.length * h + B.length * k = m)
    (h_no_wrap : i + offsets.foldr max 0 < m)
    (h_AA : i + offsets.foldr max 0 < A.length * h) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  set j := i % A.length
  have hj_lt : j < A.length := Nat.mod_lt _ hA
  refine ⟨A ++ A, j, hAA, by grind, fun s hsle => ?_⟩
  rw [Nat.mod_eq_of_lt (by grind)]
  have his_A : i + s < A.length * h := by grind
  by_cases hjs_lt : j + s < A.length
  · exact bcv_eq_A A B h _ _ _ _ his_A
      (add_mod_of_lt hjs_lt) hjs_lt (List.getElem?_append_left hjs_lt)
  · push Not at hjs_lt
    have hjs_sub : j + s - A.length < A.length := by grind
    exact bcv_eq_A A B h _ _ _ _ his_A (add_mod_sub hjs_lt (by grind)) hjs_sub (by grind)
private lemma case_no_wrap_AB (A B : List (Fin 3)) (offsets : List ℕ) (h k m i : ℕ)
    (hA : 0 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hAB : checkLinearPolychrom offsets (A ++ B) = true)
    (hm : A.length * h + B.length * k = m)
    (h_no_wrap : i + offsets.foldr max 0 < m)
    (hA_region : i < A.length * h)
    (h_cross : A.length * h ≤ i + offsets.foldr max 0) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  set j := i % A.length
  have hj_lt : j < A.length := Nat.mod_lt _ hA
  have hh_pos : 0 < h := by grind
  have hi_lo : A.length * (h - 1) ≤ i := by grind [Nat.mul_sub]
  refine ⟨A ++ B, j, hAB, by grind, fun s hsle => ?_⟩
  rw [Nat.mod_eq_of_lt (by grind)]
  by_cases hjs_lt : j + s < A.length
  · exact bcv_eq_A A B h _ _ _ _ (add_lt_of_mod_add_lt hA_region hjs_lt)
      (add_mod_of_lt hjs_lt) hjs_lt (List.getElem?_append_left hjs_lt)
  · push Not at hjs_lt
    have hjs_B : j + s - A.length < B.length := by grind
    have his_ge : A.length * h ≤ i + s := ge_mul_of_mod_add_ge hA hh_pos hi_lo hjs_lt
    refine bcv_eq_B A B h _ _ _ _ (by grind) ?_ hjs_B ?_
    · rw [sub_region_eq hA hi_lo hA_region hjs_lt, Nat.mod_eq_of_lt (by grind)]
    · grind
private lemma case_no_wrap_BB (A B : List (Fin 3)) (offsets : List ℕ) (h k m i : ℕ)
    (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hBB : checkLinearPolychrom offsets (B ++ B) = true)
    (hm : A.length * h + B.length * k = m)
    (h_no_wrap : i + offsets.foldr max 0 < m)
    (hB_region : A.length * h ≤ i) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  set j := (i - A.length * h) % B.length
  have hj_lt : j < B.length := Nat.mod_lt _ (by grind)
  refine ⟨B ++ B, j, hBB, by grind, fun s hsle => ?_⟩
  rw [Nat.mod_eq_of_lt (by grind)]
  by_cases hjs_lt : j + s < B.length
  · exact bcv_eq_B A B h _ _ _ _ (by grind)
      (by rw [Nat.sub_add_comm hB_region]; exact add_mod_of_lt hjs_lt)
      hjs_lt (List.getElem?_append_left hjs_lt)
  · push Not at hjs_lt
    have hjs_sub : j + s - B.length < B.length := by grind
    exact bcv_eq_B A B h _ _ _ _ (by grind)
      (by rw [Nat.sub_add_comm hB_region]; exact add_mod_sub hjs_lt (by grind))
      hjs_sub (by grind)
private lemma case_wrap_A (A B : List (Fin 3)) (offsets : List ℕ) (h m i : ℕ) (hA : 0 < A.length)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hAA : checkLinearPolychrom offsets (A ++ A) = true)
    (hm : A.length * h = m)
    (hi : i < m)
    (h_wrap : m ≤ i + offsets.foldr max 0)
    (hA_region : i < A.length * h) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  subst hm
  set j := i % A.length
  have hj_lt : j < A.length := Nat.mod_lt _ hA
  have hh_pos : 0 < h := by grind
  have hi_lo : A.length * (h - 1) ≤ i := by grind [Nat.mul_sub]
  have hAh : A.length ≤ A.length * h := Nat.le_mul_of_pos_right _ hh_pos
  refine ⟨A ++ A, j, hAA, by grind, fun s hsle => ?_⟩
  by_cases hjs_lt : j + s < A.length
  · have his_lt : i + s < A.length * h := add_lt_of_mod_add_lt (by grind) hjs_lt
    rw [Nat.mod_eq_of_lt his_lt]
    exact bcv_eq_A A B h _ _ _ _ his_lt
      (add_mod_of_lt hjs_lt) hjs_lt (List.getElem?_append_left hjs_lt)
  · push Not at hjs_lt
    have his_ge : A.length * h ≤ i + s := ge_mul_of_mod_add_ge hA hh_pos hi_lo hjs_lt
    have hmod : (i + s) % (A.length * h) = i + s - A.length * h := mod_eq_sub his_ge (by grind)
    have hjs_idx : j + s - A.length < A.length := by grind
    exact bcv_eq_A A B h _ _ _ _ (by grind)
      (by rw [hmod, Nat.mod_eq_of_lt (by grind), sub_region_eq hA hi_lo (by grind) hjs_lt])
      hjs_idx (by grind)
private lemma case_wrap_BA (A B : List (Fin 3)) (offsets : List ℕ) (h k m i : ℕ)
    (hA : 0 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hBA : checkLinearPolychrom offsets (B ++ A) = true)
    (hm : A.length * h + B.length * k = m)
    (hi : i < m)
    (h_wrap : m ≤ i + offsets.foldr max 0)
    (hB_region : A.length * h ≤ i)
    (hh_pos : 0 < h) (hk_pos : 0 < k) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  have hAh : A.length ≤ A.length * h := Nat.le_mul_of_pos_right _ hh_pos
  have hBk : B.length ≤ B.length * k := Nat.le_mul_of_pos_right _ hk_pos
  set j := (i - A.length * h) % B.length
  have hj_lt : j < B.length := Nat.mod_lt _ (by grind)
  have hi_B : i - A.length * h < B.length * k := by grind
  have hk_lo : B.length * (k - 1) ≤ i - A.length * h := by grind [Nat.mul_sub]
  refine ⟨B ++ A, j, hBA, by grind, fun s hsle => ?_⟩
  by_cases hjs_lt : j + s < B.length
  · -- Still in B
    have his_lt : (i - A.length * h) + s < B.length * k := add_lt_of_mod_add_lt hi_B hjs_lt
    rw [Nat.mod_eq_of_lt (by grind)]
    exact bcv_eq_B A B h _ _ _ _ (by grind)
      (by rw [Nat.sub_add_comm hB_region]; exact add_mod_of_lt hjs_lt)
      hjs_lt (List.getElem?_append_left hjs_lt)
  · -- Wrapped to A region
    push Not at hjs_lt
    have his_ge : m ≤ i + s := by grind [ge_mul_of_mod_add_ge (by grind) hk_pos hk_lo hjs_lt]
    have hmod : (i + s) % m = i + s - m := mod_eq_sub his_ge (by grind)
    have hsub_eq : i + s - m = j + s - B.length := by
      grind [sub_region_eq (by grind) hk_lo hi_B hjs_lt]
    have hjs_idx : j + s - B.length < A.length := by grind
    exact bcv_eq_A A B h _ _ _ _ (by grind)
      (by rw [hmod, Nat.mod_eq_of_lt (by grind), hsub_eq])
      hjs_idx (by grind)
private lemma case_wrap_BB (A B : List (Fin 3)) (offsets : List ℕ) (k m i : ℕ)
    (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hBB : checkLinearPolychrom offsets (B ++ B) = true)
    (hm : B.length * k = m)
    (hi : i < m)
    (h_wrap : m ≤ i + offsets.foldr max 0)
    (hk_pos : 0 < k) :
    CaseGoal A B offsets 0 m i := by
  set maxOff := offsets.foldr max 0
  have hBk : B.length ≤ B.length * k := Nat.le_mul_of_pos_right _ hk_pos
  set j := i % B.length
  have hj_lt : j < B.length := Nat.mod_lt _ (by grind)
  have hk_lo : B.length * (k - 1) ≤ i := by grind [Nat.mul_sub]
  refine ⟨B ++ B, j, hBB, by grind, fun s hsle => ?_⟩
  by_cases hjs_lt : j + s < B.length
  · have his_lt : i + s < B.length * k := add_lt_of_mod_add_lt (by grind) hjs_lt
    rw [Nat.mod_eq_of_lt (by grind)]
    exact bcv_eq_B A B 0 _ _ _ _ (by omega) (by grind [add_mod_of_lt hjs_lt])
      hjs_lt (List.getElem?_append_left hjs_lt)
  · push Not at hjs_lt
    have his_ge : m ≤ i + s := by grind [ge_mul_of_mod_add_ge (by grind) hk_pos hk_lo hjs_lt]
    have hmod : (i + s) % m = i + s - m := mod_eq_sub his_ge (by grind)
    have hsub_eq : i + s - m = j + s - B.length := by
      rw [← hm]
      exact sub_region_eq (by grind) hk_lo (by grind) hjs_lt
    have hjs_idx : j + s - B.length < B.length := by grind
    exact bcv_eq_B A B 0 _ _ _ _ (by omega)
      (by rw [Nat.mul_zero, Nat.sub_zero, hmod, Nat.mod_eq_of_lt (by grind), hsub_eq])
      hjs_idx (by grind)
end BlockColorInfra
section Table1
variable (m : ℕ)
end Table1
end

set_option autoImplicit true
open Finset Pointwise
theorem _root_.solution
    (A B : List (Fin 3)) (offsets : List ℕ)
    (hA : 0 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hpairs : checkBlockPairs offsets A B = true)
    {h k : ℕ} (hhk : 0 < h + k) {m : ℕ}
    (hm : A.length * h + B.length * k = m)
    {i : ℕ} (hi : i < m) (c : Fin 3) :
    ∃ s ∈ offsets, blockColorVal A B h ((i + s) % m) = c := by
  set maxOff := offsets.foldr max 0
  simp only [checkBlockPairs, Bool.and_eq_true] at hpairs
  obtain ⟨⟨⟨hAA, hAB⟩, hBA⟩, hBB⟩ := hpairs
  -- Reduce to CaseGoal
  suffices hg : CaseGoal A B offsets h m i by
    obtain ⟨XY, j, hXY_check, hj_bound, hcorr⟩ := hg
    obtain ⟨s, hs_mem, hs_eq⟩ := checkLinearPolychrom_spec hXY_check hj_bound c
    refine ⟨s, hs_mem, ?_⟩
    grind [hcorr s (List.le_max_of_le' 0 hs_mem le_rfl)]
  -- Dispatch to case lemmas
  by_cases h_wrap : i + maxOff < m
  · by_cases hA_region : i < A.length * h
    · by_cases h_cross : i + maxOff < A.length * h
      · exact case_no_wrap_AA A B offsets h k m i hA hmaxOff hAA hm h_wrap h_cross
      · push Not at h_cross
        have hk_pos : 0 < k := by grind
        exact case_no_wrap_AB A B offsets h k m i hA hBlen hmaxOff hAB hm h_wrap hA_region h_cross
    · push Not at hA_region
      exact case_no_wrap_BB A B offsets h k m i hBlen hmaxOff hBB hm h_wrap hA_region
  · push Not at h_wrap
    by_cases hA_region : i < A.length * h
    · have hk0 : k = 0 := by rw [hBlen] at hm; nlinarith [hmaxOff]
      subst hk0
      simp only [mul_zero, add_zero] at hm
      exact case_wrap_A A B offsets h m i hA hmaxOff hAA hm hi h_wrap hA_region
    · push Not at hA_region
      have hk_pos : 0 < k := by grind
      by_cases hh_pos : 0 < h
      · exact case_wrap_BA A B offsets h k m i hA hBlen hmaxOff
          hBA hm hi h_wrap hA_region hh_pos hk_pos
      · have hh0 : h = 0 := by grind
        subst hh0
        simp only [mul_zero, zero_add] at hm
        exact case_wrap_BB A B offsets k m i hBlen hmaxOff hBB hm hi h_wrap hk_pos
