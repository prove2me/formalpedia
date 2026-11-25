-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.harm_bucket_hl_54_v2
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T08:23:31.67217+00:00
-- url     : https://prove2.me/submissions/e850207c-fad7-4f8d-a5c1-9b28d2150c1f

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_1
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_2
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_3
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_4
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_5
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_6
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_7
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_8
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_9
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_10
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54
import Theorems.Thm_QuantumLTF_Membership_Supplement_bitonic_routing_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_lcg_sym_comb_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_lcg_sym_arith_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_alonso_schott_sil_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_harm_bucket_occ_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_harm_bucket_route_a_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_harm_bucket_route_b_54

set_option autoImplicit false

/-! ### Part 8: Step 4 (Active-Bucket Bijection & Harmonic Uniform State Preparation) -/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

/-! #### 8.1 Step 4 Disjointness & `eRec3` Field Helpers -/

lemma eRec3Kind_disjoint_eUnifCtrl (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec3Kind as n K d q a ≠ eUnifCtrl as n K d b :=
  ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨13, by decide⟩) (k2 := ⟨21, by decide⟩)
    (by decide) _ _ (ancLen_13 n K d _) q _ 2 _ 1 _

lemma eRec3Kind_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec3Kind as n K d q a ≠ eArith345 as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨13, by decide⟩) (k2 := ⟨22, by decide⟩)
    (by decide) _ _ (ancLen_13 n K d _) q _ 2 _ subLen _

lemma eUnifCtrl_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1) :
    ∀ a b, eUnifCtrl as n K d a ≠ eArith345 as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨21, by decide⟩) (k2 := ⟨22, by decide⟩)
    (by decide) _ _)

lemma eUnifCtrl_disjoint_eRec3DVal (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eUnifCtrl as n K d a ≠ eRec3DVal as n K d q b :=
  fun a b h => ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨13, by decide⟩) (k2 := ⟨21, by decide⟩)
    (by decide) _ _ (ancLen_13 n K d _) q _ (wOf K) _ 1 _ b a h.symm

lemma eRec3DVal_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec3DVal as n K d q a ≠ eArith345 as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨13, by decide⟩) (k2 := ⟨22, by decide⟩)
    (by decide) _ _ (ancLen_13 n K d _) q _ (wOf K) _ subLen _

lemma eRec3_disjoint_eUnifCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec3 as n K d a ≠ eUnifCtrl as n K d b :=
  trans_disjoint_right (eRec3_disjoint_anc_other as n K d ⟨21, by decide⟩ (by decide))

lemma eRec3_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1) :
    ∀ a b, eRec3 as n K d a ≠ eArith345 as n K d subLen hle b :=
  trans_disjoint_right (eRec3_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))

lemma eUnifCtrl_disjoint_eRec3 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eUnifCtrl as n K d a ≠ eRec3 as n K d b :=
  fun a b h => eRec3_disjoint_eUnifCtrl as n K d b a h.symm

lemma eRec3DVal_disjoint_eRec3Kind (as : AlonsoSchottSil54) (n K d : ℕ)
    (q0 q1 : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec3DVal as n K d q0 a ≠ eRec3Kind as n K d q1 b := by
  by_cases hqq : q0 = q1
  · subst hqq
    exact ancRegField_disjoint_field_same as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K)
      (ancLen_13 n K d _) q0 _ _ (Or.inr (le_refl _))
  · exact ancRegField_disjoint_slot as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K)
      (ancLen_13 n K d _) hqq _ _

lemma eRec3DVal_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {q0 q1 : Fin (arity (dHbOf K + 1))} (hq : q0 ≠ q1) :
    ∀ a b, eRec3DVal as n K d q0 a ≠ eRec3DVal as n K d q1 b :=
  ancRegField_disjoint_slot as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K)
    (ancLen_13 n K d _) hq _ _

lemma comp_eRec3Kind (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec3Kind as n K d q = natToBits 2 (L[q.1]'(by omega)).kind := by
  dsimp only [eRec3Kind]
  rw [comp_ancRegField as n K d ⟨13, by decide⟩ _ _ (ancLen_13 n K d _) z _ hz q]
  exact rec3SlotFn_comp_3 ..

lemma comp_eRec3DVal (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec3DVal as n K d q = d_arr q := by
  dsimp only [eRec3DVal]
  rw [comp_ancRegField as n K d ⟨13, by decide⟩ _ _ (ancLen_13 n K d _) z _ hz q]
  exact rec3SlotFn_comp_4 ..

lemma updateOn_eRec3DVal_eq (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) (dv : Qubits (wOf K)) :
    updateOn (eRec3DVal as n K d q) z dv =
      updateOn (eRec3 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL (Function.update d_arr q dv))) := by
  have h1 := updateOn_ancRegSlot_eq as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K)
    (ancLen_13 n K d _) z (hb3ArrOfList K L hL d_arr) hz q
    (hbRecToRec3Bits (wOf K) (L[q.1]'(by omega)) dv)
  have hupd_slot : updateOn (sliceEmb (wK2Hb K + 2) (wOf K) (by dsimp [wR2Hb, wP2Hb]; omega))
      (hb3ArrOfList K L hL d_arr q) dv = hbRecToRec3Bits (wOf K) (L[q.1]'(by omega)) dv := by
    dsimp [hb3ArrOfList, hbRecToRec3Bits]
    exact updateOn_rec3SlotFn_4 ..
  dsimp only [eRec3DVal]
  rw [updateOn_ancRegField_eq_slot,
    comp_ancRegSlot as n K d ⟨13, by decide⟩ _ _ (ancLen_13 n K d _) z _ hz q, hupd_slot, h1]
  have hrec_eq : ancRegSlice as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) =
      eRec3 as n K d := rfl
  rw [hrec_eq]
  apply congrArg (updateOn (eRec3 as n K d) z)
  apply congrArg (flatReg (arity (dHbOf K + 1)) (wR2Hb K))
  funext r
  by_cases hr : r = q
  · subst hr; simp [hb3ArrOfList]
  · simp [hb3ArrOfList, hr]

/-! #### 8.2 Active-Bucket Combinatorial Bijection -/

private lemma runOcc_lt_of_lt {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α)
    {a b : Fin N} (hab : a < b) (hm : runOffset l a = runOffset l b) :
    runOcc l a < runOcc l b := by
  dsimp [runOcc]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨fun x hx => ?_, fun heq => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 hab, hx.2.trans hm⟩
  · have ha_mem : a ∈ Finset.univ.filter (fun x : Fin N => x < b ∧ runOffset l x = runOffset l b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hab, hm⟩
    rw [← heq] at ha_mem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha_mem
    exact lt_irrefl a ha_mem.1

lemma runOffset_runOcc_inj {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) :
    Function.Injective (fun i : Fin N => (runOffset l i, runOcc l i)) := by
  intro a b h
  rcases Prod.ext_iff.mp h with ⟨hm, ho⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact ne_of_lt (runOcc_lt_of_lt l hab hm) ho
  · exact ne_of_lt (runOcc_lt_of_lt l hba hm.symm) ho.symm

def hbKind0Inv {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (r : HBRec) : Prop :=
  r.kind = 0 → ∃ h : r.orig < 2 * K,
    2 ≤ runOffset l ⟨r.orig, h⟩ ∧ r.m = runOffset l ⟨r.orig, h⟩ ∧ r.occ = runOcc l ⟨r.orig, h⟩

lemma hbKind0Inv_hbInit {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    ∀ r ∈ hbInit (2 * K) (arity (dHbOf K)) l, hbKind0Inv l r := by
  intro r hr
  dsimp [hbInit] at hr
  rcases List.mem_append.mp hr with h1 | h2
  · rcases List.mem_map.mp h1 with ⟨i, _, rfl⟩
    by_cases hi : i.1 < 2 * K
    · rw [dif_pos hi]
      by_cases h2le : 2 ≤ runOffset l ⟨i.1, hi⟩
      · rw [if_pos h2le]; intro _; exact ⟨hi, h2le, rfl, rfl⟩
      · rw [if_neg h2le]; intro h0; simp at h0
    · rw [dif_neg hi]; intro h0; simp at h0
  · rcases List.mem_map.mp h2 with ⟨b, _, rfl⟩
    by_cases hb : b.1 < (bucketPairs (2 * K)).length
    · rw [dif_pos hb]; intro h0; simp at h0
    · rw [dif_neg hb]; intro h0; simp at h0

lemma hbKind0Inv_hbNeighborStep {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (L : List HBRec) (p : ℕ) (hL : ∀ r ∈ L, hbKind0Inv l r) :
    ∀ r ∈ hbNeighborStep L p, hbKind0Inv l r := by
  dsimp [hbNeighborStep]
  split_ifs with hp hc
  · intro r hr
    rcases List.mem_iff_getElem.mp hr with ⟨idx, hidx, rfl⟩
    have hlen : (L.set p { L[p] with dest := L[p + 1].dest }).length = L.length := by simp
    by_cases hidx1 : idx = p + 1
    · subst hidx1; rw [List.getElem_set_self]; intro h0; simp at h0
    · have hidx_lt : idx < L.length := by simp only [List.length_set] at hidx; exact hidx
      rw [List.getElem_set_ne (Ne.symm hidx1)]
      by_cases hidx0 : idx = p
      · subst hidx0; rw [List.getElem_set_self]
        intro _; exact hL L[idx] (List.getElem_mem hidx_lt) hc.1
      · rw [List.getElem_set_ne (Ne.symm hidx0)]
        exact hL L[idx] (List.getElem_mem hidx_lt)
  · exact hL
  · exact hL

lemma hbKind0Inv_hbSeqState {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (L : List HBRec) (hL : ∀ r ∈ L, hbKind0Inv l r) (k : ℕ) :
    ∀ r ∈ hbSeqState L k, hbKind0Inv l r := by
  induction k with
  | zero => exact hL
  | succ k ih => rw [hbSeqState_succ]; exact hbKind0Inv_hbNeighborStep l _ k ih

lemma hbKind0Inv_hb2SortedList {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    ∀ r ∈ hb2SortedList K l, hbKind0Inv l r := by
  intro r hr
  have hr_pass : r ∈ hbSeqPass (hb1SortedList K l) := (List.mergeSort_perm _ _).mem_iff.mp hr
  have h1pos : 1 ≤ (hb1SortedList K l).length := by
    rw [hb1SortedList_length, arity_eq_two_pow]; exact Nat.two_pow_pos _
  rw [hbSeqPass_eq_hbSeqState _ h1pos] at hr_pass
  refine hbKind0Inv_hbSeqState l (hb1SortedList K l) ?_ _ r hr_pass
  intro r' hr'
  exact hbKind0Inv_hbInit l r' ((hb1SortedList_mem_iff K l r').mp hr')

lemma hb2SortedList_kind_le_three (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) :
    ∀ r ∈ hb2SortedList K l, r.kind ≤ 3 := fun r hr =>
  (hbSeqPass_hb1_bounds comb h1K l r ((List.mergeSort_perm _ _).mem_iff.mp hr)).1

lemma hb2SortedList_routing_spec (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l) :
    let s2 := hb2SortedList K l
    let bpLen := (bucketPairs (2 * K)).length
    (∀ (b : ℕ) (hb : b < bpLen) (hbN : b < arity (dHbOf K + 1)),
      let r := s2[b]'(by rw [hb2SortedList_length]; exact hbN)
      (r.kind = 0 ↔ ∃ i : Fin (2 * K), 2 ≤ runOffset l i ∧ (runOffset l i, runOcc l i) = (bucketPairs (2 * K))[b]'hb) ∧
      (r.kind = 0 → ∃ h : r.orig < 2 * K,
        2 ≤ runOffset l ⟨r.orig, h⟩ ∧
        (runOffset l ⟨r.orig, h⟩, runOcc l ⟨r.orig, h⟩) = (bucketPairs (2 * K))[b]'hb ∧
        r.m = ((bucketPairs (2 * K))[b]'hb).1) ∧
      (r.kind ≠ 0 → r.kind = 1)) ∧
    (∀ (q : ℕ) (hqN : q < arity (dHbOf K + 1)), bpLen ≤ q →
      (s2[q]'(by rw [hb2SortedList_length]; exact hqN)).kind ≠ 0) := by
  have h2K_B2 : 2 * K ≤ arity (dHbOf K) := Nat.le_of_lt (two_K_lt_B2 h1K)
  have hbp_B2 : (bucketPairs (2 * K)).length ≤ arity (dHbOf K) :=
    Nat.le_of_lt (bucketPairs_length_lt_B2 comb)
  have hspec := comb.harmBucket_routing_spec (2 * K) (arity (dHbOf K)) h2K_B2 hbp_B2 l hl
  have hs2_len : (hb2SortedList K l).length = arity (dHbOf K + 1) := hb2SortedList_length K l
  have har := arity_succ_eq (dHbOf K)
  refine ⟨?_, ?_⟩
  · intro b hb hbN
    have hbB : b < arity (dHbOf K) := lt_of_lt_of_le hb hbp_B2
    have hsp_b := (hspec.2 ⟨b, hbB⟩).2.2 hb
    have hget_bang : (hb2SortedList K l)[b]! = (hb2SortedList K l)[b]'(by rw [hs2_len]; exact hbN) := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hs2_len]; exact hbN)]
    change _ ∧ _ ∧ _
    have hspec_eq : ((hbSeqPass ((hbInit (2 * K) (arity (dHbOf K)) l).mergeSort
        fun x y => decide (hbKey1 x ≤ hbKey1 y))).mergeSort fun x y => decide (hbKey2 x ≤ hbKey2 y))[b]! =
        (hb2SortedList K l)[b]! := rfl
    rw [hspec_eq, hget_bang] at hsp_b
    refine ⟨hsp_b.1, fun hk0 => ?_, hsp_b.2.2⟩
    have hk0inv := hbKind0Inv_hb2SortedList l _ (List.getElem_mem (by rw [hs2_len]; exact hbN)) hk0
    rcases hk0inv with ⟨horig, h2le, hm_eq, ho_eq⟩
    have hm_sp := hsp_b.2.1 hk0
    refine ⟨horig, h2le, Prod.ext (hm_eq.symm.trans hm_sp.1) (ho_eq.symm.trans hm_sp.2.1), hm_sp.1⟩
  · intro q hqN hqbp hk0
    have hk0inv := hbKind0Inv_hb2SortedList l _ (List.getElem_mem (by rw [hs2_len]; exact hqN)) hk0
    rcases hk0inv with ⟨horig, h2le, _, _⟩
    let i : Fin (2 * K) := ⟨_, horig⟩
    have hmem_bp : (runOffset l i, runOcc l i) ∈ bucketPairs (2 * K) := by
      rw [comb.mem_bucketPairs_iff]
      exact ⟨h2le, comb.runOffset_le_N l i, comb.runOcc_lt_div hl i⟩
    rcases List.mem_iff_getElem.mp hmem_bp with ⟨b, hb_lt, hb_eq⟩
    have hbN : b < arity (dHbOf K + 1) := by
      have := bucketPairs_length_lt_B2 comb (K := K); omega
    have hb_ltB : b < arity (dHbOf K) := lt_of_lt_of_le hb_lt hbp_B2
    have hsp_b := (hspec.2 ⟨b, hb_ltB⟩).2.2 hb_lt
    have hget_bang : (hb2SortedList K l)[b]! = (hb2SortedList K l)[b]'(by rw [hs2_len]; exact hbN) := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hs2_len]; exact hbN)]
    have hspec_eq : ((hbSeqPass ((hbInit (2 * K) (arity (dHbOf K)) l).mergeSort
        fun x y => decide (hbKey1 x ≤ hbKey1 y))).mergeSort fun x y => decide (hbKey2 x ≤ hbKey2 y))[b]! =
        (hb2SortedList K l)[b]! := rfl
    rw [hspec_eq, hget_bang] at hsp_b
    have hbk0 : ((hb2SortedList K l)[b]'(by rw [hs2_len]; exact hbN)).kind = 0 :=
      hsp_b.1.mpr ⟨i, h2le, hb_eq.symm⟩
    have hbinv := hbKind0Inv_hb2SortedList l _ (List.getElem_mem (by rw [hs2_len]; exact hbN)) hbk0
    rcases hbinv with ⟨hb_orig, _, hb_m, hb_occ⟩
    have hm_sp := hsp_b.2.1 hbk0
    have hpair_eq : (runOffset l ⟨_, hb_orig⟩, runOcc l ⟨_, hb_orig⟩) = (runOffset l i, runOcc l i) := by
      ext
      · exact hb_m.symm.trans (hm_sp.1.trans (congrArg Prod.fst hb_eq))
      · exact hb_occ.symm.trans (hm_sp.2.1.trans (congrArg Prod.snd hb_eq))
    have hi_eq := runOffset_runOcc_inj l hpair_eq
    have horig_eq : ((hb2SortedList K l)[b]'(by rw [hs2_len]; exact hbN)).orig =
        ((hb2SortedList K l)[q]'(by rw [hs2_len]; exact hqN)).orig :=
      congrArg Fin.val hi_eq
    have hbq : b = q := by
      have hnd := hb2SortedList_orig_nodup K l
      rw [List.nodup_iff_injective_getElem] at hnd
      have hget := @hnd ⟨b, by rw [List.length_map, hs2_len]; exact hbN⟩
        ⟨q, by rw [List.length_map, hs2_len]; exact hqN⟩
      simp only [List.getElem_map] at hget
      exact Fin.val_eq_of_eq (hget horig_eq)
    omega

noncomputable def bucketOfActive (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l) :
    { b : Fin (bucketPairs (2 * K)).length //
      ((hb2SortedList K l)[b.1]'(by
        rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K)
        have := arity_succ_eq (dHbOf K); omega)).kind = 0 } ≃
    { i : Fin (2 * K) // 2 ≤ runOffset l i } :=
  have hrt := hb2SortedList_routing_spec comb h1K l hl
  have hN_len : ∀ b : Fin (bucketPairs (2 * K)).length, b.1 < (hb2SortedList K l).length := fun b => by
    rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega
  have hN_lenA : ∀ b : Fin (bucketPairs (2 * K)).length, b.1 < arity (dHbOf K + 1) := fun b => by
    have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega
  let f : { b : Fin (bucketPairs (2 * K)).length //
      ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0 } →
      { i : Fin (2 * K) // 2 ≤ runOffset l i } := fun b =>
    let hsp := (hrt.1 b.1 b.1.isLt (hN_lenA b.1)).2.1 b.2
    ⟨⟨((hb2SortedList K l)[b.1.1]'(hN_len b.1)).orig, hsp.choose⟩, hsp.choose_spec.1⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro b₁ b₂ heq
      have hval : ((hb2SortedList K l)[b₁.1.1]'(hN_len b₁.1)).orig =
          ((hb2SortedList K l)[b₂.1.1]'(hN_len b₂.1)).orig :=
        congrArg (fun x => x.1.1) heq
      have hnd := List.nodup_iff_injective_getElem.mp (hb2SortedList_orig_nodup K l)
      have hlen_map : ((hb2SortedList K l).map (·.orig)).length = (hb2SortedList K l).length :=
        List.length_map _
      have hval_get : ((hb2SortedList K l).map (·.orig))[b₁.1.1]'(hlen_map ▸ hN_len b₁.1) =
          ((hb2SortedList K l).map (·.orig))[b₂.1.1]'(hlen_map ▸ hN_len b₂.1) := by
        simp only [List.getElem_map]; exact hval
      have heq_idx := @hnd ⟨b₁.1.1, hlen_map ▸ hN_len b₁.1⟩ ⟨b₂.1.1, hlen_map ▸ hN_len b₂.1⟩ hval_get
      exact Subtype.ext (Fin.ext (Fin.mk.inj heq_idx))
    · intro ⟨i, hi⟩
      have hmem : (runOffset l i, runOcc l i) ∈ bucketPairs (2 * K) := by
        rw [comb.mem_bucketPairs_iff]; exact ⟨hi, comb.runOffset_le_N l i, comb.runOcc_lt_div hl i⟩
      rcases List.mem_iff_getElem.mp hmem with ⟨b, hb_lt, hb_eq⟩
      have hk0 : ((hb2SortedList K l)[b]'(hN_len ⟨b, hb_lt⟩)).kind = 0 :=
        (hrt.1 b hb_lt (hN_lenA ⟨b, hb_lt⟩)).1.mpr ⟨i, hi, hb_eq.symm⟩
      refine ⟨⟨⟨b, hb_lt⟩, hk0⟩, Subtype.ext ?_⟩
      have hsp := ((hrt.1 b hb_lt (hN_lenA ⟨b, hb_lt⟩)).2.1 hk0).choose_spec
      exact runOffset_runOcc_inj l (hsp.2.1.trans hb_eq)
  Equiv.ofBijective f hbij

lemma bucketOfActive_spec (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (b : Fin (bucketPairs (2 * K)).length)
    (hk0 : ((hb2SortedList K l)[b.1]'(by
      rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K)
      have := arity_succ_eq (dHbOf K); omega)).kind = 0) :
    let i := (bucketOfActive comb h1K l hl ⟨b, hk0⟩).1
    i.1 = ((hb2SortedList K l)[b.1]'(by
      rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K)
      have := arity_succ_eq (dHbOf K); omega)).orig ∧
    runOffset l i = ((bucketPairs (2 * K))[b.1]).1 := by
  dsimp [bucketOfActive]
  have hN_len : b.1 < arity (dHbOf K + 1) := by
    have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega
  have hsp := ((hb2SortedList_routing_spec comb h1K l hl).1 b.1 b.isLt hN_len).2.1 hk0
  exact ⟨rfl, congrArg Prod.fst hsp.choose_spec.2.1⟩

def M_hb (comb : LcgSym54Comb) (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (b : Fin (bucketPairs (2 * K)).length) : ℕ :=
  if ((hb2SortedList K l)[b.1]'(by
    rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K)
    have := arity_succ_eq (dHbOf K); omega)).kind = 0
  then ((bucketPairs (2 * K))[b.1]).1 else 1

def M_pref (comb : LcgSym54Comb) (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (k : ℕ) (b : Fin (bucketPairs (2 * K)).length) : ℕ :=
  if b.1 < k then M_hb comb K l b else 1

def dOfHBRec (w N : ℕ) {α : Type*} [LinearOrder α] (l : Fin N → α) (d : (i : Fin N) → Fin (runOffset l i))
    (r : HBRec) : Qubits w :=
  if r.kind = 0 then if h : r.orig < N then natToBits w (d ⟨r.orig, h⟩).1 else fun _ => false
  else fun _ => false

noncomputable def dRec3Of (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
  dOfHBRec (wOf K) (2 * K) l dFn ((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt))

noncomputable def dArrOfPref (comb : LcgSym54Comb) (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (k : ℕ) (dP : (b : Fin (bucketPairs (2 * K)).length) → Fin (M_pref comb K l k b))
    (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
  if hqb : q.1 < (bucketPairs (2 * K)).length then
    if q.1 < k ∧ ((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt)).kind = 0 then
      natToBits (wOf K) (dP ⟨q.1, hqb⟩).1
    else fun _ => false
  else fun _ => false

noncomputable def dEquivActiveBucket (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l) :
    ((b : Fin (bucketPairs (2 * K)).length) → Fin (M_hb comb K l b)) ≃
      ((i : Fin (2 * K)) → Fin (runOffset l i)) :=
  let hN_len : ∀ b : Fin (bucketPairs (2 * K)).length, b.1 < (hb2SortedList K l).length := fun b => by
    rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega
  let e := bucketOfActive comb h1K l hl
  let toFun : ((b : Fin (bucketPairs (2 * K)).length) → Fin (M_hb comb K l b)) →
      ((i : Fin (2 * K)) → Fin (runOffset l i)) := fun dB i =>
    if hi : 2 ≤ runOffset l i then
      let b := e.symm ⟨i, hi⟩
      have hm_eq : M_hb comb K l b.1 = runOffset l i := by
        have hsp := bucketOfActive_spec comb h1K l hl b.1 b.2
        have hb_eq : e b = ⟨i, hi⟩ := e.apply_symm_apply ⟨i, hi⟩
        have hi_eq : (e b).1 = i := congrArg Subtype.val hb_eq
        dsimp [M_hb]; rw [if_pos b.2, ← hsp.2, hi_eq]
      Fin.cast hm_eq (dB b.1)
    else
      ⟨0, comb.runOffset_pos l i⟩
  let invFun : ((i : Fin (2 * K)) → Fin (runOffset l i)) →
      ((b : Fin (bucketPairs (2 * K)).length) → Fin (M_hb comb K l b)) := fun dFn b =>
    if hk0 : ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0 then
      let i := e ⟨b, hk0⟩
      have hm_eq : runOffset l i.1 = M_hb comb K l b := by
        have hsp := bucketOfActive_spec comb h1K l hl b hk0
        dsimp [M_hb]; rw [if_pos hk0]; exact hsp.2
      Fin.cast hm_eq (dFn i.1)
    else
      ⟨0, by dsimp [M_hb]; rw [if_neg hk0]; omega⟩
  { toFun := toFun
    invFun := invFun
    left_inv := fun dB => by
      funext b
      dsimp only [toFun, invFun]
      by_cases hk0 : ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0
      · rw [dif_pos hk0]
        have hi := (e ⟨b, hk0⟩).2
        rw [dif_pos hi]
        have hsymm : e.symm (e ⟨b, hk0⟩) = ⟨b, hk0⟩ := e.symm_apply_apply _
        apply Fin.ext
        simp only [Fin.val_cast]
        exact congrArg (fun x : { b // _ } => (dB x.1).1) hsymm
      · rw [dif_neg hk0]
        have hm1 : M_hb comb K l b = 1 := by dsimp [M_hb]; rw [if_neg hk0]
        apply Fin.ext; have hlt := (dB b).isLt; omega
    right_inv := fun dFn => by
      funext i
      dsimp only [toFun, invFun]
      by_cases hi : 2 ≤ runOffset l i
      · rw [dif_pos hi]
        let b := e.symm ⟨i, hi⟩
        rw [dif_pos b.2]
        have heq : e b = ⟨i, hi⟩ := e.apply_symm_apply ⟨i, hi⟩
        apply Fin.ext
        simp only [Fin.val_cast]
        exact congrArg (fun x : { i // _ } => (dFn x.1).1) heq
      · rw [dif_neg hi]
        have hpos := comb.runOffset_pos l i
        apply Fin.ext; have hlt := (dFn i).isLt; omega }

lemma dArrOfPref_full_eq_dRec3Of (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (dB : (b : Fin (bucketPairs (2 * K)).length) → Fin (M_hb comb K l b)) :
    dArrOfPref comb K l (bucketPairs (2 * K)).length
        (fun b => Fin.cast (by dsimp [M_pref]; rw [if_pos b.isLt]) (dB b)) =
      dRec3Of K l (dEquivActiveBucket comb h1K l hl dB) := by
  funext q
  have hrt := hb2SortedList_routing_spec comb h1K l hl
  dsimp only [dArrOfPref, dRec3Of, dOfHBRec]
  by_cases hqb : q.1 < (bucketPairs (2 * K)).length
  · rw [dif_pos hqb]
    by_cases hk0 : ((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt)).kind = 0
    · rw [if_pos ⟨hqb, hk0⟩, if_pos hk0]
      have hsp := bucketOfActive_spec comb h1K l hl ⟨q.1, hqb⟩ hk0
      have horig : ((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt)).orig < 2 * K := by
        rw [← hsp.1]; exact (bucketOfActive comb h1K l hl ⟨⟨q.1, hqb⟩, hk0⟩).1.isLt
      rw [dif_pos horig]
      congr 1
      dsimp only [dEquivActiveBucket, Equiv.coe_fn_mk]
      let i : Fin (2 * K) := ⟨((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt)).orig, horig⟩
      have hi_act : 2 ≤ runOffset l i := by
        have h1 := (bucketOfActive comb h1K l hl ⟨⟨q.1, hqb⟩, hk0⟩).2
        have hieq : i = (bucketOfActive comb h1K l hl ⟨⟨q.1, hqb⟩, hk0⟩).1 := Fin.ext hsp.1
        rw [hieq]; exact h1
      rw [dif_pos hi_act]
      have hieq : (⟨i, hi_act⟩ : { i // 2 ≤ runOffset l i }) = bucketOfActive comb h1K l hl ⟨⟨q.1, hqb⟩, hk0⟩ :=
        Subtype.ext (Fin.ext hsp.1)
      simp only [Fin.val_cast]
      have hsymm : (bucketOfActive comb h1K l hl).symm ⟨i, hi_act⟩ = ⟨⟨q.1, hqb⟩, hk0⟩ := by
        have h := (bucketOfActive comb h1K l hl).symm_apply_apply ⟨⟨q.1, hqb⟩, hk0⟩
        rw [← hieq] at h; exact h
      exact congrArg (fun x : { b // _ } => (dB x.1).1) hsymm.symm
    · rw [if_neg (fun h => hk0 h.2), if_neg hk0]
  · rw [dif_neg hqb]
    have hnk0 := hrt.2 q.1 q.isLt (Nat.not_lt.mp hqb)
    rw [if_neg hnk0]

private lemma prod_sqrt_inv_real {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) (_hf : ∀ i, 1 ≤ f i) :
    (∏ i : ι, (if f i = 1 then (1 : ℝ) else 1 / Real.sqrt (f i : ℝ))) =
      1 / Real.sqrt ((∏ i : ι, f i : ℕ) : ℝ) := by
  have h1 : ∀ i : ι, (if f i = 1 then (1 : ℝ) else 1 / Real.sqrt (f i : ℝ)) =
      (Real.sqrt (f i : ℝ))⁻¹ := fun i => by
    split_ifs with h
    · simp [h]
    · rw [one_div]
  simp_rw [h1, Finset.prod_inv_distrib, Nat.cast_prod]
  rw [← one_div]
  congr 1
  have hsq : ∀ (s : Finset ι), (∏ i ∈ s, Real.sqrt (f i : ℝ)) = Real.sqrt (∏ i ∈ s, (f i : ℝ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
        Real.sqrt_mul (Nat.cast_nonneg _)]
  exact hsq Finset.univ

lemma prod_M_hb_inv_sqrt_eq (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l) :
    ((∏ b : Fin (bucketPairs (2 * K)).length,
      (if ((hb2SortedList K l)[b.1]'(by
          rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K)
          have := arity_succ_eq (dHbOf K); omega)).kind = 0
        then 1 / Real.sqrt (((bucketPairs (2 * K))[b.1]).1 : ℝ) else 1) : ℝ) : ℂ) =
      ((1 / Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) : ℂ) := by
  congr 1
  have hN_len : ∀ b : Fin (bucketPairs (2 * K)).length, b.1 < (hb2SortedList K l).length := fun b => by
    rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega
  have hpos_M : ∀ b : Fin (bucketPairs (2 * K)).length, 1 ≤ M_hb comb K l b := fun b => by
    dsimp [M_hb]; split_ifs with hk0
    · have hmem : (bucketPairs (2 * K))[b.1] ∈ bucketPairs (2 * K) := List.getElem_mem b.isLt
      have hm := (comb.mem_bucketPairs_iff (2 * K) _ _).mp hmem
      simp only [List.get_eq_getElem] at hm
      omega
    · omega
  have heq_ite : ∀ b : Fin (bucketPairs (2 * K)).length,
      (if ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0
        then 1 / Real.sqrt (((bucketPairs (2 * K))[b.1]).1 : ℝ) else 1) =
      (if M_hb comb K l b = 1 then (1 : ℝ) else 1 / Real.sqrt (M_hb comb K l b : ℝ)) := fun b => by
    by_cases hk0 : ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0
    · have hmem : (bucketPairs (2 * K))[b.1] ∈ bucketPairs (2 * K) := List.getElem_mem b.isLt
      have hm := (comb.mem_bucketPairs_iff (2 * K) _ _).mp hmem
      simp only [List.get_eq_getElem] at hm
      have hm1 : M_hb comb K l b ≠ 1 := by dsimp [M_hb]; rw [if_pos hk0]; omega
      rw [if_pos hk0, if_neg hm1]; dsimp [M_hb]; rw [if_pos hk0]
    · have hm1 : M_hb comb K l b = 1 := by dsimp [M_hb]; rw [if_neg hk0]
      rw [if_neg hk0, if_pos hm1]
  simp_rw [heq_ite]
  rw [prod_sqrt_inv_real (M_hb comb K l) hpos_M]
  congr 2
  have hprod_M : ∏ b : Fin (bucketPairs (2 * K)).length, M_hb comb K l b =
      ∏ i : Fin (2 * K), runOffset l i := by
    have hsplitL : ∏ b : Fin (bucketPairs (2 * K)).length, M_hb comb K l b =
        ∏ b : { b : Fin (bucketPairs (2 * K)).length // ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0 },
          M_hb comb K l b.1 := by
      rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin (bucketPairs (2 * K)).length))
        (fun b => ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0)]
      have hone : (∏ b ∈ Finset.univ.filter (fun b => ¬ ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0),
          M_hb comb K l b) = 1 := Finset.prod_eq_one fun b hb => by
        have hnot := (Finset.mem_filter.mp hb).2
        dsimp [M_hb]; rw [if_neg hnot]
      rw [hone, mul_one, ← Finset.prod_subtype (Finset.univ.filter (fun b => ((hb2SortedList K l)[b.1]'(hN_len b)).kind = 0))
        (by intro x; simp)]
    have hsplitR : ∏ i : Fin (2 * K), runOffset l i =
        ∏ i : { i : Fin (2 * K) // 2 ≤ runOffset l i }, runOffset l i.1 := by
      rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin (2 * K)))
        (fun i => 2 ≤ runOffset l i)]
      have hone : (∏ i ∈ Finset.univ.filter (fun i => ¬ 2 ≤ runOffset l i), runOffset l i) = 1 :=
        Finset.prod_eq_one fun i hi => by
          have hnot := (Finset.mem_filter.mp hi).2
          have hpos := comb.runOffset_pos l i
          omega
      rw [hone, mul_one, ← Finset.prod_subtype (Finset.univ.filter (fun i => 2 ≤ runOffset l i))
        (by intro x; simp)]
    rw [hsplitL, hsplitR]
    refine Fintype.prod_equiv (bucketOfActive comb h1K l hl) _ _ fun b => ?_
    have hsp := bucketOfActive_spec comb h1K l hl b.1 b.2
    dsimp [M_hb]; rw [if_pos b.2]; exact hsp.2.symm
  rw [hprod_M, comb.prod_runOffset_eq_prod_modeCount (2 * K) l hl,
    ← comb.card_stabGroup_eq_prod_modeCount (2 * K) l]

/-! #### 8.3 Step 4 Circuit (`unifBucketsCirc`) -/

private lemma act_smul' {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act A (c • ψ) = c • act A ψ := by
  ext i; simp [act, Matrix.mulVec_smul]

private lemma act_sum' {ι κ : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (s : Finset κ) (f : κ → EuclideanSpace ℂ ι) :
    act A (∑ x ∈ s, f x) = ∑ x ∈ s, act A (f x) := by
  ext i; simp [act, Matrix.mulVec_sum]

private lemma updateOn_comb3_padZero_unif {w m : ℕ}
    (e1 : Fin 1 ↪ Fin m) (e2 : Fin w ↪ Fin m) (e3 : Fin w ↪ Fin m)
    (h12 : ∀ i j, e1 i ≠ e2 j) (h13 : ∀ i k, e1 i ≠ e3 k) (h23 : ∀ j k, e2 j ≠ e3 k)
    (z : Qubits m) (ctrlBit : Bool) (h1 : z ∘ e1 = fun _ => ctrlBit) (h3 : z ∘ e3 = fun _ => false)
    (v : Qubits w) :
    updateOn (comb3 e1 e2 e3 h12 h13 h23) z
        (padZero (1 + w) w (Fin.append (fun _ : Fin 1 => ctrlBit) v)) =
      updateOn e2 z v := by
  dsimp only [comb3]
  funext u
  by_cases hu2 : u ∈ Set.range e2
  · rcases hu2 with ⟨j, rfl⟩
    have hmem : e2 j = combineEmb (combineEmb e1 e2 h12) e3 (emb_disjoint_combineEmb h12 h13 h23)
        (Fin.castAdd w (Fin.natAdd 1 j)) := by simp
    conv_lhs => rw [hmem, updateOn_apply_emb]
    rw [padZero_castAdd, Fin.append_right, updateOn_apply_emb]
  · rw [updateOn_apply_not_mem _ _ _ hu2]
    by_cases hu1 : u ∈ Set.range e1
    · rcases hu1 with ⟨i, rfl⟩
      have hmem : e1 i = combineEmb (combineEmb e1 e2 h12) e3 (emb_disjoint_combineEmb h12 h13 h23)
          (Fin.castAdd w (Fin.castAdd w i)) := by simp
      conv_lhs => rw [hmem, updateOn_apply_emb]
      rw [padZero_castAdd, Fin.append_left]
      exact (congrFun h1 i).symm
    · by_cases hu3 : u ∈ Set.range e3
      · rcases hu3 with ⟨k, rfl⟩
        have hmem : e3 k = combineEmb (combineEmb e1 e2 h12) e3 (emb_disjoint_combineEmb h12 h13 h23)
            (Fin.natAdd (1 + w) k) := by simp
        conv_lhs => rw [hmem, updateOn_apply_emb]
        rw [padZero_natAdd]
        exact (congrFun h3 k).symm
      · have hnot : u ∉ Set.range (combineEmb (combineEmb e1 e2 h12) e3 (emb_disjoint_combineEmb h12 h13 h23)) := by
          rintro ⟨x, rfl⟩
          induction x using Fin.addCases with
          | left xy =>
            induction xy using Fin.addCases with
            | left i => apply hu1; exact ⟨i, by simp⟩
            | right j => apply hu2; exact ⟨j, by simp⟩
          | right k => apply hu3; exact ⟨k, by simp⟩
        rw [updateOn_apply_not_mem _ _ _ hnot]

def unifBucketStepCirc (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (b : ℕ) (hb : b < (bucketPairs (2 * K)).length) : LayeredCircuit (totWiresDef as n K d) :=
  have h5w := five_le_wOf h1K
  have hqB : b < arity (dHbOf K + 1) := by
    have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega
  let qB : Fin (arity (dHbOf K + 1)) := ⟨b, hqB⟩
  let m_b := ((bucketPairs (2 * K))[b]'hb).1
  have hm_mem := (comb.mem_bucketPairs_iff (2 * K) m_b _).mp (by
    change (bucketPairs (2 * K))[b]'hb ∈ bucketPairs (2 * K); exact List.getElem_mem hb)
  have hm1 : 1 ≤ m_b := by omega
  have hm2 : m_b ≤ 2 ^ wOf K := by
    have hlt := two_K_lt_B2 h1K
    have hbw := two_mul_B2_add_one_lt_two_pow_wOf h1K
    omega
  let cEq := (arith.eqConstMSBCircuit 2 0).mapWires
    (comb3 (eRec3Kind as n K d qB) (eUnifCtrl as n K d) (eArith345 as n K d 2 (by omega))
      (eRec3Kind_disjoint_eUnifCtrl as n K d qB)
      (eRec3Kind_disjoint_eArith345 as n K d 2 (by omega) qB)
      (eUnifCtrl_disjoint_eArith345 as n K d 2 (by omega)))
  let cUnif := (br.unifPrefixCircuit (wOf K) m_b hm1 hm2).mapWires
    (comb3 (eUnifCtrl as n K d) (eRec3DVal as n K d qB) (eArith345 as n K d (wOf K) (Nat.le_succ _))
      (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
      (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
      (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB))
  LayeredCircuit.seqList [cEq, cUnif, cEq]

lemma unifBucketStepCirc_size (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (b : ℕ) (hb : b < (bucketPairs (2 * K)).length) :
    ((unifBucketStepCirc comb br as arith n K d h1K b hb).size : ℝ) ≤
      80 + br.C_unif * ((wOf K : ℝ) + 1) ^ 2 := by
  dsimp [unifBucketStepCirc]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size, Nat.cast_add]
  have h1 : ((arith.eqConstMSBCircuit 2 0).size : ℝ) ≤ 40 := by
    exact_mod_cast (by have := arith.eqConstMSBCircuit_size 2 0; omega : (arith.eqConstMSBCircuit 2 0).size ≤ 40)
  have h5w := five_le_wOf h1K
  have hm_mem := (comb.mem_bucketPairs_iff (2 * K) ((bucketPairs (2 * K))[b]'hb).1 _).mp
    (List.getElem_mem hb)
  simp only [List.get_eq_getElem] at hm_mem
  have hm1 : 1 ≤ ((bucketPairs (2 * K))[b]'hb).1 := by omega
  have hm2 : ((bucketPairs (2 * K))[b]'hb).1 ≤ 2 ^ wOf K := by
    have hlt := two_K_lt_B2 h1K
    have hbw := two_mul_B2_add_one_lt_two_pow_wOf h1K
    omega
  have h2 := br.unifPrefixCircuit_size (wOf K) ((bucketPairs (2 * K))[b]'hb).1 hm1 hm2
  linarith

lemma act_unifBucketStepCirc (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) {l : Fin (2 * K) → Fin (n + 1)}
    (_hl : Monotone l) (b : ℕ) (hb : b < (bucketPairs (2 * K)).length)
    (z : Qubits (totWiresDef as n K d))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz3 : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) d_arr))
    (hqB_zero : d_arr ⟨b, by
      have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega⟩ = fun _ => false)
    (hzCtrl : z ∘ eUnifCtrl as n K d = fun _ => false)
    (hz22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false) :
    let qB : Fin (arity (dHbOf K + 1)) := ⟨b, by
      have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega⟩
    let rB := (hb2SortedList K l)[b]'(by rw [hb2SortedList_length]; exact qB.isLt)
    let m_b := ((bucketPairs (2 * K))[b]'hb).1
    act (unifBucketStepCirc comb br as arith n K d h1K b hb).unitary (ket z) =
      if rB.kind = 0 then
        ((1 / Real.sqrt (m_b : ℝ) : ℝ) : ℂ) • ∑ v : Fin m_b,
          ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
            (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l)
              (Function.update d_arr qB (natToBits (wOf K) v.1)))))
      else ket z := by
  have h5w := five_le_wOf h1K
  intro qB rB m_b
  have hk_lt4 : rB.kind < 4 := by
    have := hb2SortedList_kind_le_three comb h1K l rB (List.getElem_mem (by rw [hb2SortedList_length]; exact qB.isLt))
    omega
  have hz_k : z ∘ eRec3Kind as n K d qB = natToBits 2 rB.kind :=
    comp_eRec3Kind as n K d z _ (hb2SortedList_length K l) d_arr hz3 qB
  have hz_dv : z ∘ eRec3DVal as n K d qB = fun _ => false :=
    (comp_eRec3DVal as n K d z _ (hb2SortedList_length K l) d_arr hz3 qB).trans hqB_zero
  have hz_a2 : z ∘ eArith345 as n K d 2 (by omega) = fun _ => false := funext fun j => congrFun hz22 _
  have hz_aW : z ∘ eArith345 as n K d (wOf K) (Nat.le_succ _) = fun _ => false := funext fun j => congrFun hz22 _
  let flag : Bool := decide (rB.kind = 0)
  have hdec : decide (z ∘ eRec3Kind as n K d qB = natToBits 2 0) = flag := by
    rw [hz_k, Bool.eq_iff_iff, decide_eq_true_eq]
    dsimp [flag]; rw [decide_eq_true_eq]
    exact ⟨fun h => by have := congrArg bitsToNat h; rw [comb.bitsToNat_natToBits hk_lt4, comb.bitsToNat_natToBits (by norm_num)] at this; exact this,
      fun h => by rw [h]⟩
  let z1 := updateOn (eUnifCtrl as n K d) z (fun _ => flag)
  dsimp only [unifBucketStepCirc, comb3]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  -- 1. cEq: set eUnifCtrl = flag
  rw [act_eqConstOn arith
    (hIO := eRec3Kind_disjoint_eUnifCtrl as n K d qB)
    (hIA := eRec3Kind_disjoint_eArith345 as n K d 2 (by omega) qB)
    (hOA := eUnifCtrl_disjoint_eArith345 as n K d 2 (by omega))
    (hzAnc := hz_a2)]
  have hzCtrl0 : z (eUnifCtrl as n K d 0) = false := congrFun hzCtrl 0
  rw [hzCtrl0, hdec, xor_false_left]
  change act _ (act _ (ket z1)) = _
  -- Facts on z1
  have hz1_ctrl : z1 ∘ eUnifCtrl as n K d = fun _ => flag := updateOn_comp_emb _ _ _
  have hz1_dv : z1 ∘ eRec3DVal as n K d qB = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eUnifCtrl_disjoint_eRec3DVal as n K d qB)]; exact hz_dv
  have hz1_aW : z1 ∘ eArith345 as n K d (wOf K) (Nat.le_succ _) = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))]
    exact hz_aW
  have hz1_a2 : z1 ∘ eArith345 as n K d 2 (by omega) = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eUnifCtrl_disjoint_eArith345 as n K d 2 (by omega))]
    exact hz_a2
  have hz1_k : z1 ∘ eRec3Kind as n K d qB = natToBits 2 rB.kind := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec3Kind_disjoint_eUnifCtrl as n K d qB b a h.symm)]
    exact hz_k
  have hcomp_unif : z1 ∘ combineEmb (combineEmb (eUnifCtrl as n K d) (eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB))
      (eArith345 as n K d (wOf K) (Nat.le_succ _))
      (emb_disjoint_combineEmb (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
        (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB)) =
      padZero (1 + wOf K) (wOf K) (Fin.append (fun _ : Fin 1 => flag) (fun _ : Fin (wOf K) => false)) := by
    funext u
    induction u using Fin.addCases with
    | left ij =>
      rw [Function.comp_apply, combineEmb_castAdd, padZero_castAdd]
      induction ij using Fin.addCases with
      | left i => rw [combineEmb_castAdd, Fin.append_left]; exact congrFun hz1_ctrl i
      | right j => rw [combineEmb_natAdd, Fin.append_right]; exact congrFun hz1_dv j
    | right k =>
      rw [Function.comp_apply, combineEmb_natAdd, padZero_natAdd]; exact congrFun hz1_aW k
  have hm1 : 1 ≤ m_b := by
    have hm := (comb.mem_bucketPairs_iff (2 * K) m_b _).mp (List.getElem_mem hb)
    omega
  have hm2 : m_b ≤ 2 ^ wOf K := by
    have hm := (comb.mem_bucketPairs_iff (2 * K) m_b _).mp (List.getElem_mem hb)
    have hlt := two_K_lt_B2 h1K
    have hbw := two_mul_B2_add_one_lt_two_pow_wOf h1K
    omega
  by_cases hrk0 : rB.kind = 0
  · have hflag : flag = true := decide_eq_true hrk0
    rw [if_pos hrk0]
    have hunif := LcgSym54.act_mapWires_ket_sum (br.unifPrefixCircuit (wOf K) m_b hm1 hm2)
      (combineEmb (combineEmb (eUnifCtrl as n K d) (eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB))
        (eArith345 as n K d (wOf K) (Nat.le_succ _))
        (emb_disjoint_combineEmb (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
          (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
          (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB)))
      z1 (Finset.univ : Finset (Fin m_b)) (fun _ => ((1 / Real.sqrt (m_b : ℝ) : ℝ) : ℂ))
      (fun v => padZero (1 + wOf K) (wOf K) (Fin.append (fun _ : Fin 1 => true) (natToBits (wOf K) v.1)))
      (by
        rw [hcomp_unif, hflag]
        simpa [Finset.smul_sum] using br.act_unifPrefixCircuit_true (wOf K) m_b hm1 hm2)
    rw [hunif, ← Finset.smul_sum, act_smul', act_sum']
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    have hupd_z : updateOn (combineEmb (combineEmb (eUnifCtrl as n K d) (eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB))
        (eArith345 as n K d (wOf K) (Nat.le_succ _))
        (emb_disjoint_combineEmb (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
          (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
          (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB))) z1
        (padZero (1 + wOf K) (wOf K) (Fin.append (fun _ : Fin 1 => true) (natToBits (wOf K) v.1))) =
        updateOn (eRec3DVal as n K d qB) z1 (natToBits (wOf K) v.1) := by
      have h1 : z1 ∘ eUnifCtrl as n K d = fun _ => true := by rw [hz1_ctrl, hflag]
      exact updateOn_comb3_padZero_unif (eUnifCtrl as n K d) (eRec3DVal as n K d qB)
        (eArith345 as n K d (wOf K) (Nat.le_succ _))
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
        (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB)
        z1 true h1 hz1_aW (natToBits (wOf K) v.1)
    rw [hupd_z]
    let z2v := updateOn (eRec3DVal as n K d qB) z1 (natToBits (wOf K) v.1)
    have hz2_a2 : z2v ∘ eArith345 as n K d 2 (by omega) = fun _ => false := by
      dsimp only [z2v]
      rw [updateOn_comp_disjoint _ _ (eRec3DVal_disjoint_eArith345 as n K d 2 (by omega) qB)]
      exact hz1_a2
    rw [act_eqConstOn arith
      (hIO := eRec3Kind_disjoint_eUnifCtrl as n K d qB)
      (hIA := eRec3Kind_disjoint_eArith345 as n K d 2 (by omega) qB)
      (hOA := eUnifCtrl_disjoint_eArith345 as n K d 2 (by omega))
      (hzAnc := hz2_a2)]
    have hz2_k : z2v ∘ eRec3Kind as n K d qB = natToBits 2 rB.kind := by
      dsimp only [z2v]
      rw [updateOn_comp_disjoint _ _ (eRec3DVal_disjoint_eRec3Kind as n K d qB qB)]
      exact hz1_k
    have hdec2 : decide (z2v ∘ eRec3Kind as n K d qB = natToBits 2 0) = true := by
      rw [hz2_k, decide_eq_true_eq, hrk0]
    have hz2_ctrl0 : z2v (eUnifCtrl as n K d 0) = true := by
      dsimp only [z2v]
      rw [← Function.comp_apply (f := updateOn _ z1 _),
        updateOn_comp_disjoint _ _ (fun a b h => eUnifCtrl_disjoint_eRec3DVal as n K d qB b a h.symm)]
      rw [hz1_ctrl, hflag]
    rw [hz2_ctrl0, hdec2, xor_self_cancel]
    have hz2_unupd : updateOn (eUnifCtrl as n K d) z2v (fun _ => false) =
        updateOn (eRec3DVal as n K d qB) z (natToBits (wOf K) v.1) := by
      dsimp only [z2v, z1]
      rw [updateOn_comm (eUnifCtrl as n K d) (eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB), updateOn_idem,
        updateOn_noop (eUnifCtrl as n K d) z (fun _ => false) hzCtrl]
    rw [hz2_unupd, updateOn_eRec3DVal_eq as n K d z _ (hb2SortedList_length K l) d_arr hz3 qB]
  · have hflag : flag = false := decide_eq_false hrk0
    rw [if_neg hrk0]
    have hz1_eq_z : z1 = z := by
      dsimp only [z1]; rw [hflag]; apply updateOn_noop; exact hzCtrl
    rw [hz1_eq_z]
    have hcomp_f := hcomp_unif
    rw [hz1_eq_z, hflag] at hcomp_f
    have hunif_f := act_mapWires_ket_singleton (br.unifPrefixCircuit (wOf K) m_b hm1 hm2) _ z
      (padZero (1 + wOf K) (wOf K) (Fin.append (fun _ : Fin 1 => false) (fun _ : Fin (wOf K) => false)))
      (by
        rw [hcomp_f]
        exact br.act_unifPrefixCircuit_false (wOf K) m_b hm1 hm2 (fun _ => false))
    rw [hunif_f]
    have hupd_f : updateOn (combineEmb (combineEmb (eUnifCtrl as n K d) (eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB))
        (eArith345 as n K d (wOf K) (Nat.le_succ _))
        (emb_disjoint_combineEmb (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
          (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
          (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB))) z
        (padZero (1 + wOf K) (wOf K) (Fin.append (fun _ : Fin 1 => false) (fun _ : Fin (wOf K) => false))) = z := by
      change updateOn (comb3 (eUnifCtrl as n K d) (eRec3DVal as n K d qB) (eArith345 as n K d (wOf K) (Nat.le_succ _))
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
        (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB)) z
        (padZero (1 + wOf K) (wOf K) (Fin.append (fun _ : Fin 1 => false) (fun _ : Fin (wOf K) => false))) = z
      rw [updateOn_comb3_padZero_unif (eUnifCtrl as n K d) (eRec3DVal as n K d qB)
        (eArith345 as n K d (wOf K) (Nat.le_succ _))
        (eUnifCtrl_disjoint_eRec3DVal as n K d qB)
        (eUnifCtrl_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _))
        (eRec3DVal_disjoint_eArith345 as n K d (wOf K) (Nat.le_succ _) qB)
        z false hzCtrl hz_aW (fun _ => false)]
      apply updateOn_noop; exact hz_dv
    rw [hupd_f]
    rw [act_eqConstOn arith
      (hIO := eRec3Kind_disjoint_eUnifCtrl as n K d qB)
      (hIA := eRec3Kind_disjoint_eArith345 as n K d 2 (by omega) qB)
      (hOA := eUnifCtrl_disjoint_eArith345 as n K d 2 (by omega))
      (hzAnc := hz_a2)]
    have hdec_f : decide (z ∘ eRec3Kind as n K d qB = natToBits 2 0) = false := by
      rw [hdec]; exact hflag
    have hzCtrl0' : z (eUnifCtrl as n K d 0) = false := congrFun hzCtrl 0
    rw [hzCtrl0', hdec_f, Bool.xor_false]
    congr 1; apply updateOn_noop; exact hzCtrl

def unifBucketsCirc (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) : LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (bucketPairs (2 * K)).length).map fun b =>
    if hb : b < (bucketPairs (2 * K)).length then unifBucketStepCirc comb br as arith n K d h1K b hb
    else LayeredCircuit.id _)

lemma unifBucketsCirc_size (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    ((unifBucketsCirc comb br as arith n K d h1K).size : ℝ) ≤
      ((bucketPairs (2 * K)).length : ℝ) * (80 + br.C_unif * ((wOf K : ℝ) + 1) ^ 2) := by
  dsimp [unifBucketsCirc]
  rw [LayeredCircuit.seqList_size, Nat.cast_list_sum]
  have hlen : ((List.range (bucketPairs (2 * K)).length).map fun b =>
      if hb : b < (bucketPairs (2 * K)).length then unifBucketStepCirc comb br as arith n K d h1K b hb
      else LayeredCircuit.id _).length = (bucketPairs (2 * K)).length := by simp
  have hsum := List.sum_le_card_nsmul
    (((List.range (bucketPairs (2 * K)).length).map fun b =>
      if hb : b < (bucketPairs (2 * K)).length then unifBucketStepCirc comb br as arith n K d h1K b hb
      else LayeredCircuit.id _).map fun lc => (lc.size : ℝ))
    (80 + br.C_unif * ((wOf K : ℝ) + 1) ^ 2)
    (fun s hs => by
      rcases List.mem_map.mp hs with ⟨lc, hlc, rfl⟩
      rcases List.mem_map.mp hlc with ⟨b, _, rfl⟩
      by_cases hb : b < (bucketPairs (2 * K)).length
      · rw [dif_pos hb]; exact unifBucketStepCirc_size comb br as arith n K d h1K b hb
      · rw [dif_neg hb]; simp only [LayeredCircuit.id_size, Nat.cast_zero]
        have := br.hC_unif_pos
        positivity)
  rw [List.length_map, List.length_map, List.length_range, nsmul_eq_mul] at hsum
  simpa only [List.map_map, Function.comp_def] using hsum

private def piPrefStepEquiv (comb : LcgSym54Comb) (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (k : ℕ) (hk : k < (bucketPairs (2 * K)).length) :
    ((b : Fin (bucketPairs (2 * K)).length) → Fin (M_pref comb K l k b)) ×
        Fin (M_hb comb K l ⟨k, hk⟩) ≃
      ((b : Fin (bucketPairs (2 * K)).length) → Fin (M_pref comb K l (k + 1) b)) :=
  let bk : Fin (bucketPairs (2 * K)).length := ⟨k, hk⟩
  { toFun := fun ⟨dP, v⟩ b =>
      if h : b = bk then
        Fin.cast (by subst h; dsimp [M_pref]; rw [if_pos (Nat.lt_succ_self k)]) v
      else
        have hlt : b.1 < k + 1 ↔ b.1 < k := by
          have hne : b.1 ≠ k := fun hv => h (Fin.ext hv)
          omega
        Fin.cast (by dsimp [M_pref]; simp only [hlt]) (dP b)
    invFun := fun dP' =>
      (fun b =>
        if h : b = bk then
          ⟨0, by subst h; dsimp [M_pref]; rw [if_neg (lt_irrefl k)]; omega⟩
        else
          have hlt : b.1 < k ↔ b.1 < k + 1 := by
            have hne : b.1 ≠ k := fun hv => h (Fin.ext hv)
            omega
          Fin.cast (by dsimp [M_pref]; simp only [hlt]) (dP' b),
       Fin.cast (by dsimp [M_pref]; rw [if_pos (Nat.lt_succ_self k)]) (dP' bk))
    left_inv := fun ⟨dP, v⟩ => by
      apply Prod.ext
      · funext b
        by_cases h : b = bk
        · subst h; apply Fin.ext
          have hm1 : M_pref comb K l k bk = 1 := by dsimp [M_pref]; rw [if_neg (lt_irrefl k)]
          have hlt := (dP bk).isLt; omega
        · simp [h]
      · apply Fin.ext; simp
    right_inv := fun dP' => by
      funext b
      by_cases h : b = bk
      · subst h; apply Fin.ext; simp
      · apply Fin.ext; simp [h] }

lemma act_unifBucketsCirc (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) {l : Fin (2 * K) → Fin (n + 1)}
    (hl : Monotone l) (z : Qubits (totWiresDef as n K d))
    (hz3 : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (fun _ _ => false)))
    (hzCtrl : z ∘ eUnifCtrl as n K d = fun _ => false)
    (hz22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false) :
    act (unifBucketsCirc comb br as arith n K d h1K).unitary (ket z) =
      ((1 / Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) : ℂ) •
        ∑ dFn : (i : Fin (2 * K)) → Fin (runOffset l i),
          ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
            (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn)))) := by
  let bpLen := (bucketPairs (2 * K)).length
  have hN_len : ∀ b : ℕ, b < bpLen → b < (hb2SortedList K l).length := fun b hb => by
    rw [hb2SortedList_length]; have := bucketPairs_length_lt_B2 comb (K := K); have := arity_succ_eq (dHbOf K); omega
  let scalarPref (k : ℕ) : ℂ :=
    ((∏ b : Fin k,
      (if hbk : b.1 < bpLen then
        if ((hb2SortedList K l)[b.1]'(hN_len b.1 hbk)).kind = 0
          then 1 / Real.sqrt (((bucketPairs (2 * K))[b.1]'hbk).1 : ℝ) else 1
      else 1) : ℝ) : ℂ)
  let vec (k : ℕ) : EuclideanSpace ℂ (Qubits (totWiresDef as n K d)) :=
    if hk : k ≤ bpLen then
      scalarPref k • ∑ dP : (b : Fin bpLen) → Fin (M_pref comb K l k b),
        ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
          (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dArrOfPref comb K l k dP))))
    else 0
  have hvec0 : vec 0 = ket z := by
    dsimp only [vec, scalarPref]
    rw [dif_pos (Nat.zero_le _)]
    simp only [Fin.prod_univ_zero, Complex.ofReal_one, one_smul]
    let d0 : (b : Fin bpLen) → Fin (M_pref comb K l 0 b) := fun b => ⟨0, by dsimp [M_pref]; omega⟩
    rw [Finset.sum_eq_single d0
      (fun dP _ hne => absurd (funext fun b => Fin.ext (by
        have hlt := (dP b).isLt; dsimp [M_pref] at hlt; dsimp [d0]; omega)) hne)
      (by simp)]
    have hd0 : dArrOfPref comb K l 0 d0 = fun _ _ => false := funext fun q => by
      dsimp only [dArrOfPref]; split_ifs with h1 h2
      · exact absurd h2.1 (Nat.not_lt_zero _)
      · rfl
      · rfl
    rw [hd0]
    congr 1
    apply updateOn_noop; exact hz3
  have hstep : ∀ k < (bucketPairs (2 * K)).length,
      act (if hk : k < (bucketPairs (2 * K)).length then
        unifBucketStepCirc comb br as arith n K d h1K k hk else LayeredCircuit.id _).unitary (vec k) =
      vec (k + 1) := by
    intro k (hk : k < bpLen)
    rw [dif_pos hk]
    dsimp only [vec]
    rw [dif_pos (Nat.le_of_lt hk), dif_pos (Nat.succ_le_of_lt hk)]
    rw [act_smul', act_sum']
    let qk : Fin (arity (dHbOf K + 1)) := ⟨k, (hb2SortedList_length K l) ▸ hN_len k hk⟩
    let rk := (hb2SortedList K l)[k]'(by rw [hb2SortedList_length]; exact qk.isLt)
    let mk := ((bucketPairs (2 * K))[k]'hk).1
    have hterm : ∀ dP : (b : Fin bpLen) → Fin (M_pref comb K l k b),
        act (unifBucketStepCirc comb br as arith n K d h1K k hk).unitary
          (ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
            (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dArrOfPref comb K l k dP))))) =
          (if rk.kind = 0 then
            ((1 / Real.sqrt (mk : ℝ) : ℝ) : ℂ) • ∑ v : Fin mk,
              ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
                (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l)
                  (Function.update (dArrOfPref comb K l k dP) qk (natToBits (wOf K) v.1)))))
          else
            ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
              (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dArrOfPref comb K l k dP))))) := by
      intro dP
      set zP := updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
        (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dArrOfPref comb K l k dP)))
      have hzP3 : zP ∘ eRec3 as n K d = _ := updateOn_comp_emb _ _ _
      have hqk0 : dArrOfPref comb K l k dP qk = fun _ => false := by
        dsimp only [dArrOfPref, qk]; rw [dif_pos hk, if_neg (by omega)]
      have hzPC : zP ∘ eUnifCtrl as n K d = fun _ => false := by
        dsimp only [zP]; rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_eUnifCtrl as n K d)]; exact hzCtrl
      have hzP22 : zP ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
        dsimp only [zP]; rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
        exact hz22
      have hact := act_unifBucketStepCirc comb br as arith n K d h1K hl k hk zP (dArrOfPref comb K l k dP)
        hzP3 hqk0 hzPC hzP22
      simpa only [zP, updateOn_idem] using hact
    simp_rw [hterm]
    by_cases hrk0 : rk.kind = 0
    · simp only [if_pos hrk0]
      have hmk_eq : M_hb comb K l ⟨k, hk⟩ = mk := by dsimp [M_hb]; rw [if_pos hrk0]
      rw [← Finset.smul_sum, smul_smul]
      have hscal : scalarPref k * ((1 / Real.sqrt (mk : ℝ) : ℝ) : ℂ) = scalarPref (k + 1) := by
        dsimp only [scalarPref]
        rw [← Complex.ofReal_mul]
        congr 1
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [dif_pos hk, if_pos hrk0]
      rw [hscal]
      apply congrArg (scalarPref (k + 1) • ·)
      have hupd_eq : ∀ (dP : (b : Fin bpLen) → Fin (M_pref comb K l k b)) (v : Fin mk),
          Function.update (dArrOfPref comb K l k dP) qk (natToBits (wOf K) v.1) =
            dArrOfPref comb K l (k + 1)
              (piPrefStepEquiv comb K l k hk (dP, (Fin.castOrderIso hmk_eq.symm).toEquiv v)) := by
        intro dP v
        funext q
        by_cases hqq : q = qk
        · subst hqq
          dsimp only [dArrOfPref, piPrefStepEquiv, Equiv.coe_fn_mk, qk]
          rw [dif_pos hk, if_pos ⟨Nat.lt_succ_self k, hrk0⟩, dif_pos rfl, Function.update_self]
          rfl
        · rw [Function.update_of_ne hqq]
          dsimp only [dArrOfPref, piPrefStepEquiv, Equiv.coe_fn_mk]
          by_cases hqb : q.1 < bpLen
          · rw [dif_pos hqb, dif_pos hqb]
            have hne_bk : (⟨q.1, hqb⟩ : Fin bpLen) ≠ ⟨k, hk⟩ := fun hv =>
              hqq (Fin.ext (congrArg (Fin.val : Fin bpLen → ℕ) hv))
            have hne_k : q.1 ≠ k := fun hv => hqq (Fin.ext hv)
            have hlt_iff : q.1 < k + 1 ↔ q.1 < k := by omega
            rw [dif_neg hne_bk]
            simp only [hlt_iff, Fin.val_cast]
          · rw [dif_neg hqb, dif_neg hqb]
      have hinner : ∀ dP : (b : Fin bpLen) → Fin (M_pref comb K l k b),
          (∑ v : Fin mk,
            ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
              (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l)
                (Function.update (dArrOfPref comb K l k dP) qk (natToBits (wOf K) v.1)))))) =
          ∑ wv : Fin (M_hb comb K l ⟨k, hk⟩),
            ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
              (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l)
                (dArrOfPref comb K l (k + 1) (piPrefStepEquiv comb K l k hk (dP, wv)))))) := by
        intro dP
        simp_rw [hupd_eq dP]
        exact (Fin.castOrderIso hmk_eq.symm).toEquiv.sum_comp (fun wv =>
          ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
            (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l)
              (dArrOfPref comb K l (k + 1) (piPrefStepEquiv comb K l k hk (dP, wv)))))))
      simp_rw [hinner]
      rw [← Fintype.sum_prod_type']
      exact (piPrefStepEquiv comb K l k hk).sum_comp (fun dP =>
        ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
          (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l)
            (dArrOfPref comb K l (k + 1) dP)))))
    · simp only [if_neg hrk0]
      have hmk1 : M_hb comb K l ⟨k, hk⟩ = 1 := by dsimp [M_hb]; rw [if_neg hrk0]
      have hscal : scalarPref (k + 1) = scalarPref k := by
        dsimp only [scalarPref]
        congr 1
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [dif_pos hk, if_neg hrk0, mul_one]
      rw [hscal]
      apply congrArg (scalarPref k • ·)
      let eOne : Fin 1 ≃ Fin (M_hb comb K l ⟨k, hk⟩) := (Fin.castOrderIso hmk1.symm).toEquiv
      let eStep : ((b : Fin bpLen) → Fin (M_pref comb K l k b)) ≃
          ((b : Fin bpLen) → Fin (M_pref comb K l (k + 1) b)) :=
        ((Equiv.prodUnique _ (Fin 1)).symm.trans (Equiv.prodCongrRight (fun _ => eOne))).trans
          (piPrefStepEquiv comb K l k hk)
      have hd_eq : ∀ dP : (b : Fin bpLen) → Fin (M_pref comb K l k b),
          dArrOfPref comb K l k dP = dArrOfPref comb K l (k + 1) (eStep dP) := by
        intro dP
        funext q
        dsimp only [eStep, Equiv.trans_apply, Equiv.prodCongrRight_apply, Equiv.prodUnique_symm_apply,
          piPrefStepEquiv, Equiv.coe_fn_mk, dArrOfPref]
        by_cases hqb : q.1 < bpLen
        · rw [dif_pos hqb, dif_pos hqb]
          by_cases hqk : q.1 = k
          · have hne : ¬ (q.1 < k + 1 ∧ ((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt)).kind = 0) := by
              have hrk : ((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt)).kind = rk.kind := by
                congr 1; simp only [rk]; congr 1
              rw [hrk]; exact fun h => hrk0 h.2
            rw [if_neg hne, if_neg (by omega)]
          · have hne_bk : (⟨q.1, hqb⟩ : Fin bpLen) ≠ ⟨k, hk⟩ := fun hv =>
              hqk (congrArg (Fin.val : Fin bpLen → ℕ) hv)
            have hlt_iff : q.1 < k + 1 ↔ q.1 < k := by omega
            rw [dif_neg hne_bk]
            simp only [hlt_iff, Fin.val_cast]
        · rw [dif_neg hqb, dif_neg hqb]
      simp_rw [hd_eq]
      exact eStep.sum_comp (fun dP =>
        ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
          (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l)
            (dArrOfPref comb K l (k + 1) dP)))))
  have hloop := act_seqList_range_vec vec
    (fun b => if hb : b < (bucketPairs (2 * K)).length then unifBucketStepCirc comb br as arith n K d h1K b hb else LayeredCircuit.id _)
    (bucketPairs (2 * K)).length hstep
  rw [hvec0] at hloop
  dsimp only [unifBucketsCirc]
  rw [hloop]
  dsimp only [vec]
  rw [dif_pos (le_refl bpLen)]
  have hscal_final : scalarPref bpLen = ((1 / Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) : ℂ) := by
    have h0 : scalarPref bpLen =
        ((∏ b : Fin bpLen,
          (if ((hb2SortedList K l)[b.1]'(hN_len b.1 b.isLt)).kind = 0
            then 1 / Real.sqrt (((bucketPairs (2 * K))[b.1]).1 : ℝ) else 1) : ℝ) : ℂ) := by
      dsimp only [scalarPref]; congr 1; congr 1; funext b; exact dif_pos b.isLt
    rw [h0]
    exact prod_M_hb_inv_sqrt_eq comb h1K l hl
  rw [hscal_final]
  apply congrArg (((1 / Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) : ℂ) • ·)
  let ePref : ((b : Fin bpLen) → Fin (M_hb comb K l b)) ≃
      ((b : Fin bpLen) → Fin (M_pref comb K l bpLen b)) :=
    { toFun := fun dB b => Fin.cast (by dsimp [M_pref]; rw [if_pos b.isLt]) (dB b)
      invFun := fun dP b => Fin.cast (by dsimp [M_pref]; rw [if_pos b.isLt]) (dP b)
      left_inv := fun dB => funext fun b => Fin.ext rfl
      right_inv := fun dP => funext fun b => Fin.ext rfl }
  have hd_final : ∀ dP : (b : Fin bpLen) → Fin (M_pref comb K l bpLen b),
      dArrOfPref comb K l bpLen dP =
        dRec3Of K l ((ePref.symm.trans (dEquivActiveBucket comb h1K l hl)) dP) := fun dP => by
    dsimp only [Equiv.trans_apply]
    rw [← dArrOfPref_full_eq_dRec3Of comb h1K l hl (ePref.symm dP)]
    congr 1
  rw [Finset.sum_congr rfl fun dP _ => by
    change ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dArrOfPref comb K l bpLen dP)))) = _
    rw [hd_final dP]]
  exact (ePref.symm.trans (dEquivActiveBucket comb h1K l hl)).sum_comp (fun dFn =>
    ket (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn)))))

end HarmBucketWork54


/-! ### Part 9: Step 5 (Unrouting, Subtraction, Ancilla Uncomputation) & Step 6 (`alonsoSchottCircuit`) -/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

/-! #### 9.1 Step 5–6 Register Embeddings & Disjointness -/

def eDReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin ((2 * K) * wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlice as n K d ⟨15, by decide⟩ (2 * K) (wOf K) (ancLen_15 n K d _)

def eDSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlot as n K d ⟨15, by decide⟩ (2 * K) (wOf K) (ancLen_15 n K d _) i

def eSubTmp (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨16, by decide⟩ (wOf K) (by rw [ancLen_16])

def eAsAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (as.alonsoSchottAnc (2 * K) d) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨23, by decide⟩ (as.alonsoSchottAnc (2 * K) d) (by rw [ancLen_23])

lemma eRec3DVal_disjoint_eRec2DVal (as : AlonsoSchottSil54) (n K d : ℕ)
    (q1 q2 : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec3DVal as n K d q1 a ≠ eRec2DVal as n K d q2 b :=
  ancRegField_disjoint_ancRegField as n K d (k1 := ⟨13, by decide⟩) (k2 := ⟨11, by decide⟩)
    (by decide) (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q1
    (wK2Hb K + 2) (wOf K) (by dsimp [wR2Hb, wP2Hb]; omega)
    (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q2
    (wK1Hb K + 2 + wOf K) (wOf K) (by dsimp [wR1Hb, wP1Hb]; omega)

lemma eRec2DVal_disjoint_eDSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) (i : Fin (2 * K)) :
    ∀ a b, eRec2DVal as n K d q a ≠ eDSlot as n K d i b :=
  ancRegField_disjoint_ancRegSlot as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨15, by decide⟩)
    (by decide) (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (wK1Hb K + 2 + wOf K) (wOf K) (by dsimp [wR1Hb, wP1Hb]; omega)
    (2 * K) (wOf K) (ancLen_15 n K d _) i

lemma eRec2DVal_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {q0 q1 : Fin (arity (dHbOf K + 1))} (hq : q0 ≠ q1) :
    ∀ a b, eRec2DVal as n K d q0 a ≠ eRec2DVal as n K d q1 b :=
  ancRegField_disjoint_slot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K)
    (ancLen_11 n K d _) hq _ _

lemma eDSlot_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {i1 i2 : Fin (2 * K)} (hi : i1 ≠ i2) :
    ∀ a b, eDSlot as n K d i1 a ≠ eDSlot as n K d i2 b :=
  ancRegSlot_disjoint_slot as n K d ⟨15, by decide⟩ (2 * K) (wOf K) (ancLen_15 n K d _) hi

lemma eDSlot_disjoint_eSubTmp (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eDSlot as n K d i a ≠ eSubTmp as n K d b :=
  ancRegSlot_disjoint_ancPrefix as n K d (k1 := ⟨15, by decide⟩) (k2 := ⟨16, by decide⟩)
    (by decide) (2 * K) (wOf K) (ancLen_15 n K d _) i (wOf K) (by rw [ancLen_16])

lemma eSubTmp_disjoint_eDSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eSubTmp as n K d a ≠ eDSlot as n K d i b :=
  fun a b h => eDSlot_disjoint_eSubTmp as n K d i b a h.symm

lemma eDSlot_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1)
    (i : Fin (2 * K)) :
    ∀ a b, eDSlot as n K d i a ≠ eArith345 as n K d subLen hle b :=
  ancRegSlot_disjoint_ancPrefix as n K d (k1 := ⟨15, by decide⟩) (k2 := ⟨22, by decide⟩)
    (by decide) (2 * K) (wOf K) (ancLen_15 n K d _) i subLen (by rw [ancLen_22]; exact hle)

lemma eSubTmp_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1) :
    ∀ a b, eSubTmp as n K d a ≠ eArith345 as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨16, by decide⟩) (k2 := ⟨22, by decide⟩)
    (by decide) (wOf K) (by rw [ancLen_16]))

lemma eSubTmp_disjoint_eOutSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d)) :
    ∀ a b, eSubTmp as n K d a ≠ eOutSlot as n K d j b :=
  fun a b h => eOutSlot_disjoint_ancPrefix as n K d j ⟨16, by decide⟩ (wOf K) (by rw [ancLen_16]) b a h.symm

lemma eOutSlot_disjoint_eSubTmp (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d)) :
    ∀ a b, eOutSlot as n K d j a ≠ eSubTmp as n K d b :=
  eOutSlot_disjoint_ancPrefix as n K d j ⟨16, by decide⟩ (wOf K) (by rw [ancLen_16])

lemma eRec3_disjoint_eRec2DVal (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec3 as n K d a ≠ eRec2DVal as n K d q b :=
  trans_disjoint_left (anc_disjoint_ancRegField as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨13, by decide⟩)
    (by decide) (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (wK1Hb K + 2 + wOf K) (wOf K) (by dsimp [wR1Hb, wP1Hb]; omega))

lemma eRec2_disjoint_eDSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eRec2 as n K d a ≠ eDSlot as n K d i b :=
  fun a b => ancRegSlice_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨15, by decide⟩)
    (by decide) (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) a _

lemma eRec2_disjoint_eDReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eDReg as n K d b :=
  fun a b => ancRegSlice_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨15, by decide⟩)
    (by decide) (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) a _

lemma eDReg_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (hk : k ≠ ⟨15, by decide⟩) :
    ∀ a b, eDReg as n K d a ≠ ancEmb as n K d k b :=
  ancRegSlice_disjoint_anc as n K d (k1 := ⟨15, by decide⟩) (k2 := k) hk.symm (2 * K) (wOf K) (ancLen_15 n K d _)

lemma eOut_disjoint_anc_any (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) :
    ∀ a b, eOut as n K d a ≠ ancEmb as n K d k b :=
  eOut_disjoint_anc as n K d k

lemma eOut_disjoint_eAsAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOut as n K d a ≠ eAsAnc as n K d b :=
  trans_disjoint_right (eOut_disjoint_anc as n K d ⟨23, by decide⟩)

private lemma eOut_disjoint_eDReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOut as n K d a ≠ eDReg as n K d b :=
  trans_disjoint_right (eOut_disjoint_anc as n K d ⟨15, by decide⟩)

private lemma eOut_disjoint_eSubTmp (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOut as n K d a ≠ eSubTmp as n K d b :=
  trans_disjoint_right (eOut_disjoint_anc as n K d ⟨16, by decide⟩)

private lemma eOut_disjoint_eDSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eOut as n K d a ≠ eDSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right (eOut_disjoint_anc as n K d ⟨15, by decide⟩))

private lemma eDReg_disjoint_eSubTmp (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eDReg as n K d a ≠ eSubTmp as n K d b :=
  trans_disjoint_right (eDReg_disjoint_anc_other as n K d ⟨16, by decide⟩ (by decide))

private lemma eDReg_disjoint_eMReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eDReg as n K d a ≠ eMReg as n K d b :=
  trans_disjoint_right (eDReg_disjoint_anc_other as n K d ⟨0, by decide⟩ (by decide))

private lemma eDReg_disjoint_eActReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eDReg as n K d a ≠ eActReg as n K d b :=
  trans_disjoint_right (eDReg_disjoint_anc_other as n K d ⟨1, by decide⟩ (by decide))

private lemma eDReg_disjoint_eOccReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eDReg as n K d a ≠ eOccReg as n K d b :=
  trans_disjoint_right (eDReg_disjoint_anc_other as n K d ⟨2, by decide⟩ (by decide))

private lemma eOutSlot_disjoint_eDSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d)) (i : Fin (2 * K)) :
    ∀ a b, eOutSlot as n K d j a ≠ eDSlot as n K d i b :=
  eOutSlot_disjoint_ancRegSlot as n K d j ⟨15, by decide⟩ (2 * K) (wOf K) (ancLen_15 n K d _) i

private lemma eDSlot_disjoint_eOutSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (j : Fin (arity d)) :
    ∀ a b, eDSlot as n K d i a ≠ eOutSlot as n K d j b :=
  fun a b h => eOutSlot_disjoint_eDSlot as n K d j i b a h.symm

private lemma eOutSlot_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ wOf K + 1) (j : Fin (arity d)) :
    ∀ a b, eOutSlot as n K d j a ≠ eArith345 as n K d subLen hle b :=
  eOutSlot_disjoint_ancPrefix as n K d j ⟨22, by decide⟩ subLen (by rw [ancLen_22]; exact hle)

private lemma eMReg_disjoint_eOut (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eMReg as n K d a ≠ eOut as n K d b :=
  trans_disjoint_left (anc_disjoint_eOut as n K d ⟨0, by decide⟩)

private lemma eActReg_disjoint_eOut (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eActReg as n K d a ≠ eOut as n K d b :=
  trans_disjoint_left (anc_disjoint_eOut as n K d ⟨1, by decide⟩)

private lemma eOccReg_disjoint_eOut (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOccReg as n K d a ≠ eOut as n K d b :=
  trans_disjoint_left (anc_disjoint_eOut as n K d ⟨2, by decide⟩)

private lemma eMReg_disjoint_eOut' (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOut as n K d a ≠ eMReg as n K d b :=
  fun a b h => eMReg_disjoint_eOut as n K d b a h.symm

private lemma eTr2b_disjoint_eRec3 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2b as n K d a ≠ eRec3 as n K d b :=
  fun a b h => eRec3_disjoint_eTr2b as n K d b a h.symm

private lemma eTr2b_disjoint_eUnifCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2b as n K d a ≠ eUnifCtrl as n K d b :=
  trans_disjoint_right (eTr2b_disjoint_anc_other as n K d ⟨21, by decide⟩ (by decide))

private lemma eTr2a_disjoint_eUnifCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2a as n K d a ≠ eUnifCtrl as n K d b :=
  trans_disjoint_right (eTr2a_disjoint_anc_other as n K d ⟨21, by decide⟩ (by decide))

private lemma eRec2_disjoint_eUnifCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eUnifCtrl as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨21, by decide⟩ (by decide))

lemma comp_eRec2DVal (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec2DVal as n K d q = d_arr q := by
  dsimp only [eRec2DVal]
  rw [comp_ancRegField as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z _ hz q]
  exact rec2SlotFn_comp_7 ..

lemma updateOn_eRec2DVal_eq (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) (dv : Qubits (wOf K)) :
    updateOn (eRec2DVal as n K d q) z dv =
      updateOn (eRec2 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL (Function.update d_arr q dv))) := by
  have h1 := updateOn_ancRegSlot_eq as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K)
    (ancLen_11 n K d _) z (hb1ArrOfList K L hL d_arr) hz q
    (hbRecToBits (wOf K) (L[q.1]'(by omega)) dv)
  have hupd_slot : updateOn (sliceEmb (wK1Hb K + 2 + wOf K) (wOf K) (by dsimp [wR1Hb, wP1Hb]; omega))
      (hb1ArrOfList K L hL d_arr q) dv = hbRecToBits (wOf K) (L[q.1]'(by omega)) dv := by
    dsimp [hb1ArrOfList, hbRecToBits]
    exact updateOn_rec2SlotFn_7 ..
  dsimp only [eRec2DVal]
  rw [updateOn_ancRegField_eq_slot,
    comp_ancRegSlot as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z _ hz q, hupd_slot, h1]
  have hrec_eq : ancRegSlice as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) =
      eRec2 as n K d := rfl
  rw [hrec_eq]
  apply congrArg (updateOn (eRec2 as n K d) z)
  apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K))
  funext r
  by_cases hr : r = q
  · subst hr; simp [hb1ArrOfList]
  · simp [hb1ArrOfList, hr]

lemma comp_eDSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (d_reg : Fin (2 * K) → Qubits (wOf K))
    (hz : z ∘ eDReg as n K d = flatReg (2 * K) (wOf K) d_reg) (i : Fin (2 * K)) :
    z ∘ eDSlot as n K d i = d_reg i := by
  dsimp only [eDSlot]
  exact comp_ancRegSlot as n K d ⟨15, by decide⟩ (2 * K) (wOf K) (ancLen_15 n K d _) z d_reg hz i

lemma updateOn_eDSlot_eq (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (d_reg : Fin (2 * K) → Qubits (wOf K))
    (hz : z ∘ eDReg as n K d = flatReg (2 * K) (wOf K) d_reg) (i : Fin (2 * K)) (val : Qubits (wOf K)) :
    updateOn (eDSlot as n K d i) z val =
      updateOn (eDReg as n K d) z (flatReg (2 * K) (wOf K) (Function.update d_reg i val)) := by
  dsimp only [eDSlot]
  exact updateOn_ancRegSlot_eq as n K d ⟨15, by decide⟩ (2 * K) (wOf K) (ancLen_15 n K d _)
    z d_reg hz i val

/-! #### 9.2 Payload Arrays Across Unrouting & `hbNeighborStep` Invariance -/

lemma dOfHBRec_hbNeighborStep (w N : ℕ) {α : Type*} [LinearOrder α] (l : Fin N → α)
    (dFn : (i : Fin N) → Fin (runOffset l i)) (L : List HBRec) (p q : ℕ) (hq : q < L.length) :
    dOfHBRec w N l dFn ((hbNeighborStep L p)[q]'(by rw [hbNeighborStep_length]; exact hq)) =
      dOfHBRec w N l dFn (L[q]'hq) := by
  dsimp only [hbNeighborStep]
  split_ifs with hp hc
  · by_cases hqp1 : q = p + 1
    · subst hqp1
      rw [List.getElem_set_self]
      dsimp only [dOfHBRec]
      have h0 : L[p + 1].kind = 1 := hc.2.1
      simp [h0]
    · rw [List.getElem_set_ne (Ne.symm hqp1)]
      by_cases hqp : q = p
      · subst hqp
        rw [List.getElem_set_self]
        simp [dOfHBRec]
      · rw [List.getElem_set_ne (Ne.symm hqp)]
  · rfl
  · rfl

lemma dOfHBRec_hbSeqState (w N : ℕ) {α : Type*} [LinearOrder α] (l : Fin N → α)
    (dFn : (i : Fin N) → Fin (runOffset l i)) (s1 : List HBRec) (k q : ℕ) (hq : q < s1.length) :
    dOfHBRec w N l dFn ((hbSeqState s1 k)[q]'(by rw [hbSeqState_length]; exact hq)) =
      dOfHBRec w N l dFn (s1[q]'hq) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [hbSeqState_succ]
    rw [dOfHBRec_hbNeighborStep w N l dFn _ k q (by rw [hbSeqState_length]; exact hq)]
    exact ih

noncomputable def dPassOf (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
  dOfHBRec (wOf K) (2 * K) l dFn
    ((hbSeqPass (hb1SortedList K l))[q.1]'(by rw [hbSeqPass_length, hb1SortedList_length]; exact q.isLt))

noncomputable def dS1Of (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
  dOfHBRec (wOf K) (2 * K) l dFn
    ((hb1SortedList K l)[q.1]'(by rw [hb1SortedList_length]; exact q.isLt))

noncomputable def dInitOf (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
  dOfHBRec (wOf K) (2 * K) l dFn
    ((hbInit (2 * K) (arity (dHbOf K)) l)[q.1]'(by
      rw [hbInit_length]; exact Nat.lt_of_lt_of_eq q.isLt (arity_succ_eq _)))

lemma dPassOf_eq_dS1Of (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) :
    dPassOf K l dFn = dS1Of K l dFn := funext fun q => by
  have h1pos : 1 ≤ (hb1SortedList K l).length := by
    rw [hb1SortedList_length, arity_eq_two_pow]; exact Nat.two_pow_pos _
  have hlen : q.1 < (hb1SortedList K l).length := by rw [hb1SortedList_length]; exact q.isLt
  have hpass : hbSeqPass (hb1SortedList K l) = hbSeqState (hb1SortedList K l) ((hb1SortedList K l).length - 1) :=
    hbSeqPass_eq_hbSeqState _ h1pos
  have hget : (hbSeqPass (hb1SortedList K l))[q.1]'(by rw [hbSeqPass_length]; exact hlen) =
      (hbSeqState (hb1SortedList K l) ((hb1SortedList K l).length - 1))[q.1]'(by rw [hbSeqState_length]; exact hlen) := by
    congr 1
  dsimp only [dPassOf, dS1Of]
  rw [hget]
  exact dOfHBRec_hbSeqState (wOf K) (2 * K) l dFn _ ((hb1SortedList K l).length - 1) q.1 hlen

lemma dInitOf_lt_2K (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1))
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (i : Fin (2 * K)) :
    let hB : i.1 < arity (dHbOf K + 1) := by
      have := two_K_lt_B2 h1K; have := arity_succ_eq (dHbOf K); omega
    dInitOf K l dFn ⟨i.1, hB⟩ = natToBits (wOf K) (dFn i).1 := by
  intro hB
  dsimp only [dInitOf, dOfHBRec]
  have hiB : i.1 < arity (dHbOf K) := lt_trans i.isLt (two_K_lt_B2 h1K)
  rw [hbInit_getElem_lt_2K l i.isLt hiB]
  by_cases hact : 2 ≤ runOffset l i
  · rw [if_pos hact]; dsimp only
    rw [dif_pos i.isLt]
    rfl
  · rw [if_neg hact]; dsimp only
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    have hpos := comb.runOffset_pos l i
    have hd0 : (dFn i).1 = 0 := by have hlt := (dFn i).isLt; omega
    rw [hd0, natToBits_zero comb]

lemma dInitOf_ge_2K {n K : ℕ} (_h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1))
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (q : Fin (arity (dHbOf K + 1))) (hq : 2 * K ≤ q.1) :
    dInitOf K l dFn q = fun _ => false := by
  dsimp only [dInitOf, dOfHBRec]
  by_cases hqB : q.1 < arity (dHbOf K)
  · rw [hbInit_getElem_mid l (Nat.not_lt.mpr hq) hqB]
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  · have hk : ((hbInit (2 * K) (arity (dHbOf K)) l)[q.1]'(by
        rw [hbInit_length]; exact Nat.lt_of_lt_of_eq q.isLt (arity_succ_eq _))).kind ≠ 0 := by
      rw [hbInit_getElem_ge_B2 l hqB q.isLt]
      split_ifs <;> simp
    rw [if_neg hk]

/-! #### 9.3 Trace-Based Sort Unrouting with Payload `d` (`sortHb2Circ` & `sortHb1Circ`) -/

lemma act_sortHb2Circ_with_d (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (br : BitonicRouting54)
    (n K d : ℕ) (h1K : 1 ≤ K) {l : Fin (2 * K) → Fin (n + 1)}
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hbSeqPass (hb1SortedList K l))
        (by rw [hbSeqPass_length, hb1SortedList_length]) (dPassOf K l dFn)))
    (hzTr : z ∘ ancEmb as n K d ⟨14, by decide⟩ = fun _ => false)
    (hzAnc : z ∘ ancEmb as n K d ⟨18, by decide⟩ = fun _ => false) :
    act (sortHb2Circ as br n K d).unitary (ket z) =
      ket (updateOn (eTr2b as n K d)
        (updateOn (eRec3 as n K d) z
          (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
            (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn))))
        (rec3SortTr K l)) := by
  let arr0 := hb3ArrOfList K (hbSeqPass (hb1SortedList K l))
    (by rw [hbSeqPass_length, hb1SortedList_length]) (dPassOf K l dFn)
  let arrS := hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn)
  let key : Qubits (wR2Hb K) → ℕ := fun r => bitsToNat (recKey54 r)
  have hkey_eq : recKey54 ∘ arr0 = recKey54 ∘ rec3InitArr K l := by
    funext q; dsimp [arr0, rec3InitArr, hb3ArrOfList, hbRecToRec3Bits]
    rw [recKey54_rec3SlotFn, recKey54_rec3SlotFn]
  have htr_eq : sortTrace key (dHbOf K + 1) true arr0 = rec3SortTr K l := by
    change sortTrace ((fun k : Qubits (wK2Hb K) => bitsToNat k) ∘ recKey54) (dHbOf K + 1) true arr0 =
      sortTrace ((fun k : Qubits (wK2Hb K) => bitsToNat k) ∘ recKey54) (dHbOf K + 1) true (rec3InitArr K l)
    rw [br.sortTrace_of_key_comp (fun k : Qubits (wK2Hb K) => bitsToNat k) recKey54,
      br.sortTrace_of_key_comp (fun k : Qubits (wK2Hb K) => bitsToNat k) recKey54, hkey_eq]
  have hsort_eq : sort key (dHbOf K + 1) true arr0 = arrS := by
    let f3 : HBRec → Qubits (wR2Hb K) := fun r => hbRecToRec3Bits (wOf K) r (dOfHBRec (wOf K) (2 * K) l dFn r)
    let L₁ : List (Qubits (wR2Hb K)) := List.ofFn (sort key (dHbOf K + 1) true arr0)
    let L₂ : List (Qubits (wR2Hb K)) := (hb2SortedList K l).map f3
    have hofFn0 : List.ofFn arr0 = (hbSeqPass (hb1SortedList K l)).map f3 := by
      apply List.ext_getElem
      · simp [hbSeqPass_length, hb1SortedList_length]
      · intro idx h1 h2
        rw [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, List.getElem_map, arr0, hb3ArrOfList, f3, dPassOf]
    have hperm12 : L₁.Perm L₂ := by
      have hp1 : L₁.Perm (List.ofFn arr0) := br.sort_perm key (dHbOf K + 1) true arr0
      rw [hofFn0] at hp1
      exact hp1.trans ((List.mergeSort_perm _ _).symm.map _)
    have hp1 : L₁.Pairwise (fun x y => key x ≤ key y) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_ofFn] at hi hj
      simp only [L₁, List.getElem_ofFn]
      exact br.monotone_sort key (dHbOf K + 1) arr0 (Nat.le_of_lt hij)
    have hpw_s2 : (hb2SortedList K l).Pairwise (fun a b => hbKey2 a ≤ hbKey2 b) := by
      have hpw : (hb2SortedList K l).Pairwise (fun a b => decide (hbKey2 a ≤ hbKey2 b) = true) := by
        dsimp [hb2SortedList]
        exact List.pairwise_mergeSort
          (fun a b c => by simp only [decide_eq_true_eq]; exact le_trans)
          (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
          (hbSeqPass (hb1SortedList K l))
      exact hpw.imp (fun {a b} h => decide_eq_true_eq.mp h)
    have hbnd : ∀ r ∈ hb2SortedList K l, r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := by
      intro r hr
      have hr' := (List.mergeSort_perm _ _).mem_iff.mp hr
      have h := hbSeqPass_hb1_bounds comb h1K l r hr'
      exact ⟨h.2.2.2.1, h.2.2.2.2⟩
    have hp2 : L₂.Pairwise (fun x y => key x ≤ key y) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_map] at hi hj
      simp only [L₂, List.getElem_map]
      have ha := hbnd _ (List.getElem_mem hi)
      have hb := hbnd _ (List.getElem_mem hj)
      dsimp [key, f3]
      rw [hbKey2_bitsToNat_le_iff comb (wOf K) _ _ _ _ ha.1 hb.1 ha.2 hb.2]
      exact (List.pairwise_iff_getElem.mp hpw_s2) i j hi hj hij
    have hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y := by
      intro x hx y hy hxy
      rcases List.mem_map.mp hx with ⟨rx, hrx, rfl⟩
      rcases List.mem_map.mp hy with ⟨ry, hry, rfl⟩
      have ha := hbnd rx hrx
      have hb := hbnd ry hry
      dsimp [key, f3] at hxy
      rw [hbKey2_bitsToNat_eq_iff comb (wOf K) _ _ _ _ ha.1 hb.1 ha.2 hb.2] at hxy
      have horig := comb.hbKey2_orig_inj rx ry hxy
      have hreq := eq_of_mem_of_nodup_map (·.orig) (hb2SortedList_orig_nodup K l) hrx hry horig
      rw [hreq]
    have hlist_eq := comb.perm_eq_of_sorted_of_inj key L₁ L₂ hperm12 hp1 hp2 hinj
    funext q
    have hget := congrArg (fun L : List (Qubits (wR2Hb K)) => L[q.1]!) hlist_eq
    have hq1 : q.1 < L₁.length := by rw [List.length_ofFn]; exact q.isLt
    have hq2 : q.1 < L₂.length := by rw [List.length_map, hb2SortedList_length]; exact q.isLt
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hq1,
      List.getElem?_eq_getElem hq2, Option.getD_some, L₁, L₂, List.getElem_ofFn, List.getElem_map] at hget
    exact hget
  dsimp only [sortHb2Circ]
  have htr : z ∘ eTr2b as n K d = fun _ => false := funext fun j => congrFun hzTr _
  have hanc : z ∘ eSort2bAnc as n K d = fun _ => false := funext fun k => congrFun hzAnc _
  have hcomp := comp_packDTA54Emb (eRec3 as n K d) (eTr2b as n K d) (eSort2bAnc as n K d)
    (eRec3_disjoint_eTr2b as n K d) (eRec3_disjoint_eSort2bAnc as n K d) (eTr2b_disjoint_eSort2bAnc as n K d)
    z arr0 (fun _ => false) hzRec htr hanc
  have hact := act_mapWires_ket_singleton _ _ z _ (by
    rw [hcomp]
    exact br.act_bitonicSortKeyCircuit_ket (dHbOf K + 1) (wK2Hb K) (wP2Hb K) true arr0)
  rw [hact, htr_eq, hsort_eq]; congr 1
  exact updateOn_packDTA54_eq_two (eRec3 as n K d) (eTr2b as n K d) (eSort2bAnc as n K d)
    (eRec3_disjoint_eTr2b as n K d) (eRec3_disjoint_eSort2bAnc as n K d) (eTr2b_disjoint_eSort2bAnc as n K d)
    z hanc arrS (rec3SortTr K l)

lemma act_sortHb1Circ_with_d (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (br : BitonicRouting54)
    (n K d : ℕ) (h1K : 1 ≤ K) {l : Fin (2 * K) → Fin (n + 1)}
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K)
      (hb1ArrOfList K (hbInit (2 * K) (arity (dHbOf K)) l)
        (by rw [hbInit_length, arity_succ_eq]) (dInitOf K l dFn)))
    (hzTr : z ∘ ancEmb as n K d ⟨12, by decide⟩ = fun _ => false)
    (hzAnc : z ∘ ancEmb as n K d ⟨17, by decide⟩ = fun _ => false) :
    act (sortHb1Circ as br n K d).unitary (ket z) =
      ket (updateOn (eTr2a as n K d)
        (updateOn (eRec2 as n K d) z
          (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
            (hb1ArrOfList K (hb1SortedList K l) (hb1SortedList_length K l) (dS1Of K l dFn))))
        (rec2SortTr K l)) := by
  let arr0 := hb1ArrOfList K (hbInit (2 * K) (arity (dHbOf K)) l)
    (by rw [hbInit_length, arity_succ_eq]) (dInitOf K l dFn)
  let arrS := hb1ArrOfList K (hb1SortedList K l) (hb1SortedList_length K l) (dS1Of K l dFn)
  let key : Qubits (wR1Hb K) → ℕ := fun r => bitsToNat (recKey54 r)
  have hkey_eq : recKey54 ∘ arr0 = recKey54 ∘ hbInitArr K l := by
    funext q; dsimp [arr0, hbInitArr, hb1ArrOfList, hbRecToBits]
    rw [recKey54_rec2SlotFn, recKey54_rec2SlotFn]
  have htr_eq : sortTrace key (dHbOf K + 1) true arr0 = rec2SortTr K l := by
    change sortTrace ((fun k : Qubits (wK1Hb K) => bitsToNat k) ∘ recKey54) (dHbOf K + 1) true arr0 =
      sortTrace ((fun k : Qubits (wK1Hb K) => bitsToNat k) ∘ recKey54) (dHbOf K + 1) true (hbInitArr K l)
    rw [br.sortTrace_of_key_comp (fun k : Qubits (wK1Hb K) => bitsToNat k) recKey54,
      br.sortTrace_of_key_comp (fun k : Qubits (wK1Hb K) => bitsToNat k) recKey54, hkey_eq]
  have hsort_eq : sort key (dHbOf K + 1) true arr0 = arrS := by
    let f1 : HBRec → Qubits (wR1Hb K) := fun r => hbRecToBits (wOf K) r (dOfHBRec (wOf K) (2 * K) l dFn r)
    let L₁ : List (Qubits (wR1Hb K)) := List.ofFn (sort key (dHbOf K + 1) true arr0)
    let L₂ : List (Qubits (wR1Hb K)) := (hb1SortedList K l).map f1
    have hofFn0 : List.ofFn arr0 = (hbInit (2 * K) (arity (dHbOf K)) l).map f1 := by
      apply List.ext_getElem
      · rw [List.length_ofFn, List.length_map, hbInit_length, arity_succ_eq]
      · intro idx h1 h2
        rw [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, List.getElem_map, arr0, hb1ArrOfList, f1, dInitOf]
    have hperm12 : L₁.Perm L₂ := by
      have hp1 : L₁.Perm (List.ofFn arr0) := br.sort_perm key (dHbOf K + 1) true arr0
      rw [hofFn0] at hp1
      exact hp1.trans ((List.mergeSort_perm _ _).symm.map _)
    have hp1 : L₁.Pairwise (fun x y => key x ≤ key y) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_ofFn] at hi hj
      simp only [L₁, List.getElem_ofFn]
      exact br.monotone_sort key (dHbOf K + 1) arr0 (Nat.le_of_lt hij)
    have hpw_s1 : (hb1SortedList K l).Pairwise (fun a b => hbKey1 a ≤ hbKey1 b) := by
      have hpw : (hb1SortedList K l).Pairwise (fun a b => decide (hbKey1 a ≤ hbKey1 b) = true) := by
        dsimp [hb1SortedList]
        exact List.pairwise_mergeSort
          (fun a b c => by simp only [decide_eq_true_eq]; exact le_trans)
          (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
          (hbInit (2 * K) (arity (dHbOf K)) l)
      exact hpw.imp (fun {a b} h => decide_eq_true_eq.mp h)
    have hbnd : ∀ r ∈ hb1SortedList K l,
        r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := by
      intro r hr
      have h := hbInit_bounds comb h1K l r ((hb1SortedList_mem_iff K l r).mp hr)
      exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2⟩
    have hp2 : L₂.Pairwise (fun x y => key x ≤ key y) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_map] at hi hj
      simp only [L₂, List.getElem_map]
      have ha := hbnd _ (List.getElem_mem hi)
      have hb := hbnd _ (List.getElem_mem hj)
      dsimp [key, f1]
      rw [hbKey1_bitsToNat_le_iff comb (wOf K) _ _ _ _ ha.2.2.1 hb.2.2.1
        ha.2.2.2.1 hb.2.2.2.1 ha.2.2.2.2 hb.2.2.2.2]
      exact (List.pairwise_iff_getElem.mp hpw_s1) i j hi hj hij
    have hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y := by
      intro x hx y hy hxy
      rcases List.mem_map.mp hx with ⟨rx, hrx, rfl⟩
      rcases List.mem_map.mp hy with ⟨ry, hry, rfl⟩
      have ha := hbnd rx hrx
      have hb := hbnd ry hry
      dsimp [key, f1] at hxy
      rw [hbKey1_bitsToNat_eq_iff comb (wOf K) _ _ _ _ ha.2.2.1 hb.2.2.1
        ha.2.2.2.1 hb.2.2.2.1 ha.2.2.2.2 hb.2.2.2.2] at hxy
      have horig := comb.hbKey1_orig_inj rx ry hxy
      have hreq := eq_of_mem_of_nodup_map (·.orig) (hb1SortedList_orig_nodup K l) hrx hry horig
      rw [hreq]
    have hlist_eq := comb.perm_eq_of_sorted_of_inj key L₁ L₂ hperm12 hp1 hp2 hinj
    funext q
    have hget := congrArg (fun L : List (Qubits (wR1Hb K)) => L[q.1]!) hlist_eq
    have hq1 : q.1 < L₁.length := by rw [List.length_ofFn]; exact q.isLt
    have hq2 : q.1 < L₂.length := by rw [List.length_map, hb1SortedList_length]; exact q.isLt
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hq1,
      List.getElem?_eq_getElem hq2, Option.getD_some, L₁, L₂, List.getElem_ofFn, List.getElem_map] at hget
    exact hget
  dsimp only [sortHb1Circ]
  have htr : z ∘ eTr2a as n K d = fun _ => false := funext fun j => congrFun hzTr _
  have hanc : z ∘ eSort2aAnc as n K d = fun _ => false := funext fun k => congrFun hzAnc _
  have hcomp := comp_packDTA54Emb (eRec2 as n K d) (eTr2a as n K d) (eSort2aAnc as n K d)
    (eRec2_disjoint_eTr2a as n K d) (eRec2_disjoint_eSort2aAnc as n K d) (eTr2a_disjoint_eSort2aAnc as n K d)
    z arr0 (fun _ => false) hzRec htr hanc
  have hact := act_mapWires_ket_singleton _ _ z _ (by
    rw [hcomp]
    exact br.act_bitonicSortKeyCircuit_ket (dHbOf K + 1) (wK1Hb K) (wP1Hb K) true arr0)
  rw [hact, htr_eq, hsort_eq]; congr 1
  exact updateOn_packDTA54_eq_two (eRec2 as n K d) (eTr2a as n K d) (eSort2aAnc as n K d)
    (eRec2_disjoint_eTr2a as n K d) (eRec2_disjoint_eSort2aAnc as n K d) (eTr2a_disjoint_eSort2aAnc as n K d)
    z hanc arrS (rec2SortTr K l)

/-! #### 9.4 Swap Circuits & Subtraction/Uncomputation Circuits -/

def swapRec3ToRec2DCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (arity (dHbOf K + 1))).map fun q =>
    if hq : q < arity (dHbOf K + 1) then
      (arith.swapRegCircuit (wOf K)).mapWires
        (combineEmb (eRec3DVal as n K d ⟨q, hq⟩) (eRec2DVal as n K d ⟨q, hq⟩)
          (eRec3DVal_disjoint_eRec2DVal as n K d ⟨q, hq⟩ ⟨q, hq⟩))
    else LayeredCircuit.id _)

lemma swapRec3ToRec2DCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    (swapRec3ToRec2DCirc as arith n K d).size ≤ arity (dHbOf K + 1) * (3 * wOf K) := by
  dsimp [swapRec3ToRec2DCirc]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (arity (dHbOf K + 1))).map fun q =>
      if hq : q < arity (dHbOf K + 1) then
        (arith.swapRegCircuit (wOf K)).mapWires
          (combineEmb (eRec3DVal as n K d ⟨q, hq⟩) (eRec2DVal as n K d ⟨q, hq⟩)
            (eRec3DVal_disjoint_eRec2DVal as n K d ⟨q, hq⟩ ⟨q, hq⟩))
      else LayeredCircuit.id _)
    (3 * wOf K)
    (fun lc hlc => by
      rcases List.mem_map.mp hlc with ⟨q, _, rfl⟩
      split_ifs with hq
      · rw [LayeredCircuit.mapWires_size, arith.swapRegCircuit_size]
      · simp)
  simpa using h

lemma act_swapRec3ToRec2DCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz3 : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL d_arr))
    (hz2 : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL (fun _ _ => false))) :
    act (swapRec3ToRec2DCirc as arith n K d).unitary (ket z) =
      ket (updateOn (eRec2 as n K d)
        (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL (fun _ _ => false))))
        (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))) := by
  let arr3 (p : ℕ) (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
    if q.1 < p then fun _ => false else d_arr q
  let arr2 (p : ℕ) (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
    if q.1 < p then d_arr q else fun _ => false
  let st (p : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eRec2 as n K d)
      (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL (arr3 p))))
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL (arr2 p)))
  have hst0 : st 0 = z := by
    dsimp only [st]
    have ha3 : arr3 0 = d_arr := funext fun q => by simp [arr3]
    have ha2 : arr2 0 = fun _ _ => false := funext fun q => by simp [arr2]
    rw [ha3, ha2, updateOn_noop (eRec3 as n K d) z _ hz3, updateOn_noop (eRec2 as n K d) z _ hz2]
  conv_lhs => rw [← hst0]
  dsimp [swapRec3ToRec2DCirc]
  have hloop := act_seqList_range st
    (fun q => if hq : q < arity (dHbOf K + 1) then
      (arith.swapRegCircuit (wOf K)).mapWires
        (combineEmb (eRec3DVal as n K d ⟨q, hq⟩) (eRec2DVal as n K d ⟨q, hq⟩)
          (eRec3DVal_disjoint_eRec2DVal as n K d ⟨q, hq⟩ ⟨q, hq⟩))
      else LayeredCircuit.id _)
    (arity (dHbOf K + 1))
    (fun q hq => by
      let qF : Fin (arity (dHbOf K + 1)) := ⟨q, hq⟩
      rw [dif_pos hq]
      have hst2 : st q ∘ eRec2 as n K d =
          flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL (arr2 q)) :=
        updateOn_comp_emb _ _ _
      have hst3 : st q ∘ eRec3 as n K d =
          flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL (arr3 q)) := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eRec3 as n K d), updateOn_comp_emb]
      have h3v : st q ∘ eRec3DVal as n K d qF = d_arr qF := by
        rw [comp_eRec3DVal as n K d (st q) L hL (arr3 q) hst3 qF]
        simp [arr3, qF]
      have h2v : st q ∘ eRec2DVal as n K d qF = fun _ => false := by
        rw [comp_eRec2DVal as n K d (st q) L hL (arr2 q) hst2 qF]
        simp [arr2, qF]
      rw [act_swapRegOn arith _ _ _ (st q), h3v, h2v]
      have hu1 := updateOn_eRec3DVal_eq as n K d (st q) L hL (arr3 q) hst3 qF (fun _ => false)
      rw [hu1]
      let z_mid := updateOn (eRec3 as n K d) (st q)
        (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL (Function.update (arr3 q) qF (fun _ => false))))
      have hzmid2 : z_mid ∘ eRec2 as n K d =
          flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL (arr2 q)) := by
        dsimp only [z_mid]
        rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_eRec2 as n K d)]
        exact hst2
      rw [updateOn_eRec2DVal_eq as n K d z_mid L hL (arr2 q) hzmid2 qF (d_arr qF)]
      dsimp only [z_mid, st]
      rw [updateOn_comm (eRec3 as n K d) (eRec2 as n K d) (eRec3_disjoint_eRec2 as n K d),
        updateOn_idem, updateOn_idem]
      have ha3 : Function.update (arr3 q) qF (fun _ => false) = arr3 (q + 1) := funext fun r => by
        by_cases hr : r = qF
        · subst hr; simp [arr3, qF]
        · rw [Function.update_of_ne hr]
          have hne : r.1 ≠ q := fun hv => hr (Fin.ext hv)
          have hlt : r.1 < q + 1 ↔ r.1 < q := by omega
          dsimp only [arr3]; simp only [hlt]
      have ha2 : Function.update (arr2 q) qF (d_arr qF) = arr2 (q + 1) := funext fun r => by
        by_cases hr : r = qF
        · subst hr; simp [arr2, qF]
        · rw [Function.update_of_ne hr]
          have hne : r.1 ≠ q := fun hv => hr (Fin.ext hv)
          have hlt : r.1 < q + 1 ↔ r.1 < q := by omega
          dsimp only [arr2]; simp only [hlt]
      rw [ha3, ha2])
  rw [hloop]
  have ha3N : arr3 (arity (dHbOf K + 1)) = fun _ _ => false := funext fun q => by
    dsimp only [arr3]; rw [if_pos q.isLt]
  have ha2N : arr2 (arity (dHbOf K + 1)) = d_arr := funext fun q => by
    dsimp only [arr2]; rw [if_pos q.isLt]
  dsimp only [st]; rw [ha3N, ha2N]

def swapRec2ToDCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (2 * K)).map fun i =>
    if hi : i < 2 * K then
      have hiB : i < arity (dHbOf K + 1) := by
        have := two_K_lt_B2 h1K; have := arity_succ_eq (dHbOf K); omega
      (arith.swapRegCircuit (wOf K)).mapWires
        (combineEmb (eRec2DVal as n K d ⟨i, hiB⟩) (eDSlot as n K d ⟨i, hi⟩)
          (eRec2DVal_disjoint_eDSlot as n K d ⟨i, hiB⟩ ⟨i, hi⟩))
    else LayeredCircuit.id _)

lemma swapRec2ToDCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    (swapRec2ToDCirc as arith n K d h1K).size ≤ (2 * K) * (3 * wOf K) := by
  dsimp [swapRec2ToDCirc]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (2 * K)).map fun i =>
      if hi : i < 2 * K then
        have hiB : i < arity (dHbOf K + 1) := by
          have := two_K_lt_B2 h1K; have := arity_succ_eq (dHbOf K); omega
        (arith.swapRegCircuit (wOf K)).mapWires
          (combineEmb (eRec2DVal as n K d ⟨i, hiB⟩) (eDSlot as n K d ⟨i, hi⟩)
            (eRec2DVal_disjoint_eDSlot as n K d ⟨i, hiB⟩ ⟨i, hi⟩))
      else LayeredCircuit.id _)
    (3 * wOf K)
    (fun lc hlc => by
      rcases List.mem_map.mp hlc with ⟨i, _, rfl⟩
      split_ifs with hi
      · rw [LayeredCircuit.mapWires_size, arith.swapRegCircuit_size]
      · simp)
  simpa using h

lemma act_swapRec2ToDCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) {l : Fin (2 * K) → Fin (n + 1)}
    (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) (z : Qubits (totWiresDef as n K d))
    (hz2 : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K)
      (hb1ArrOfList K (hbInit (2 * K) (arity (dHbOf K)) l)
        (by rw [hbInit_length, arity_succ_eq]) (dInitOf K l dFn)))
    (hzD : z ∘ ancEmb as n K d ⟨15, by decide⟩ = fun _ => false) :
    act (swapRec2ToDCirc as arith n K d h1K).unitary (ket z) =
      ket (updateOn (eDReg as n K d)
        (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l)))
        (flatReg (2 * K) (wOf K) (fun i => natToBits (wOf K) (dFn i).1))) := by
  let L0 := hbInit (2 * K) (arity (dHbOf K)) l
  have hL0 : L0.length = arity (dHbOf K + 1) := by rw [hbInit_length, arity_succ_eq]
  let arr2 (p : ℕ) (q : Fin (arity (dHbOf K + 1))) : Qubits (wOf K) :=
    if q.1 < p then fun _ => false else dInitOf K l dFn q
  let arrD (p : ℕ) (i : Fin (2 * K)) : Qubits (wOf K) :=
    if i.1 < p then natToBits (wOf K) (dFn i).1 else fun _ => false
  let st (p : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eDReg as n K d)
      (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L0 hL0 (arr2 p))))
      (flatReg (2 * K) (wOf K) (arrD p))
  have hzD' : z ∘ eDReg as n K d = flatReg (2 * K) (wOf K) (arrD 0) := by
    funext idx
    rcases finProdFinEquiv.surjective idx with ⟨⟨i, b⟩, rfl⟩
    have h0 : z (eDReg as n K d (finProdFinEquiv (i, b))) = false := congrFun hzD _
    simp [h0, arrD, flatReg]
  have hst0 : st 0 = z := by
    dsimp only [st]
    have ha2 : arr2 0 = dInitOf K l dFn := funext fun q => by simp [arr2]
    rw [ha2, updateOn_noop (eRec2 as n K d) z _ hz2, updateOn_noop (eDReg as n K d) z _ hzD']
  conv_lhs => rw [← hst0]
  dsimp [swapRec2ToDCirc]
  have hloop := act_seqList_range st
    (fun i => if hi : i < 2 * K then
      have hiB : i < arity (dHbOf K + 1) := by
        have := two_K_lt_B2 h1K; have := arity_succ_eq (dHbOf K); omega
      (arith.swapRegCircuit (wOf K)).mapWires
        (combineEmb (eRec2DVal as n K d ⟨i, hiB⟩) (eDSlot as n K d ⟨i, hi⟩)
          (eRec2DVal_disjoint_eDSlot as n K d ⟨i, hiB⟩ ⟨i, hi⟩))
      else LayeredCircuit.id _)
    (2 * K)
    (fun i hi => by
      have hiB : i < arity (dHbOf K + 1) := by
        have := two_K_lt_B2 h1K; have := arity_succ_eq (dHbOf K); omega
      let iF : Fin (2 * K) := ⟨i, hi⟩
      let qF : Fin (arity (dHbOf K + 1)) := ⟨i, hiB⟩
      rw [dif_pos hi]
      have hstD : st i ∘ eDReg as n K d = flatReg (2 * K) (wOf K) (arrD i) := updateOn_comp_emb _ _ _
      have hst2 : st i ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L0 hL0 (arr2 i)) := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (fun a b h => eRec2_disjoint_eDReg as n K d b a h.symm),
          updateOn_comp_emb]
      have h2v : st i ∘ eRec2DVal as n K d qF = natToBits (wOf K) (dFn iF).1 := by
        rw [comp_eRec2DVal as n K d (st i) L0 hL0 (arr2 i) hst2 qF]
        dsimp only [arr2, qF]
        rw [if_neg (lt_irrefl i)]
        exact dInitOf_lt_2K comb h1K l dFn iF
      have hDv : st i ∘ eDSlot as n K d iF = fun _ => false := by
        rw [comp_eDSlot as n K d (st i) (arrD i) hstD iF]
        simp [arrD, iF]
      rw [act_swapRegOn arith _ _ _ (st i), h2v, hDv]
      rw [updateOn_eRec2DVal_eq as n K d (st i) L0 hL0 (arr2 i) hst2 qF (fun _ => false)]
      let z_mid := updateOn (eRec2 as n K d) (st i)
        (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L0 hL0 (Function.update (arr2 i) qF (fun _ => false))))
      have hzmidD : z_mid ∘ eDReg as n K d = flatReg (2 * K) (wOf K) (arrD i) := by
        dsimp only [z_mid]
        rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eDReg as n K d)]
        exact hstD
      rw [updateOn_eDSlot_eq as n K d z_mid (arrD i) hzmidD iF (natToBits (wOf K) (dFn iF).1)]
      dsimp only [z_mid, st]
      rw [updateOn_comm (eRec2 as n K d) (eDReg as n K d) (eRec2_disjoint_eDReg as n K d),
        updateOn_idem, updateOn_idem]
      have ha2 : Function.update (arr2 i) qF (fun _ => false) = arr2 (i + 1) := funext fun r => by
        by_cases hr : r = qF
        · subst hr; simp [arr2, qF]
        · rw [Function.update_of_ne hr]
          have hne : r.1 ≠ i := fun hv => hr (Fin.ext hv)
          have hlt : r.1 < i + 1 ↔ r.1 < i := by omega
          dsimp only [arr2]; simp only [hlt]
      have haD : Function.update (arrD i) iF (natToBits (wOf K) (dFn iF).1) = arrD (i + 1) := funext fun r => by
        by_cases hr : r = iF
        · subst hr; simp [arrD, iF]
        · rw [Function.update_of_ne hr]
          have hne : r.1 ≠ i := fun hv => hr (Fin.ext hv)
          have hlt : r.1 < i + 1 ↔ r.1 < i := by omega
          dsimp only [arrD]; simp only [hlt]
      rw [ha2, haD])
  rw [hloop]
  have ha2N : arr2 (2 * K) = fun _ _ => false := funext fun q => by
    dsimp only [arr2]
    by_cases hq : q.1 < 2 * K
    · rw [if_pos hq]
    · rw [if_neg hq]; exact dInitOf_ge_2K h1K l dFn q (Nat.not_lt.mp hq)
  have haDN : arrD (2 * K) = fun i => natToBits (wOf K) (dFn i).1 := funext fun i => by
    dsimp only [arrD]; rw [if_pos i.isLt]
  dsimp only [st]; rw [ha2N, haDN]
  congr 1

def subSlotCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) (i : Fin (2 * K)) :
    LayeredCircuit (totWiresDef as n K d) :=
  have h5w := five_le_wOf h1K
  let eD := eDSlot as n K d i
  let eTmp := eSubTmp as n K d
  let eO := eOutSlot as n K d ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩
  let eA := eArith345 as n K d 1 (by omega)
  let c1 := (arith.setConstMSBCircuit (wOf K) i.1).mapWires eTmp
  let c2 := (arith.subInPlaceMSBCircuit (wOf K)).mapWires
    (combineEmb (combineEmb eD eTmp (eDSlot_disjoint_eSubTmp as n K d i)) eA
      (emb_disjoint_combineEmb (eDSlot_disjoint_eSubTmp as n K d i)
        (eDSlot_disjoint_eArith345 as n K d 1 (by omega) i)
        (eSubTmp_disjoint_eArith345 as n K d 1 (by omega))))
  let c3 := (copyLowBitsCircuit (wOf K) d).mapWires
    (combineEmb eTmp eO (eSubTmp_disjoint_eOutSlot as n K d _))
  let c4 := (arith.addInPlaceMSBCircuit (wOf K)).mapWires
    (combineEmb (combineEmb eTmp eD (eSubTmp_disjoint_eDSlot as n K d i)) eA
      (emb_disjoint_combineEmb (eSubTmp_disjoint_eDSlot as n K d i)
        (eSubTmp_disjoint_eArith345 as n K d 1 (by omega))
        (eDSlot_disjoint_eArith345 as n K d 1 (by omega) i)))
  let c5 := (arith.setConstMSBCircuit (wOf K) i.1).mapWires eD
  let c6 := (copyLowBitsCircuit d (wOf K)).mapWires
    (combineEmb eO eTmp (eOutSlot_disjoint_eSubTmp as n K d _))
  LayeredCircuit.seqList [c1, c2, c3, c4, c5, c6]

lemma subSlotCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) (i : Fin (2 * K)) :
    (subSlotCirc as arith n K d h1K hNM i).size ≤ 32 * wOf K := by
  dsimp [subSlotCirc]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
  have h1 := arith.setConstMSBCircuit_size (wOf K) i.1
  have h2 := arith.subInPlaceMSBCircuit_size (wOf K)
  have h3 := arith.addInPlaceMSBCircuit_size (wOf K)
  have h4 := copyLowBitsCircuit_size (wOf K) d
  have h5 := copyLowBitsCircuit_size d (wOf K)
  omega

lemma act_subSlotCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) {l : Fin (2 * K) → Fin (n + 1)}
    (hl : Monotone l) (dFn : (i : Fin (2 * K)) → Fin (runOffset l i))
    (z : Qubits (totWiresDef as n K d)) (i : Fin (2 * K))
    (hzD : z ∘ eDSlot as n K d i = natToBits (wOf K) (dFn i).1)
    (hzTmp : z ∘ eSubTmp as n K d = fun _ => false)
    (hzOut : z ∘ eOutSlot as n K d ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩ = fun _ => false)
    (hzAnc22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false) :
    let s_i := i.1 - (dFn i).1
    act (subSlotCirc as arith n K d h1K hNM i).unitary (ket z) =
      ket (updateOn (eDSlot as n K d i)
        (updateOn (eOutSlot as n K d ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩) z (natToBits d s_i))
        (fun _ => false)) := by
  have h5w := five_le_wOf h1K
  intro s_i
  have hrs := comb.runStart_le hl i
  have hdoff : (dFn i).1 < runOffset l i := (dFn i).isLt
  have hle_i : (dFn i).1 ≤ i.1 := by dsimp [runOffset] at hdoff; omega
  have h2K_w : 2 * K < 2 ^ wOf K := by
    have := two_K_lt_B2 h1K; have := two_mul_B2_add_one_lt_two_pow_wOf h1K; omega
  have hi_w : i.1 < 2 ^ wOf K := lt_trans i.isLt h2K_w
  have hd_w : (dFn i).1 < 2 ^ wOf K := lt_of_le_of_lt hle_i hi_w
  have hs_lt_min : s_i < 2 ^ min (wOf K) d := by
    dsimp [s_i]
    rcases le_total (wOf K) d with hwd | hdw
    · rw [min_eq_left hwd]; exact lt_of_le_of_lt (Nat.sub_le _ _) hi_w
    · rw [min_eq_right hdw]
      have h2d : 2 * K ≤ 2 ^ d := by simpa [arity_eq_two_pow] using hNM
      exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le i.isLt h2d)
  have hs_w : s_i < 2 ^ wOf K := lt_of_le_of_lt (Nat.sub_le _ _) hi_w
  have hs_d : s_i < 2 ^ d := by
    have h2d : 2 * K ≤ 2 ^ d := by simpa [arity_eq_two_pow] using hNM
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le i.isLt h2d)
  let eD := eDSlot as n K d i
  let eTmp := eSubTmp as n K d
  let eO := eOutSlot as n K d ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩
  let eA := eArith345 as n K d 1 (by omega)
  have hzA : z ∘ eA = fun _ => false := funext fun j => congrFun hzAnc22 _
  let z1 := updateOn eTmp z (natToBits (wOf K) i.1)
  have hz1_D : z1 ∘ eD = natToBits (wOf K) (dFn i).1 := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eSubTmp_disjoint_eDSlot as n K d i)]; exact hzD
  have hz1_Tmp : z1 ∘ eTmp = natToBits (wOf K) i.1 := updateOn_comp_emb _ _ _
  have hz1_O : z1 ∘ eO = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eSubTmp_disjoint_eOutSlot as n K d _)]; exact hzOut
  have hz1_A : z1 ∘ eA = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eSubTmp_disjoint_eArith345 as n K d 1 (by omega))]; exact hzA
  have hc1_val : (fun b : Fin (wOf K) => xor (z (eTmp b)) (natToBits (wOf K) i.1 b)) = natToBits (wOf K) i.1 :=
    funext fun b => by rw [show z (eTmp b) = false from congrFun hzTmp b]; exact Bool.false_xor _
  have hs1 : act ((arith.setConstMSBCircuit (wOf K) i.1).mapWires eTmp).unitary (ket z) = ket z1 := by
    rw [act_setConstOn arith i.1 eTmp z, hc1_val]
  let z2 := updateOn eTmp z (natToBits (wOf K) s_i)
  have hz2_D : z2 ∘ eD = natToBits (wOf K) (dFn i).1 := by
    dsimp only [z2]; rw [updateOn_comp_disjoint _ _ (eSubTmp_disjoint_eDSlot as n K d i)]; exact hzD
  have hz2_Tmp : z2 ∘ eTmp = natToBits (wOf K) s_i := updateOn_comp_emb _ _ _
  have hz2_O : z2 ∘ eO = fun _ => false := by
    dsimp only [z2]; rw [updateOn_comp_disjoint _ _ (eSubTmp_disjoint_eOutSlot as n K d _)]; exact hzOut
  have hz2_A : z2 ∘ eA = fun _ => false := by
    dsimp only [z2]; rw [updateOn_comp_disjoint _ _ (eSubTmp_disjoint_eArith345 as n K d 1 (by omega))]; exact hzA
  have hsub_val : natToBits (wOf K) (2 ^ wOf K + bitsToNat (z1 ∘ eTmp) - bitsToNat (z1 ∘ eD)) =
      natToBits (wOf K) s_i := by
    rw [hz1_Tmp, hz1_D, comb.bitsToNat_natToBits hi_w, comb.bitsToNat_natToBits hd_w]
    rw [show 2 ^ wOf K + i.1 - (dFn i).1 = 2 ^ wOf K + s_i by dsimp [s_i]; omega]
    exact natToBits_two_pow_add (wOf K) s_i
  have hs2 : act ((arith.subInPlaceMSBCircuit (wOf K)).mapWires
      (combineEmb (combineEmb eD eTmp (eDSlot_disjoint_eSubTmp as n K d i)) eA
        (emb_disjoint_combineEmb (eDSlot_disjoint_eSubTmp as n K d i)
          (eDSlot_disjoint_eArith345 as n K d 1 (by omega) i)
          (eSubTmp_disjoint_eArith345 as n K d 1 (by omega))))).unitary (ket z1) = ket z2 := by
    rw [act_subInPlaceOn arith eD eTmp eA
      (eDSlot_disjoint_eSubTmp as n K d i)
      (eDSlot_disjoint_eArith345 as n K d 1 (by omega) i)
      (eSubTmp_disjoint_eArith345 as n K d 1 (by omega)) z1 hz1_A, hsub_val]
    dsimp only [z2, z1]; rw [updateOn_idem]
  let z3 := updateOn eO z2 (natToBits d s_i)
  have hz3_D : z3 ∘ eD = natToBits (wOf K) (dFn i).1 := by
    dsimp only [z3, eO, eD]
    rw [updateOn_comp_disjoint _ _ (eOutSlot_disjoint_eDSlot as n K d _ i)]
    exact hz2_D
  have hz3_Tmp : z3 ∘ eTmp = natToBits (wOf K) s_i := by
    dsimp only [z3]; rw [updateOn_comp_disjoint _ _ (eOutSlot_disjoint_eSubTmp as n K d _)]; exact hz2_Tmp
  have hz3_O : z3 ∘ eO = natToBits d s_i := updateOn_comp_emb _ _ _
  have hz3_A : z3 ∘ eA = fun _ => false := by
    dsimp only [z3, eO, eA]
    rw [updateOn_comp_disjoint _ _ (eOutSlot_disjoint_eArith345 as n K d 1 (by omega) _)]
    exact hz2_A
  have hs3 : act ((copyLowBitsCircuit (wOf K) d).mapWires
      (combineEmb eTmp eO (eSubTmp_disjoint_eOutSlot as n K d _))).unitary (ket z2) = ket z3 :=
    act_copyLowBitsOn_zero comb arith eTmp eO (eSubTmp_disjoint_eOutSlot as n K d _) z2 s_i hs_lt_min hz2_Tmp hz2_O
  let z4 := updateOn eD z3 (natToBits (wOf K) i.1)
  have hz4_D : z4 ∘ eD = natToBits (wOf K) i.1 := updateOn_comp_emb _ _ _
  have hz4_Tmp : z4 ∘ eTmp = natToBits (wOf K) s_i := by
    dsimp only [z4]; rw [updateOn_comp_disjoint _ _ (eDSlot_disjoint_eSubTmp as n K d i)]; exact hz3_Tmp
  have hz4_O : z4 ∘ eO = natToBits d s_i := by
    dsimp only [z4, eD, eO]
    rw [updateOn_comp_disjoint _ _ (eDSlot_disjoint_eOutSlot as n K d i _)]
    exact hz3_O
  have hadd_val : natToBits (wOf K) (bitsToNat (z3 ∘ eTmp) + bitsToNat (z3 ∘ eD)) = natToBits (wOf K) i.1 := by
    rw [hz3_Tmp, hz3_D, comb.bitsToNat_natToBits hs_w, comb.bitsToNat_natToBits hd_w]
    rw [show s_i + (dFn i).1 = i.1 by dsimp [s_i]; omega]
  have hs4 : act ((arith.addInPlaceMSBCircuit (wOf K)).mapWires
      (combineEmb (combineEmb eTmp eD (eSubTmp_disjoint_eDSlot as n K d i)) eA
        (emb_disjoint_combineEmb (eSubTmp_disjoint_eDSlot as n K d i)
          (eSubTmp_disjoint_eArith345 as n K d 1 (by omega))
          (eDSlot_disjoint_eArith345 as n K d 1 (by omega) i)))).unitary (ket z3) = ket z4 := by
    rw [act_addInPlaceOn arith eTmp eD eA
      (eSubTmp_disjoint_eDSlot as n K d i)
      (eSubTmp_disjoint_eArith345 as n K d 1 (by omega))
      (eDSlot_disjoint_eArith345 as n K d 1 (by omega) i) z3 hz3_A, hadd_val]
  let z5 := updateOn eD z4 (fun _ => false)
  have hz5_O : z5 ∘ eO = natToBits d s_i := by
    dsimp only [z5, eD, eO]
    rw [updateOn_comp_disjoint _ _ (eDSlot_disjoint_eOutSlot as n K d i _)]
    exact hz4_O
  have hz5_Tmp : z5 ∘ eTmp = natToBits (wOf K) s_i := by
    dsimp only [z5]; rw [updateOn_comp_disjoint _ _ (eDSlot_disjoint_eSubTmp as n K d i)]; exact hz4_Tmp
  have hc5_val : (fun b : Fin (wOf K) => xor (z4 (eD b)) (natToBits (wOf K) i.1 b)) = fun _ => false :=
    funext fun b => by rw [show z4 (eD b) = natToBits (wOf K) i.1 b from congrFun hz4_D b]; exact Bool.xor_self _
  have hs5 : act ((arith.setConstMSBCircuit (wOf K) i.1).mapWires eD).unitary (ket z4) = ket z5 := by
    rw [act_setConstOn arith i.1 eD z4, hc5_val]
  have hs6 : act ((copyLowBitsCircuit d (wOf K)).mapWires
      (combineEmb eO eTmp (eOutSlot_disjoint_eSubTmp as n K d _))).unitary (ket z5) =
      ket (updateOn eTmp z5 (fun _ => false)) :=
    act_copyLowBitsOn_uncompute comb arith eO eTmp (eOutSlot_disjoint_eSubTmp as n K d _) z5 s_i
      (by rw [min_comm]; exact hs_lt_min) hz5_O hz5_Tmp
  dsimp only [subSlotCirc]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  rw [hs1, hs2, hs3, hs4, hs5, hs6]
  congr 1
  dsimp only [z5, z4, z3, z2, eTmp, eD, eO]
  rw [updateOn_idem,
    updateOn_comm (eSubTmp as n K d) (eDSlot as n K d i) (eSubTmp_disjoint_eDSlot as n K d i),
    updateOn_comm (eSubTmp as n K d) (eOutSlot as n K d ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩)
      (eSubTmp_disjoint_eOutSlot as n K d _),
    updateOn_idem,
    updateOn_noop (eSubTmp as n K d) z (fun _ => false) hzTmp]

def subAndUncomputeDCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) : LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (2 * K)).map fun i =>
    if hi : i < 2 * K then subSlotCirc as arith n K d h1K hNM ⟨i, hi⟩
    else LayeredCircuit.id _)

lemma subAndUncomputeDCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) :
    (subAndUncomputeDCirc as arith n K d h1K hNM).size ≤ (2 * K) * (32 * wOf K) := by
  dsimp [subAndUncomputeDCirc]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (2 * K)).map fun i =>
      if hi : i < 2 * K then subSlotCirc as arith n K d h1K hNM ⟨i, hi⟩
      else LayeredCircuit.id _)
    (32 * wOf K)
    (fun lc hlc => by
      rcases List.mem_map.mp hlc with ⟨i, _, rfl⟩
      split_ifs with hi
      · exact subSlotCirc_size as arith n K d h1K hNM ⟨i, hi⟩
      · simp)
  simpa using h

lemma act_subAndUncomputeDCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) {l : Fin (2 * K) → Fin (n + 1)}
    (hl : Monotone l) (dFn : (i : Fin (2 * K)) → Fin (runOffset l i))
    (z : Qubits (totWiresDef as n K d))
    (hzD : z ∘ eDReg as n K d = flatReg (2 * K) (wOf K) (fun i => natToBits (wOf K) (dFn i).1))
    (hzTmp : z ∘ eSubTmp as n K d = fun _ => false)
    (hzOut : z ∘ eOut as n K d = fun _ => false)
    (hzAnc22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false) :
    let sFn := (isLESOfEquivPiFinOf (2 * K) l (comb.runStart_le hl)).symm dFn
    act (subAndUncomputeDCirc as arith n K d h1K hNM).unitary (ket z) =
      ket (updateOn (eOut as n K d)
        (updateOn (eDReg as n K d) z (fun _ => false))
        (flatReg (arity d) d (padZeroLESBits (2 * K) d sFn.1))) := by
  intro sFn
  let arrD (p : ℕ) (i : Fin (2 * K)) : Qubits (wOf K) :=
    if i.1 < p then fun _ => false else natToBits (wOf K) (dFn i).1
  let arrOut (p : ℕ) (j : Fin (arity d)) : Qubits d :=
    if j.1 < p then (if hj : j.1 < 2 * K then natToBits d (sFn.1 ⟨j.1, hj⟩) else fun _ => false)
    else fun _ => false
  let st (p : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eOut as n K d)
      (updateOn (eDReg as n K d) z (flatReg (2 * K) (wOf K) (arrD p)))
      (flatReg (arity d) d (arrOut p))
  have hzOut' : z ∘ eOut as n K d = flatReg (arity d) d (arrOut 0) := by
    funext idx
    rcases finProdFinEquiv.surjective idx with ⟨⟨j, b⟩, rfl⟩
    have h0 : z (eOut as n K d (finProdFinEquiv (j, b))) = false := congrFun hzOut _
    simp [h0, arrOut, flatReg]
  have hst0 : st 0 = z := by
    dsimp only [st]
    have haD : arrD 0 = fun i => natToBits (wOf K) (dFn i).1 := funext fun i => by simp [arrD]
    rw [haD, updateOn_noop (eDReg as n K d) z _ hzD, updateOn_noop (eOut as n K d) z _ hzOut']
  conv_lhs => rw [← hst0]
  dsimp [subAndUncomputeDCirc]
  have hloop := act_seqList_range st
    (fun i => if hi : i < 2 * K then subSlotCirc as arith n K d h1K hNM ⟨i, hi⟩ else LayeredCircuit.id _)
    (2 * K)
    (fun i hi => by
      let iF : Fin (2 * K) := ⟨i, hi⟩
      let jF : Fin (arity d) := ⟨i, lt_of_lt_of_le hi hNM⟩
      rw [dif_pos hi]
      have hstOut : st i ∘ eOut as n K d = flatReg (arity d) d (arrOut i) := updateOn_comp_emb _ _ _
      have hstD : st i ∘ eDReg as n K d = flatReg (2 * K) (wOf K) (arrD i) := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eOut_disjoint_eDReg as n K d), updateOn_comp_emb]
      have hDv : st i ∘ eDSlot as n K d iF = natToBits (wOf K) (dFn iF).1 := by
        rw [comp_eDSlot as n K d (st i) (arrD i) hstD iF]
        simp [arrD, iF]
      have hTmpv : st i ∘ eSubTmp as n K d = fun _ => false := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eOut_disjoint_eSubTmp as n K d),
          updateOn_comp_disjoint _ _ (eDReg_disjoint_eSubTmp as n K d)]
        exact hzTmp
      have hOutv : st i ∘ eOutSlot as n K d jF = fun _ => false := by
        dsimp only [eOutSlot]
        have hcomp : st i ∘ (slotInReg (arity d) d jF).trans (eOut as n K d) =
            (st i ∘ eOut as n K d) ∘ slotInReg (arity d) d jF := rfl
        rw [hcomp, hstOut]
        funext b; simp only [flatReg_comp_slotInReg, arrOut, jF, if_neg (lt_irrefl i)]
      have hAnc22v : st i ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eOut_disjoint_anc as n K d ⟨22, by decide⟩)]
        rw [updateOn_comp_disjoint _ _ (eDReg_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
        exact hzAnc22
      rw [act_subSlotCirc comb as arith n K d h1K hNM hl dFn (st i) iF hDv hTmpv hOutv hAnc22v]
      have hs_eq : iF.1 - (dFn iF).1 = sFn.1 iF := rfl
      rw [hs_eq]
      have heq_out : updateOn (eOutSlot as n K d jF) (st i) (natToBits d (sFn.1 iF)) =
          updateOn (eOut as n K d) (updateOn (eDReg as n K d) z (flatReg (2 * K) (wOf K) (arrD i)))
            (flatReg (arity d) d (Function.update (arrOut i) jF (natToBits d (sFn.1 iF)))) := by
        dsimp only [eOutSlot, st]
        exact updateOn_slot_absorb (eOut as n K d) _ (arrOut i) jF (natToBits d (sFn.1 iF))
      rw [heq_out, updateOn_comm (eDSlot as n K d iF) (eOut as n K d)
        (fun a b h => eOut_disjoint_eDSlot as n K d iF b a h.symm)]
      have heq_d : updateOn (eDSlot as n K d iF)
          (updateOn (eDReg as n K d) z (flatReg (2 * K) (wOf K) (arrD i))) (fun _ => false) =
          updateOn (eDReg as n K d) z (flatReg (2 * K) (wOf K) (Function.update (arrD i) iF (fun _ => false))) := by
        dsimp only [eDSlot, eDReg]
        exact updateOn_slot_absorb (ancRegSlice as n K d ⟨15, by decide⟩ (2 * K) (wOf K) (ancLen_15 n K d _))
          z (arrD i) iF (fun _ => false)
      rw [heq_d]
      have haD_succ : Function.update (arrD i) iF (fun _ => false) = arrD (i + 1) := funext fun r => by
        by_cases hr : r = iF
        · subst hr; simp [arrD, iF]
        · rw [Function.update_of_ne hr]
          have hne : r.1 ≠ i := fun hv => hr (Fin.ext hv)
          have hlt : r.1 < i + 1 ↔ r.1 < i := by omega
          dsimp only [arrD]; simp only [hlt]
      have haO_succ : Function.update (arrOut i) jF (natToBits d (sFn.1 iF)) = arrOut (i + 1) := funext fun r => by
        by_cases hr : r = jF
        · subst hr; simp [arrOut, jF, iF, hi]
        · rw [Function.update_of_ne hr]
          have hne : r.1 ≠ i := fun hv => hr (Fin.ext hv)
          have hlt : r.1 < i + 1 ↔ r.1 < i := by omega
          dsimp only [arrOut]; simp only [hlt]
      dsimp only [st]; rw [haD_succ, haO_succ])
  rw [hloop]
  dsimp only [st]
  have haDN : flatReg (2 * K) (wOf K) (arrD (2 * K)) = fun _ => false := by
    funext idx; rcases finProdFinEquiv.surjective idx with ⟨⟨i, b⟩, rfl⟩
    simp [flatReg, arrD, i.isLt]
  have haON : arrOut (2 * K) = padZeroLESBits (2 * K) d sFn.1 := funext fun j => by
    dsimp [arrOut, padZeroLESBits]
    by_cases hj : j.1 < 2 * K
    · rw [if_pos hj, dif_pos hj]
    · rw [if_neg hj, dif_neg hj]
  rw [haDN, haON]

/-! #### 9.5 Full Uncomputation Circuit (`unrouteAndSubCirc`) & Step 6 (`asPermCirc`) -/

def unrouteAndSubCirc (_occ : HarmBucketOcc54) (_comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) : LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList [
    (sortHb2Circ as br n K d).adj,
    swapRec3ToRec2DCirc as arith n K d,
    (copyToRec3Circ as arith n K d).adj,
    (hbSeqPassCirc as arith n K d h1K).adj,
    (sortHb1Circ as br n K d).adj,
    swapRec2ToDCirc as arith n K d h1K,
    (hbInitCirc as arith n K d).adj,
    subAndUncomputeDCirc as arith n K d h1K hNM,
    (step12Circ as arith br n K d h1K).adj
  ]

lemma unrouteAndSubCirc_size (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (routeA : HarmBucketRouteA54)
    (routeB : HarmBucketRouteB54) (n K d : ℕ) (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) :
    ((unrouteAndSubCirc occ comb br as arith n K d h1K hNM).size : ℝ) ≤
      br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR2Hb K : ℝ) + 1) +
      (arity (dHbOf K + 1) * (3 * wOf K) : ℕ) +
      (arity (dHbOf K + 1) * (2 * wOf K + 3) : ℕ) +
      ((arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) : ℕ) +
      br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + 1) +
      ((2 * K) * (3 * wOf K) : ℕ) +
      (arity (dHbOf K + 1) * (11 * wOf K + 12) : ℕ) +
      ((2 * K) * (32 * wOf K) : ℕ) +
      ((wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) +
        2 * (arity (dOccOf K) * (2 * wOf K + 2) : ℕ) +
        2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) +
        ((2 * K - 1) * (49 * wOf K + 236) : ℕ) +
        ((2 * K) * (3 * wOf K) : ℕ)) := by
  dsimp only [unrouteAndSubCirc]
  rw [LayeredCircuit.seqList_size]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    LayeredCircuit.adj_size]
  conv_lhs => simp only [Nat.cast_add]
  have h1 := routeB.sortHb2Circ_size as br n K d
  have h2 : ((swapRec3ToRec2DCirc as arith n K d).size : ℝ) ≤ (arity (dHbOf K + 1) * (3 * wOf K) : ℕ) :=
    Nat.cast_le.mpr (swapRec3ToRec2DCirc_size as arith n K d)
  have h3 : ((copyToRec3Circ as arith n K d).size : ℝ) ≤ (arity (dHbOf K + 1) * (2 * wOf K + 3) : ℕ) :=
    Nat.cast_le.mpr (routeB.copyToRec3Circ_size as arith n K d)
  have h4 : ((hbSeqPassCirc as arith n K d h1K).size : ℝ) ≤ ((arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) : ℕ) :=
    Nat.cast_le.mpr (routeA.hbSeqPassCirc_size as arith n K d h1K)
  have h5 := routeA.sortHb1Circ_size as br n K d
  have h6 : ((swapRec2ToDCirc as arith n K d h1K).size : ℝ) ≤ ((2 * K) * (3 * wOf K) : ℕ) :=
    Nat.cast_le.mpr (swapRec2ToDCirc_size as arith n K d h1K)
  have h7 : ((hbInitCirc as arith n K d).size : ℝ) ≤ (arity (dHbOf K + 1) * (11 * wOf K + 12) : ℕ) :=
    Nat.cast_le.mpr (routeA.hbInitCirc_size as arith n K d)
  have h8 : ((subAndUncomputeDCirc as arith n K d h1K hNM).size : ℝ) ≤ ((2 * K) * (32 * wOf K) : ℕ) :=
    Nat.cast_le.mpr (subAndUncomputeDCirc_size as arith n K d h1K hNM)
  have h9 := occ.step12Circ_size as arith br n K d h1K
  linarith

private lemma padZero_eL_comp (as : AlonsoSchottSil54) (n K d : ℕ)
    (a : Qubits (2 * K * sOf n)) (b : Qubits (arity d * d)) :
    padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append a b) ∘ eL as n K d = a := by
  funext i
  have hidx : eL as n K d i = Fin.castAdd (harmBucketAncDef as n K d) (Fin.castAdd (arity d * d) i) :=
    Fin.ext (by simp [eL])
  dsimp only [Function.comp_apply]
  rw [hidx, padZero_castAdd, Fin.append_left]

private lemma padZero_eOut_comp (as : AlonsoSchottSil54) (n K d : ℕ)
    (a : Qubits (2 * K * sOf n)) (b : Qubits (arity d * d)) :
    padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append a b) ∘ eOut as n K d = b := by
  funext j
  have hidx : eOut as n K d j = Fin.castAdd (harmBucketAncDef as n K d) (Fin.natAdd (2 * K * sOf n) j) :=
    Fin.ext (by simp [eOut])
  dsimp only [Function.comp_apply]
  rw [hidx, padZero_castAdd, Fin.append_right]

private lemma padZero_anc_comp (as : AlonsoSchottSil54) (n K d : ℕ)
    (v : Qubits (2 * K * sOf n + arity d * d)) (k : Fin 24) :
    padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) v ∘ ancEmb as n K d k = fun _ => false := by
  funext i
  have hidx : ancEmb as n K d k i = Fin.natAdd (2 * K * sOf n + arity d * d)
      ⟨ancOff n K d (as.alonsoSchottAnc (2 * K) d) k + i.1, by
        have := ancOff_add_ancLen_le_sum n K d (as.alonsoSchottAnc (2 * K) d) k
        unfold harmBucketAncDef; omega⟩ :=
    Fin.ext (by simp [ancEmb, add_assoc])
  dsimp only [Function.comp_apply]
  rw [hidx, padZero_natAdd]

private lemma padZero_eAsAnc_comp (as : AlonsoSchottSil54) (n K d : ℕ)
    (v : Qubits (2 * K * sOf n + arity d * d)) :
    padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) v ∘ eAsAnc as n K d = fun _ => false := by
  funext k
  have hklt : 0 + k.1 < ancLen n K d (as.alonsoSchottAnc (2 * K) d) ⟨23, by decide⟩ := by
    rw [ancLen_23, zero_add]; exact k.isLt
  have hk : eAsAnc as n K d k = ancEmb as n K d ⟨23, by decide⟩ ⟨0 + k.1, hklt⟩ := rfl
  dsimp only [Function.comp_apply]
  rw [hk]
  exact congrFun (padZero_anc_comp as n K d v ⟨23, by decide⟩) ⟨0 + k.1, hklt⟩

private lemma updateOn_eOut_padZero (as : AlonsoSchottSil54) (n K d : ℕ)
    (a : Qubits (2 * K * sOf n)) (b₀ b₁ : Qubits (arity d * d)) :
    updateOn (eOut as n K d)
        (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append a b₀)) b₁ =
      padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append a b₁) := by
  funext u
  by_cases hu : u ∈ Set.range (eOut as n K d)
  · rcases hu with ⟨j, rfl⟩
    rw [updateOn_apply_emb]
    exact (congrFun (padZero_eOut_comp as n K d a b₁) j).symm
  · rw [updateOn_apply_not_mem _ _ _ hu]
    rcases Nat.lt_or_ge u.1 (2 * K * sOf n + arity d * d) with hlt | hge
    · have hlt_a : u.1 < 2 * K * sOf n := by
        by_contra hnot
        have hj : 2 * K * sOf n ≤ u.1 := Nat.not_lt.mp hnot
        exact hu ⟨⟨u.1 - 2 * K * sOf n, by omega⟩, Fin.ext (by simp [eOut]; omega)⟩
      have hu_eq : u = Fin.castAdd (harmBucketAncDef as n K d) (Fin.castAdd (arity d * d) ⟨u.1, hlt_a⟩) :=
        Fin.ext rfl
      rw [hu_eq, padZero_castAdd, padZero_castAdd, Fin.append_left, Fin.append_left]
    · have hu_lt : u.1 < (2 * K * sOf n + arity d * d) + harmBucketAncDef as n K d := u.isLt
      have hsub : (2 * K * sOf n + arity d * d) + (u.1 - (2 * K * sOf n + arity d * d)) = u.1 :=
        Nat.add_sub_of_le hge
      have hlt' : u.1 - (2 * K * sOf n + arity d * d) < harmBucketAncDef as n K d :=
        Nat.sub_lt_left_of_lt_add hge hu_lt
      have hu_eq : u = Fin.natAdd (2 * K * sOf n + arity d * d) ⟨u.1 - (2 * K * sOf n + arity d * d), hlt'⟩ :=
        Fin.ext (by simp only [Fin.val_natAdd]; exact hsub.symm)
      rw [hu_eq, padZero_natAdd, padZero_natAdd]

private lemma act_unroute_51_53 (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (routeB : HarmBucketRouteB54)
    (n K d : ℕ) (h1K : 1 ≤ K)
    {l : Fin (2 * K) → Fin (n + 1)} (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) :
    let aL := flatReg (2 * K) (sOf n) (fun p => particleSym54 n (sOf n) (l p))
    let z0 := padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append aL (fun _ => false))
    let z1 := updateOn (eOccReg as n K d)
      (updateOn (eActReg as n K d)
        (updateOn (eMReg as n K d) z0 (flatReg (2 * K) (wOf K) (mBitsFn K l)))
        (flatReg (2 * K) 1 (actBitsFn K l)))
      (flatReg (2 * K) (wOf K) (occBitsFn K l))
    let z3 := updateOn (eTr2b as n K d)
      (updateOn (eRec3 as n K d)
        (updateOn (eTr2a as n K d)
          (updateOn (eRec2 as n K d) z1
            (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
              (hb1ArrOfList K (hbSeqPass (hb1SortedList K l))
                (by rw [hbSeqPass_length, hb1SortedList_length]) (fun _ _ => false))))
          (rec2SortTr K l))
        (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3SortedArr K l)))
      (rec3SortTr K l)
    let z4 := updateOn (eRec3 as n K d) z3 (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn)))
    let s2 := hbSeqPass (hb1SortedList K l)
    let z_rec2_pass_d := updateOn (eRec2 as n K d) z1
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K s2 (by rw [hbSeqPass_length, hb1SortedList_length]) (dPassOf K l dFn)))
    let z_tr2a_d := updateOn (eTr2a as n K d) z_rec2_pass_d (rec2SortTr K l)
    act (copyToRec3Circ as arith n K d).adj.unitary
      (act (swapRec3ToRec2DCirc as arith n K d).unitary
        (act (sortHb2Circ as br n K d).adj.unitary (ket z4))) =
      ket z_tr2a_d := by
  intro aL z0 z1 z3 z4 s2 z_rec2_pass_d z_tr2a_d
  have hz0_anc : ∀ k : Fin 24, z0 ∘ ancEmb as n K d k = fun _ => false := fun k => padZero_anc_comp as n K d _ k
  have hz1_anc_ge3 : ∀ k : Fin 24, 3 ≤ k.1 → z1 ∘ ancEmb as n K d k = fun _ => false := fun k hk => by
    have h0 : k ≠ ⟨0, by decide⟩ := fun h => by subst h; simp at hk
    have h1 : k ≠ ⟨1, by decide⟩ := fun h => by subst h; simp at hk
    have h2 : k ≠ ⟨2, by decide⟩ := fun h => by subst h; simp at hk
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_anc_other as n K d k h2)]
    rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_anc_other as n K d k h1)]
    rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_anc_other as n K d k h0)]
    exact hz0_anc k
  -- 5.1: (sortHb2Circ).adj
  have hs2_len : s2.length = arity (dHbOf K + 1) := by
    dsimp only [s2]; rw [hbSeqPass_length, hb1SortedList_length]
  let z_rec2_pass := updateOn (eRec2 as n K d) z1
    (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K s2 hs2_len (fun _ _ => false)))
  let z_tr2a := updateOn (eTr2a as n K d) z_rec2_pass (rec2SortTr K l)
  let z_pass := updateOn (eRec3 as n K d) z_tr2a
    (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K s2 hs2_len (dPassOf K l dFn)))
  have hz4_eq : z4 = updateOn (eTr2b as n K d)
      (updateOn (eRec3 as n K d) z_pass
        (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
          (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn))))
      (rec3SortTr K l) := by
    dsimp only [z4, z3, z_pass, z_tr2a, z_rec2_pass, s2]
    rw [updateOn_comm (eRec3 as n K d) (eTr2b as n K d) (eRec3_disjoint_eTr2b as n K d),
      updateOn_idem, updateOn_idem]
  have h5_1 : act (sortHb2Circ as br n K d).adj.unitary (ket z4) = ket z_pass := by
    rw [hz4_eq]
    refine act_adj_ket _ (act_sortHb2Circ_with_d comb as br n K d h1K dFn z_pass ?_ ?_ ?_)
    · exact updateOn_comp_emb _ _ _
    · dsimp only [z_pass, z_tr2a, z_rec2_pass]
      rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_anc_other as n K d ⟨14, by decide⟩ (by decide))]
      rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨14, by decide⟩ (by decide))]
      rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨14, by decide⟩ (by decide))]
      exact hz1_anc_ge3 ⟨14, by decide⟩ (by decide)
    · dsimp only [z_pass, z_tr2a, z_rec2_pass]
      rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))]
      rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))]
      rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))]
      exact hz1_anc_ge3 ⟨18, by decide⟩ (by decide)
  rw [h5_1]
  -- 5.2: swapRec3ToRec2DCirc
  let z_rec3_zero := updateOn (eRec3 as n K d) z_tr2a_d
    (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K s2 hs2_len (fun _ _ => false)))
  have hzpass_rec2 : z_pass ∘ eRec2 as n K d =
      flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K s2 hs2_len (fun _ _ => false)) := by
    dsimp only [z_pass, z_tr2a, z_rec2_pass]
    rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_eRec2 as n K d),
      updateOn_comp_disjoint _ _ (eTr2a_disjoint_eRec2 as n K d),
      updateOn_comp_emb]
  have h5_2 : act (swapRec3ToRec2DCirc as arith n K d).unitary (ket z_pass) = ket z_rec3_zero := by
    rw [act_swapRec3ToRec2DCirc as arith n K d z_pass s2 hs2_len (dPassOf K l dFn)
      (updateOn_comp_emb _ _ _) hzpass_rec2]
    congr 1
    dsimp only [z_rec3_zero, z_tr2a_d, z_rec2_pass_d, z_pass, z_tr2a, z_rec2_pass]
    rw [updateOn_idem,
      updateOn_comm (eRec2 as n K d) (eRec3 as n K d) (eRec2_disjoint_eRec3 as n K d),
      updateOn_comm (eRec2 as n K d) (eTr2a as n K d) (eRec2_disjoint_eTr2a as n K d),
      updateOn_idem,
      updateOn_comm (eTr2a as n K d) (eRec2 as n K d) (eTr2a_disjoint_eRec2 as n K d),
      updateOn_comm (eRec3 as n K d) (eRec2 as n K d) (eRec3_disjoint_eRec2 as n K d)]
  rw [h5_2]
  -- 5.3: (copyToRec3Circ).adj
  have hztr2a_rec2 : z_tr2a_d ∘ eRec2 as n K d =
      flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K s2 hs2_len (dPassOf K l dFn)) := by
    dsimp only [z_tr2a_d, z_rec2_pass_d]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eRec2 as n K d), updateOn_comp_emb]
  have hztr2a_13 : z_tr2a_d ∘ ancEmb as n K d ⟨13, by decide⟩ = fun _ => false := by
    dsimp only [z_tr2a_d, z_rec2_pass_d]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨13, by decide⟩ (by decide)),
      updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨13, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨13, by decide⟩ (by decide)
  have hs2_kind : ∀ r ∈ s2, r.kind ≤ 3 := fun r hr => (hbSeqPass_hb1_bounds comb h1K l r hr).1
  exact act_adj_ket _ (routeB.act_copyToRec3Circ comb as arith n K d z_tr2a_d s2 hs2_len hs2_kind
    (dPassOf K l dFn) hztr2a_rec2 hztr2a_13)

private lemma act_unroute_54 (comb : LcgSym54Comb)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (routeA : HarmBucketRouteA54)
    (n K d : ℕ) (h1K : 1 ≤ K)
    {l : Fin (2 * K) → Fin (n + 1)} (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) :
    let aL := flatReg (2 * K) (sOf n) (fun p => particleSym54 n (sOf n) (l p))
    let z0 := padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append aL (fun _ => false))
    let z1 := updateOn (eOccReg as n K d)
      (updateOn (eActReg as n K d)
        (updateOn (eMReg as n K d) z0 (flatReg (2 * K) (wOf K) (mBitsFn K l)))
        (flatReg (2 * K) 1 (actBitsFn K l)))
      (flatReg (2 * K) (wOf K) (occBitsFn K l))
    let s1 := hb1SortedList K l
    let s2 := hbSeqPass s1
    let z_rec2_pass_d := updateOn (eRec2 as n K d) z1
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K s2 (by rw [hbSeqPass_length, hb1SortedList_length]) (dPassOf K l dFn)))
    let z_tr2a_d := updateOn (eTr2a as n K d) z_rec2_pass_d (rec2SortTr K l)
    let z_rec2_s1 := updateOn (eRec2 as n K d) z1
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K s1 (hb1SortedList_length K l) (dS1Of K l dFn)))
    let z_tr2a_s1 := updateOn (eTr2a as n K d) z_rec2_s1 (rec2SortTr K l)
    act (hbSeqPassCirc as arith n K d h1K).adj.unitary (ket z_tr2a_d) = ket z_tr2a_s1 := by
  intro aL z0 z1 s1 s2 z_rec2_pass_d z_tr2a_d z_rec2_s1 z_tr2a_s1
  have hz0_anc : ∀ k : Fin 24, z0 ∘ ancEmb as n K d k = fun _ => false := fun k => padZero_anc_comp as n K d _ k
  have hz1_anc_ge3 : ∀ k : Fin 24, 3 ≤ k.1 → z1 ∘ ancEmb as n K d k = fun _ => false := fun k hk => by
    have h0 : k ≠ ⟨0, by decide⟩ := fun h => by subst h; simp at hk
    have h1 : k ≠ ⟨1, by decide⟩ := fun h => by subst h; simp at hk
    have h2 : k ≠ ⟨2, by decide⟩ := fun h => by subst h; simp at hk
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_anc_other as n K d k h2)]
    rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_anc_other as n K d k h1)]
    rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_anc_other as n K d k h0)]
    exact hz0_anc k
  have hs1_len : s1.length = arity (dHbOf K + 1) := hb1SortedList_length K l
  have hs1_bnd : ∀ r ∈ s1, r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ (r.kind = 0 → r.dest = 0) ∧
      r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := fun r hr =>
    hbInit_bounds comb h1K l r ((hb1SortedList_mem_iff K l r).mp hr)
  have hztr_s1_rec2 : z_tr2a_s1 ∘ eRec2 as n K d =
      flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K s1 hs1_len (dS1Of K l dFn)) := by
    dsimp only [z_tr2a_s1, z_rec2_s1]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eRec2 as n K d), updateOn_comp_emb]
  have hztr_s1_19 : z_tr2a_s1 ∘ eSeqB as n K d = fun _ => false := by
    dsimp only [z_tr2a_s1, z_rec2_s1]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eSeqB as n K d),
      updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqB as n K d)]
    funext j; exact congrFun (hz1_anc_ge3 ⟨19, by decide⟩ (by decide)) _
  have hztr_s1_20 : z_tr2a_s1 ∘ eSeqCtrl as n K d = fun _ => false := by
    dsimp only [z_tr2a_s1, z_rec2_s1]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eSeqCtrl as n K d),
      updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqCtrl as n K d)]
    funext j; exact congrFun (hz1_anc_ge3 ⟨20, by decide⟩ (by decide)) _
  have hztr_s1_22 : z_tr2a_s1 ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
    dsimp only [z_tr2a_s1, z_rec2_s1]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide)),
      updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨22, by decide⟩ (by decide)
  have hfwd_pass : act (hbSeqPassCirc as arith n K d h1K).unitary (ket z_tr2a_s1) = ket z_tr2a_d := by
    rw [routeA.act_hbSeqPassCirc comb as arith n K d h1K z_tr2a_s1 s1 hs1_len hs1_bnd
      (dS1Of K l dFn) hztr_s1_rec2 hztr_s1_19 hztr_s1_20 hztr_s1_22]
    congr 1
    dsimp only [z_tr2a_d, z_rec2_pass_d, z_tr2a_s1, z_rec2_s1, s2, s1]
    rw [updateOn_comm (eRec2 as n K d) (eTr2a as n K d) (eRec2_disjoint_eTr2a as n K d),
      updateOn_idem, dPassOf_eq_dS1Of K l dFn]
  exact act_adj_ket _ hfwd_pass

private lemma act_unroute_55 (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54)
    (n K d : ℕ) (h1K : 1 ≤ K)
    {l : Fin (2 * K) → Fin (n + 1)} (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) :
    let aL := flatReg (2 * K) (sOf n) (fun p => particleSym54 n (sOf n) (l p))
    let z0 := padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append aL (fun _ => false))
    let z1 := updateOn (eOccReg as n K d)
      (updateOn (eActReg as n K d)
        (updateOn (eMReg as n K d) z0 (flatReg (2 * K) (wOf K) (mBitsFn K l)))
        (flatReg (2 * K) 1 (actBitsFn K l)))
      (flatReg (2 * K) (wOf K) (occBitsFn K l))
    let s1 := hb1SortedList K l
    let z_rec2_s1 := updateOn (eRec2 as n K d) z1
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K s1 (hb1SortedList_length K l) (dS1Of K l dFn)))
    let z_tr2a_s1 := updateOn (eTr2a as n K d) z_rec2_s1 (rec2SortTr K l)
    let L0 := hbInit (2 * K) (arity (dHbOf K)) l
    let z_rec2_init_d := updateOn (eRec2 as n K d) z1
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K L0 (by rw [hbInit_length, arity_succ_eq]) (dInitOf K l dFn)))
    act (sortHb1Circ as br n K d).adj.unitary (ket z_tr2a_s1) = ket z_rec2_init_d := by
  intro aL z0 z1 s1 z_rec2_s1 z_tr2a_s1 L0 z_rec2_init_d
  have hz0_anc : ∀ k : Fin 24, z0 ∘ ancEmb as n K d k = fun _ => false := fun k => padZero_anc_comp as n K d _ k
  have hz1_anc_ge3 : ∀ k : Fin 24, 3 ≤ k.1 → z1 ∘ ancEmb as n K d k = fun _ => false := fun k hk => by
    have h0 : k ≠ ⟨0, by decide⟩ := fun h => by subst h; simp at hk
    have h1 : k ≠ ⟨1, by decide⟩ := fun h => by subst h; simp at hk
    have h2 : k ≠ ⟨2, by decide⟩ := fun h => by subst h; simp at hk
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_anc_other as n K d k h2)]
    rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_anc_other as n K d k h1)]
    rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_anc_other as n K d k h0)]
    exact hz0_anc k
  have hzinit_12 : z_rec2_init_d ∘ ancEmb as n K d ⟨12, by decide⟩ = fun _ => false := by
    dsimp only [z_rec2_init_d]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨12, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨12, by decide⟩ (by decide)
  have hzinit_17 : z_rec2_init_d ∘ ancEmb as n K d ⟨17, by decide⟩ = fun _ => false := by
    dsimp only [z_rec2_init_d]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨17, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨17, by decide⟩ (by decide)
  have hfwd_sort1 : act (sortHb1Circ as br n K d).unitary (ket z_rec2_init_d) = ket z_tr2a_s1 := by
    rw [act_sortHb1Circ_with_d comb as br n K d h1K dFn z_rec2_init_d
      (updateOn_comp_emb _ _ _) hzinit_12 hzinit_17]
    congr 1; dsimp only [z_tr2a_s1, z_rec2_s1, z_rec2_init_d, s1]
    rw [updateOn_idem]
  exact act_adj_ket _ hfwd_sort1

private lemma act_unroute_partB (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (routeA : HarmBucketRouteA54)
    (n K d : ℕ) (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d)
    {l : Fin (2 * K) → Fin (n + 1)} (hl : Monotone l) (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) :
    let aL := flatReg (2 * K) (sOf n) (fun p => particleSym54 n (sOf n) (l p))
    let z0 := padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append aL (fun _ => false))
    let z1 := updateOn (eOccReg as n K d)
      (updateOn (eActReg as n K d)
        (updateOn (eMReg as n K d) z0 (flatReg (2 * K) (wOf K) (mBitsFn K l)))
        (flatReg (2 * K) 1 (actBitsFn K l)))
      (flatReg (2 * K) (wOf K) (occBitsFn K l))
    let L0 := hbInit (2 * K) (arity (dHbOf K)) l
    let z_rec2_init_d := updateOn (eRec2 as n K d) z1
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K L0 (by rw [hbInit_length, arity_succ_eq]) (dInitOf K l dFn)))
    let sFn := (isLESOfEquivPiFinOf (2 * K) l (comb.runStart_le hl)).symm dFn
    act (step12Circ as arith br n K d h1K).adj.unitary
      (act (subAndUncomputeDCirc as arith n K d h1K hNM).unitary
        (act (hbInitCirc as arith n K d).adj.unitary
          (act (swapRec2ToDCirc as arith n K d h1K).unitary (ket z_rec2_init_d)))) =
      ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
        (Fin.append aL (flatReg (arity d) d (padZeroLESBits (2 * K) d sFn.1)))) := by
  intro aL z0 z1 L0 z_rec2_init_d sFn
  have hz0_L : z0 ∘ eL as n K d = aL := padZero_eL_comp as n K d aL _
  have hz0_Out : z0 ∘ eOut as n K d = fun _ => false := padZero_eOut_comp as n K d aL _
  have hz0_anc : ∀ k : Fin 24, z0 ∘ ancEmb as n K d k = fun _ => false := fun k => padZero_anc_comp as n K d _ k
  have hz1_anc_ge3 : ∀ k : Fin 24, 3 ≤ k.1 → z1 ∘ ancEmb as n K d k = fun _ => false := fun k hk => by
    have h0 : k ≠ ⟨0, by decide⟩ := fun h => by subst h; simp at hk
    have h1 : k ≠ ⟨1, by decide⟩ := fun h => by subst h; simp at hk
    have h2 : k ≠ ⟨2, by decide⟩ := fun h => by subst h; simp at hk
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_anc_other as n K d k h2)]
    rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_anc_other as n K d k h1)]
    rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_anc_other as n K d k h0)]
    exact hz0_anc k
  have hz1_Out : z1 ∘ eOut as n K d = fun _ => false := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_eOut as n K d)]
    rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_eOut as n K d)]
    rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_eOut as n K d)]
    exact hz0_Out
  have hz1_M : z1 ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_eMReg as n K d)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eMReg_disjoint_eActReg as n K d b a h.symm)]
    exact updateOn_comp_emb _ _ _
  have hz1_A : z1 ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_eActReg as n K d)]
    exact updateOn_comp_emb _ _ _
  have hz1_O : z1 ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l) := updateOn_comp_emb _ _ _
  -- 5.6: swapRec2ToDCirc
  let d_bits : Fin (2 * K) → Qubits (wOf K) := fun i => natToBits (wOf K) (dFn i).1
  let z_d := updateOn (eDReg as n K d) z1 (flatReg (2 * K) (wOf K) d_bits)
  let z_d_rec2 := updateOn (eRec2 as n K d) z_d (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l))
  have hzinit_15 : z_rec2_init_d ∘ ancEmb as n K d ⟨15, by decide⟩ = fun _ => false := by
    dsimp only [z_rec2_init_d]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨15, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨15, by decide⟩ (by decide)
  have h5_6 : act (swapRec2ToDCirc as arith n K d h1K).unitary (ket z_rec2_init_d) = ket z_d_rec2 := by
    rw [act_swapRec2ToDCirc comb as arith n K d h1K dFn z_rec2_init_d (updateOn_comp_emb _ _ _) hzinit_15]
    congr 1
    dsimp only [z_d_rec2, z_d, z_rec2_init_d]
    rw [updateOn_idem, updateOn_comm (eDReg as n K d) (eRec2 as n K d) (fun a b h => eRec2_disjoint_eDReg as n K d b a h.symm)]
  rw [h5_6]
  -- 5.7: (hbInitCirc).adj
  have hzd_A : z_d ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) := by
    dsimp only [z_d]
    rw [updateOn_comp_disjoint _ _ (eDReg_disjoint_eActReg as n K d)]
    exact hz1_A
  have hzd_M : z_d ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) := by
    dsimp only [z_d]
    rw [updateOn_comp_disjoint _ _ (eDReg_disjoint_eMReg as n K d)]
    exact hz1_M
  have hzd_O : z_d ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l) := by
    dsimp only [z_d]
    rw [updateOn_comp_disjoint _ _ (eDReg_disjoint_eOccReg as n K d)]
    exact hz1_O
  have hzd_11 : z_d ∘ ancEmb as n K d ⟨11, by decide⟩ = fun _ => false := by
    dsimp only [z_d]
    rw [updateOn_comp_disjoint _ _ (eDReg_disjoint_anc_other as n K d ⟨11, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨11, by decide⟩ (by decide)
  have h5_7 : act (hbInitCirc as arith n K d).adj.unitary (ket z_d_rec2) = ket z_d :=
    act_adj_ket _ (routeA.act_hbInitCirc comb as arith n K d z_d hzd_A hzd_M hzd_O hzd_11)
  rw [h5_7]
  -- 5.8: subAndUncomputeDCirc
  let z_out_z1 := updateOn (eOut as n K d) z1 (flatReg (arity d) d (padZeroLESBits (2 * K) d sFn.1))
  have hzd_16 : z_d ∘ eSubTmp as n K d = fun _ => false := by
    dsimp only [z_d]
    rw [updateOn_comp_disjoint _ _ (eDReg_disjoint_eSubTmp as n K d)]
    funext j; exact congrFun (hz1_anc_ge3 ⟨16, by decide⟩ (by decide)) _
  have hzd_Out : z_d ∘ eOut as n K d = fun _ => false := by
    dsimp only [z_d]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eOut_disjoint_eDReg as n K d b a h.symm)]
    exact hz1_Out
  have hzd_22 : z_d ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
    dsimp only [z_d]
    rw [updateOn_comp_disjoint _ _ (eDReg_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨22, by decide⟩ (by decide)
  have h5_8 : act (subAndUncomputeDCirc as arith n K d h1K hNM).unitary (ket z_d) = ket z_out_z1 := by
    rw [act_subAndUncomputeDCirc comb as arith n K d h1K hNM hl dFn z_d (updateOn_comp_emb _ _ _) hzd_16 hzd_Out hzd_22]
    congr 1; dsimp only [z_out_z1, z_d]
    rw [updateOn_idem,
      updateOn_noop (eDReg as n K d) z1 (fun _ => false) (funext fun j => congrFun (hz1_anc_ge3 ⟨15, by decide⟩ (by decide)) _)]
  rw [h5_8]
  -- 5.9: (step12Circ).adj
  let z_out_z0 := updateOn (eOut as n K d) z0 (flatReg (arity d) d (padZeroLESBits (2 * K) d sFn.1))
  have hzout_L : z_out_z0 ∘ eL as n K d = flatReg (2 * K) (sOf n) (fun p => particleSym54 n (sOf n) (l p)) := by
    dsimp only [z_out_z0]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eL_disjoint_eOut as n K d b a h.symm)]
    exact hz0_L
  have hzout_anc : ∀ k : Fin 24, k.1 ≤ 10 → z_out_z0 ∘ ancEmb as n K d k = fun _ => false := fun k _ => by
    dsimp only [z_out_z0]
    rw [updateOn_comp_disjoint _ _ (eOut_disjoint_anc as n K d k)]
    exact hz0_anc k
  have hfwd_12 : act (step12Circ as arith br n K d h1K).unitary (ket z_out_z0) = ket z_out_z1 := by
    rw [occ.act_step12Circ comb as arith br n K d h1K l hl z_out_z0 hzout_L hzout_anc]
    congr 1; dsimp only [z_out_z1, z_out_z0, z1]
    rw [updateOn_comm (eMReg as n K d) (eOut as n K d) (eMReg_disjoint_eOut as n K d),
      updateOn_comm (eActReg as n K d) (eOut as n K d) (eActReg_disjoint_eOut as n K d),
      updateOn_comm (eOccReg as n K d) (eOut as n K d) (eOccReg_disjoint_eOut as n K d)]
  have h5_9 : act (step12Circ as arith br n K d h1K).adj.unitary (ket z_out_z1) = ket z_out_z0 :=
    act_adj_ket _ hfwd_12
  rw [h5_9]
  dsimp only [z_out_z0, z0]
  rw [updateOn_eOut_padZero]

lemma act_unrouteAndSubCirc_single (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (routeA : HarmBucketRouteA54)
    (routeB : HarmBucketRouteB54) (n K d : ℕ) (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d)
    {l : Fin (2 * K) → Fin (n + 1)} (hl : Monotone l) (dFn : (i : Fin (2 * K)) → Fin (runOffset l i)) :
    let aL := flatReg (2 * K) (sOf n) (fun p => particleSym54 n (sOf n) (l p))
    let z0 := padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append aL (fun _ => false))
    let z1 := updateOn (eOccReg as n K d)
      (updateOn (eActReg as n K d)
        (updateOn (eMReg as n K d) z0 (flatReg (2 * K) (wOf K) (mBitsFn K l)))
        (flatReg (2 * K) 1 (actBitsFn K l)))
      (flatReg (2 * K) (wOf K) (occBitsFn K l))
    let z3 := updateOn (eTr2b as n K d)
      (updateOn (eRec3 as n K d)
        (updateOn (eTr2a as n K d)
          (updateOn (eRec2 as n K d) z1
            (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
              (hb1ArrOfList K (hbSeqPass (hb1SortedList K l))
                (by rw [hbSeqPass_length, hb1SortedList_length]) (fun _ _ => false))))
          (rec2SortTr K l))
        (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3SortedArr K l)))
      (rec3SortTr K l)
    let z4 := updateOn (eRec3 as n K d) z3 (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn)))
    let sFn := (isLESOfEquivPiFinOf (2 * K) l (comb.runStart_le hl)).symm dFn
    act (unrouteAndSubCirc occ comb br as arith n K d h1K hNM).unitary (ket z4) =
      ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
        (Fin.append aL (flatReg (arity d) d (padZeroLESBits (2 * K) d sFn.1)))) := by
  intro aL z0 z1 z3 z4 sFn
  dsimp only [unrouteAndSubCirc]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  rw [act_unroute_51_53 comb br as arith routeB n K d h1K dFn,
    act_unroute_54 comb as arith routeA n K d h1K dFn,
    act_unroute_55 comb br as n K d h1K dFn]
  exact act_unroute_partB occ comb br as arith routeA n K d h1K hNM hl dFn

def asPermCirc (as : AlonsoSchottSil54) (n K d : ℕ) (h1K : 1 ≤ K) (h1d : 1 ≤ d) (hNM : 2 * K ≤ arity d) :
    LayeredCircuit (totWiresDef as n K d) :=
  (as.alonsoSchottCircuit (2 * K) d (by omega) h1d hNM).mapWires
    (combineEmb (eOut as n K d) (eAsAnc as n K d) (eOut_disjoint_eAsAnc as n K d))

lemma asPermCirc_size (as : AlonsoSchottSil54) (n K d : ℕ) (h1K : 1 ≤ K) (h1d : 1 ≤ d) (hNM : 2 * K ≤ arity d) :
    ((asPermCirc as n K d h1K h1d hNM).size : ℝ) ≤
      as.C_as * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by
  dsimp [asPermCirc]
  rw [LayeredCircuit.mapWires_size]
  exact as.alonsoSchottCircuit_size (2 * K) d (by omega) h1d hNM

private lemma updateOn_combine_eOut_eAsAnc_padZero (as : AlonsoSchottSil54) (n K d : ℕ)
    (a : Qubits (2 * K * sOf n)) (b₀ b₁ : Qubits (arity d * d)) :
    updateOn (combineEmb (eOut as n K d) (eAsAnc as n K d) (eOut_disjoint_eAsAnc as n K d))
        (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append a b₀))
        (padZero (arity d * d) (as.alonsoSchottAnc (2 * K) d) b₁) =
      padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append a b₁) := by
  rw [← updateOn_eOut_padZero as n K d a b₀ b₁]
  funext u
  by_cases huOut : u ∈ Set.range (eOut as n K d)
  · rcases huOut with ⟨j, rfl⟩
    have hmem : eOut as n K d j = combineEmb (eOut as n K d) (eAsAnc as n K d) (eOut_disjoint_eAsAnc as n K d)
        (Fin.castAdd (as.alonsoSchottAnc (2 * K) d) j) := by simp
    conv_lhs => rw [hmem, updateOn_apply_emb]
    rw [padZero_castAdd, updateOn_apply_emb]
  · rw [updateOn_apply_not_mem _ _ _ huOut]
    by_cases huAnc : u ∈ Set.range (eAsAnc as n K d)
    · rcases huAnc with ⟨k, rfl⟩
      have hmem : eAsAnc as n K d k = combineEmb (eOut as n K d) (eAsAnc as n K d) (eOut_disjoint_eAsAnc as n K d)
          (Fin.natAdd (arity d * d) k) := by simp
      conv_lhs => rw [hmem, updateOn_apply_emb]
      rw [padZero_natAdd]
      exact (congrFun (padZero_eAsAnc_comp as n K d (Fin.append a b₀)) k).symm
    · have hnot : u ∉ Set.range (combineEmb (eOut as n K d) (eAsAnc as n K d) (eOut_disjoint_eAsAnc as n K d)) := by
        rintro ⟨ij, rfl⟩
        induction ij using Fin.addCases with
        | left j => apply huOut; exact ⟨j, by simp⟩
        | right k => apply huAnc; exact ⟨k, by simp⟩
      rw [updateOn_apply_not_mem _ _ _ hnot]

lemma act_asPermCirc_single (as : AlonsoSchottSil54) (n K d : ℕ) (h1K : 1 ≤ K) (h1d : 1 ≤ d)
    (hNM : 2 * K ≤ arity d) (a : Qubits (2 * K * sOf n)) (σ : Equiv.Perm (Fin (2 * K))) :
    act (asPermCirc as n K d h1K h1d hNM).unitary
        (ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
          (Fin.append a (flatReg (arity d) d (padZeroLESBits (2 * K) d (permToLES (2 * K) σ)))))) =
      ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
        (Fin.append a (flatReg (arity d) d (permRegBits (2 * K) d hNM σ⁻¹)))) := by
  let z := padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
    (Fin.append a (flatReg (arity d) d (padZeroLESBits (2 * K) d (permToLES (2 * K) σ))))
  let emb := combineEmb (eOut as n K d) (eAsAnc as n K d) (eOut_disjoint_eAsAnc as n K d)
  have hz_comp : z ∘ emb = padZero (arity d * d) (as.alonsoSchottAnc (2 * K) d)
      (flatReg (arity d) d (padZeroLESBits (2 * K) d (permToLES (2 * K) σ))) := by
    funext ij
    induction ij using Fin.addCases with
    | left j =>
      change z (emb (Fin.castAdd _ j)) = _
      rw [combineEmb_castAdd, padZero_castAdd]
      exact congrFun (padZero_eOut_comp as n K d a _) j
    | right k =>
      change z (emb (Fin.natAdd _ k)) = _
      rw [combineEmb_natAdd, padZero_natAdd]
      exact congrFun (padZero_eAsAnc_comp as n K d _) k
  dsimp only [asPermCirc]
  have hact := act_mapWires_ket_singleton (as.alonsoSchottCircuit (2 * K) d (by omega) h1d hNM) emb z
    (padZero (arity d * d) (as.alonsoSchottAnc (2 * K) d) (flatReg (arity d) d (permRegBits (2 * K) d hNM σ⁻¹)))
    (by rw [hz_comp]; exact as.act_alonsoSchottCircuit (2 * K) d (by omega) h1d hNM σ)
  rw [hact]
  congr 1
  exact updateOn_combine_eOut_eAsAnc_padZero as n K d a _ _

noncomputable def isLESOfEquivStabGroup (comb : LcgSym54Comb) {n K : ℕ}
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l) :
    { s : Fin (2 * K) → ℕ // IsLESOf (2 * K) l s } ≃ stabGroup (2 * K) l where
  toFun s :=
    ⟨comb.lesToPerm (2 * K) s.1 (fun j => (s.2 j).2),
     (comb.mem_stabGroup_iff_isLESOf (2 * K) l hl s.1 (fun j => (s.2 j).2)).mpr s.2⟩
  invFun h :=
    ⟨permToLES (2 * K) h.1,
     (comb.mem_stabGroup_iff_isLESOf (2 * K) l hl (permToLES (2 * K) h.1)
       (comb.permToLES_isLES (2 * K) h.1)).mp (by
         have hsub : (⟨permToLES (2 * K) h.1, comb.permToLES_isLES (2 * K) h.1⟩ :
             { s : Fin (2 * K) → ℕ // IsLES (2 * K) s }) = (comb.lesEquivPerm (2 * K)).symm h.1 :=
           Subtype.ext (comb.lesEquivPerm_symm_apply (2 * K) h.1).symm
         have heq : comb.lesToPerm (2 * K) (permToLES (2 * K) h.1) (comb.permToLES_isLES (2 * K) h.1) = h.1 := by
           rw [comb.lesToPerm_eq, hsub, (comb.lesEquivPerm (2 * K)).apply_symm_apply]
         rw [heq]; exact h.2)⟩
  left_inv s := Subtype.ext (comb.permToLES_lesToPerm (2 * K) s.1 (fun j => (s.2 j).2))
  right_inv h := Subtype.ext (by
    dsimp only
    have hsub : (⟨permToLES (2 * K) h.1, comb.permToLES_isLES (2 * K) h.1⟩ :
        { s : Fin (2 * K) → ℕ // IsLES (2 * K) s }) = (comb.lesEquivPerm (2 * K)).symm h.1 :=
      Subtype.ext (comb.lesEquivPerm_symm_apply (2 * K) h.1).symm
    have hpi : ∀ hs : IsLES (2 * K) (permToLES (2 * K) h.1),
        comb.lesToPerm (2 * K) (permToLES (2 * K) h.1) hs = h.1 := fun hs => by
      have heq : comb.lesToPerm (2 * K) (permToLES (2 * K) h.1) hs =
          comb.lesToPerm (2 * K) (permToLES (2 * K) h.1) (comb.permToLES_isLES (2 * K) h.1) := rfl
      rw [heq, comb.lesToPerm_eq, hsub, (comb.lesEquivPerm (2 * K)).apply_symm_apply]
    exact hpi _)

/-! #### 9.6 Full `HarmBucketHL54V2` Assembly & `K_hl := 4` Gate Bound -/

def harmBucketH_lCircuitDef (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (_h1n : 1 ≤ n) (h1K : 1 ≤ K) (h1d : 1 ≤ d) (hNM : 2 * K ≤ arity d) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList [
    step12Circ as arith br n K d h1K,
    step3Circ as br arith n K d h1K,
    unifBucketsCirc comb br as arith n K d h1K,
    unrouteAndSubCirc occ comb br as arith n K d h1K hNM,
    asPermCirc as n K d h1K h1d hNM
  ]

private lemma step12_rhs_le_KL4 (br : BitonicRouting54) {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    ((wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) : ℝ) +
      2 * ((arity (dOccOf K) * (2 * wOf K + 2) : ℕ) : ℝ) +
      2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) +
      (((2 * K - 1) * (49 * wOf K + 236) : ℕ) : ℝ) +
      (((2 * K) * (3 * wOf K) : ℕ) : ℝ) ≤
      (811 + 352 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 := by
  have h4L : 4 ≤ lOf n K := four_le_lOf h1n h1K
  have hs_L : sOf n ≤ lOf n K := sOf_le_lOf
  have hdOcc_L : dOccOf K ≤ lOf n K := dOcc_le_lOf h1n h1K
  have harOcc : arity (dOccOf K) ≤ 4 * K := le_of_lt (arity_dOcc_lt_four_K h1K)
  have hw_L : wOf K ≤ 2 * lOf n K + 2 := wOf_le h1n h1K
  have hCs := br.hC_sort_pos
  have ha : ((wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) : ℝ) ≤
      325 * (K : ℝ) * (lOf n K : ℝ) := by
    have hn : wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) ≤ 325 * K * lOf n K := by
      have hw3 : wOf K ≤ 3 * lOf n K := by omega
      have hk1 : wOf K ≤ 3 * K * lOf n K := by nlinarith
      have hk2 : 2 * K - 1 ≤ 2 * K := Nat.sub_le _ _
      have hk3 : 28 * sOf n + 42 * wOf K + 28 ≤ 28 * lOf n K + 126 * lOf n K + 7 * lOf n K := by omega
      have hring : 3 * K * lOf n K + 2 * K * (28 * lOf n K + 126 * lOf n K + 7 * lOf n K) =
          325 * K * lOf n K := by ring
      rw [← hring]
      exact Nat.add_le_add hk1 (Nat.mul_le_mul hk2 hk3)
    exact_mod_cast hn
  have hb : (2 * ((arity (dOccOf K) * (2 * wOf K + 2) : ℕ) : ℝ)) ≤
      56 * (K : ℝ) * (lOf n K : ℝ) := by
    have hnb : 2 * (arity (dOccOf K) * (2 * wOf K + 2)) ≤ 56 * K * lOf n K := by
      have hw7 : 2 * wOf K + 2 ≤ 7 * lOf n K := by omega
      have hring : 2 * (4 * K * (7 * lOf n K)) = 56 * K * lOf n K := by ring
      rw [← hring]
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul harOcc hw7)
    exact_mod_cast hnb
  have hc : 2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) ≤
      352 * br.C_sort * (K : ℝ) * (lOf n K : ℝ) ^ 3 := by
    have h2d : (2 ^ (dOccOf K) : ℝ) ≤ 4 * (K : ℝ) := by
      have : 2 ^ dOccOf K ≤ 4 * K := by simpa [arity_eq_two_pow] using harOcc
      exact_mod_cast this
    have hd1 : ((dOccOf K : ℝ) + 1) ^ 2 ≤ (2 * (lOf n K : ℝ)) ^ 2 := by
      have hnat : dOccOf K + 1 ≤ 2 * lOf n K := by omega
      have hcast : (dOccOf K : ℝ) + 1 ≤ 2 * (lOf n K : ℝ) := by exact_mod_cast hnat
      exact pow_le_pow_left₀ (by positivity) hcast 2
    have hwr1 : (wR1Occ K : ℝ) + 1 ≤ 11 * (lOf n K : ℝ) := by
      have : wR1Occ K + 1 ≤ 11 * lOf n K := by dsimp [wR1Occ, wK1Occ, wP1Occ]; omega
      exact_mod_cast this
    have hmul : (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1) ≤
        (4 * (K : ℝ)) * ((2 * (lOf n K : ℝ)) ^ 2) * (11 * (lOf n K : ℝ)) :=
      mul_le_mul (mul_le_mul h2d hd1 (by positivity) (by positivity)) hwr1 (by positivity) (by positivity)
    have hring : (4 * (K : ℝ)) * ((2 * (lOf n K : ℝ)) ^ 2) * (11 * (lOf n K : ℝ)) =
        176 * (K : ℝ) * (lOf n K : ℝ) ^ 3 := by ring
    have h176 : (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1) ≤
        176 * (K : ℝ) * (lOf n K : ℝ) ^ 3 := hmul.trans_eq hring
    nlinarith [mul_le_mul_of_nonneg_left h176 (by positivity : 0 ≤ 2 * br.C_sort)]
  have hd_bnd : (((2 * K - 1) * (49 * wOf K + 236) : ℕ) : ℝ) +
      (((2 * K) * (3 * wOf K) : ℕ) : ℝ) ≤ 430 * (K : ℝ) * (lOf n K : ℝ) := by
    have hnd : (2 * K - 1) * (49 * wOf K + 236) + (2 * K) * (3 * wOf K) ≤ 430 * K * lOf n K := by
      have hw1 : 49 * wOf K + 236 ≤ 147 * lOf n K + 59 * lOf n K := by omega
      have hw2 : 3 * wOf K ≤ 9 * lOf n K := by omega
      have hk2 : 2 * K - 1 ≤ 2 * K := Nat.sub_le _ _
      have hring : (2 * K) * (147 * lOf n K + 59 * lOf n K) + (2 * K) * (9 * lOf n K) =
          430 * K * lOf n K := by ring
      rw [← hring]
      exact Nat.add_le_add (Nat.mul_le_mul hk2 hw1) (Nat.mul_le_mul_left _ hw2)
    exact_mod_cast hnd
  have hLr4 : (4 : ℝ) ≤ (lOf n K : ℝ) := by exact_mod_cast h4L
  have hKr1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1K
  have hL1 : (1 : ℝ) ≤ (lOf n K : ℝ) := by linarith
  have hL12 : (lOf n K : ℝ) ≤ (lOf n K : ℝ) ^ 2 := by nlinarith
  have hL23 : (lOf n K : ℝ) ^ 2 ≤ (lOf n K : ℝ) ^ 3 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hL34 : (lOf n K : ℝ) ^ 3 ≤ (lOf n K : ℝ) ^ 4 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hKL_le : (K : ℝ) * (lOf n K : ℝ) ≤ (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left (hL12.trans (hL23.trans hL34)) (by positivity)
  have hKL3_le : (K : ℝ) * (lOf n K : ℝ) ^ 3 ≤ (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left hL34 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hKL_le (by norm_num : (0 : ℝ) ≤ 811),
    mul_le_mul_of_nonneg_left hKL3_le (by positivity : 0 ≤ 352 * br.C_sort)]

private lemma unroute_hb_nat_le {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    arity (dHbOf K + 1) * (3 * wOf K) + arity (dHbOf K + 1) * (2 * wOf K + 3) +
      (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) + (2 * K) * (3 * wOf K) +
      arity (dHbOf K + 1) * (11 * wOf K + 12) + (2 * K) * (32 * wOf K) ≤
      3360 * (K * lOf n K ^ 2) := by
  have h4L : 4 ≤ lOf n K := four_le_lOf h1n h1K
  have hw_L : wOf K ≤ 2 * lOf n K + 2 := wOf_le h1n h1K
  have hB2_le : arity (dHbOf K) ≤ 5 * K * lOf n K := by have := B2_le h1n h1K; nlinarith
  have harHb : arity (dHbOf K + 1) ≤ 10 * K * lOf n K := by
    have hring : 2 * (5 * K * lOf n K) = 10 * K * lOf n K := by ring
    rw [arity_succ_eq, ← hring]; exact Nat.mul_le_mul_left 2 hB2_le
  have h1a : arity (dHbOf K + 1) * (3 * wOf K) + arity (dHbOf K + 1) * (2 * wOf K + 3) +
      (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) + arity (dHbOf K + 1) * (11 * wOf K + 12) ≤
      3150 * (K * lOf n K ^ 2) := by
    have hsub : arity (dHbOf K + 1) - 1 ≤ arity (dHbOf K + 1) := Nat.sub_le _ _
    have h1a_1 : (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) ≤
        arity (dHbOf K + 1) * (61 * wOf K + 321) := Nat.mul_le_mul_right _ hsub
    have h1a_2 : arity (dHbOf K + 1) * (3 * wOf K) + arity (dHbOf K + 1) * (2 * wOf K + 3) +
        arity (dHbOf K + 1) * (61 * wOf K + 321) + arity (dHbOf K + 1) * (11 * wOf K + 12) =
        arity (dHbOf K + 1) * (77 * wOf K + 336) := by ring
    have hle : arity (dHbOf K + 1) * (77 * wOf K + 336) ≤
        (10 * K * lOf n K) * (315 * lOf n K) := Nat.mul_le_mul harHb (by omega)
    have hring : (10 * K * lOf n K) * (315 * lOf n K) = 3150 * (K * lOf n K ^ 2) := by ring
    have h1a' : arity (dHbOf K + 1) * (3 * wOf K) + arity (dHbOf K + 1) * (2 * wOf K + 3) +
        (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) + arity (dHbOf K + 1) * (11 * wOf K + 12) ≤
        arity (dHbOf K + 1) * (77 * wOf K + 336) := by omega
    exact le_trans h1a' (hle.trans_eq hring)
  have h2 : (2 * K) * (3 * wOf K) + (2 * K) * (32 * wOf K) ≤ 210 * (K * lOf n K ^ 2) := by
    have h2a : (2 * K) * (3 * wOf K) + (2 * K) * (32 * wOf K) = (2 * K) * (35 * wOf K) := by ring
    have h2b : (2 * K) * (35 * wOf K) ≤ (2 * K) * (105 * lOf n K) := Nat.mul_le_mul_left _ (by omega)
    have h2c : (2 * K) * (105 * lOf n K) = 210 * (K * lOf n K) := by ring
    have hl : lOf n K ≤ lOf n K ^ 2 := by
      rw [sq]; exact Nat.le_mul_of_pos_right (lOf n K) (by omega)
    have h2d : 210 * (K * lOf n K) ≤ 210 * (K * lOf n K ^ 2) :=
      Nat.mul_le_mul_left 210 (Nat.mul_le_mul_left K hl)
    have h2ab : (2 * K) * (3 * wOf K) + (2 * K) * (32 * wOf K) ≤ 210 * (K * lOf n K) := by
      rw [h2a]; exact h2b.trans_eq h2c
    exact h2ab.trans h2d
  have hsw : arity (dHbOf K + 1) * (3 * wOf K) + arity (dHbOf K + 1) * (2 * wOf K + 3) +
      (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) + (2 * K) * (3 * wOf K) +
      arity (dHbOf K + 1) * (11 * wOf K + 12) + (2 * K) * (32 * wOf K) =
      (arity (dHbOf K + 1) * (3 * wOf K) + arity (dHbOf K + 1) * (2 * wOf K + 3) +
      (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) + arity (dHbOf K + 1) * (11 * wOf K + 12)) +
      ((2 * K) * (3 * wOf K) + (2 * K) * (32 * wOf K)) := by ring
  omega

private lemma sortHb_term_le_KL4 (br : BitonicRouting54) {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    (arity (dHbOf K + 1) : ℝ) *
        (br.C_sort * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2)) ≤
      2070 * br.C_sort * (K : ℝ) * (lOf n K : ℝ) ^ 4 := by
  have h4L : 4 ≤ lOf n K := four_le_lOf h1n h1K
  have hB2_le : arity (dHbOf K) ≤ 5 * K * lOf n K := by have := B2_le h1n h1K; nlinarith
  have harHb : arity (dHbOf K + 1) ≤ 10 * K * lOf n K := by
    have hring : 2 * (5 * K * lOf n K) = 10 * K * lOf n K := by ring
    rw [arity_succ_eq, ← hring]; exact Nat.mul_le_mul_left 2 hB2_le
  have hdHb_L : dHbOf K ≤ 2 * lOf n K := dHb_le_two_mul_lOf h1n h1K
  have hw_L : wOf K ≤ 2 * lOf n K + 2 := wOf_le h1n h1K
  have hCs := br.hC_sort_pos
  have har' : (arity (dHbOf K + 1) : ℝ) ≤ 10 * (K : ℝ) * (lOf n K : ℝ) := by exact_mod_cast harHb
  have hd' : (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ (3 * (lOf n K : ℝ)) ^ 2 := by
    have hnat : dHbOf K + 1 + 1 ≤ 3 * lOf n K := by omega
    have hle : ((dHbOf K + 1 : ℕ) : ℝ) + 1 ≤ 3 * (lOf n K : ℝ) := by exact_mod_cast hnat
    exact pow_le_pow_left₀ (by positivity) hle 2
  have hw' : (wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2 ≤ 23 * (lOf n K : ℝ) := by
    have : wR1Hb K + wR2Hb K + 2 ≤ 23 * lOf n K := by
      dsimp [wR1Hb, wK1Hb, wP1Hb, wR2Hb, wK2Hb, wP2Hb]; omega
    exact_mod_cast this
  have hmul : (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2) ≤
      (3 * (lOf n K : ℝ)) ^ 2 * (23 * (lOf n K : ℝ)) :=
    mul_le_mul hd' hw' (by positivity) (by positivity)
  have hmul2 : (arity (dHbOf K + 1) : ℝ) *
      (br.C_sort * ((((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2))) ≤
      (10 * (K : ℝ) * (lOf n K : ℝ)) * (br.C_sort * ((3 * (lOf n K : ℝ)) ^ 2 * (23 * (lOf n K : ℝ)))) :=
    mul_le_mul har' (mul_le_mul_of_nonneg_left hmul (by positivity)) (by positivity) (by positivity)
  have hring : (10 * (K : ℝ) * (lOf n K : ℝ)) * (br.C_sort * ((3 * (lOf n K : ℝ)) ^ 2 * (23 * (lOf n K : ℝ)))) =
      2070 * br.C_sort * (K : ℝ) * (lOf n K : ℝ) ^ 4 := by ring
  have hmul2' : (arity (dHbOf K + 1) : ℝ) *
      (br.C_sort * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2)) =
      (arity (dHbOf K + 1) : ℝ) *
      (br.C_sort * ((((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2))) := by ring
  rw [hmul2']
  exact hmul2.trans_eq hring

private lemma step3_size_le_KL4 (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (routeB : HarmBucketRouteB54) {n K d : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    ((step3Circ as br arith n K d h1K).size : ℝ) ≤
      (3060 + 2070 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 := by
  have h4L : 4 ≤ lOf n K := four_le_lOf h1n h1K
  have hw_L : wOf K ≤ 2 * lOf n K + 2 := wOf_le h1n h1K
  have hB2_le : arity (dHbOf K) ≤ 5 * K * lOf n K := by have := B2_le h1n h1K; nlinarith
  have harHb : arity (dHbOf K + 1) ≤ 10 * K * lOf n K := by
    have hring : 2 * (5 * K * lOf n K) = 10 * K * lOf n K := by ring
    rw [arity_succ_eq, ← hring]; exact Nat.mul_le_mul_left 2 hB2_le
  have hLr4 : (4 : ℝ) ≤ (lOf n K : ℝ) := by exact_mod_cast h4L
  have hL1 : (1 : ℝ) ≤ (lOf n K : ℝ) := by linarith
  have hL23 : (lOf n K : ℝ) ^ 2 ≤ (lOf n K : ℝ) ^ 3 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hL34 : (lOf n K : ℝ) ^ 3 ≤ (lOf n K : ℝ) ^ 4 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hKL2 : (K : ℝ) * (lOf n K : ℝ) ^ 2 ≤ (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left (hL23.trans hL34) (by positivity)
  have hs3 := routeB.step3Circ_size as br arith n K d h1K
  have har' : (arity (dHbOf K + 1) : ℝ) ≤ 10 * (K : ℝ) * (lOf n K : ℝ) := by exact_mod_cast harHb
  have h74 : 74 * (wOf K : ℝ) + 336 ≤ 306 * (lOf n K : ℝ) := by
    have : 74 * wOf K + 336 ≤ 306 * lOf n K := by omega
    exact_mod_cast this
  have hp1 : (arity (dHbOf K + 1) : ℝ) * (74 * (wOf K : ℝ) + 336) ≤
      3060 * ((K : ℝ) * (lOf n K : ℝ) ^ 4) :=
    ((mul_le_mul har' h74 (by positivity) (by positivity)).trans_eq (by ring)).trans
      (mul_le_mul_of_nonneg_left hKL2 (by norm_num))
  have hexp : ((arity (dHbOf K + 1) : ℕ) : ℝ) * (74 * (wOf K : ℝ) + 336 +
      br.C_sort * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2)) =
      (arity (dHbOf K + 1) : ℝ) * (74 * (wOf K : ℝ) + 336) +
      (arity (dHbOf K + 1) : ℝ) * (br.C_sort * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2)) := by
    ring
  rw [hexp] at hs3
  exact hs3.trans ((add_le_add hp1 (sortHb_term_le_KL4 br h1n h1K)).trans_eq (by ring))

private lemma unroute_size_le_KL4 (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (routeA : HarmBucketRouteA54) (routeB : HarmBucketRouteB54)
    {n K d : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) (hNM : 2 * K ≤ arity d) :
    ((unrouteAndSubCirc occ comb br as arith n K d h1K hNM).size : ℝ) ≤
      (4171 + 2422 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 := by
  have h4L : 4 ≤ lOf n K := four_le_lOf h1n h1K
  have hLr4 : (4 : ℝ) ≤ (lOf n K : ℝ) := by exact_mod_cast h4L
  have hL1 : (1 : ℝ) ≤ (lOf n K : ℝ) := by linarith
  have hL23 : (lOf n K : ℝ) ^ 2 ≤ (lOf n K : ℝ) ^ 3 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hL34 : (lOf n K : ℝ) ^ 3 ≤ (lOf n K : ℝ) ^ 4 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hKL2 : (K : ℝ) * (lOf n K : ℝ) ^ 2 ≤ (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left (hL23.trans hL34) (by positivity)
  have hun := unrouteAndSubCirc_size occ comb br as arith routeA routeB n K d h1K hNM
  have h2p_eq : (2 ^ (dHbOf K + 1) : ℝ) = (arity (dHbOf K + 1) : ℝ) := by
    have : 2 ^ (dHbOf K + 1) = arity (dHbOf K + 1) := (arity_eq_two_pow _).symm
    exact_mod_cast this
  have hsort12' : br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR2Hb K : ℝ) + 1) +
      br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + 1) ≤
      2070 * br.C_sort * (K : ℝ) * (lOf n K : ℝ) ^ 4 := by
    have hsort12 : br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR2Hb K : ℝ) + 1) +
        br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + 1) =
        (arity (dHbOf K + 1) : ℝ) * (br.C_sort * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2)) := by
      rw [h2p_eq]; ring
    rw [hsort12]; exact sortHb_term_le_KL4 br h1n h1K
  have hlin_hb4 : ((arity (dHbOf K + 1) * (3 * wOf K) : ℕ) : ℝ) + ((arity (dHbOf K + 1) * (2 * wOf K + 3) : ℕ) : ℝ) +
      (((arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) : ℕ) : ℝ) + (((2 * K) * (3 * wOf K) : ℕ) : ℝ) +
      ((arity (dHbOf K + 1) * (11 * wOf K + 12) : ℕ) : ℝ) + (((2 * K) * (32 * wOf K) : ℕ) : ℝ) ≤
      3360 * ((K : ℝ) * (lOf n K : ℝ) ^ 4) := by
    have hlin_hb : ((arity (dHbOf K + 1) * (3 * wOf K) : ℕ) : ℝ) + ((arity (dHbOf K + 1) * (2 * wOf K + 3) : ℕ) : ℝ) +
        (((arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) : ℕ) : ℝ) + (((2 * K) * (3 * wOf K) : ℕ) : ℝ) +
        ((arity (dHbOf K + 1) * (11 * wOf K + 12) : ℕ) : ℝ) + (((2 * K) * (32 * wOf K) : ℕ) : ℝ) ≤
        3360 * ((K : ℝ) * (lOf n K : ℝ) ^ 2) := by
      exact_mod_cast unroute_hb_nat_le h1n h1K
    exact hlin_hb.trans (mul_le_mul_of_nonneg_left hKL2 (by norm_num))
  have hstep12 := step12_rhs_le_KL4 br h1n h1K
  have hreassoc : br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR2Hb K : ℝ) + 1) +
      ((arity (dHbOf K + 1) * (3 * wOf K) : ℕ) : ℝ) + ((arity (dHbOf K + 1) * (2 * wOf K + 3) : ℕ) : ℝ) +
      (((arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) : ℕ) : ℝ) +
      br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + 1) +
      (((2 * K) * (3 * wOf K) : ℕ) : ℝ) + ((arity (dHbOf K + 1) * (11 * wOf K + 12) : ℕ) : ℝ) +
      (((2 * K) * (32 * wOf K) : ℕ) : ℝ) +
      (((wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) : ℝ) +
        2 * ((arity (dOccOf K) * (2 * wOf K + 2) : ℕ) : ℝ) +
        2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) +
        (((2 * K - 1) * (49 * wOf K + 236) : ℕ) : ℝ) +
        (((2 * K) * (3 * wOf K) : ℕ) : ℝ)) =
      (br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR2Hb K : ℝ) + 1) +
        br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + 1)) +
      (((arity (dHbOf K + 1) * (3 * wOf K) : ℕ) : ℝ) + ((arity (dHbOf K + 1) * (2 * wOf K + 3) : ℕ) : ℝ) +
        (((arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) : ℕ) : ℝ) + (((2 * K) * (3 * wOf K) : ℕ) : ℝ) +
        ((arity (dHbOf K + 1) * (11 * wOf K + 12) : ℕ) : ℝ) + (((2 * K) * (32 * wOf K) : ℕ) : ℝ)) +
      (((wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) : ℝ) +
        2 * ((arity (dOccOf K) * (2 * wOf K + 2) : ℕ) : ℝ) +
        2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) +
        (((2 * K - 1) * (49 * wOf K + 236) : ℕ) : ℝ) +
        (((2 * K) * (3 * wOf K) : ℕ) : ℝ)) := by ring
  rw [hreassoc] at hun
  exact hun.trans ((add_le_add (add_le_add hsort12' hlin_hb4) hstep12).trans_eq (by ring))

private lemma step4_size_le_KL4 (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) {n K d : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    ((unifBucketsCirc comb br as arith n K d h1K).size : ℝ) ≤
      (100 + 45 * br.C_unif) * (K : ℝ) * (lOf n K : ℝ) ^ 4 := by
  have h4L : 4 ≤ lOf n K := four_le_lOf h1n h1K
  have hw_L : wOf K ≤ 2 * lOf n K + 2 := wOf_le h1n h1K
  have hB2_le : arity (dHbOf K) ≤ 5 * K * lOf n K := by have := B2_le h1n h1K; nlinarith
  have hbp_le : (bucketPairs (2 * K)).length ≤ 5 * K * lOf n K :=
    le_trans (le_of_lt (bucketPairs_length_lt_B2 comb (K := K))) hB2_le
  have hCu := br.hC_unif_pos
  have hLr4 : (4 : ℝ) ≤ (lOf n K : ℝ) := by exact_mod_cast h4L
  have hL1 : (1 : ℝ) ≤ (lOf n K : ℝ) := by linarith
  have hL23 : (lOf n K : ℝ) ^ 2 ≤ (lOf n K : ℝ) ^ 3 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hL34 : (lOf n K : ℝ) ^ 3 ≤ (lOf n K : ℝ) ^ 4 :=
    le_trans (le_mul_of_one_le_right (by positivity) hL1) (le_of_eq (by ring))
  have hKL2 : (K : ℝ) * (lOf n K : ℝ) ^ 2 ≤ (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left (hL23.trans hL34) (by positivity)
  have hKL3 : (K : ℝ) * (lOf n K : ℝ) ^ 3 ≤ (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left hL34 (by positivity)
  have hs4 := unifBucketsCirc_size comb br as arith n K d h1K
  have hbp' : ((bucketPairs (2 * K)).length : ℝ) ≤ 5 * (K : ℝ) * (lOf n K : ℝ) := by exact_mod_cast hbp_le
  have hw1 : (wOf K : ℝ) + 1 ≤ 3 * (lOf n K : ℝ) := by
    have : wOf K + 1 ≤ 3 * lOf n K := by omega
    exact_mod_cast this
  have h80 : (80 : ℝ) + br.C_unif * ((wOf K : ℝ) + 1) ^ 2 ≤
      20 * (lOf n K : ℝ) + br.C_unif * (3 * (lOf n K : ℝ)) ^ 2 := by
    have hsq : ((wOf K : ℝ) + 1) ^ 2 ≤ (3 * (lOf n K : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hw1 2
    exact add_le_add (by linarith) (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hmul : ((bucketPairs (2 * K)).length : ℝ) * (80 + br.C_unif * ((wOf K : ℝ) + 1) ^ 2) ≤
      (5 * (K : ℝ) * (lOf n K : ℝ)) * (20 * (lOf n K : ℝ) + br.C_unif * (3 * (lOf n K : ℝ)) ^ 2) :=
    mul_le_mul hbp' h80 (by positivity) (by positivity)
  have hfin : ((unifBucketsCirc comb br as arith n K d h1K).size : ℝ) ≤
      100 * ((K : ℝ) * (lOf n K : ℝ) ^ 2) + 45 * br.C_unif * ((K : ℝ) * (lOf n K : ℝ) ^ 3) :=
    hs4.trans (hmul.trans_eq (by ring))
  have h1 := mul_le_mul_of_nonneg_left hKL2 (by norm_num : (0 : ℝ) ≤ 100)
  have h2 := mul_le_mul_of_nonneg_left hKL3 (by positivity : 0 ≤ 45 * br.C_unif)
  exact hfin.trans ((add_le_add h1 h2).trans_eq (by ring))

lemma harmBucketH_lCircuitDef_size (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (routeA : HarmBucketRouteA54) (routeB : HarmBucketRouteB54)
    (n K d : ℕ) (h1n : 1 ≤ n) (h1K : 1 ≤ K) (h1d : 1 ≤ d) (hNM : 2 * K ≤ arity d) :
    let s := Nat.clog 2 n + 1
    let L := Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1
    let C_hl := (10000 : ℝ) + 5000 * br.C_sort + 100 * br.C_unif + as.C_as
    ((harmBucketH_lCircuitDef occ comb br as arith n K d h1n h1K h1d hNM).size : ℝ) ≤
      C_hl * ((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4 := by
  intro s L C_hl
  have hs_eq : s = sOf n := rfl
  have hL_eq : L = lOf n K := rfl
  have h4L : 4 ≤ lOf n K := four_le_lOf h1n h1K
  have h1s : 1 ≤ sOf n := by dsimp [sOf]; omega
  have hCs := br.hC_sort_pos
  have hCu := br.hC_unif_pos
  have hCas := as.C_as_pos
  have h_KS_base : (K : ℝ) * (lOf n K : ℝ) ^ 4 ≤ ((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4 := by
    have h1 : (K : ℝ) ≤ ((K * s + arity d : ℕ) : ℝ) := by
      have h1_nat : K ≤ K * s + arity d := by have : 1 ≤ s := h1s; nlinarith
      exact_mod_cast h1_nat
    have h2 : (lOf n K : ℝ) ^ 4 ≤ ((L + d : ℕ) : ℝ) ^ 4 := by
      have h2_nat : lOf n K ≤ L + d := by rw [hL_eq]; omega
      have h2_r : (lOf n K : ℝ) ≤ ((L + d : ℕ) : ℝ) := by exact_mod_cast h2_nat
      exact pow_le_pow_left₀ (by positivity) h2_r 4
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have h_AS_base : (arity d : ℝ) * ((d : ℝ) + 1) ^ 4 ≤ ((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4 := by
    have h1 : (arity d : ℝ) ≤ ((K * s + arity d : ℕ) : ℝ) := by
      have : arity d ≤ K * s + arity d := Nat.le_add_left _ _
      exact_mod_cast this
    have h2 : ((d : ℝ) + 1) ^ 4 ≤ ((L + d : ℕ) : ℝ) ^ 4 := by
      have h2_nat : d + 1 ≤ L + d := by rw [hL_eq]; omega
      have h2_r : (d : ℝ) + 1 ≤ ((L + d : ℕ) : ℝ) := by exact_mod_cast h2_nat
      exact pow_le_pow_left₀ (by positivity) h2_r 4
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hS12 : ((step12Circ as arith br n K d h1K).size : ℝ) ≤
      (811 + 352 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    (occ.step12Circ_size as arith br n K d h1K).trans (step12_rhs_le_KL4 br h1n h1K)
  have hS3 : ((step3Circ as br arith n K d h1K).size : ℝ) ≤
      (3060 + 2070 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    step3_size_le_KL4 br as arith routeB h1n h1K
  have hS4 : ((unifBucketsCirc comb br as arith n K d h1K).size : ℝ) ≤
      (100 + 45 * br.C_unif) * (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    step4_size_le_KL4 comb br as arith h1n h1K
  have hS_unr : ((unrouteAndSubCirc occ comb br as arith n K d h1K hNM).size : ℝ) ≤
      (4171 + 2422 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 :=
    unroute_size_le_KL4 occ comb br as arith routeA routeB h1n h1K hNM
  have hS6 : ((asPermCirc as n K d h1K h1d hNM).size : ℝ) ≤ as.C_as * (arity d : ℝ) * ((d : ℝ) + 1) ^ 4 := by
    have h := asPermCirc_size as n K d h1K h1d hNM
    push_cast at h
    exact h
  dsimp only [harmBucketH_lCircuitDef]
  rw [LayeredCircuit.seqList_size]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  conv_lhs => simp only [Nat.cast_add, ← add_assoc]
  have hkl_pos : 0 ≤ (K : ℝ) * (lOf n K : ℝ) ^ 4 := by positivity
  have hcoeff : (811 + 352 * br.C_sort) + (3060 + 2070 * br.C_sort) +
      (100 + 45 * br.C_unif) + (4171 + 2422 * br.C_sort) ≤
      10000 + 5000 * br.C_sort + 100 * br.C_unif := by linarith only [hCs, hCu]
  have hfactor : (811 + 352 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 +
      (3060 + 2070 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 +
      (100 + 45 * br.C_unif) * (K : ℝ) * (lOf n K : ℝ) ^ 4 +
      (4171 + 2422 * br.C_sort) * (K : ℝ) * (lOf n K : ℝ) ^ 4 =
      ((811 + 352 * br.C_sort) + (3060 + 2070 * br.C_sort) +
        (100 + 45 * br.C_unif) + (4171 + 2422 * br.C_sort)) * ((K : ℝ) * (lOf n K : ℝ) ^ 4) := by ring
  have hsum4 : ((step12Circ as arith br n K d h1K).size : ℝ) + ((step3Circ as br arith n K d h1K).size : ℝ) +
      ((unifBucketsCirc comb br as arith n K d h1K).size : ℝ) +
      ((unrouteAndSubCirc occ comb br as arith n K d h1K hNM).size : ℝ) ≤
      (10000 + 5000 * br.C_sort + 100 * br.C_unif) * ((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4 :=
    ((add_le_add (add_le_add (add_le_add hS12 hS3) hS4) hS_unr).trans_eq hfactor).trans
      ((mul_le_mul_of_nonneg_right hcoeff hkl_pos).trans
        ((mul_le_mul_of_nonneg_left h_KS_base
          (by positivity : 0 ≤ 10000 + 5000 * br.C_sort + 100 * br.C_unif)).trans_eq (by ring)))
  have h_as_all : ((asPermCirc as n K d h1K h1d hNM).size : ℝ) ≤
      as.C_as * (((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4) := by
    rw [mul_assoc] at hS6
    exact hS6.trans (mul_le_mul_of_nonneg_left h_AS_base (by positivity : (0 : ℝ) ≤ as.C_as))
  have hsplit : C_hl * ((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4 =
      (10000 + 5000 * br.C_sort + 100 * br.C_unif) * ((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4 +
      as.C_as * (((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ 4) := by
    dsimp only [C_hl]; ring
  rw [hsplit]
  exact add_le_add hsum4 h_as_all

lemma act_harmBucketH_lCircuitDef (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (routeA : HarmBucketRouteA54) (routeB : HarmBucketRouteB54)
    (n K d : ℕ) (h1n : 1 ≤ n) (h1K : 1 ≤ K) (h1d : 1 ≤ d) (hNM : 2 * K ≤ arity d)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l) :
    let s := Nat.clog 2 n + 1
    act (harmBucketH_lCircuitDef occ comb br as arith n K d h1n h1K h1d hNM).unitary
        (ket (padZero (2 * K * s + arity d * d) (harmBucketAncDef as n K d)
          (Fin.append (flatReg (2 * K) s fun p => particleSym54 n s (l p)) (fun _ => false)))) =
      ((1 / Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) : ℂ) •
        ∑ h : stabGroup (2 * K) l,
          ket (padZero (2 * K * s + arity d * d) (harmBucketAncDef as n K d)
            (Fin.append (flatReg (2 * K) s fun p => particleSym54 n s (l p))
              (flatReg (arity d) d (permRegBits (2 * K) d hNM h.1)))) := by
  intro s
  let aL := flatReg (2 * K) (sOf n) (fun p => particleSym54 n (sOf n) (l p))
  let z0 := padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d) (Fin.append aL (fun _ => false))
  let z1 := updateOn (eOccReg as n K d)
    (updateOn (eActReg as n K d)
      (updateOn (eMReg as n K d) z0 (flatReg (2 * K) (wOf K) (mBitsFn K l)))
      (flatReg (2 * K) 1 (actBitsFn K l)))
    (flatReg (2 * K) (wOf K) (occBitsFn K l))
  let z3 := updateOn (eTr2b as n K d)
    (updateOn (eRec3 as n K d)
      (updateOn (eTr2a as n K d)
        (updateOn (eRec2 as n K d) z1
          (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
            (hb1ArrOfList K (hbSeqPass (hb1SortedList K l))
              (by rw [hbSeqPass_length, hb1SortedList_length]) (fun _ _ => false))))
        (rec2SortTr K l))
      (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3SortedArr K l)))
    (rec3SortTr K l)
  dsimp only [harmBucketH_lCircuitDef]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  change act (asPermCirc as n K d h1K h1d hNM).unitary
    (act (unrouteAndSubCirc occ comb br as arith n K d h1K hNM).unitary
      (act (unifBucketsCirc comb br as arith n K d h1K).unitary
        (act (step3Circ as br arith n K d h1K).unitary
          (act (step12Circ as arith br n K d h1K).unitary (ket z0))))) = _
  -- Step 1–2
  have h12 : act (step12Circ as arith br n K d h1K).unitary (ket z0) = ket z1 :=
    occ.act_step12Circ comb as arith br n K d h1K l hl z0
      (padZero_eL_comp as n K d aL _) (fun k _ => padZero_anc_comp as n K d _ k)
  rw [h12]
  -- Step 3
  have hz1_anc_ge3 : ∀ k : Fin 24, 3 ≤ k.1 → z1 ∘ ancEmb as n K d k = fun _ => false := fun k hk => by
    have h0 : k ≠ ⟨0, by decide⟩ := fun h => by subst h; simp at hk
    have h1 : k ≠ ⟨1, by decide⟩ := fun h => by subst h; simp at hk
    have h2 : k ≠ ⟨2, by decide⟩ := fun h => by subst h; simp at hk
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_anc_other as n K d k h2)]
    rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_anc_other as n K d k h1)]
    rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_anc_other as n K d k h0)]
    exact padZero_anc_comp as n K d _ k
  have hz1_M : z1 ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_eMReg as n K d)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eMReg_disjoint_eActReg as n K d b a h.symm)]
    exact updateOn_comp_emb _ _ _
  have hz1_A : z1 ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_eActReg as n K d)]
    exact updateOn_comp_emb _ _ _
  have hz1_O : z1 ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l) := updateOn_comp_emb _ _ _
  have h3 : act (step3Circ as br arith n K d h1K).unitary (ket z1) = ket z3 :=
    routeB.act_step3Circ comb br as arith n K d h1K z1 hz1_A hz1_M hz1_O
      (hz1_anc_ge3 ⟨11, by decide⟩ (by decide)) (hz1_anc_ge3 ⟨12, by decide⟩ (by decide))
      (hz1_anc_ge3 ⟨13, by decide⟩ (by decide)) (hz1_anc_ge3 ⟨14, by decide⟩ (by decide))
      (hz1_anc_ge3 ⟨17, by decide⟩ (by decide)) (hz1_anc_ge3 ⟨18, by decide⟩ (by decide))
      (hz1_anc_ge3 ⟨19, by decide⟩ (by decide)) (hz1_anc_ge3 ⟨20, by decide⟩ (by decide))
      (hz1_anc_ge3 ⟨22, by decide⟩ (by decide))
  rw [h3]
  -- Step 4
  have hz3_rec3 : z3 ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K)
      (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (fun _ _ => false)) := by
    dsimp only [z3]
    rw [updateOn_comp_disjoint _ _ (eTr2b_disjoint_eRec3 as n K d),
      updateOn_comp_emb, routeB.rec3SortedArr_eq_hb2Spec comb br h1K l]
  have hz3_ctrl : z3 ∘ eUnifCtrl as n K d = fun _ => false := by
    dsimp only [z3]
    rw [updateOn_comp_disjoint _ _ (eTr2b_disjoint_eUnifCtrl as n K d),
      updateOn_comp_disjoint _ _ (eRec3_disjoint_eUnifCtrl as n K d),
      updateOn_comp_disjoint _ _ (eTr2a_disjoint_eUnifCtrl as n K d),
      updateOn_comp_disjoint _ _ (eRec2_disjoint_eUnifCtrl as n K d)]
    funext j; exact congrFun (hz1_anc_ge3 ⟨21, by decide⟩ (by decide)) _
  have hz3_22 : z3 ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
    dsimp only [z3]
    rw [updateOn_comp_disjoint _ _ (eTr2b_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide)),
      updateOn_comp_disjoint _ _ (eRec3_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide)),
      updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide)),
      updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
    exact hz1_anc_ge3 ⟨22, by decide⟩ (by decide)
  rw [act_unifBucketsCirc comb br as arith n K d h1K hl z3 hz3_rec3 hz3_ctrl hz3_22]
  -- Step 5
  rw [act_smul', act_sum']
  have h5_sum : ∀ dFn : (i : Fin (2 * K)) → Fin (runOffset l i),
      act (unrouteAndSubCirc occ comb br as arith n K d h1K hNM).unitary
        (ket (updateOn (eRec3 as n K d) z3 (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
          (hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (dRec3Of K l dFn))))) =
      ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
        (Fin.append aL (flatReg (arity d) d
          (padZeroLESBits (2 * K) d ((isLESOfEquivPiFinOf (2 * K) l (comb.runStart_le hl)).symm dFn).1)))) :=
    fun dFn => act_unrouteAndSubCirc_single occ comb br as arith routeA routeB n K d h1K hNM hl dFn
  rw [Finset.sum_congr rfl fun dFn _ => h5_sum dFn]
  -- Step 6
  rw [act_smul', act_sum']
  congr 1
  let e1 := (isLESOfEquivPiFinOf (2 * K) l (comb.runStart_le hl)).symm
  let e2 := isLESOfEquivStabGroup comb l hl
  let e3 := Equiv.inv (stabGroup (2 * K) l)
  let eTotal := e1.trans (e2.trans e3)
  have h6_sum : ∀ dFn : (i : Fin (2 * K)) → Fin (runOffset l i),
      act (asPermCirc as n K d h1K h1d hNM).unitary
        (ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
          (Fin.append aL (flatReg (arity d) d (padZeroLESBits (2 * K) d (e1 dFn).1))))) =
      ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
        (Fin.append aL (flatReg (arity d) d (permRegBits (2 * K) d hNM (eTotal dFn).1)))) := by
    intro dFn
    let sFn := e1 dFn
    let hs : IsLES (2 * K) sFn.1 := fun j => (sFn.2 j).2
    let hperm := (e2 sFn).1
    have hperm_eq : permToLES (2 * K) hperm = sFn.1 :=
      comb.permToLES_lesToPerm (2 * K) sFn.1 hs
    have heinv : (eTotal dFn).1 = hperm⁻¹ := rfl
    change act (asPermCirc as n K d h1K h1d hNM).unitary
        (ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
          (Fin.append aL (flatReg (arity d) d (padZeroLESBits (2 * K) d sFn.1))))) = _
    rw [heinv, ← hperm_eq]
    exact act_asPermCirc_single as n K d h1K h1d hNM aL hperm
  rw [Finset.sum_congr rfl fun dFn _ => h6_sum dFn]
  exact eTotal.sum_comp (fun h : stabGroup (2 * K) l =>
    ket (padZero (2 * K * sOf n + arity d * d) (harmBucketAncDef as n K d)
      (Fin.append aL (flatReg (arity d) d (permRegBits (2 * K) d hNM h.1)))))

def buildHarmBucketHL54V2 (occ : HarmBucketOcc54) (comb : LcgSym54Comb) (br : BitonicRouting54)
    (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (routeA : HarmBucketRouteA54) (routeB : HarmBucketRouteB54) :
    QuantumLTF.Membership.Supplement.HarmBucketHL54V2 where
  C_hl := 10000 + 5000 * br.C_sort + 100 * br.C_unif + as.C_as
  C_hl_pos := by
    have := br.hC_sort_pos; have := br.hC_unif_pos; have := as.C_as_pos; positivity
  K_hl := 4
  harmBucketAnc := fun n K d => harmBucketAncDef as n K d
  harmBucketH_lCircuit := fun n K d h1n h1K h1d hNM =>
    harmBucketH_lCircuitDef occ comb br as arith n K d h1n h1K h1d hNM
  harmBucketH_lCircuit_size := fun n K d h1n h1K h1d hNM =>
    harmBucketH_lCircuitDef_size occ comb br as arith routeA routeB n K d h1n h1K h1d hNM
  act_harmBucketH_lCircuit := fun n K d h1n h1K h1d hNM l hl =>
    act_harmBucketH_lCircuitDef occ comb br as arith routeA routeB n K d h1n h1K h1d hNM l hl

end HarmBucketWork54


open QuantumLTF.Membership.Supplement HarmBucketWork54 in
theorem solution : Nonempty QuantumLTF.Membership.Supplement.HarmBucketHL54V2 :=
  let ⟨occ⟩ := QuantumLTF.Membership.Supplement.harm_bucket_occ_54
  let ⟨comb⟩ := QuantumLTF.Membership.Supplement.lcg_sym_comb_54
  let ⟨br⟩ := QuantumLTF.Membership.Supplement.bitonic_routing_54
  let ⟨as⟩ := QuantumLTF.Membership.Supplement.alonso_schott_sil_54
  let ⟨arith⟩ := QuantumLTF.Membership.Supplement.lcg_sym_arith_54
  let ⟨routeA⟩ := QuantumLTF.Membership.Supplement.harm_bucket_route_a_54
  let ⟨routeB⟩ := QuantumLTF.Membership.Supplement.harm_bucket_route_b_54
  ⟨buildHarmBucketHL54V2 occ comb br as arith routeA routeB⟩
