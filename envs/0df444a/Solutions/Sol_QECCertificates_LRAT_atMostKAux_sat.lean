-- Prove2me | solution 1 for QECCertificates.LRAT.atMostKAux_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:09.357939+00:00
-- url     : https://prove2.me/submissions/6f5ab70b-0e29-40e7-bf32-a88592a5ba46

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_cntS_append
public import Theorems.Thm_QECCertificates_LRAT_cntS_singleton_true
public import Theorems.Thm_QECCertificates_LRAT_cntS_singleton_false
public import Theorems.Thm_QECCertificates_LRAT_cntS_le_length
public import Theorems.Thm_QECCertificates_LRAT_sat_two
public import Theorems.Thm_QECCertificates_LRAT_sat_three
public import Theorems.Thm_QECCertificates_LRAT_SlotOK_some_of
public import Theorems.Thm_QECCertificates_LRAT_SlotOK_none_of
public import Theorems.Thm_QECCertificates_LRAT_mem_rowClauses
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {s : Nat → Nat → Option Nat} {k : Nat}
    (hok : SlotOK s k) :
    ∀ (pre suf : List Nat),
      (∀ j, 1 ≤ j → j ≤ min pre.length (k + 1) → j ≤ cntS σ pre →
        ∃ v, s pre.length j = some v ∧ σ v = true) →
      (∀ C ∈ atMostKAux s k pre suf, SatClause σ C) →
      cntS σ (pre ++ suf) ≤ k := by
  intro pre suf hinv0 hcl0
  have aux : ∀ (suf pre : List Nat),
      (∀ j, 1 ≤ j → j ≤ min pre.length (k + 1) → j ≤ cntS σ pre →
        ∃ v, s pre.length j = some v ∧ σ v = true) →
      (∀ C ∈ atMostKAux s k pre suf, SatClause σ C) → cntS σ (pre ++ suf) ≤ k := by
    intro suf
    induction suf with
    | nil =>
      intro pre hinv hcl
      by_cases hk : k + 1 ≤ pre.length
      · obtain ⟨v, hsv⟩ := hok.some_of (i := pre.length) (j := k + 1)
          (by omega) (by simp [Nat.min_eq_right hk])
        have hmem : [(v, false)] ∈ atMostKAux s k pre [] := by
          simp only [atMostKAux, if_pos hk, hsv]
          exact List.mem_singleton_self _
        obtain ⟨l, hl, hv⟩ := hcl _ hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        obtain rfl : l = (v, false) := hl
        by_contra hle
        have hge : k + 1 ≤ cntS σ pre := by
          simp only [List.append_nil] at hle
          omega
        obtain ⟨v', hsv', hv'⟩ := hinv (k + 1) (by omega)
          (by simp [Nat.min_eq_right hk]) hge
        rw [hsv] at hsv'
        injection hsv' with hvv
        rw [← hvv] at hv'
        exact absurd hv' (by simp [hv])
      · have hpre : pre.length ≤ k := by omega
        simp only [List.append_nil]
        exact le_trans (cntS_le_length σ pre) hpre
    | cons x rest ih =>
      intro pre hinv hcl
      have hrow : ∀ C ∈ rowClauses s k (pre.length + 1) x, SatClause σ C :=
        fun C hC => hcl C (List.mem_append_left _ hC)
      have htl : ∀ C ∈ atMostKAux s k (pre ++ [x]) rest, SatClause σ C :=
        fun C hC => hcl C (List.mem_append_right _ hC)
      have hlen : (pre ++ [x]).length = pre.length + 1 := by simp
      have hcl_pre : cntS σ pre ≤ pre.length := cntS_le_length σ pre
      have hinv' : ∀ j, 1 ≤ j → j ≤ min (pre ++ [x]).length (k + 1) →
          j ≤ cntS σ (pre ++ [x]) → ∃ v, s (pre ++ [x]).length j = some v ∧ σ v = true := by
        intro j hj1 hj2 hj3
        rw [hlen] at hj2
        rw [cntS_append] at hj3
        obtain ⟨w, hsw⟩ := hok.some_of (i := pre.length + 1) (j := j) hj1 hj2
        have hswA : s (pre ++ [x]).length j = some w := by rw [hlen]; exact hsw
        cases hx : σ x
        · rw [cntS_singleton_false σ x hx, Nat.add_zero] at hj3
          obtain ⟨v, hsv, hv⟩ := hinv j hj1 (by omega) hj3
          have hmem : [(v, false), (w, true)] ∈ slotClauses s (pre.length + 1) j x := by
            by_cases hb : ∃ u, s pre.length (j - 1) = some u
            · obtain ⟨u, hu⟩ := hb
              simp [slotClauses, hsv, hsw, hu]
            · have hu : s pre.length (j - 1) = none := by
                cases h : s pre.length (j - 1) with
                | none => rfl
                | some u => exact absurd ⟨u, h⟩ hb
              simp [slotClauses, hsv, hsw, hu]
          rcases sat_two (hrow _ (mem_rowClauses hj1 hj2 hmem)) with h | h
          · rw [hv] at h; exact absurd h (by simp)
          · exact ⟨w, hswA, h⟩
        · rw [cntS_singleton_true σ x hx] at hj3
          by_cases hj : j = 1
          · subst hj
            have hb : s pre.length 0 = none := hok.none_of (i := pre.length) (j := 0) (by simp)
            have hmem : [(x, false), (w, true)] ∈ slotClauses s (pre.length + 1) 1 x := by
              by_cases ha : ∃ u, s pre.length 1 = some u
              · obtain ⟨u, hu⟩ := ha
                simp [slotClauses, hu, hb, hsw]
              · have hu : s pre.length 1 = none := by
                  cases h : s pre.length 1 with
                  | none => rfl
                  | some u => exact absurd ⟨u, h⟩ ha
                simp [slotClauses, hu, hb, hsw]
            rcases sat_two (hrow _ (mem_rowClauses (by omega) hj2 hmem)) with h | h
            · rw [hx] at h; exact absurd h (by simp)
            · exact ⟨w, hswA, h⟩
          · have hj2' : 2 ≤ j := by omega
            obtain ⟨v, hsv, hv⟩ := hinv (j - 1) (by omega) (by omega) (by omega)
            have hmem : [(v, false), (x, false), (w, true)] ∈
                slotClauses s (pre.length + 1) j x := by
              by_cases ha : ∃ u, s pre.length j = some u
              · obtain ⟨u, hu⟩ := ha
                simp [slotClauses, hu, hsv, hsw]
              · have hu : s pre.length j = none := by
                  cases h : s pre.length j with
                  | none => rfl
                  | some u => exact absurd ⟨u, h⟩ ha
                simp [slotClauses, hu, hsv, hsw]
            rcases sat_three (hrow _ (mem_rowClauses (by omega) hj2 hmem)) with h | h | h
            · rw [hv] at h; exact absurd h (by simp)
            · rw [hx] at h; exact absurd h (by simp)
            · exact ⟨w, hswA, h⟩
      have hgoal : (pre ++ x :: rest) = (pre ++ [x]) ++ rest := by
        rw [List.append_assoc, List.singleton_append]
      rw [hgoal]
      exact ih (pre ++ [x]) hinv' htl
  exact aux suf pre hinv0 hcl0
end QECCertificates.LRAT
