-- Prove2me | solution 1 for QECCertificates.LRAT.atMostK_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:05.697657+00:00
-- url     : https://prove2.me/submissions/013c856e-6b1a-4320-b2b9-8c9a85534822

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_slotBase_succ
public import Theorems.Thm_QECCertificates_LRAT_slotBase_mono
public import Theorems.Thm_QECCertificates_LRAT_slotBase_pred
public import Theorems.Thm_QECCertificates_LRAT_slotVar_of_le
public import Theorems.Thm_QECCertificates_LRAT_rowClauses_complete
public import Theorems.Thm_QECCertificates_LRAT_rowFill_at
public import Theorems.Thm_QECCertificates_LRAT_rowFill_of_notMem
public import Theorems.Thm_QECCertificates_LRAT_rowFill_prev
public import Theorems.Thm_QECCertificates_LRAT_cntS_append
public import Theorems.Thm_QECCertificates_LRAT_cntS_le_length
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_cntS_singleton_false
public import Theorems.Thm_QECCertificates_LRAT_cntS_singleton_true
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {k c : Nat} {xs : List Nat} {σ : Assign}
    (hc : ∀ t ∈ xs, t < c) (hcnt : cntS σ xs ≤ k) :
    ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
      ∀ C ∈ atMostK (slotVar c k) k xs, SatClause τ C := by
  have aux : ∀ (suf pre : List Nat) (τ : Assign),
      (∀ t ∈ pre ++ suf, τ t = σ t) →
      (∀ t ∈ pre ++ suf, t < c) →
      (∀ j, 1 ≤ j → j ≤ min pre.length (k + 1) →
        τ (c + slotBase k pre.length + (j - 1)) = decide (j ≤ cntS σ pre)) →
      cntS σ (pre ++ suf) ≤ k →
      ∃ τ' : Assign,
        (∀ t, t < c + slotBase k (pre.length + 1) → τ' t = τ t) ∧
        (∀ j, 1 ≤ j → j ≤ min (pre ++ suf).length (k + 1) →
          τ' (c + slotBase k (pre ++ suf).length + (j - 1))
            = decide (j ≤ cntS σ (pre ++ suf))) ∧
        ∀ C ∈ atMostKAux (slotVar c k) k pre suf, SatClause τ' C := by
    intro suf
    induction suf with
    | nil =>
        intro pre τ _ _ hprev hk
        have hkpre : cntS σ pre ≤ k := by simpa using hk
        refine ⟨τ, fun _ _ => rfl, ?_, ?_⟩
        · intro j hj1 hj2
          simp only [List.append_nil] at hj2 ⊢
          exact hprev j hj1 hj2
        · intro C hC
          by_cases hk' : k + 1 ≤ pre.length
          · have hsome : slotVar c k pre.length (k + 1)
                = some (c + slotBase k pre.length + (k + 1 - 1)) :=
              slotVar_of_le (by omega) (by simp [Nat.min_eq_right hk'])
            simp only [atMostKAux, if_pos hk', hsome] at hC
            rw [List.mem_singleton] at hC
            rw [hC]
            refine ⟨(c + slotBase k pre.length + (k + 1 - 1), false),
              List.mem_singleton_self _, ?_⟩
            have hv := hprev (k + 1) (by omega) (by simp [Nat.min_eq_right hk'])
            rw [hv]
            have : ¬ (k + 1 ≤ cntS σ pre) := by omega
            simp [this]
          · simp only [atMostKAux, if_neg hk'] at hC
            exact absurd hC (by simp)
    | cons x rest ih =>
        intro pre τ hagree hcc hprev hk
        set i := pre.length + 1 with hidef
        have hi : 1 ≤ i := by omega
        have hlen : (pre ++ [x]).length = i := by simp [hidef]
        have hxlt : x < c := hcc x (List.mem_append_right _ (List.mem_cons_self ..))
        have hxl : τ x = σ x := hagree x (List.mem_append_right _ (List.mem_cons_self ..))
        have hdecomp : cntS σ (pre ++ (x :: rest)) = cntS σ (pre ++ [x]) + cntS σ rest := by
          rw [show pre ++ (x :: rest) = (pre ++ [x]) ++ rest from by simp]
          exact cntS_append σ (pre ++ [x]) rest
        have hcx : cntS σ (pre ++ [x]) = cntS σ pre + (if σ x then 1 else 0) := by
          rw [cntS_append]
          by_cases h : σ x
          · rw [cntS_singleton_true σ x h]
            simp [h]
          · have hf : σ x = false := by simpa using h
            rw [cntS_singleton_false σ x hf, hf]
            simp
        have hcτ : cntS σ (pre ++ [x]) = cntS σ pre + (if τ x then 1 else 0) := by
          rw [hcx, hxl]
        have hmin : cntS σ pre ≤ min (i - 1) (k + 1) := by
          refine le_min (cntS_le_length σ pre) ?_
          have h1 : cntS σ pre ≤ cntS σ (pre ++ [x]) := by
            rw [cntS_append]; exact Nat.le_add_right _ _
          have h2 : cntS σ (pre ++ [x]) ≤ cntS σ (pre ++ (x :: rest)) := by
            rw [hdecomp]; exact Nat.le_add_right _ _
          omega
        have hpre' : ∀ j, 1 ≤ j → j ≤ min (i - 1) (k + 1) →
            τ (c + slotBase k (i - 1) + (j - 1)) = decide (j ≤ cntS σ pre) := by
          intro j hj1 hj2
          rw [show i - 1 = pre.length from by omega]
          exact hprev j hj1 hj2
        have hpre'' : ∀ j, 1 ≤ j → j ≤ min (pre ++ [x]).length (k + 1) →
            rowFill τ c k i (cntS σ (pre ++ [x]))
              (c + slotBase k (pre ++ [x]).length + (j - 1))
              = decide (j ≤ cntS σ (pre ++ [x])) := by
          intro j hj1 hj2
          rw [hlen]
          have h := rowFill_at (τ := τ) (c := c) (k := k) (i := i)
            (cnt := cntS σ (pre ++ [x])) (j := j - 1) (by omega)
          rwa [show j - 1 + 1 = j from by omega] at h
        have happ : (pre ++ [x]) ++ rest = pre ++ (x :: rest) := by simp
        have hagree' : ∀ t ∈ (pre ++ [x]) ++ rest,
            rowFill τ c k i (cntS σ (pre ++ [x])) t = σ t := by
          intro t ht
          rw [happ] at ht
          rcases List.mem_append.mp ht with ht | ht
          · rw [rowFill_of_notMem ?_]
            · exact hagree t (List.mem_append_left _ ht)
            · intro ⟨h1, _⟩
              have := hcc t (List.mem_append_left _ ht)
              omega
          · rcases List.mem_cons.mp ht with rfl | ht
            · rw [rowFill_of_notMem ?_]
              · exact hxl
              · intro ⟨h1, _⟩
                omega
            · rw [rowFill_of_notMem ?_]
              · exact hagree t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
              · intro ⟨h1, _⟩
                have := hcc t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
                omega
        have hcc' : ∀ t ∈ (pre ++ [x]) ++ rest, t < c := by
          intro t ht
          rw [happ] at ht
          exact hcc t ht
        have hk' : cntS σ ((pre ++ [x]) ++ rest) ≤ k := by
          rw [happ]; exact hk
        obtain ⟨τ'', hag, hfin, hcl⟩ :=
          ih (pre ++ [x]) (rowFill τ c k i (cntS σ (pre ++ [x]))) hagree' hcc' hpre'' hk'
        have hbound : ∀ t, t < c + slotBase k i → t < c + slotBase k ((pre ++ [x]).length + 1) := by
          intro t ht
          rw [hlen]
          exact lt_of_lt_of_le ht (Nat.add_le_add_left (slotBase_mono k (Nat.le_succ i)) c)
        have hbound' : ∀ t, t < c + slotBase k (i + 1) →
            t < c + slotBase k ((pre ++ [x]).length + 1) := by
          intro t ht
          rw [hlen]
          exact ht
        refine ⟨τ'', ?_, ?_, ?_⟩
        · intro t ht
          rw [hag t (hbound t ht)]
          exact rowFill_of_notMem (by
            rintro ⟨h1, _⟩
            omega)
        · intro j hj1 hj2
          rw [← happ] at hj2 ⊢
          exact hfin j hj1 hj2
        · have hpre''' : ∀ j, 1 ≤ j → j ≤ min (i - 1) (k + 1) →
              τ'' (c + slotBase k (i - 1) + (j - 1)) = decide (j ≤ cntS σ pre) := by
            intro j hj1 hj2
            have hlt : c + slotBase k (i - 1) + (j - 1) < c + slotBase k i := by
              rw [slotBase_pred hi]; omega
            rw [hag _ (hbound _ hlt)]
            rw [rowFill_prev hi (by omega)]
            exact hpre' j hj1 hj2
          have hcur''' : ∀ j, 1 ≤ j → j ≤ min i (k + 1) →
              τ'' (c + slotBase k i + (j - 1)) = decide (j ≤ cntS σ (pre ++ [x])) := by
            intro j hj1 hj2
            have hlt : c + slotBase k i + (j - 1) < c + slotBase k (i + 1) := by
              rw [slotBase_succ k i]
              omega
            rw [hag _ (hbound' _ hlt)]
            simpa [hlen] using hpre'' j hj1 (by rw [hlen]; exact hj2)
          have hx'' : τ'' x = τ x := by
            rw [hag x (hbound x (by omega))]
            exact rowFill_of_notMem (by rintro ⟨h1, _⟩; omega)
          have hrow := rowClauses_complete (c := c) (k := k) (i := i)
            (cnt' := cntS σ pre) (cnt := cntS σ (pre ++ [x])) (x := x)
            (τ := τ'') (bx := τ x) hx'' hcτ hmin hpre''' hcur'''
          intro C hC
          simp only [atMostKAux, List.mem_append] at hC
          rcases hC with hC | hC
          · exact hrow C hC
          · exact hcl C hC
  have hprev0 : ∀ j, 1 ≤ j → j ≤ min ([] : List Nat).length (k + 1) →
      σ (c + slotBase k ([] : List Nat).length + (j - 1)) = decide (j ≤ cntS σ []) := by
    intro j hj1 hj2
    simp only [List.length_nil, Nat.min_eq_left (Nat.zero_le _), Nat.le_zero] at hj2
    omega
  obtain ⟨τ, hag, _, hcl⟩ :=
    aux xs [] σ (by simp) (by simpa using hc) hprev0 (by simpa using hcnt)
  refine ⟨τ, ?_, ?_⟩
  · intro t ht
    have h0 : slotBase k 1 = 0 := by simp [slotBase]
    exact hag t (by rw [List.length_nil, Nat.zero_add, h0, Nat.add_zero]; exact ht)
  · simpa only [atMostK] using hcl
end QECCertificates.LRAT
