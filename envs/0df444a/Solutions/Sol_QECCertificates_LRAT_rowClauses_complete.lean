-- Prove2me | solution 1 for QECCertificates.LRAT.rowClauses_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:19.409443+00:00
-- url     : https://prove2.me/submissions/02fc49de-22f2-4878-8f33-2073b0184da4

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_slotVar_of_le
public import Theorems.Thm_QECCertificates_LRAT_slotVar_eq_none
public import Theorems.Thm_QECCertificates_LRAT_decide_imp
public import Theorems.Thm_QECCertificates_LRAT_sat_two_of_imp
public import Theorems.Thm_QECCertificates_LRAT_sat_three_of_imp
public import Theorems.Thm_QECCertificates_LRAT_sat_three_of_imp2
public import Theorems.Thm_QECCertificates_LRAT_sat_three_of_imp3
public import Theorems.Thm_QECCertificates_LRAT_slotClauses_eq_some_some
public import Theorems.Thm_QECCertificates_LRAT_slotClauses_eq_some_none
public import Theorems.Thm_QECCertificates_LRAT_slotClauses_eq_none_some
public import Theorems.Thm_QECCertificates_LRAT_slotClauses_eq_none_none
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
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
theorem _root_.solution {c k i cnt' cnt : Nat} {x : Nat} {τ : Assign} {bx : Bool}
    (hx : τ x = bx) (hcnt : cnt = cnt' + (if bx then 1 else 0))
    (hmin : cnt' ≤ min (i - 1) (k + 1))
    (hprev : ∀ j, 1 ≤ j → j ≤ min (i - 1) (k + 1) →
      τ (c + slotBase k (i - 1) + (j - 1)) = decide (j ≤ cnt'))
    (hcur : ∀ j, 1 ≤ j → j ≤ min i (k + 1) →
      τ (c + slotBase k i + (j - 1)) = decide (j ≤ cnt)) :
    ∀ C ∈ rowClauses (slotVar c k) k i x, SatClause τ C := by
  have hif : (if bx then 1 else 0) ≤ 1 := by cases bx <;> simp
  have hle : cnt' ≤ cnt := by omega
  have hle1 : cnt ≤ cnt' + 1 := by omega
  have hbx1 : bx = true → cnt = cnt' + 1 := by intro h; rw [hcnt, h]; simp
  have hbx0 : bx = false → cnt = cnt' := by intro h; rw [hcnt, h]; simp
  have ofT {P : Prop} [Decidable P] (h : decide P = true) : P := of_decide_eq_true h
  have ofF {P : Prop} [Decidable P] (h : decide P = false) : ¬ P := of_decide_eq_false h
  intro C hC
  simp only [rowClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨j', hj', hCj⟩ := hC
  set j := j' + 1 with hjdef
  have hj1 : 1 ≤ j := by omega
  have hj2 : j ≤ min i (k + 1) := by omega
  have hva := hcur j hj1 hj2
  by_cases hA : 1 ≤ j ∧ j ≤ min (i - 1) (k + 1)
  · by_cases hB : 1 ≤ j - 1 ∧ j - 1 ≤ min (i - 1) (k + 1)
    · have ha := hprev j hA.1 hA.2
      have hb := hprev (j - 1) hB.1 hB.2
      rw [slotClauses_eq_some_some (slotVar_of_le hA.1 hA.2) (slotVar_of_le hB.1 hB.2)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl | rfl | rfl
      · exact sat_two_of_imp ha hva (decide_imp fun h => le_trans h hle)
      · refine sat_three_of_imp hb hx hva fun h1 h2 => ?_
        have h1' := ofT h1
        have h2' := hbx1 h2
        simp only [decide_eq_true_eq]
        omega
      · exact sat_three_of_imp2 hva ha hx fun hs ha' => by
          have h1 := ofT hs
          have h2 := ofF ha'
          by_contra hbf
          have hb0 : bx = false := by
            cases bx with
            | false => rfl
            | true => exact absurd rfl hbf
          rw [hbx0 hb0] at h1
          omega
      · exact sat_three_of_imp3 hva ha hb fun hs ha' => by
          have h1 := ofT hs
          have h2 := ofF ha'
          simp only [decide_eq_true_eq]
          omega
    · have ha := hprev j hA.1 hA.2
      have hj1' : j = 1 := by
        by_contra h
        exact hB ⟨by omega, by omega⟩
      rw [slotClauses_eq_some_none (slotVar_of_le hA.1 hA.2) (slotVar_eq_none hB)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl | rfl
      · exact sat_two_of_imp ha hva (decide_imp fun h => le_trans h hle)
      · exact sat_two_of_imp hx hva fun hxT => by
          simp only [decide_eq_true_eq]
          rw [hbx1 hxT] at *
          omega
      · exact sat_three_of_imp2 hva ha hx fun hs ha' => by
          have h1 := ofT hs
          have h2 := ofF ha'
          by_contra hbf
          have hb0 : bx = false := by
            cases bx with
            | false => rfl
            | true => exact absurd rfl hbf
          rw [hbx0 hb0] at h1
          omega
  · have hjA : min (i - 1) (k + 1) < j := by
      by_contra hle'
      exact hA ⟨hj1, by omega⟩
    by_cases hB : 1 ≤ j - 1 ∧ j - 1 ≤ min (i - 1) (k + 1)
    · have hb := hprev (j - 1) hB.1 hB.2
      rw [slotClauses_eq_none_some (slotVar_eq_none hA) (slotVar_of_le hB.1 hB.2)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl | rfl
      · refine sat_three_of_imp hb hx hva fun h1 h2 => ?_
        have h1' := ofT h1
        have h2' := hbx1 h2
        simp only [decide_eq_true_eq]
        omega
      · exact sat_two_of_imp hva hx fun hs => by
          have h1 := ofT hs
          by_contra hbf
          have hb0 : bx = false := by
            cases bx with
            | false => rfl
            | true => exact absurd rfl hbf
          rw [hbx0 hb0] at h1
          omega
      · exact sat_two_of_imp hva hb fun hs => by
          have h1 := ofT hs
          simp only [decide_eq_true_eq]
          omega
    · have hj1' : j = 1 := by
        by_contra h
        refine hB ⟨by omega, ?_⟩
        omega
      have hmin0 : min (i - 1) (k + 1) = 0 := by
        by_contra h
        exact hA ⟨hj1, by omega⟩
      have hcnt0' : cnt' = 0 := le_antisymm (hmin0 ▸ hmin) (Nat.zero_le _)
      rw [slotClauses_eq_none_none (slotVar_eq_none hA) (slotVar_eq_none hB)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl
      · exact sat_two_of_imp hx hva fun hxT => by
          simp only [decide_eq_true_eq]
          rw [hbx1 hxT, hcnt0']
          omega
      · exact sat_two_of_imp hva hx fun hs => by
          have h1 := ofT hs
          rw [hj1'] at h1
          cases bx with
          | false =>
              rw [hbx0 rfl, hcnt0'] at h1
              exact absurd h1 (by omega)
          | true => rfl
end QECCertificates.LRAT
