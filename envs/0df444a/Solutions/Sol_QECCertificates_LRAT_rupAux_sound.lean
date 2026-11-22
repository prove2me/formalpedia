-- Prove2me | solution 1 for QECCertificates.LRAT.rupAux_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:00.8688+00:00
-- url     : https://prove2.me/submissions/bb12d941-d849-4889-ac32-95ffcc85fe60

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Theorems.Thm_QECCertificates_LRAT_scan_nil
public import Theorems.Thm_QECCertificates_LRAT_scan_singleton
public import Theorems.Thm_QECCertificates_LRAT_litFree_eq_false
section
@[expose] public section
namespace QECCertificates.LRAT
private theorem bool_not_self (b : Bool) : (!b : Bool) = b → False := by
  cases b <;> simp
namespace ClauseDB
end ClauseDB
end QECCertificates.LRAT
end
end

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {K : Type} (D : ClauseDB K) {σ : Assign} {d : K} :
    ∀ (hints : List Nat) (a : PAssign), agrees σ a →
      (∀ h ∈ hints, ∀ E, D.get? d (h - 1) = some E → SatClause σ E) →
      rupAux D d a hints = true → False := by
  intro hints
  induction hints with
  | nil =>
      intro a _ _ hr
      simp [rupAux] at hr
  | cons h rest ih =>
      intro a ha hsat hr
      rw [rupAux] at hr
      cases hE : D.get? d (h - 1) with
      | none =>
          rw [hE] at hr
          simp at hr
      | some E =>
          rw [hE] at hr
          dsimp only at hr
          have hsatE : SatClause σ E := hsat h (by simp) E hE
          cases hs : scan a E with
          | nil =>
              rw [hs] at hr
              obtain ⟨l, hl, hsatl⟩ := hsatE
              have h1 : σ l.1 = (!l.2 : Bool) := litFree_eq_false (scan_nil hs l hl) ha
              exact bool_not_self l.2 (h1.symm.trans hsatl)
          | cons x xs =>
              cases xs with
              | nil =>
                  rw [hs] at hr
                  have hx : σ x.1 = x.2 := by
                    obtain ⟨l', hl', hsatl'⟩ := hsatE
                    by_cases hne : l' = x
                    · rw [hne] at hsatl'
                      exact hsatl'
                    · have hlf : litFree a l' = false := (scan_singleton hs).2 l' hl' hne
                      have h1 : σ l'.1 = (!l'.2 : Bool) := litFree_eq_false hlf ha
                      exact absurd (h1.symm.trans hsatl') (bool_not_self l'.2)
                  exact ih (x :: a)
                    (fun l hl => by
                      rcases List.mem_cons.mp hl with rfl | hl
                      · exact hx
                      · exact ha l hl)
                    (fun h' hh' E' hE' => hsat h' (List.mem_cons_of_mem _ hh') E' hE') hr
              | cons y ys =>
                  rw [hs] at hr
                  simp at hr
end QECCertificates.LRAT
