-- Prove2me | solution 1 for QECCertificates.LRAT.checkAux_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:37.348828+00:00
-- url     : https://prove2.me/submissions/876dddc4-2cba-45ca-ad6c-dbb2008efede

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Theorems.Thm_QECCertificates_LRAT_rupAux_sound

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {K : Type} (D : ClauseDB K) {σ : Assign} :
    ∀ (d : K) (steps : List LStep), (∀ C, D.Mem d C → SatClause σ C) →
      checkAux D d steps = true → False := by
  intro d steps
  induction steps generalizing d with
  | nil => intro _ h; simp [checkAux] at h
  | cons s rest ih =>
      intro hdb h
      rw [checkAux] at h
      by_cases hcond : s.id = D.size d + 1 ∧ rupCheck D d s.clause s.hints
      · rw [if_pos hcond] at h
        have hrup : rupCheck D d s.clause s.hints = true := hcond.2
        have hsat : SatClause σ s.clause := by
          by_contra hc
          simp only [SatClause, not_exists, not_and] at hc
          refine rupAux_sound D (d := d) (σ := σ) s.hints (s.clause.map litNeg) ?_ ?_ hrup
          · intro l hl
            rcases List.mem_map.mp hl with ⟨l₀, hl₀, rfl⟩
            have hne : ¬(σ l₀.1 = l₀.2) := hc l₀ hl₀
            simp only [litNeg]
            cases h1 : σ l₀.1 <;> cases h2 : l₀.2 <;> simp_all
          · intro _ _ E hE
            exact hdb E (D.get?_mem hE)
        rcases Bool.or_eq_true_iff.mp h with hemp | hrest
        · rw [List.isEmpty_iff.mp hemp] at hsat
          obtain ⟨l, hl, _⟩ := hsat
          simp at hl
        · exact ih (D.push d s.clause) (fun C hC => by
            rcases D.push_mem hC with hEq | hC
            · subst hEq
              exact hsat
            · exact hdb C hC) hrest
      · rw [if_neg hcond] at h
        simp at h
end QECCertificates.LRAT
