-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.Q_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:51.69753+00:00
-- url     : https://prove2.me/submissions/5fdff29f-c50e-46ab-ba38-7128feff4fc3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
private theorem eN_val_eq_single {N : ℕ} (s : Fin N) : eN k N s.1 = Pi.single s 1 := by
  funext l
  simp only [eN, Pi.single_apply, Fin.ext_iff]
private theorem inX_apply' {n c : ℕ} (v : Fin n → k) (l : Fin (n + c)) :
    inX k n c v l = if h : l.1 < n then v ⟨l.1, h⟩ else 0 := by
  simp only [inX, LinearMap.pi_apply]
  split_ifs <;> simp
private theorem inX_single' {n c : ℕ} (s : Fin n) :
    inX k n c (Pi.single s 1) = Pi.single ⟨s.1, by have := s.2; omega⟩ 1 := by
  funext l
  rw [inX_apply']
  by_cases h : l.1 < n
  · rw [dif_pos h]
    simp only [Pi.single_apply, Fin.ext_iff]
  · rw [dif_neg h, Pi.single_apply, if_neg]
    intro e
    rw [Fin.ext_iff] at e
    have := s.2
    simp only at e
    omega
private theorem mem_Ufl_iff' {n c i : ℕ} (v : Fin (n + c) → k) :
    v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), ¬ l.1 < n + i → v l = 0 := Iff.rfl
end PI.UnfoldEquiv.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) :
    Q xj x ↔ ∀ (l : Fin (n + c)) (s : Fin (n' + (c + 1))), ¬ IsFree n' n c l.1 s.1 → x (Pi.single s 1) l = base xj l s := by
  constructor
  · rintro ⟨h1, h2, h3⟩ l s hnf
    simp only [IsFree, not_and, not_or] at hnf
    unfold base
    by_cases hs : s.1 < n'
    · rw [dif_pos hs]
      have e : (Pi.single s 1 : Fin (n' + (c + 1)) → k) =
          inX k n' (c + 1) (Pi.single ⟨s.1, hs⟩ 1) := by
        rw [inX_single']
      rw [e, h1, inX_apply']
      split_ifs with hl
      · first
          | rfl
          | (rw [LinearMap.toMatrix'_apply])
          | (rw [LinearMap.toMatrix'_apply]; congr 1; funext j'; simp [Pi.single_apply, Fin.ext_iff])
      · rfl
    · rw [dif_neg hs]
      obtain ⟨j, hj⟩ : ∃ j, s.1 = n' + j := ⟨s.1 - n', by omega⟩
      rw [hj] at hnf
      rw [hj, Nat.add_sub_cancel_left, ← eN_val_eq_single s, hj]
      obtain ⟨hjc, hj2⟩ := hnf (by omega)
      simp only [Nat.add_sub_cancel_left] at hjc hj2
      by_cases hj0 : j = 0
      · subst hj0
        have hc : 0 < c := by omega
        have k2 := congrFun (h2 hc) l
        simpa [eN] using k2
      · have hjlt : j < c := by have := s.2; omega
        obtain ⟨hl1, hl2⟩ := hj2 (by omega)
        have hl : ¬ l.1 < n + j := by omega
        have k4 := (mem_Ufl_iff' _).1 (h3 j (by omega) hjlt) l hl
        rw [Pi.sub_apply, sub_eq_zero] at k4
        rw [k4]
        simp only [eN]
  · intro H
    have Hs : ∀ (l : Fin (n + c)) (s : ℕ) (hs : s < n' + (c + 1)), ¬ IsFree n' n c l.1 s →
        x (eN k (n' + (c + 1)) s) l = base xj l ⟨s, hs⟩ := by
      intro l s hs h
      have k5 := H l ⟨s, hs⟩ h
      rw [← eN_val_eq_single] at k5
      exact k5
    refine ⟨?_, ?_, ?_⟩
    · intro v
      have e : x ∘ₗ inX k n' (c + 1) = inX k n c ∘ₗ xj := by
        ext s' l
        simp only [LinearMap.comp_apply, LinearMap.single_apply]
        have hs' := s'.2
        rw [inX_single', ← eN_val_eq_single, Hs l s'.1 (by omega) (by simp only [IsFree]; omega),
          inX_apply']
        unfold base
        rw [dif_pos hs']
        split_ifs with hl
        · first
            | rfl
            | (rw [LinearMap.toMatrix'_apply])
            | (rw [LinearMap.toMatrix'_apply]; congr 1; funext j'; simp [Pi.single_apply, Fin.ext_iff])
        · rfl
      exact LinearMap.congr_fun e v
    · intro hc
      funext l
      rw [Hs l n' (by omega) (by simp only [IsFree]; omega)]
      simp [base, eN]
    · intro j hj1 hjc
      rw [mem_Ufl_iff']
      intro l hl
      have hnl : ¬ n' + j < n' := by omega
      rw [Pi.sub_apply, Hs l (n' + j) (by omega) (by simp only [IsFree]; omega)]
      simp [base, eN, hnl]
end PI.UnfoldEquiv.UnitaryGroupMassFormula
