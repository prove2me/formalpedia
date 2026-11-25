-- Prove2me | solution 1 for PI.MSC.reorder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:01:10.466598+00:00
-- url     : https://prove2.me/submissions/136d5537-dacb-49a4-b4f1-56e3e0e90998

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Theorems.Thm_PI_MSC_card_colLen_gt
import Theorems.Thm_PI_MSC_rowLen_eq_zero
import Theorems.Thm_PI_MSC_colLen_pos
import Theorems.Thm_PI_MSC_card_fiber
import Theorems.Thm_PI_MSC_initMinor_cast
import Theorems.Thm_PI_MSC_initMinor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace PI.MSC
private theorem reorder_lemma {α β : Type} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ)
    (h : ∀ v, Nat.card {x // f x = v} = Nat.card {y // g y = v}) :
    ∃ e : α ≃ β, ∀ x, g (e x) = f x := by
  classical
  have h' : ∀ v, Nonempty ({x // f x = v} ≃ {y // g y = v}) := fun v => Finite.card_eq.1 (h v)
  let ev : ∀ v, {x // f x = v} ≃ {y // g y = v} := fun v => (h' v).some
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight ev).trans
    (Equiv.sigmaFiberEquiv g)), fun x => ?_⟩
  exact (ev (f x) ⟨x, rfl⟩).2
end PI.MSC
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC
namespace PI.MSC
theorem _root_.solution (R : Type) [CommRing R] (ν : YoungDiagram) (N : ℕ) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ ν.colLen 0) (I : ∀ k, Fin (sz k) → Fin N) (hI : ∀ k, StrictMono (I k))
    (hsh : shapeDeg sz = nuR ν) :
    ∃ J : ∀ c : Fin (ν.rowLen 0), Fin (sz0 ν c) → Fin N, (∀ c, StrictMono (J c)) ∧
      bideterminant R sz hsz I = bideterminant R (sz0 ν) (hsz0 ν) J := by
  classical
  have hcnt : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card =
      (Finset.univ.filter fun c : Fin (ν.rowLen 0) => t < ν.colLen c).card := by
    intro t
    rw [card_colLen_gt]
    by_cases ht : t < ν.colLen 0
    · have h := congrFun hsh ⟨t, ht⟩
      simpa [shapeDeg, nuR] using h
    · rw [rowLen_eq_zero ν (not_lt.1 ht), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      have := hsz k
      omega
  have hfib : ∀ v, 0 < v → (Finset.univ.filter fun k => sz k = v).card =
      (Finset.univ.filter fun c : Fin (ν.rowLen 0) => ν.colLen c = v).card := by
    intro v hv
    have h1 := card_fiber sz hv
    have h2 : (Finset.univ.filter fun c : Fin (ν.rowLen 0) => ν.colLen c = v).card +
        (Finset.univ.filter fun c : Fin (ν.rowLen 0) => v < ν.colLen c).card =
        (Finset.univ.filter fun c : Fin (ν.rowLen 0) => v - 1 < ν.colLen c).card :=
      card_fiber (fun c : Fin (ν.rowLen 0) => ν.colLen c) hv
    rw [hcnt, hcnt] at h1
    omega
  have hcard : ∀ v, Nat.card {x : {k : Fin K // 0 < sz k} // sz x.1 = v} =
      Nat.card {c : Fin (ν.rowLen 0) // ν.colLen c = v} := by
    intro v
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [Fintype.card_eq_zero_iff.2 ⟨fun x => by have := x.2; have := x.1.2; omega⟩,
        Fintype.card_eq_zero_iff.2 ⟨fun c => by have := c.2; have := colLen_pos ν c.1; omega⟩]
    · rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun k => 0 < sz k)
        (fun k => sz k = v)), Fintype.card_subtype, Fintype.card_subtype, ← hfib v hv]
      have hf : (Finset.univ.filter fun k : Fin K => 0 < sz k ∧ sz k = v) =
          Finset.univ.filter fun k => sz k = v :=
        Finset.filter_congr fun k _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      rw [hf]
  obtain ⟨e, he⟩ := reorder_lemma (fun x : {k : Fin K // 0 < sz k} => sz x.1)
    (fun c : Fin (ν.rowLen 0) => ν.colLen c) hcard
  have hJ : ∀ c, sz0 ν c = sz (e.symm c).1 := by
    intro c
    have h := he (e.symm c)
    rw [e.apply_symm_apply] at h
    exact h
  refine ⟨fun c => I (e.symm c).1 ∘ Fin.cast (hJ c), fun c => ?_, ?_⟩
  · intro a b hab
    exact hI _ hab
  · unfold bideterminant
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => 0 < sz k)]
    have h1 : ∏ k : {k // ¬ 0 < sz k}, initMinor R (I k.1) (hsz k.1) = 1 :=
      Finset.prod_eq_one fun k _ => initMinor_zero R (by have := k.2; omega) _ _
    rw [h1, mul_one]
    exact (Fintype.prod_equiv e.symm _ _
      (fun c => initMinor_cast R (hJ c) (I (e.symm c).1) (hsz _) (hsz0 ν c))).symm
end PI.MSC
