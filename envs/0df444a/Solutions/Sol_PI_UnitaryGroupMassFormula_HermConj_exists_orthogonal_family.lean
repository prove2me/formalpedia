-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:06.453864+00:00
-- url     : https://prove2.me/submissions/d4d285db-c554-409b-87ff-32d06c4c63c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
import Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_IsHermForm_eq_zero_of_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HermConj
open Matrix
variable {E : Type} [Field E]
namespace PI.UnitaryGroupMassFormula.HermConj
theorem _root_.solution [CharZero E] (σ : E →+* E) :
    ∀ (k : ℕ) (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V],
      Module.finrank E V = k → ∀ h : V → V → E, IsHermForm σ h →
        ∃ v : Fin k → V, LinearIndependent E v ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 := by
  intro k
  induction k with
  | zero =>
    intro V _ _ _ hk h hh
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro V _ _ _ hk h hh
    by_cases hzero : ∀ x, h x x = 0
    · let b := Module.finBasisOfFinrankEq E V hk
      exact ⟨b, b.linearIndependent, fun i j _ => hh.eq_zero_of_diag hzero _ _⟩
    · push_neg at hzero
      obtain ⟨v, hv⟩ := hzero
      let f : V →ₗ[E] E :=
        { toFun := h v
          map_add' := hh.add v
          map_smul' := fun a y => by
            simp only [RingHom.id_apply, smul_eq_mul]
            exact hh.smul v a y }
      have hfv : ∀ y, f y = h v y := fun _ => rfl
      have hf : f v ≠ 0 := hv
      have hsurj : Function.Surjective f := by
        intro c
        refine ⟨(c / f v) • v, ?_⟩
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf]
      have hW : Module.finrank E (LinearMap.ker f) = k := by
        have := LinearMap.finrank_range_add_finrank_ker f
        rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at this
        omega
      obtain ⟨w, hwi, hwo⟩ := ih (LinearMap.ker f) hW (fun x y => h x y)
        ⟨fun x y z => hh.add _ _ _, fun x a y => hh.smul _ _ _, fun x y => hh.herm _ _⟩
      have hw0 : ∀ i, h v (w i) = 0 := fun i => by
        rw [← hfv]; exact LinearMap.mem_ker.1 (w i).2
      refine ⟨Fin.cons v (fun i => (w i : V)), ?_, ?_⟩
      · rw [linearIndependent_fin_cons]
        refine ⟨hwi.map' (LinearMap.ker f).subtype (Submodule.ker_subtype _), ?_⟩
        intro hmem
        have hle : Submodule.span E (Set.range fun i => (w i : V)) ≤ LinearMap.ker f :=
          Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (w i).2)
        exact hf (LinearMap.mem_ker.1 (hle hmem))
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hw0 j
        | succ i =>
          cases j using Fin.cases with
          | zero =>
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hh.herm, hw0 i, map_zero]
          | succ j =>
            simp only [Fin.cons_succ]
            exact hwo i j (fun e => hij (by rw [e]))
end PI.UnitaryGroupMassFormula.HermConj
