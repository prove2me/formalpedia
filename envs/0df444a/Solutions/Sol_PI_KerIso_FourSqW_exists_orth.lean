-- Prove2me | solution 1 for PI.KerIso.FourSqW.exists_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:45.013541+00:00
-- url     : https://prove2.me/submissions/fc279437-a867-4ccf-bd43-d3ee71c88c8c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Theorems.Thm_PI_KerIso_FourSqW_trL_apply
import Theorems.Thm_PI_KerIso_FourSqW_tr_swap_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KerIso.FourSqW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) :
    ∀ m : ℕ, m ≤ finrank K E → ∃ e : Fin m → E, (∀ i, e i ≠ 0) ∧
      ∀ i j, i ≠ j → Algebra.trace K E (e i * cj (e j)) = 0 := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨e, he0, heo⟩ := ih (by omega)
    let F : E →ₗ[K] (Fin m → K) := LinearMap.pi (fun i => trL cj (e i))
    have hF : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fin_fun]; omega)
    obtain ⟨x, hxk, hx0⟩ := (Submodule.ne_bot_iff _).mp hF
    have hxo : ∀ i, Algebra.trace K E (x * cj (e i)) = 0 := by
      intro i
      have := congrArg (fun f => f i) (LinearMap.mem_ker.mp hxk)
      simpa [F, trL_apply] using this
    refine ⟨Fin.snoc e x, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hx0
      · simpa using he0 i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using hxo j
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using tr_swap_zero cj hc _ _ (hxo i)
        | cast j =>
          have : i ≠ j := fun h => hij (by rw [h])
          simpa using heo i j this
end PI.KerIso.FourSqW
