-- Prove2me | solution 1 for PI.KoszulExact.weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:14:28.293476+00:00
-- url     : https://prove2.me/submissions/b2e0a5df-3081-4634-a6b2-6a5a7c7ca086

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_OfListTakeOfFn
import Theorems.Thm_PI_KoszulExact_ofList_take_ofFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
open RingTheory.Sequence
namespace PI.KoszulExact
theorem _root_.solution {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R)
    (hs : IsWeaklyRegular R (List.ofFn s)) (i : Fin D) (r : R) (hr : s i * r ∈ Ii s i) :
    r ∈ Ii s i := by
  have key := hs.regular_mod_prev i (by simp)
  have hsm : (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R) = Ii s i := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ofList_take_ofFn]
  have e : (List.ofFn s)[(i : ℕ)]'(by simp) = s i := by simp
  rw [e] at key
  have h1 : s i • (Submodule.Quotient.mk r :
      R ⧸ (Ideal.ofList ((List.ofFn s).take i) • ⊤ : Submodule R R)) = s i • 0 := by
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, smul_eq_mul]
    exact hr
  have h2 := key h1
  rwa [Submodule.Quotient.mk_eq_zero, hsm] at h2
end PI.KoszulExact
