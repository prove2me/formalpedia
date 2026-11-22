-- Prove2me | solution 1 for UpperTheory.Reformulated.B.IsPFSum.isPF_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:54.332558+00:00
-- url     : https://prove2.me/submissions/89836d1d-4877-4a90-b515-dc48f655d605

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPF
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IsPFSum
theorem _root_.solution :
    ∀ {A : Type} [inst : Ring A] [inst_1 : Algebra ℂ A] {ι : Type} (s : Finset ι) {f : ι → ℂ → A},
      (∀ i ∈ s, UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF (f i)) → UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF fun (Y : ℂ) ↦ ∑ i ∈ s, f i Y := by
  intro A _ _ ι s f h
  classical
  unfold UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF at h ⊢
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun Y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨q, hq⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨p + q, fun Y => ?_⟩
    have h1 : (∑ i ∈ s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) q := hq Y
    show (∑ i ∈ insert a s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) (p + q)
    rw [Finset.sum_insert ha, hp, h1, Polynomial.eval_add]
end UpperTheory.Reformulated.B.IsPFSum
