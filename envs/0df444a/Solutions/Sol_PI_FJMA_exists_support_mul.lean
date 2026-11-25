-- Prove2me | solution 1 for PI.FJMA.exists_support_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:44.143347+00:00
-- url     : https://prove2.me/submissions/7e4b76aa-b644-4335-ae0f-e5dcee338acd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
import Theorems.Thm_PI_FJMA_vars_zero_of_supported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable {σ : Type}
namespace PI.FJMA
theorem _root_.solution {S : Set σ} {F G : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) (hF0 : F ≠ 0)
    (hG : FreeOf S G) {e' : σ →₀ ℕ} (he' : e' ∈ G.support) :
    ∃ e ∈ (F * G).support, ∀ v ∉ S, e v = e' v := by
  classical
  obtain ⟨e0, he0⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hF0)
  have hvars := vars_zero_of_supported hF
  refine ⟨e0 + e', ?_, fun v hv => by simp [hvars e0 he0 v hv]⟩
  rw [mem_support_iff, coeff_mul, Finset.sum_eq_single (e0, e')]
  · exact mul_ne_zero (mem_support_iff.1 he0) (mem_support_iff.1 he')
  · rintro ⟨x, y⟩ hxy hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
    by_contra h
    have hx : x ∈ F.support := mem_support_iff.2 (left_ne_zero_of_mul h)
    have hy : y ∈ G.support := mem_support_iff.2 (right_ne_zero_of_mul h)
    apply hne
    have h1 : x = e0 := by
      ext v
      have := congrArg (fun f => f v) hxy
      simp only [Finsupp.add_apply] at this
      by_cases hv : v ∈ S
      · rw [hG y hy v hv, hG e' he' v hv] at this; omega
      · rw [hvars x hx v hv, hvars e0 he0 v hv]
    subst h1
    have h2 : y = e' := by
      ext v
      have := congrArg (fun f => f v) hxy
      simp only [Finsupp.add_apply] at this
      omega
    subst h2
    rfl
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (show (e0, e').1 + (e0, e').2 = e0 + e' from rfl)) h
end PI.FJMA
