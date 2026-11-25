-- Prove2me | solution 1 for P2M_PI_FockOneDegW_Core_exists_monomial_weight__7e76f9f36b77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:28.134175+00:00
-- url     : https://prove2.me/submissions/a39cefd6-b6fd-40f3-995c-a47d0fcc5609

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Diag_coeff_of_diag


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
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution {σ ι : Type*} [Fintype σ]
    (T : ι → Module.End ℂ (MvPolynomial σ ℂ)) (f : ι → (σ →₀ ℕ) → ℚ)
    (hT : ∀ a β, T a (MvPolynomial.monomial β 1) =
      ((f a β : ℚ) : ℂ) • MvPolynomial.monomial β 1)
    (μ : ι → ℚ) (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P ∈ homog σ d) (h0 : P ≠ 0)
    (hw : ∀ a, (T a - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ (MvPolynomial σ ℂ))) P = 0) :
    ∃ α : σ →₀ ℕ, MvPolynomial.coeff α P ≠ 0 ∧ ∑ i, α i = d ∧ ∀ a, μ a = f a α := by
  obtain ⟨α, hα⟩ := MvPolynomial.exists_coeff_ne_zero h0
  refine ⟨α, hα, ?_, fun a => ?_⟩
  · have hh : P.IsHomogeneous d := hP
    by_contra hne
    exact hα (hh.coeff_eq_zero (by rwa [Finsupp.degree_eq_sum]))
  · have h1 := congrArg (MvPolynomial.coeff α) (hw a)
    rw [LinearMap.sub_apply, MvPolynomial.coeff_sub,
      coeff_of_diag (T a) (fun β => ((f a β : ℚ) : ℂ)) (hT a),
      LinearMap.smul_apply, LinearMap.id_apply, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero,
      smul_eq_mul, ← sub_mul] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_right hα
    exact_mod_cast (sub_eq_zero.1 h2).symm
end PI.FockOneDegW.Core
