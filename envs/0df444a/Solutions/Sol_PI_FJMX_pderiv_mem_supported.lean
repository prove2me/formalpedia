-- Prove2me | solution 1 for PI.FJMX.pderiv_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:14:28.544306+00:00
-- url     : https://prove2.me/submissions/447b737f-00e4-4d35-81a8-ac051049df76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Theorems.Thm_PI_FJMX_pderiv_eq_zero_of_supported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.FJMX
theorem _root_.solution {S : Set σ} {f : MvPolynomial σ R} (hf : f ∈ supported R S)
    (v : σ) : pderiv v f ∈ supported R S := by
  classical
  by_cases hv : v ∈ S
  · rw [supported_eq_range_rename] at hf ⊢
    obtain ⟨g, rfl⟩ := hf
    have := pderiv_rename (R := R) Subtype.val_injective (⟨v, hv⟩ : S) g
    simp only at this
    change pderiv v (rename Subtype.val g) ∈ _
    rw [this]
    exact AlgHom.mem_range_self _ _
  · rw [pderiv_eq_zero_of_supported hf hv]
    exact Subalgebra.zero_mem _
end PI.FJMX
