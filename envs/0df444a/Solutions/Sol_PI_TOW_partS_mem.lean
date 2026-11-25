-- Prove2me | solution 1 for PI.TOW.partS_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:26.615662+00:00
-- url     : https://prove2.me/submissions/9d10c0cd-8b64-44a5-831c-d5988b4472bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength

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
open PI PI.TOW
open PI.TO
namespace PI.TOW
theorem _root_.solution {K : Type} [CommRing K] {n' m : ℕ} {d : Fin n' → ℕ} (μ : Fin n' × Fin (m + 1) →₀ ℕ)
    (hμ : μ ∈ {μ : Fin n' × Fin (m + 1) →₀ ℕ | ∀ i, multideg μ i = d i}) (t : Fin n') :
    monomial (partS μ t) (1 : K) ∈ Hd K (m + 1) (d t) := by
  show monomial (partS μ t) (1 : K) ∈ restrictSupport K {ν : Fin (m + 1) →₀ ℕ | ∑ c, ν c = d t}
  rw [mem_restrictSupport_iff]
  intro x hx
  have hx' := support_monomial_subset hx
  rw [Finset.mem_singleton] at hx'
  subst hx'
  have h := hμ t
  simpa [partS, multideg] using h
end PI.TOW
