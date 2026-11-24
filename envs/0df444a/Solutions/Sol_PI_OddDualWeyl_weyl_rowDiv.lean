-- Prove2me | solution 1 for PI.OddDualWeyl.weyl_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:02.938591+00:00
-- url     : https://prove2.me/submissions/8761d4d9-05e4-41ad-89a9-7912c83b9eb8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
variable {R : Type} [CommRing R] {k M : ℕ}
namespace PI.OddDualWeyl
theorem _root_.solution {ν : Fin k → ℕ} (a b : Fin k) (j : ℕ) {f : MvPolynomial (Fin k × Fin k) R}
    (hf : f ∈ weyl R k k le_rfl ν) : rowDiv R a b j f ∈ weyl R k k le_rfl ν := by
  have key : weyl R k k le_rfl ν ≤ (weyl R k k le_rfl ν).comap (rowDivL a b j) := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, j) :: w, rfl⟩
  exact key hf
end PI.OddDualWeyl
