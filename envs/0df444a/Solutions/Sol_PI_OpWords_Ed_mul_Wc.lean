-- Prove2me | solution 1 for PI.OpWords.Ed_mul_Wc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:53.512498+00:00
-- url     : https://prove2.me/submissions/d3f5e9f4-c068-46da-a6d8-94d84ed0344d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable (K : Type) [Field K] [CharZero K] (k d : ℕ)
namespace PI.OpWords
theorem _root_.solution (c : ℕ) (a b : Fin k) {B : Module.End K ↥(homogeneousSubmodule (Fin k) K d)}
    (hB : B ∈ Wc K k d c) : Formalism.MainNotions.TestSideCounting.Ed K k d a b * B ∈ Wc K k d (c + 1) := by
  unfold Wc at hB ⊢
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨(a, b) :: l, by simpa using hl, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx
end PI.OpWords
