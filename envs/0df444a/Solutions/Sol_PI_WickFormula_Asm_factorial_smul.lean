-- Prove2me | solution 1 for PI.WickFormula.Asm.factorial_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:07.367941+00:00
-- url     : https://prove2.me/submissions/fde19ff9-0362-41df-828c-52969bb02ba7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}
namespace PI.WickFormula.Asm
theorem _root_.solution (n : ℕ) (S : MvPolynomial (Fin r ⊕ Fin s) k) :
    (((n + 1).factorial : ℚ)⁻¹ • ((n + 1) • S)) = ((n.factorial : ℚ)⁻¹ • S) := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
end PI.WickFormula.Asm
