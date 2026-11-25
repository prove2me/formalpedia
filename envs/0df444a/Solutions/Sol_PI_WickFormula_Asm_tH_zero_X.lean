-- Prove2me | solution 1 for PI.WickFormula.Asm.tH_zero_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:08.396391+00:00
-- url     : https://prove2.me/submissions/be6b2771-efa1-420e-b4e8-68bb4cb076f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
import Theorems.Thm_PI_WickFormula_Asm_tH_apply

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
variable {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}
namespace PI.WickFormula.Asm
theorem _root_.solution (h1 : OrdLin) (h2 : OrdX) (H : Hyp a b a' b' κ σ₀) (i : Fin r)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ 0 (X (Sum.inl i) * R) = a i • tH h1 a a' κ σ₀ 0 R := by
  simp only [tH_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply]
  rw [h2 k AA r s a a' (fun i i' => (H.h1 i i').1) i R, mul_smul]
end PI.WickFormula.Asm
