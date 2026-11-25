-- Prove2me | solution 1 for PI.WickFormula.Asm.psi_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:26:53.571865+00:00
-- url     : https://prove2.me/submissions/ca53c94e-c771-4580-8b4b-b8297b9ee5f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
import Theorems.Thm_PI_WickFormula_Asm_ordEval_zero
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
theorem _root_.solution (h1 : OrdLin) (g3 : Gen.VanL) (N : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k)
    (hR : ∀ m ∈ R.support, xdeg m = 0) :
    psi h1 a a' κ σ₀ (N + 1) R = ordEval a a' R • σ₀ := by
  unfold psi
  rw [Finset.sum_range_succ']
  have hz : ∀ n, tH h1 a a' κ σ₀ (n + 1) R = 0 := by
    intro n
    have hd : delta κ = Gen.gdelta κ := rfl
    rw [tH_apply, hd, g3 k (Fin r) (Fin s) κ R (n + 1) (fun m hm => by
      have := hR m hm
      unfold xdeg at this
      omega), smul_zero, ordEval_zero h1, zero_smul]
  simp only [hz, Finset.sum_const_zero, zero_add, tH_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, pow_zero, Module.End.one_apply]
end PI.WickFormula.Asm
