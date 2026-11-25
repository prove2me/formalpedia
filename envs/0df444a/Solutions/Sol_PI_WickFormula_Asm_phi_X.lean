-- Prove2me | solution 1 for PI.WickFormula.Asm.phi_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:15:47.20486+00:00
-- url     : https://prove2.me/submissions/51f8f982-09d3-477f-aef7-be3d7fee2992

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
import Theorems.Thm_PI_WickFormula_Asm_phiH_apply

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
theorem _root_.solution (h1 : OrdLin) (h2 : OrdX) (h4 : BComm) (H : Hyp a b a' b' κ σ₀) (i : Fin r)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    phiH h1 a b a' b' σ₀ (X (Sum.inl i) * R) =
      a i • phiH h1 a b a' b' σ₀ R + phiH h1 a b a' b' σ₀ (Gen.dL κ i R) := by
  have hc : ∀ i i', Commute ((a + b) i) ((a + b) i') := by
    intro i i'
    simp only [Pi.add_apply]
    exact ((H.h1 i i').1.add_right (H.h1 i i').2.1).add_left
      (((H.h1 i' i).2.1.symm).add_right (H.h1 i i').2.2)
  simp only [phiH_apply]
  rw [h2 k AA r s (a + b) (a' + b') hc i R, Pi.add_apply, add_mul, add_smul, mul_smul, mul_smul,
    h4 k AA M r s a b a' b' κ σ₀ H i R]
end PI.WickFormula.Asm
