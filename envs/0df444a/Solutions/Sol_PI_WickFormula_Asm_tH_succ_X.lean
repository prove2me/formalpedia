-- Prove2me | solution 1 for PI.WickFormula.Asm.tH_succ_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:22:57.141964+00:00
-- url     : https://prove2.me/submissions/7dce88ee-aeaa-4e8f-9875-9ab84c4e873f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
import Theorems.Thm_PI_WickFormula_Asm_tH_apply
import Theorems.Thm_PI_WickFormula_Asm_factorial_smul

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
theorem _root_.solution (h1 : OrdLin) (h2 : OrdX) (g1 : Gen.PowXL) (g2 : Gen.CommL) (H : Hyp a b a' b' κ σ₀)
    (i : Fin r) (n : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ (n + 1) (X (Sum.inl i) * R) =
      a i • tH h1 a a' κ σ₀ (n + 1) R + tH h1 a a' κ σ₀ n (Gen.dL κ i R) := by
  simp only [tH_apply]
  have hd : delta κ = Gen.gdelta κ := rfl
  rw [hd, g1 k (Fin r) (Fin s) κ i R n, g2 k (Fin r) (Fin s) κ i R n, smul_add, factorial_smul,
    ← mul_smul_comm, ordEval_add h1, h2 k AA r s a a' (fun i i' => (H.h1 i i').1) i, add_smul,
    mul_smul]
end PI.WickFormula.Asm
