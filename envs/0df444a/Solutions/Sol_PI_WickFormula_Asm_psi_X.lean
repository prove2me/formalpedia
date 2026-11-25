-- Prove2me | solution 1 for PI.WickFormula.Asm.psi_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:13.096981+00:00
-- url     : https://prove2.me/submissions/93a2aafe-4b5d-45e1-b471-4d9dff003dfd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
import Theorems.Thm_PI_WickFormula_Asm_tH_zero_X
import Theorems.Thm_PI_WickFormula_Asm_tH_succ_X

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
    (i : Fin r) (N : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    psi h1 a a' κ σ₀ (N + 1) (X (Sum.inl i) * R) =
      a i • psi h1 a a' κ σ₀ (N + 1) R + psi h1 a a' κ σ₀ N (Gen.dL κ i R) := by
  unfold psi
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun n => tH h1 a a' κ σ₀ n R)]
  simp only [tH_succ_X h1 h2 g1 g2 H, tH_zero_X h1 h2 H, Finset.sum_add_distrib, smul_add,
    Finset.smul_sum]
  abel
end PI.WickFormula.Asm
