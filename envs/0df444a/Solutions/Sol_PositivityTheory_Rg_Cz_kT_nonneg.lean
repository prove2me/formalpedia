-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kT_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:41.768874+00:00
-- url     : https://prove2.me/submissions/f306edca-4013-4862-a834-ee297d97ac67

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KugaAbsHolds
import Theorems.Thm_PositivityTheory_Rg_Cz_kIp_kD
import Theorems.Thm_PositivityTheory_Rg_Cz_kD_kDel
import Theorems.Thm_PositivityTheory_Rg_Cz_kB_re_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_KAdjoint_kIp_kD


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution {β : Type} [Fintype β] (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P)
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (hB : ∀ x y, B y x = starRingEnd ℂ (B x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re) (hTT : ∀ X x y, B (T X x) y = B x (T' X y))
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M) :
    0 ≤ (∑ J : Fin q → β, B (ω (b ∘ J))
      (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i)))))).re := by
  cases q with
  | zero => simp
  | succ n =>
    have h1 : ∀ J : Fin (n + 1) → β, (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i))))) =
        kD T (kDel T' b ω) (b ∘ J) := fun J => (kD_kDel T T' b ω (b ∘ J)).symm
    simp_rw [h1]
    have h2 : (∑ J : Fin (n + 1) → β, B (ω (b ∘ J)) (kD T (kDel T' b ω) (b ∘ J))) =
        starRingEnd ℂ (kIp B b (kD T (kDel T' b ω)) ω) := by
      unfold kIp
      rw [map_sum]
      exact Finset.sum_congr rfl fun J _ => hB _ _
    rw [h2, kIp_kD B b T T' hTT (kDel T' b ω) ω, Complex.conj_re, Complex.mul_re]
    have : (((n : ℂ) + 1)).im = 0 := by simp
    rw [this, zero_mul, sub_zero]
    have : (((n : ℂ) + 1)).re = (n : ℝ) + 1 := by simp
    rw [this]
    apply mul_nonneg (by positivity)
    unfold kIp
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun J _ => kB_re_nonneg B hpos _
end PositivityTheory.Rg.Cz
