-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_L4_hwProj_comm__9e268cd004a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:24.567219+00:00
-- url     : https://prove2.me/submissions/c3385ff5-69c6-4b74-b9fa-e6948433a35a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_proj_comm_abs__dd44a5ea645a
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_lowIm_keep__abc410c6108a
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (ρ : Fin r) (la : Fin r → ℤ)
    (PE A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la)
    (h3 : LinearMap.ker PE ⊓ WtSpC p LL j univ la = lowIm' p LL j ρ ⊓ WtSpC p LL j univ la)
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x))
    (hW : ∀ x ∈ WtSpC p LL j univ la, A x ∈ WtSpC p LL j univ la) :
    ∀ x ∈ WtSpC p LL j univ la, PE (A x) = A (PE x) := by
  have hsub : WtSpC p LL j univ la ≤ WtSpC p LL j (univ.erase ρ) la := by
    intro x hx
    simp only [WtSpC, MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Finsupp.mem_supported, Submodule.mem_comap,
      LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply] at hx ⊢
    intro m hm c _
    exact hx (show m ∈ (↑x.support : Set _) from hm) c (Finset.mem_univ c)
  have hR : ∀ x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la,
      A x ∈ HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la := by
    intro x hx
    have hAx := hW x hx.2
    refine ⟨?_, hAx⟩
    have hx1 : x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d) := hx.1
    show A x ∈ WtSpC p LL j (univ.erase ρ) la ⊓
        ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ c < d), LinearMap.ker (glAct p LL j c d)
    rw [Submodule.mem_inf] at hx1 ⊢
    refine ⟨hsub hAx, ?_⟩
    have hx2 := hx1.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
    intro c d hcd
    rw [← hA c hcd.1 d hcd.2.1, hx2 c d hcd, map_zero]
  have h2' : LinearMap.range PE
      = (HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la) ⊓ WtSpC p LL j univ la := by
    rw [h2, inf_assoc, inf_idem]
  exact proj_comm_abs' PE A _ _ _ h1 h2' h3 hR hW (lowIm_keep' LL j ρ A hA)
end Formalism.InvariantFactorPaths.L4
