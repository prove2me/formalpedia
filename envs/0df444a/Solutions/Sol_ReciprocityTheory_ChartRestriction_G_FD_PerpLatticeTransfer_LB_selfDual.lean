-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.LB_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:19.760005+00:00
-- url     : https://prove2.me/submissions/bf812fd2-dc20-4ffe-a054-0aa0d0453070

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_Sform_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_herm_perp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_herm_cross
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_add_right__436ee063c834
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_herm_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermitian_lattice_pairing_duality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
theorem _root_.solution (hξ : X.IsIso ξ) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin n → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    ReciprocityTheory.MultiplicativeHeights.IsSelfDual (Sform X β) (LBsub X β ξ) := by
  refine ⟨?_, ?_⟩
  · rintro c ⟨e, he⟩ c' ⟨e', he'⟩
    rw [Sform_h, ← herm_cross X β ξ hβξ hξ.2.1 c c' e e']
    exact ⟨⟨_, X.L'_int _ he' _ he⟩, rfl⟩
  · intro c hc
    obtain ⟨e, he⟩ := hermitian_lattice_pairing_duality r X ξ hξ (∑ k, c k • β k) (herm_perp X β ξ hβξ c) (by
      intro y hy hyξ
      obtain ⟨c', e', rfl⟩ := hspan y hyξ
      have hc' : c' ∈ LBsub X β ξ := ⟨e', hy⟩
      obtain ⟨z, hz⟩ := hc c' hc'
      rw [Sform_h] at hz
      have h1 : herm X.Gm (∑ k, c k • β k) (∑ k, c' k • β k + e' • ξ) =
          cc (herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k)) := by
        rw [herm_add_right', HermitianTraceFormVanishing.herm_smul_right, herm_perp X β ξ hβξ c, mul_zero, add_zero,
          HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm]
      rw [h1, ← hz]
      exact isIntegral_cc (RingOfIntegers.isIntegral_coe z))
    exact ⟨e, he⟩
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
