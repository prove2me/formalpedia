-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.PosH.sup_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:42.419934+00:00
-- url     : https://prove2.me/submissions/d9951b62-d465-4c62-979b-ef48c3dc9f57

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SupPerp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_inf_perp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_sum_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}
open PositivityTheory.Rg.Sw.LC.CoreA.PosH
variable (h : PosH φ)
include h
namespace PositivityTheory.Rg.Sw.LC.CoreA.PosH
theorem _root_.solution [FiniteDimensional ℂ V] (W : Submodule ℂ V) : W ⊔ h.perp W = ⊤ := by
  classical
  let b := Module.finBasis ℂ W
  let L : V →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun v k => φ (b k : V) v
      map_add' := fun v w => by funext k; exact h.add _ v w
      map_smul' := fun r v => by funext k; simp [h.smul] }
  have hker : LinearMap.ker L ≤ h.perp W := by
    intro v hv w hw
    have hv' : ∀ k, φ (b k : V) v = 0 := fun k => congrFun (LinearMap.mem_ker.1 hv) k
    have hw' : w = ∑ k, (b.repr ⟨w, hw⟩ k) • (b k : V) := by
      have h2 : ((∑ k, b.repr ⟨w, hw⟩ k • b k : W) : V) = w := by rw [b.sum_repr]
      rw [Submodule.coe_sum] at h2
      simp only [Submodule.coe_smul] at h2
      exact h2.symm
    rw [hw', h.sum_left]
    simp [hv']
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hr : Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ W := by
    calc Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ (Fin (Module.finrank ℂ W) → ℂ) :=
          Submodule.finrank_le _
      _ = Module.finrank ℂ W := by simp
  have hk : Module.finrank ℂ (LinearMap.ker L) ≤ Module.finrank ℂ (h.perp W) := Submodule.finrank_mono hker
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (h.perp W)
  rw [h.inf_perp, finrank_bot] at hsum
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  omega
end PositivityTheory.Rg.Sw.LC.CoreA.PosH
