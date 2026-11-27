-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNE_proof_865dae93a4ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:14.956144+00:00
-- url     : https://prove2.me/submissions/214859a0-25c8-45ea-b9b8-aad7fa153dfb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_integral_fin_zero_ff47667ab96f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_exists_goodProj_0a835ee29f11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_bij_fibre_d4c596ff703d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_density_ge_eae28a06c810

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open PtsIntegralZeroLowerNEAux
namespace GroundTheory.Heights₂.Heights
namespace PtsIntegralZeroLowerNE
theorem _root_.solution : PtsIntegralZeroLowerNE.Statement := by
  intro K _ _ ι _ W φ g c hW hfin _ hc
  classical
  obtain ⟨Ψ0, hΨ0⟩ := exists_goodProj hfin
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj W Ψ := ⟨Ψ0, hΨ0⟩
  unfold ptsIntegral
  rw [dif_pos hex]
  have hΨ : IsGoodProj W hex.choose := hex.choose_spec
  let y : Fin 0 → ℂ := fun i => i.elim0
  unfold ptsIntegralAt
  rw [integral_fin_zero _ y]
  obtain ⟨M, hM⟩ := bij_fibre hW hex.choose hΨ y
  have := hfin
  have : Finite (fibre W hex.choose y) := Finite.of_surjective M hM.2
  have hF : (fibre W hex.choose y).Finite := Set.toFinite _
  have hcard : degC W = hF.toFinset.card := by
    rw [← Nat.card_eq_card_finite_toFinset hF, ← Nat.card_eq_of_bijective M hM]
    rfl
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, hcard]
  have h := Finset.card_nsmul_le_sum hF.toFinset (fun w => sheetDensity W hex.choose φ g y w) c
    (fun w hw => density_ge hc ((Set.Finite.mem_toFinset hF).mp hw))
  rw [nsmul_eq_mul] at h
  linarith
end PtsIntegralZeroLowerNE
end GroundTheory.Heights₂.Heights
