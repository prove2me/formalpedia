-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_fibreVec_lineCoef_72af0e9a7beb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:35.90907+00:00
-- url     : https://prove2.me/submissions/b5e22240-9118-4691-9a59-d597208326eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulEqSmulOfFinrankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_eq_aad90511fb53

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K}
variable {N : Submodule (𝓞 K) E.carrier} (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier}
  (hl : l ∈ N) (hl0 : l ≠ 0)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution (σ : K →+* ℂ) (w : N) :
    fibreVec E.metric σ (w : E.carrier) = σ (lineCoef hN hl hl0 w) • fibreVec E.metric σ l := by
  obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
  have hst : σ (t : K) ≠ 0 := by rw [map_ne_zero]; exact_mod_cast ht
  have h1 := congrArg (fibreVec E.metric σ) h
  rw [fibreVec_smul, fibreVec_smul] at h1
  rw [lineCoef_eq hN hl hl0 w ht h, map_div₀, div_eq_inv_mul, mul_smul, ← h1, smul_smul,
    inv_mul_cancel₀ hst, one_smul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
