-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_dualLattice_inv_smul_6bc15559e293
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:51.499238+00:00
-- url     : https://prove2.me/submissions/2eb2ae66-25d0-42ac-a3b2-f895dc3d21a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdaptedReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sesq_unitary_smul_183a127d023b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (g : h.unitaryGroup) (La : AddSubgroup W) :
    dualLattice h (g⁻¹ • La) = g⁻¹ • dualLattice h La := by
  ext y
  rw [mem_inv_smul_iff]
  change (∀ x ∈ g⁻¹ • La, h.toSesq y x ∈ integralClosure ℤ E) ↔
    ∀ x ∈ La, h.toSesq (g • y) x ∈ integralClosure ℤ E
  constructor
  · intro hy x hx
    have hx' : g⁻¹ • x ∈ g⁻¹ • La := by rw [mem_inv_smul_iff, smul_inv_smul]; exact hx
    have := hy _ hx'
    rwa [← sesq_unitary_smul g, smul_inv_smul] at this
  · intro hy x hx
    rw [mem_inv_smul_iff] at hx
    rw [← sesq_unitary_smul g]
    exact hy _ hx
end GroundTheory.Heights₂.Heights.FiniteCovolume
