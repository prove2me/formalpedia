-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_proof_31a64a79b68f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:26.86267+00:00
-- url     : https://prove2.me/submissions/6cf1a4ef-de6e-47e6-8fac-b0836446e777

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_isMultiHomogIdeal_map_81a0ea2d0932
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chain_245c974d72d6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocRankAdjoin
theorem _root_.solution (hF : SemilocRankFrac.Statement) (hT : ChartScalingIndep.Statement) :
    SemilocRankAdjoin.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G s α W i' hv hP' hZ hs hsP hW hi'

  have hker : ∀ f : MRing ι', aeval G.x' f = 0 ↔ f ∈ P' := fun f => by rw [← RingHom.mem_ker, G.genericFibre_ker_target]
  have : CharZero G.Φ' := charZero_of_inj_zero fun m hm => by
    have h : (C (m : ℤ) : MRing ι') ∈ P' := (hker _).1 (by rw [aeval_C]; exact_mod_cast hm)
    have h' : (m : ℤ) ∈ P'.comap (C : ℤ →+* MRing ι') := h
    rw [hP'.2.2.1, Ideal.mem_bot] at h'
    exact_mod_cast h'
  have : CharZero G.Φ := (RingHom.charZero_iff (algebraMap G.Φ G.Φ').injective).2 inferInstance
  have : IsScalarTower ℚ G.Φ G.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

  have hkerQ : RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ') =
      P'.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι' →+* MRingOver ℚ ι') := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k', ι' k') (R := ℤ) (S := ℚ)
    have _ : IsLocalization ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι') :=
      MvPolynomial.isLocalization _ _
    refine (IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι')
      (RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ'))).symm.trans ?_
    congr 1
    ext f
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_def, aeval_map_algebraMap, hker]
  have hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hi' k' ((hker _).1 (by rw [aeval_X, h]))
  rw [hF K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi',
    SemilocRankAdjoin.chain hT G i' ℚ hv hx (hkerQ ▸ SemilocRankAdjoin.isMultiHomogIdeal_map hP'.2.1.2.1)]
end SemilocRankAdjoin
end GroundTheory.Heights₂.Heights.Inter
