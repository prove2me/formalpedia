-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFibreTor_mem_of_smul_mem_2be63fe3ed26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:35.236279+00:00
-- url     : https://prove2.me/submissions/f99b41b9-5ab1-4f1f-b0eb-78728b1c66d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreTor

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace GenericFibreTor
theorem _root_.solution {σ ι : Type*} (t : σ → ℂ)
    (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) {x : MvPolynomial ι (MvPolynomial σ ℂ)} (hx : x ∈ L)
    {u : MvPolynomial σ ℂ} (hu : eval t u ≠ 0)
    (h : u • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L) :
    x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
  set J := (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L
  rw [smul_eq_C_mul] at h
  have h1 : C (u - MvPolynomial.C (eval t u)) * x ∈ J :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])) hx
  have h2 : C (MvPolynomial.C (eval t u)) * x ∈ J := by
    have := J.sub_mem h h1
    rwa [← sub_mul, ← map_sub, sub_sub_cancel] at this
  have hunit : IsUnit (C (MvPolynomial.C (eval t u)) : MvPolynomial ι (MvPolynomial σ ℂ)) :=
    (hu.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ))
  exact (Ideal.unit_mul_mem_iff_mem J hunit).1 h2
end GenericFibreTor
end GroundTheory.Heights₂.Heights
