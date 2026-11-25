-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_exists_relComps_of_mem_incidence_field_506d0f3a1809
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:38.252683+00:00
-- url     : https://prove2.me/submissions/6c71dc74-4f3d-4ad9-b1ad-60521bed39c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSpecFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecFirstNeField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {F : Type*} [Field F] {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) F)} {v : Fin k × Fin n → AlgebraicClosure F}
    (hv : v ∈ incidence J k) : ∃ W ∈ relComps J, v ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxv⟩ := hv
  have hP : (RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F)).IsPrime :=
    RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) :=
    fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxv⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  simpa using RingHom.mem_ker.mp (hWP hj)
end GroundTheory.Heights₂.Heights.Vertical
