-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_psiQ_mk_c419026b54a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:13.106252+00:00
-- url     : https://prove2.me/submissions/2191549e-d0f7-409a-b8f4-2adad2d5a491

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)
  (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution (hPh : IsMultiHomogIdeal P) (f : MRing ι R) :
    psiQ T hPW hT hPh (Ideal.Quotient.mk P f) = psi T hT f := Ideal.Quotient.lift_mk _ _ _
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
