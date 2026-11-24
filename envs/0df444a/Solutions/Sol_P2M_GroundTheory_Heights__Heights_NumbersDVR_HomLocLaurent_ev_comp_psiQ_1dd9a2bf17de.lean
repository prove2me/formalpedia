-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_ev_comp_psiQ_1dd9a2bf17de
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:50.464829+00:00
-- url     : https://prove2.me/submissions/bc82486c-6aab-4d98-8bb8-878500cee1b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_psiQ_mk_c419026b54a3

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
theorem _root_.solution (hPh : IsMultiHomogIdeal P) :
    (ev T hPW hT).comp (psiQ T hPW hT hPh) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun f => ?_)
  simp only [RingHom.comp_apply, psiQ_mk]
  rw [← RingHom.comp_apply (ev T hPW hT), ev_comp_psi]
  rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
