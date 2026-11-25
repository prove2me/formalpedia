-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_length_quotient_incAC_b70758caeff4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:06.277269+00:00
-- url     : https://prove2.me/submissions/9937edea-0976-428d-bbf3-696163d664ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_incAC_isLocalHom_02e2103e1a9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_map_maximalIdeal_incAC_0e098a0654dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_flat_incAC_807febf08188

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
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
  (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hT
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution (hPh : IsMultiHomogIdeal P) (hWh : IsMultiHomogIdeal W)
    [IsLocalRing (homLocRing P W)] (a : homLocRing P W) :
    Module.length (locC hPW) (locC hPW ⧸ Ideal.span {incAC hPW a}) =
      Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {a}) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  haveI := IsLocalization.AtPrime.isLocalRing (locC hPW) (W.map (Ideal.Quotient.mk P))
  letI := (incAC hPW).toAlgebra
  haveI : IsLocalHom (algebraMap (homLocRing P W) (locC hPW)) := incAC_isLocalHom T hPW hT
  haveI := flat_incAC T hPW hT hPh
  have key := IsLocalRing.length_baseChange (homLocRing P W) (locC hPW)
    (homLocRing P W ⧸ Ideal.span {a})
  have hm := map_maximalIdeal_incAC T hPW hT hWh
  have h1 : Module.length (locC hPW) (locC hPW ⧸ IsLocalRing.maximalIdeal (locC hPW)) = 1 := by
    have : IsSimpleModule (locC hPW) (locC hPW ⧸ IsLocalRing.maximalIdeal (locC hPW)) :=
      isSimpleModule_iff_quot_maximal.mpr
        ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  rw [show algebraMap (homLocRing P W) (locC hPW) = incAC hPW from rfl, hm, h1, mul_one,
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (locC hPW)
      (Ideal.span {a})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton] at key
  exact key
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
