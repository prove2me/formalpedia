-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_localMult_ker_eval_eq_zero_cfc4bb44e600
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:34.320006+00:00
-- url     : https://prove2.me/submissions/8fb414e7-e6b3-437a-a72d-3969198ae3dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveBranchLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveBranchLength

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∈ J) (hgq : eval q g ≠ 0) :
    localMult J (RingHom.ker (eval q)) = 0 := by
  have htop : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))
  have hs := Ideal.Quotient.subsingleton_iff.2 htop
  rw [localMult, dif_pos (isPrime_ker_eval q), Module.length_eq_zero_iff.2 hs]
  rfl
end GroundTheory.Heights₂.Heights
