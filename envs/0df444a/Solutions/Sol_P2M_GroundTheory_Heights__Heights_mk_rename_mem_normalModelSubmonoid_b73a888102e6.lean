-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mk_rename_mem_normalModelSubmonoid_b73a888102e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:39.790184+00:00
-- url     : https://prove2.me/submissions/6a46737f-0679-40cb-84bb-e29e94978b4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization

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
open MvPolynomial ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    Ideal.Quotient.mk M.ideal (rename Sum.inl f) ∈ normalModelSubmonoid M q :=
  Submonoid.mem_map_of_mem _ (show f ∈ (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl from
    fun h ↦ hf (RingHom.mem_ker.1 h))
end GroundTheory.Heights₂.Heights
