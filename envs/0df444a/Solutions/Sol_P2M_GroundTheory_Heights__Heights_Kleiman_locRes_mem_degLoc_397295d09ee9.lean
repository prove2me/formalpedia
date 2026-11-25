-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locRes_mem_degLoc_397295d09ee9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:52.979824+00:00
-- url     : https://prove2.me/submissions/249ed36f-64e8-470c-b3f3-d85f2e483ae2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (𝓜 : GradedPMod S N M) (c : ℤ) (I J : StdCell N) (h : I.1 ⊆ J.1)
    {x : LocMod S N M I.1} (hx : x ∈ degLoc 𝓜 c I) : locRes h x ∈ degLoc 𝓜 c J := by
  have key : degLoc 𝓜 c I ≤ (degLoc 𝓜 c J).comap (locResS I J h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    show locRes h (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) ∈ degLoc 𝓜 c J
    rw [locRes_mk]
    exact Submodule.subset_span ⟨m, ⟨s, monos_mono h s.2⟩, a, e, hm, hs, hae, rfl⟩
  exact key hx
end GroundTheory.Heights₂.Heights.Kleiman
