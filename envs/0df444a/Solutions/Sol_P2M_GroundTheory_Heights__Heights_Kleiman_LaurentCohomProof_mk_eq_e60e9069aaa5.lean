-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mk_eq_e60e9069aaa5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:14.549803+00:00
-- url     : https://prove2.me/submissions/453cfe6e-2930-4f24-bd0e-33ae0c51e55e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom

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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
theorem _root_.solution {c : ℤ} {i : ℕ} {z w : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i)
    (hw : w ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i)
    (h : z - w ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    (Submodule.Quotient.mk ⟨z, hz⟩ : laurentCohom S N i c) = Submodule.Quotient.mk ⟨w, hw⟩ :=
  (Submodule.Quotient.eq _).mpr h
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
