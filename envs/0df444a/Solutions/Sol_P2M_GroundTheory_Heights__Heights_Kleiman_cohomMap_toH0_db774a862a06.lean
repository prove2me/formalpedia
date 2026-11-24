-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_toH0_db774a862a06
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:55.92065+00:00
-- url     : https://prove2.me/submissions/3ab8b57c-f377-403f-b180-e9337d4c570c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto

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
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜') (c : ℤ)
    (m : 𝓜.piece c) : cohomMap f 0 c (toH0 𝓜 c m) = toH0 𝓜' c ⟨f.toLin m, f.map_piece c m m.2⟩ := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  funext I
  change locMap f.toLin I.1.1 (LocalizedModule.mk (m : M) 1) = LocalizedModule.mk (f.toLin m) 1
  exact locMap_mk _ _ _ _
end GroundTheory.Heights₂.Heights.Kleiman
