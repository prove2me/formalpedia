-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_leftInverse_b296a5e4e453
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:04.649479+00:00
-- url     : https://prove2.me/submissions/dff7c6cc-9e1c-45b2-951b-832b9dc04e4c

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
theorem _root_.solution {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜')
    (g : GradedHom 𝓜' 𝓜) (hfg : ∀ m, g.toLin (f.toLin m) = m) (i : ℕ) (c : ℤ) (y : cohom 𝓜 i c) :
    cohomMap g i c (cohomMap f i c y) = y := by
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  funext I
  change locMap g.toLin I.1.1 (locMap f.toLin I.1.1 ((s : Cech.Cochain (locSys S N M) i) I)) =
    (s : Cech.Cochain (locSys S N M) i) I
  generalize ((s : Cech.Cochain (locSys S N M) i) I) = z
  induction z using LocalizedModule.induction_on with
  | h m t => rw [locMap_mk, locMap_mk, hfg]
end GroundTheory.Heights₂.Heights.Kleiman
