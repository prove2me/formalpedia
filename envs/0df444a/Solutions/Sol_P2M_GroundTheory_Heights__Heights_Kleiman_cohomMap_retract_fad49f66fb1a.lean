-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_retract_fad49f66fb1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:12.241513+00:00
-- url     : https://prove2.me/submissions/72964f9e-5838-4dba-a2e0-146e1dc6462e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCohomRetract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMap_retract_393d1aa75454

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
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'}
    (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜) (hgf : Function.LeftInverse g.toLin f.toLin)
    (i : ℕ) (c : ℤ) : Function.LeftInverse (cohomMap g i c) (cohomMap f i c) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (funext fun I => locMap_retract f.toLin g.toLin hgf I.1.1 (z.1 I)))
end GroundTheory.Heights₂.Heights.Kleiman
