-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_coh_mk_eq_904b9ec6a130
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:37.706545+00:00
-- url     : https://prove2.me/submissions/c692bc65-04f1-4729-8cee-ced577551ecc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
open Module
variable {F : Type} [Field F] {X Y : ℕ → Type} [∀ n, AddCommGroup (X n)] [∀ n, Module F (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module F (Y n)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
theorem _root_.solution {CX : ∀ n, Submodule F (X n)} {dX : ∀ n, X n →ₗ[F] X (n + 1)} {n : ℕ}
    (x y : cyc CX dX n) :
    (Submodule.Quotient.mk x : coh CX dX n) = Submodule.Quotient.mk y ↔ (x : X n) - y ∈ bnd CX dX n :=
  Submodule.Quotient.eq _
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
