-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_cohMap_mk_a56981702285
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:10.152928+00:00
-- url     : https://prove2.me/submissions/3a61af22-1133-455c-bb03-6f0813cda885

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
variable (CX : ∀ n, Submodule F (X n)) (dX : ∀ n, X n →ₗ[F] X (n + 1))
  (CY : ∀ n, Submodule F (Y n)) (dY : ∀ n, Y n →ₗ[F] Y (n + 1)) (h : ∀ n, X n →ₗ[F] Y n)
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
theorem _root_.solution (hC : ∀ n, ∀ x ∈ CX n, h n x ∈ CY n)
    (hd : ∀ n, ∀ x ∈ CX n, dY n (h n x) = h (n + 1) (dX n x)) (n : ℕ) (x : cyc CX dX n) :
    cohMap CX dX CY dY h hC hd n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨h n x, map_mem_cyc CX dX CY dY h hC hd n x x.2⟩ :=
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
