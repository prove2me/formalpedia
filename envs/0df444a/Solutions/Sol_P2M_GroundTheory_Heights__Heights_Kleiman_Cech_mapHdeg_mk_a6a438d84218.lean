-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapHdeg_mk_a6a438d84218
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:07.822836+00:00
-- url     : https://prove2.me/submissions/f8e08c11-2c20-48cd-bb54-1daa356dfdce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact

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
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A B C : Cell U → Type v}
  [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
  {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J}
  {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
  {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
  {dA : ∀ I, Submodule R (A I)} {dB : ∀ I, Submodule R (B I)} {dC : ∀ I, Submodule R (C I)}
  {φ : ∀ I, A I →ₗ[R] B I} {ψ : ∀ I, B I →ₗ[R] C I}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech
theorem _root_.solution (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) {i : ℕ} (z : cocyDeg A dA ρA i)
    (w : cocyDeg B dB ρB i) (h : mapC φ i z.1 = w.1) :
    mapHdeg dA dB φ hφ hφd i (Hdeg.mk z) = Hdeg.mk w := by
  obtain ⟨w, hw⟩ := w
  change mapC φ i z.1 = w at h
  subst h
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.Cech
