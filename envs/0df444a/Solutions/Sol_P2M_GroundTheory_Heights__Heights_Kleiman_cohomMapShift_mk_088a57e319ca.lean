-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:47.3558+00:00
-- url     : https://prove2.me/submissions/815b3330-82d2-4d6c-8a6a-9a1540e5b8aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree

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
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M')
    (t : ℤ) (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) (i : ℕ) {c c' : ℤ}
    (hc : c' = c + t) (z : Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS i) :
    ∃ z' : Cech.cocyDeg (locSys S N M') (degLoc 𝓜' c') locResS i,
      cohomMapShift f t hf i hc (Submodule.Quotient.mk z : cohom 𝓜 i c) =
        (Submodule.Quotient.mk z' : cohom 𝓜' i c') ∧ ∀ I, z'.1 I = locMap f I.1.1 (z.1 I) :=
  ⟨_, rfl, fun _ => rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
