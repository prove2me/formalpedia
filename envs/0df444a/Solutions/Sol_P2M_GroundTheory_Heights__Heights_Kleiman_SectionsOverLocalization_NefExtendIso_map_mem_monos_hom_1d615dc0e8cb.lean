-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_mem_monos_hom_1d615dc0e8cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:34.438453+00:00
-- url     : https://prove2.me/submissions/bddb2af1-6952-474d-970b-4a1fb9181366

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    {I : Finset (Fin (N + 1))} {s : Kleiman.Poly R N} (hs : s ∈ Kleiman.monos I) :
    map g s ∈ Kleiman.monos (S := R') I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
