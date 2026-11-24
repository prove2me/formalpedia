-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:22.470339+00:00
-- url     : https://prove2.me/submissions/17ede394-73da-48cb-8cdf-644f2fce7f60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) (z : Ω) :
    z ∈ (Q.pow 0).sub I ↔ z ∈ Kleiman.chartRing S x I := by
  obtain ⟨i, hi⟩ := I.2.1
  change z ∈ Kleiman.twistMod S x 0 I ↔ _
  rw [Kleiman.twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Kleiman.chartRing_smul_def, mul_one]
    exact a.2
  · intro hz
    exact ⟨⟨z, hz⟩, by rw [Kleiman.chartRing_smul_def, mul_one]⟩
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
