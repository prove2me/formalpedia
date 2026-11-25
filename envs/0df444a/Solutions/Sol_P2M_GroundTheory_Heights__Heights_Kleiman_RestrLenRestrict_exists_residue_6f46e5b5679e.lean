-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_exists_residue_6f46e5b5679e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:17.140774+00:00
-- url     : https://prove2.me/submissions/fe1067d2-799c-4cb4-b877-73d0f7815a56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict

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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
theorem _root_.solution {k : Type u} [Field k] {R : Type w} [CommRing R] [Algebra k R] (P : Ideal R)
    [P.IsPrime] : ∃ (K : Type w) (_ : Field K) (_ : Algebra k K) (ψ : R →ₐ[k] K), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
    ← map_zero (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))),
    (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))).eq_iff, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
