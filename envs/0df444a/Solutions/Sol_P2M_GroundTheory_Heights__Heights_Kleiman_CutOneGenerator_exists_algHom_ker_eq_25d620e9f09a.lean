-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_algHom_ker_eq_25d620e9f09a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:12:25.613981+00:00
-- url     : https://prove2.me/submissions/a356cf94-3da0-4282-9d45-477dd2506d6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutOneGenerator

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {Q : SubSystem k x Ω} {Q' : SubSystem k y K'} {ρ : Ω → K'}
namespace GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
theorem _root_.solution {R : Type w} [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] :
    ∃ (F : Type w) (_ : Field F) (_ : Algebra k F) (ψ : R →ₐ[k] F), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  rw [RingHom.mem_ker]
  change algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
