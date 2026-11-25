-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_finrank_kaehler_eq_card_119c331f97c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:23.142514+00:00
-- url     : https://prove2.me/submissions/f185ae00-eb91-4d92-b45a-9bb20ca2fb22

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace JacobianRankGeneric
theorem _root_.solution {k K : Type} [Field k] [Field K] [Algebra k K] (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (H : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K) :
    Module.finrank K Ω[K⁄k] = s.card := by
  have hx : AlgebraicIndependent k (fun i : s => (i : K)) := hs.1
  let _ : Algebra (MvPolynomial s k) K := (aeval (fun i : s => (i : K))).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial s k) K := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  let _ : Algebra (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    ((hx.aevalEquivField).toRingHom.comp (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)))).toAlgebra
  let e : FractionRing (MvPolynomial s k) ≃ₐ[MvPolynomial s k]
      IntermediateField.adjoin k (Set.range fun i : s => (i : K)) :=
    { hx.aevalEquivField with commutes' := fun q => rfl }
  have : Algebra.FormallyEtale (MvPolynomial s k) (FractionRing (MvPolynomial s k)) :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    .of_equiv e
  have : IsScalarTower (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    IsScalarTower.of_algebraMap_eq fun q => by
      change aeval (fun i : s => (i : K)) q =
        ((hx.aevalEquivField (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) q) : _) : K)
      rw [hx.aevalEquivField_algebraMap_apply_coe]
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K := by
    convert! H <;> simp
  have : Algebra.FormallyEtale (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    .of_isSeparable _ K
  have : Algebra.FormallyEtale (MvPolynomial s k) K :=
    .comp (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K
  have : Module.Free (MvPolynomial s k) Ω[MvPolynomial s k⁄k] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis k s)
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial s k) K).finrank_eq,
    Module.finrank_baseChange, Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k s),
    Fintype.card_coe]
end JacobianRankGeneric
end GroundTheory.Heights₂.Heights
