-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814.sum_moving_degrees_of_whole_bound_yukon_d0d63597e9b0
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T07:15:36.447536+00:00
-- url     : https://prove2.me/submissions/d43ecb81-b22f-4768-beb8-0f7a507e8e4e

import Definitions.Def_Yukon_ad71038421ad49c036e88a5d



import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_16f81088431f3e99fb7c7147
import Definitions.Def_Yukon_9ee250b49ffcc1fbd0a8d65b
import Definitions.Def_Yukon_cda8436acadf847465c34963
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCount6814
end MovingSourceWholeCount6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
end MovingSourceGeometricBudget6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814
end MovingSourceWholeCarrier6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceTargetField6814
end MovingSourceTargetField6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
end MovingFiberThreeSources6811
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN344
end RCN344
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN313
end RCN313
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN264
end RCN264
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN208
end RCN208
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN207
end RCN207
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN202
end RCN202
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN199
end RCN199
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN135
end RCN135
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN134
end RCN134
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN084
end RCN084
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814 MovingSourceWholeCarrier6814
open MovingSourceGeometricBudget6814 MovingSourceWholeCount6814
variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814.instAlgebraRatFuncGenericField
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814.instIsScalarTowerGenericFieldRatFunc
theorem _root_.solution [CharP K 2130706433]
    {I : Type} [Fintype I]
    (F : MvPolynomial (Fin 4) K) (S : Source F) (p : FlagDegree)
    (Q A : MvPolynomial (Fin 3) Omega) (hbound : WholePointBound F S p Q A)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (W : FlagDegree) (hcut : PolynomialInFlag W (targetCut n coeff Q A))
    (old : I → OriginalFamily F n coeff) (hold : Function.Injective old)
    (hleading : ∀ i, S.leading (polynomialEmbedding K)∉(old i).1)
    (hA : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Omega (CoordinateField Omega (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Omega (CoordinateField Omega (old i).1) (projection i)=
      movingValue (old i).1 (baseH F) (baseG F) Q A) :
    7*(∑ i, SeparableCoordinate.degree Omega (CoordinateField Omega (old i).1) (projection i))≤
      W.zOnly*flagMixed p unitZFlag ⟨3252,132,51⟩+7*(W.yz*25470+W.all*88560)  := by
  classical
  let prime := fun i => (old i).1
  letI : ∀ i, Algebra (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).embedding.toRingHom.toAlgebra
  letI : ∀ i, IsScalarTower Omega (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => IsScalarTower.of_algebraMap_eq fun a => ((projection i).embedding.commutes a).symm
  letI : ∀ i, FiniteDimensional (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).finite
  letI : ∀ i, Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).separable
  let points := genericFiberPoints (B:=RatFunc Omega) (L:=OmegaT) prime
  have hinj : Function.Injective prime := by
    intro i j h
    exact hold (Subtype.ext h)
  have certificate (i : I) (f : CoordinateField Omega (prime i) →ₐ[RatFunc Omega] OmegaT) :
      let x := embeddingPoint (prime i) (f.restrictScalars Omega)
      MvPolynomial.eval x (wholeCarrier F)=0 ∧
      MvPolynomial.eval x (regularEquation F Q A)=0 ∧
      MvPolynomial.aeval x (targetCut n coeff Q A)=0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*lift A)≠0 ∧
      IsolatedPoint (wholeCarrier F) (regularEquation F Q A) (targetCut n coeff Q A) x := by
    have hj : algebraMap (RatFunc Omega) (CoordinateField Omega (prime i)) (rationalVariable Omega)=
        movingValue (old i).1 (baseH F) (baseG F) Q A := hvalue i
    have hc := embedding_point_certificate (baseCarrier F) (baseH F) (baseG F) Q A n coeff
      (old i) hj (hA i) f
    simpa only [scalar_eq_lift,baseCarrier,baseH,baseG,lift_surface,target_variable,
      wholeCarrier,regularEquation,targetCut] using hc
  have hc : ∀ x ∈ points,
      MvPolynomial.eval x (wholeCarrier F)=0 ∧ MvPolynomial.eval x (regularEquation F Q A)=0 ∧
      MvPolynomial.eval x (regularDenominator F A*S.leading phi)≠0 ∧
      MvPolynomial.aeval x (targetCut n coeff Q A)=0 ∧
      IsolatedPoint (wholeCarrier F) (regularEquation F Q A) (targetCut n coeff Q A) x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hh := certificate i f
    dsimp only at hh ⊢
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.1,hh.2.2.2.2⟩
    have hHA := hh.2.2.2.1
    rw [map_mul,mul_ne_zero_iff] at hHA
    have hL : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (S.leading phi)≠0 := by
      have he : S.leading phi=lift (S.leading (polynomialEmbedding K)) := (lift_surface _).symm
      rw [he,eval_lift_embedding]
      intro hz
      exact hleading i ((SecondJetComponentRoots.evaluation_zero_iff (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
    simpa only [commonBaseEmbeddingPoint,regularDenominator,map_mul,map_ofNat] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hHA.1) (mul_ne_zero h2 hHA.2)) hL
  have hb := hbound W (targetCut n coeff Q A) hcut points
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2.1)
    (fun x hx => (hc x hx).2.2.1) (fun x hx => (hc x hx).2.2.2.1)
    (fun x hx => (hc x hx).2.2.2.2)
  have hcard := genericFiberPoints_card (B:=RatFunc Omega) (L:=OmegaT) prime hinj
  simpa only [points,hcard,SeparableCoordinate.degree,prime] using hb
end
end MovingSourceMovingDegrees6814
end SubmissionLower
end ProximityPrize
