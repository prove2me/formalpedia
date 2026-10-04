-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceWholeCount6814.helpers_or_whole_point_bound_yukon_9ff0d533bdeb
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T07:52:43.93856+00:00
-- url     : https://prove2.me/submissions/86b41eaf-765c-416e-9a07-b3155e0411fa

import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceWholeCarrier6814_helper_or_whole_projection_yukon_30585f547133
import Definitions.Def_Yukon_9ee250b49ffcc1fbd0a8d65b



import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_cda8436acadf847465c34963
import Definitions.Def_Yukon_5f00e2c5310c2b2de34fe4e2
import Definitions.Def_Yukon_ca06e00072579899a61b0098
import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
import Definitions.Def_Yukon_a98065d48a835a5fe7279317
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.helper_or_whole_projection := @ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.helper_or_whole_projection_yukon_30585f547133
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
end WholeSpaceCubeUniform6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
end WholeSpaceCube6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
end MovingFiberThreeSources6811
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
end MovingSourceRegularRestriction6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
end MovingSourceCarrierField6814
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
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN207
end RCN207
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
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN084
end RCN084
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN046
end RCN046
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN234 RCN156 RCN341
open MovingSourceWholeCarrier6814 MovingSourceGeometricBudget6814 MovingSourceCarrierField6814
open MovingSourceRegularRestriction6814 MovingFiberThreeSources6811
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
/-- The whole regular simple-J branch. Both source suppliers are actual
181255-agreement constructions. The two proper-helper exits remain
explicit; neither is silently treated as impossible. -/
theorem _root_.solution [CharP K 2130706433]
    {N : Type} [Fintype N] (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (hFT : 3429<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (p : FlagDegree) (hp : PolynomialInFlag p (wholeCarrier F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433) :
    (∃ Q, MovingSourceZSupplier6814.ProperHelper F Q r y t nodes u0 u1) ∨
    (∃ Q, WholeSpaceSourceAlternative6814.ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ S : Source F, S.d=7 ∧ S.flag=⟨3252,132,51⟩ ∧ WholePointBound F S p quadratic A  := by
  rcases MovingSourceZSupplier6814.exists_helper_or_z_source nodes u0 u1 hN F Fact.out
    hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  obtain ⟨S,hd,hs,hk⟩ := hret
  rcases helper_or_whole_projection nodes u0 u1 hN J hJi hmid hB hJdegree
    U T hU hUmax hUT hT hJbounds F (by omega) r y t hr hy ht hF hpos hsmall hroot
    quadratic A hden hquadratic hA with hhelp | hfamily
  · exact Or.inr (Or.inl hhelp)
  obtain ⟨base,⟨unit⟩⟩ := hfamily
  exact Or.inr (Or.inr ⟨S,hd,hs,wholePointBound_of_projection F
    (Fact.out : Irreducible F).ne_zero S hd hs hk p hp hunit U T hU hUmax hUT hT
    quadratic A hquadratic hA base unit⟩)
end
end MovingSourceWholeCount6814
end SubmissionLower
end ProximityPrize
