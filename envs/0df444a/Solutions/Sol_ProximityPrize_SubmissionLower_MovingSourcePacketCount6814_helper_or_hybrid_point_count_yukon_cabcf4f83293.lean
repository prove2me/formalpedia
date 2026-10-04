-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourcePacketCount6814.helper_or_hybrid_point_count_yukon_cabcf4f83293
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T04:59:38.176078+00:00
-- url     : https://prove2.me/submissions/85c25c97-1d5d-440b-9a29-b0e34d03af37

import Definitions.Def_Yukon_46b156c3eef80304ae6564f7



import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourcePacket6814_exists_helper_or_regular_projection_yukon_4d83fed39b4f
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_f53921b9b22d3fcb96996433
import Definitions.Def_Yukon_ca06e00072579899a61b0098
import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
import Definitions.Def_Yukon_a98065d48a835a5fe7279317
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourcePacket6814.exists_helper_or_regular_projection := @ProximityPrize.SubmissionLower.MovingSourcePacket6814.exists_helper_or_regular_projection_yukon_4d83fed39b4f
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
end MovingFiberThreeSources6811
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
end MovingSourceRegularRestriction6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceHybridCount6814
end MovingSourceHybridCount6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
end MovingSourceGeometricBudget6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourcePacket6814
end MovingSourcePacket6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
end MovingSourceCarrierField6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814
end WholeSpaceSourceAlternative6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
end WholeSpaceCubeUniform6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
end WholeSpaceCube6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN264
end RCN264
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
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourcePacketCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 100000
set_option profiler true
open MvPolynomial RCN002 RCN084 RCN095 RCN135 RCN136 RCN207 RCN234 RCN156 RCN264
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierField6814 MovingSourcePacket6814 MovingSourceGeometricBudget6814
open MovingSourceHybridCount6814 MovingSourceRegularRestriction6814 MovingFiberThreeSources6811
variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
theorem _root_.solution
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hJU : 9≤U) (hUT : U≤T) (hT : T≤1700)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (G : MvPolynomial (Fin 3) OmegaT) (hcarrier : G∣surfaceMap phi F)
    (hG : Irreducible G) (hproper : ¬G∣regularEquation F quadratic A)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (p q : FlagDegree) (hp : PolynomialInFlag p G)
    (hq : PolynomialInFlag q (regularEquation F quadratic A))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<2130706433)
    (S : Source F) (hSk : S.k<2130706433)
    (W : FlagDegree) (cut : MvPolynomial (Fin 3) OmegaT) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → OmegaT))
    (hpointsG : ∀ x ∈ points, MvPolynomial.eval x G=0)
    (hpointsM : ∀ x ∈ points, MvPolynomial.eval x (regularEquation F quadratic A)=0)
    (hregular : ∀ x ∈ points,
      MvPolynomial.eval x (regularDenominator F A*S.leading phi)≠0)
    (hzero : ∀ x ∈ points, MvPolynomial.aeval x cut=0)
    (hisolated : ∀ x ∈ points, IsolatedPoint G (regularEquation F quadratic A) cut x) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
    S.d*points.card ≤ W.zOnly*flagMixed p unitZFlag S.flag+
      S.d*(W.yz*flagMixed ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unitYZFlag+
        W.all*flagMixed ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unitAllFlag)  := by
  rcases exists_helper_or_regular_projection nodes u0 u1 hN J hJi hmid hB hJdegree
    U T hJU hUT hT hJbounds F hFT r y t hr hy ht hF hpos hsmall hroot
    quadratic A hden hquadratic hA G hcarrier hG hproper hderiv p q hp hq
    (by omega) hmix with hhelp | hfamily
  · exact Or.inl hhelp
  obtain ⟨base,⟨unit⟩⟩ := hfamily
  have hHdiv : surfaceMap phi (RCN313.polyH K F)∣regularDenominator F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2 : (2 : OmegaT)≠0 :=
    (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (S.k.factorial : OmegaT)≠0 := SecondJetOwnShape.factorial_ne S.k hSk
  exact Or.inr (restricted_source_point_count phi F S G p hG.ne_zero hcarrier hp
    2130706433 hunit h2 hfact (lift quadratic) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hquadratic) (inFlag_map _ hA)
    (regularDenominator F A) hHdiv base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unit
    W cut hcut points hpointsG hpointsM hregular hzero hisolated)
end
end MovingSourcePacketCount6814
end SubmissionLower
end ProximityPrize
