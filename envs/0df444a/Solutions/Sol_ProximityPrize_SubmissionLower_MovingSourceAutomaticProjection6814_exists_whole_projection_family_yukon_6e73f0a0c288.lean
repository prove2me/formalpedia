-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814.exists_whole_projection_family_yukon_6e73f0a0c288
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T05:59:13.334453+00:00
-- url     : https://prove2.me/submissions/e3951631-f0a6-4b4b-9c05-752aa2452eaf




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_5bee0eb731f90d2a0bcf4c44
import Definitions.Def_Yukon_b65780c687b1145241867ef4
import Definitions.Def_Yukon_1bcd4c4ffdf14561f9186504
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814
end MovingSourcePoleBudget6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814
end MovingSourcePrimeFamily6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814
end MovingSourceProjectionFamily6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN264
end RCN264
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN116
end RCN116
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN093
end RCN093
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN046
end RCN046
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN037
end RCN037
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN022
end RCN022
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN046 RCN093 RCN095 RCN116 RCN264 RCN341
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814 MovingSourcePoleBudget6814
/-- A reducible old carrier receives one projection budget from the actual
coprime pair. Only the pair's two mixed bounds are compared with the
characteristic; no degree gate or irreducibility of the carrier is used. -/
theorem _root_.solution
    {K : Type} [Field K] [IsAlgClosed K]
    (G M R B H : MvPolynomial (Fin 3) K)
    (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ C : RegularComponent K G M R, B∈C.1)
    (hHmem : ∀ C : RegularComponent K G M R, H∈C.1)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H)
    (c : ℕ) [CharP K c]
    (hZsmall : flagMixed p q unitZFlag<c) (hYsmall : flagMixed p q unitYZFlag<c)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0) :
    ∃ base : ∀ C : RegularComponent K G M R, SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamily base p q)  := by
  have hY (C : RegularComponent K G M R) : LiteralProjectionGate C 0 := by
    intro ht
    have ht' : Transcendental K (flagEvaluation K C.1 0 0 0 (MvPolynomial.X (Axis.u.order 0))) := by
      simpa [Axis.order,RCN125.uOrder,affineU] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.uOrder,affineU])
    have hh := prime_projection_gate C.1 .u 0 0 0 ht' B H hB hH hrel (hBmem C) (hHmem C)
      p q hp hq c hYsmall
    rw [he] at hh
    exact hh
  have hZ (C : RegularComponent K G M R) : LiteralProjectionGate C 2 := by
    intro ht
    have ht' : Transcendental K (flagEvaluation K C.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))) := by
      simpa [Axis.order,RCN125.zOrder] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder])
    have hh := prime_projection_gate C.1 .z 0 0 0 ht' B H hB hH hrel (hBmem C) (hHmem C)
      p q hp hq c hZsmall
    rw [he] at hh
    exact hh
  let base (C : RegularComponent K G M R) : SeparableLiteralCoordinate C.1 :=
    Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates C.1
      (regularComponent_ne_point K G M R C) (hY C) (hZ C))
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  exact ⟨base,⟨projectionFamily_of_coprime_pair base hY hZ hderiv D
    B H hB hH hrel hBmem hHmem p q hp hq⟩⟩
end
end MovingSourceAutomaticProjection6814
end SubmissionLower
end ProximityPrize
