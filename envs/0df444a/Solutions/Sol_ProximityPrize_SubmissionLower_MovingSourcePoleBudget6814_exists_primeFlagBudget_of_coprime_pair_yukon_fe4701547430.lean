-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814.exists_primeFlagBudget_of_coprime_pair_yukon_fe4701547430
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T02:42:41.275438+00:00
-- url     : https://prove2.me/submissions/cec30f5e-4f11-4ece-8235-fa90fe9f84e3




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_b65780c687b1145241867ef4
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814
end MovingSourcePrimeFamily6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814
end MovingSourceProjectionFamily6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN344
end RCN344
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
namespace ProximityPrize.SubmissionLower.RCN237
end RCN237
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN116
end RCN116
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN114
end RCN114
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
namespace ProximityPrize.SubmissionLower.RCN042
end RCN042
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
namespace ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN042 RCN046 RCN093 RCN095 RCN114 RCN116 RCN237 RCN264 RCN341 RCN344
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
variable {K : Type} [Field K] [IsAlgClosed K]
    {G T R : MvPolynomial (Fin 3) K}
theorem _root_.solution
    (base : ∀ C : RegularComponent K G T R, SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent K G T R, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent K G T R, LiteralProjectionGate C 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ C : RegularComponent K G T R, B∈C.1)
    (hHmem : ∀ C : RegularComponent K G T R, H∈C.1)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    Nonempty (PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=R) p q)  := by
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  exact ⟨(projectionFamily_of_coprime_pair base hY hZ hderiv D
    B H hB hH hrel hBmem hHmem p q hp hq).toPrimeFlagBudgetFamily⟩
end
end MovingSourcePoleBudget6814
end SubmissionLower
end ProximityPrize
