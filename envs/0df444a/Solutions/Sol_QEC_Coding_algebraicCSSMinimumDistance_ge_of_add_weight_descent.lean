-- Prove2me | solution 1 for QEC.Coding.algebraicCSSMinimumDistance_ge_of_add_weight_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:13:38.444365+00:00
-- url     : https://prove2.me/submissions/4f2f6933-d66a-439d-8810-62c7a1ccfdea

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Theorems.Thm_QEC_Coding_logical_weight_ge_of_add_weight_descent

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F]
  [DecidableEq F] [Fintype ι]
namespace QEC.Coding
theorem _root_.solution
    (xCode zCode : LinearCode F ι)
    (hX : xCode.carrier ≤ zCode.dual.carrier)
    (hZ : zCode.carrier ≤ xCode.dual.carrier) (threshold : Nat)
    (hreduceX : ∀ x : Word F ι, x ∈ zCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ xCode.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (hreduceZ : ∀ x : Word F ι, x ∈ xCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ zCode.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    {distance : Nat}
    (hmin : AlgebraicCSSMinimumDistance xCode zCode distance) :
    threshold ≤ distance := by
  obtain ⟨x, hsector, hweight, _hleast⟩ := hmin
  rw [← hweight]
  rcases hsector with hsector | hsector
  · exact logical_weight_ge_of_add_weight_descent
      zCode.dual xCode hX threshold hreduceX x hsector.1 hsector.2
  · exact logical_weight_ge_of_add_weight_descent
      xCode.dual zCode hZ threshold hreduceZ x hsector.1 hsector.2
end QEC.Coding
