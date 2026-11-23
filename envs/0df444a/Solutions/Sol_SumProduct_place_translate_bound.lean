-- Prove2me | solution 1 for SumProduct.place_translate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:04:23.103049+00:00
-- url     : https://prove2.me/submissions/79de3435-f0d7-4c41-8c99-56870d9e74f1

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_place_natCast

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (n : ℕ) {r : ℝ} {b : 𝓞 K} (hb : b ∈ boxAdd K r) :
    (n : ℝ) - r ≤ w (((n : 𝓞 K) + b : 𝓞 K) : K) ∧
      w (((n : 𝓞 K) + b : 𝓞 K) : K) ≤ (n : ℝ) + r := by
  rw [mem_boxAdd] at hb
  have hwb : w (b : K) ≤ r := hb w
  have hwn : w (n : K) = n := place_natCast w n
  have hcast : (((n : 𝓞 K) + b : 𝓞 K) : K) = (n : K) + (b : K) := by push_cast; ring
  rw [hcast]
  refine ⟨?_, ?_⟩
  · have htri : w (n : K) ≤ w ((n : K) + (b : K)) + w (b : K) := by
      have hh := w.1.add_le ((n : K) + (b : K)) (-(b : K))
      rw [add_neg_cancel_right, AbsoluteValue.map_neg] at hh
      exact hh
    linarith
  · calc w ((n : K) + (b : K)) ≤ w (n : K) + w (b : K) := w.1.add_le _ _
      _ ≤ (n : ℝ) + r := by rw [hwn]; linarith
end SumProduct
