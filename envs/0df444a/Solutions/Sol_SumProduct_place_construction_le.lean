-- Prove2me | solution 1 for SumProduct.place_construction_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:20.171947+00:00
-- url     : https://prove2.me/submissions/57cc712c-d604-47d0-a7cf-d36abd080498

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_place_translate_bound
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (w : NumberField.InfinitePlace K) {Y : ℝ} {g : (𝓞 K)ˣ} (hg : g ∈ boxMult K Y)
    {n : ℕ} {r : ℝ} {b : 𝓞 K} (hb : b ∈ boxAdd K r) :
    w (((g : 𝓞 K) * ((n : 𝓞 K) + b) : 𝓞 K) : K) ≤ Real.exp Y * ((n : ℝ) + r) := by
  have hgpos : 0 < w ((g : 𝓞 K) : K) :=
    NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero g)
  have hgle : w ((g : 𝓞 K) : K) ≤ Real.exp Y := by
    have hlog : Real.log (w ((g : 𝓞 K) : K)) ≤ Y :=
      le_trans (le_abs_self _) ((mem_boxMult.mp hg) w)
    calc w ((g : 𝓞 K) : K) = Real.exp (Real.log (w ((g : 𝓞 K) : K))) := (Real.exp_log hgpos).symm
      _ ≤ Real.exp Y := Real.exp_le_exp.mpr hlog
  have hble : w (((n : 𝓞 K) + b : 𝓞 K) : K) ≤ (n : ℝ) + r := (place_translate_bound w n hb).2
  have hcoe : (((g : 𝓞 K) * ((n : 𝓞 K) + b) : 𝓞 K) : K)
      = ((g : 𝓞 K) : K) * (((n : 𝓞 K) + b : 𝓞 K) : K) := by push_cast; ring
  rw [hcoe, map_mul]
  exact mul_le_mul hgle hble (apply_nonneg w _) (Real.exp_pos Y).le
end SumProduct
