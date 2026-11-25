-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_isMulCoboundary__pow_card_427b229fa3ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:11.780426+00:00
-- url     : https://prove2.me/submissions/176fed62-d7cf-48fe-ba11-32cb1e443ae4

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Splitting
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open TensorProduct Module groupCohomology
universe u
namespace GroundTheory.Brauer
theorem _root_.solution {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] {f : G × G → M} (hf : IsMulCocycle₂ f) :
    IsMulCoboundary₂ (f ^ Fintype.card G) := by
  classical
  refine ⟨fun g => ∏ j, f (g, j), fun g h => ?_⟩
  have H : (∏ j, f (g * h, j)) * f (g, h) ^ Fintype.card G =
      g • (∏ j, f (h, j)) * ∏ j, f (g, j) := by
    calc (∏ j, f (g * h, j)) * f (g, h) ^ Fintype.card G = ∏ j, (f (g * h, j) * f (g, h)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ = ∏ j, (g • f (h, j) * f (g, h * j)) := Finset.prod_congr rfl fun j _ => hf g h j
      _ = (∏ j, g • f (h, j)) * ∏ j, f (g, h * j) := Finset.prod_mul_distrib
      _ = g • (∏ j, f (h, j)) * ∏ j, f (g, j) := by
          rw [Finset.smul_prod']
          congr 1
          exact Equiv.prod_comp (Equiv.mulLeft h) (fun j => f (g, j))
  rw [Pi.pow_apply, div_mul_eq_mul_div, div_eq_iff_eq_mul, ← H, mul_comm]
end GroundTheory.Brauer
