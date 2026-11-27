-- Prove2me | solution 1 for PositivityTheory.Lord.hasProd_compl_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:30.741798+00:00
-- url     : https://prove2.me/submissions/ae78a779-b591-4aff-9b58-f21b1882eae6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FinMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Lord
namespace PositivityTheory.Lord
theorem _root_.solution {ι : Type*} [DecidableEq ι] (f g : ι → ℂ) (a : ℂ) (T S : Finset ι) (hST : S ⊆ T)
    (hg : HasProd g a) (hg0 : ∀ v ∈ T, g v ≠ 0) (hfg : ∀ v, v ∉ T → f v = g v) :
    HasProd (fun v : {v // v ∉ S} => f v) (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
  let F : ι → ℂ := Set.mulIndicator {v | v ∉ S} f
  let k : ι → ℂ := fun v => if v ∈ T then (g v)⁻¹ * F v else 1
  have hkT : HasProd k (∏ v ∈ T, k v) :=
    hasProd_prod_of_ne_finset_one (fun v hv => if_neg hv)
  have hgk : ∀ v, g v * k v = F v := by
    intro v
    by_cases hv : v ∈ T
    · show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = F v
      rw [if_pos hv, ← mul_assoc, mul_inv_cancel₀ (hg0 v hv), one_mul]
    · have hvS : v ∉ S := fun h => hv (hST h)
      show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = Set.mulIndicator {v | v ∉ S} f v
      rw [if_neg hv, mul_one, Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS), hfg v hv]
  have hFT : ∏ v ∈ T, F v = ∏ v ∈ T \ S, f v := by
    rw [Finset.sdiff_eq_filter, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    by_cases hvS : v ∈ S
    · rw [if_neg (not_not.2 hvS)]
      exact Set.mulIndicator_of_notMem (show v ∉ {v | v ∉ S} from not_not.2 hvS) f
    · rw [if_pos hvS]
      exact Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS) f
  have hkprod : ∏ v ∈ T, k v = (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v := by
    rw [← hFT, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v hv => if_pos hv)
  have hF : HasProd F (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
    have h := hg.mul hkT
    rw [hkprod, ← mul_assoc] at h
    convert h using 1
    funext v
    exact (hgk v).symm
  exact (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 hF
end PositivityTheory.Lord
