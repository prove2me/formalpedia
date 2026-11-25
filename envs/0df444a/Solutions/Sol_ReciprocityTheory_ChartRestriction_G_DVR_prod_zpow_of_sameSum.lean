-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.prod_zpow_of_sameSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:57:35.66008+00:00
-- url     : https://prove2.me/submissions/4ab75e3c-9890-4517-a77d-43a7a75ca469

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_zpow_fsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {M : Type} [CommGroup M]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (hs : LB.SameSum φ ε φ' ε') (e : (Y ⟶ X) → M) :
    ∏ k, e (φ k) ^ ε k = ∏ k', e (φ' k') ^ ε' k' := by
  set S : Finset (Y ⟶ X) := Finset.univ.image φ ∪ Finset.univ.image φ'
  have h1 : ∏ k, e (φ k) ^ ε k = ∏ ψ ∈ S, e ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := φ)
      (fun k _ => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
    refine Finset.prod_congr rfl fun ψ _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, zpow_fsum]
    refine Finset.prod_congr (by ext; simp) fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]
  have h2 : ∏ k', e (φ' k') ^ ε' k' = ∏ ψ ∈ S, e ψ ^ (∑ k', if φ' k' = ψ then ε' k' else 0) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := φ')
      (fun k _ => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
    refine Finset.prod_congr rfl fun ψ _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, zpow_fsum]
    refine Finset.prod_congr (by ext; simp) fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]
  rw [h1, h2]
  refine Finset.prod_congr rfl fun ψ _ => ?_
  have := hs ψ
  convert congrArg (fun n => e ψ ^ n) this using 2 <;> simp
end ReciprocityTheory.ChartRestriction.G.DVR
