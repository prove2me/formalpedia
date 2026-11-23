-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.pp_of_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:50.801836+00:00
-- url     : https://prove2.me/submissions/7ce327d1-4984-4678-b98c-090a55b730dc

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {K : Type*} [Group K] {n : ℕ} (t : Fin (n + 1) → K) (h0 : t 0 = 1) (k : Fin (n + 1)) :
    Fin.partialProd (fun i : Fin n => (t i.castSucc)⁻¹ * t i.succ) k = t k := by
  induction k using Fin.induction with
  | zero => rw [Fin.partialProd_zero, h0]
  | succ i ih => rw [Fin.partialProd_succ, ih, mul_inv_cancel_left]
end ReciprocityTheory.Coh.CCA
