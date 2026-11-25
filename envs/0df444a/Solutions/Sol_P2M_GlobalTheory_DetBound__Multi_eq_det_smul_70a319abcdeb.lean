-- Prove2me | solution 1 for P2M_GlobalTheory_DetBound__Multi_eq_det_smul_70a319abcdeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:18.553944+00:00
-- url     : https://prove2.me/submissions/0fb54bed-683e-44aa-9067-d589c9b3ef8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {n : ℕ}
    (b : Module.Basis (Fin n) O M) (v : Fin n → M) :
    exteriorPower.ιMulti O n v = b.det v • exteriorPower.ιMulti O n b := by
  have h : exteriorPower.ιMulti O n (M := M) = b.det.smulRight (exteriorPower.ιMulti O n b) := by
    refine Module.Basis.ext_alternating b fun i hi => ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change exteriorPower.ιMulti O n (b ∘ σ) = b.det (b ∘ σ) • exteriorPower.ιMulti O n b
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]
  exact DFunLike.congr_fun h v
end GlobalTheory.DetBound
