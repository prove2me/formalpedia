-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le___999ce6594f0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:35.630037+00:00
-- url     : https://prove2.me/submissions/3523067f-7881-48c6-9ece-401c49ba9e3c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_sub_le_of_le
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_c_le___d1e0bfc83eb1
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_pow_le
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_pow_sub_pow_le___4bebacc7034d

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
open GroundTheory.PAdicHodge.NormTower
variable {K Ω p} (t : NormTower K Ω p)
namespace GroundTheory.PAdicHodge.NormTower
theorem _root_.solution (n : ℕ) {a b : Ω} (ha : a ∈ t.E (n + 1)) (hb : b ∈ t.E (n + 1))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) (hab : nrm K (a - b) ≤ t.ρ) :
    nrm K (t.N n a - t.N n b) ≤ t.ρ := by
  have e : t.N n a - t.N n b = (t.N n a - a ^ (p ^ t.k n)) + (a ^ (p ^ t.k n) - b ^ (p ^ t.k n)) -
      (t.N n b - b ^ (p ^ t.k n)) := by ring
  rw [e]
  refine nrm_sub_le_of_le (nrm_add_le_of_le ?_ (t.nrm_pow_sub_pow_le_ρ ha1 hb1 hab _)) ?_
  · exact (t.nrm_N_sub_pow_le n ha ha1).trans t.c_le_ρ
  · exact (t.nrm_N_sub_pow_le n hb hb1).trans t.c_le_ρ
end GroundTheory.PAdicHodge.NormTower
