-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_add_sub_le___484fd36eb6a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:52:09.937203+00:00
-- url     : https://prove2.me/submissions/d73414d1-4680-4806-8372-4b5221adb261

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_sub_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_pow_prime_pow_sub_le
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_c_le___d1e0bfc83eb1
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_p_le___1e1687606494
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_pow_le

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
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) :
    nrm K (t.N n (a + b) - t.N n a - t.N n b) ≤ t.ρ := by
  set d := p ^ t.k n
  have e : t.N n (a + b) - t.N n a - t.N n b = (t.N n (a + b) - (a + b) ^ d) +
      ((a + b) ^ d - a ^ d - b ^ d) - (t.N n a - a ^ d) - (t.N n b - b ^ d) := by ring
  rw [e]
  refine nrm_sub_le_of_le (nrm_sub_le_of_le (nrm_add_le_of_le ?_ ?_) ?_) ?_
  · exact (t.nrm_N_sub_pow_le n (add_mem ha hb) (nrm_add_le_one ha1 hb1)).trans t.c_le_ρ
  · exact (nrm_add_pow_prime_pow_sub_le t.prime ha1 hb1 _).trans t.nrm_p_le_ρ
  · exact (t.nrm_N_sub_pow_le n ha ha1).trans t.c_le_ρ
  · exact (t.nrm_N_sub_pow_le n hb hb1).trans t.c_le_ρ
end GroundTheory.PAdicHodge.NormTower
