-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_NormTower_nrm_Nto_add_sub_le___3ec02eeaf1ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:35.732693+00:00
-- url     : https://prove2.me/submissions/79720b0f-9a6e-4539-81e0-9914ce70e81c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_mem
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___nonneg_2e425604b7b3
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower_nrm_N_add_sub_le___484fd36eb6a8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_one
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
open GroundTheory.PAdicHodge.NormTower
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
  (t : NormTower K Ω p)
namespace GroundTheory.PAdicHodge.NormTower
theorem _root_.solution (i : ℕ) {j : ℕ} {a b : Ω} (ha : a ∈ t.E (i + j)) (hb : b ∈ t.E (i + j))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) :
    nrm K (t.Nto i j (a + b) - t.Nto i j a - t.Nto i j b) ≤ t.ρ := by
  induction j generalizing a b with
  | zero => simp [t.ρ_nonneg]
  | succ j ih =>
    simp only [Nto_succ]
    have hNa := t.N_mem _ ha
    have hNb := t.N_mem _ hb
    have hNa1 := t.nrm_N_le_one (i + j) ha1
    have hNb1 := t.nrm_N_le_one (i + j) hb1
    have h1 := t.nrm_Nto_sub_Nto_le_ρ i (t.N_mem _ (add_mem ha hb)) (add_mem hNa hNb)
      (t.nrm_N_le_one _ (nrm_add_le_one ha1 hb1)) (nrm_add_le_one hNa1 hNb1)
      (by rw [sub_add_eq_sub_sub]; exact t.nrm_N_add_sub_le_ρ _ ha hb ha1 hb1)
    have h2 := ih hNa hNb hNa1 hNb1
    have e : t.Nto i j (t.N (i + j) (a + b)) - t.Nto i j (t.N (i + j) a) - t.Nto i j (t.N (i + j) b) =
        (t.Nto i j (t.N (i + j) (a + b)) - t.Nto i j (t.N (i + j) a + t.N (i + j) b)) +
        (t.Nto i j (t.N (i + j) a + t.N (i + j) b) - t.Nto i j (t.N (i + j) a) -
          t.Nto i j (t.N (i + j) b)) := by ring
    rw [e]
    exact nrm_add_le_of_le h1 h2
end GroundTheory.PAdicHodge.NormTower
