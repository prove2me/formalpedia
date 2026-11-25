-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_of_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:47.904588+00:00
-- url     : https://prove2.me/submissions/450eab39-16a9-4e20-9149-c9888d9a2a0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_StdHSingleZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsIsometryMemLocalizedAtSingle
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isKv_of_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isKv_of_nsmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m] {l : ℕ} (hl : l.Prime) {Λ : AddSubgroup (m → ℂ)}
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0) {v : m → ℂ} (hv : SatMem l Λ v) :
    IsKv b d lam v := by
  obtain ⟨n, hln, hn⟩ := hv
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hln (dvd_zero l)
  set S := stdLat (cmL a b d ha hd lam hlam) m
  have hmem : (S.addSubgroupOf Λ).index • (⟨n • v, hn⟩ : Λ) ∈ S.addSubgroupOf Λ :=
    AddSubgroup.nsmul_index_mem _ _
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul, smul_smul] at hmem
  have hN : (S.addSubgroupOf Λ).index * n ≠ 0 := mul_ne_zero h1 hn0
  exact isKv_of_nsmul hN (isKv_of_mem hmem)
end PI.UnitaryGroupMassFormula.UnimodLocStd
