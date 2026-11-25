-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_mem_quotField_80f3aaaa24c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:26:02.936584+00:00
-- url     : https://prove2.me/submissions/a0241a83-4885-4bcc-9717-8b8810740937

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_yEval_eq_5a232bddc35c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_single_zero_55c62bc01ab6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_yEval_C_mul_390f53e7d566
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_intSmul_1c54165cdeb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_exists_linear_of_mem_6d2dc9a00622
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_smul_mem_latticeDual_603c1b9810fa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hL : L.FG) (hφ : IsDualBasis L φ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) ∈ quotField φ := by
  obtain ⟨n, hn, hnu⟩ := exists_int_smul_mem_latticeDual hL u
  obtain ⟨n', hn', hne⟩ := exists_int_smul_mem_latticeDual hL (Pi.single 0 1 : Fin (r + 1) → K)
  obtain ⟨g, hg, hgu⟩ := exists_linear_of_mem (N := N) hφ hnu
  obtain ⟨h, hh, hhe⟩ := exists_linear_of_mem (N := N) hφ hne
  have hg' : yEval φ g = n * dehom K r (latticeForm u) := by
    rw [yEval_eq, hgu, dehom_latticeForm_intSmul]
  have hh' : yEval φ h = n' := by
    rw [yEval_eq, hhe, dehom_latticeForm_intSmul, dehom_single_zero, mul_one]
  refine ⟨1, C n' * g, C n * h, by simpa using (isHomogeneous_C _ _).mul hg,
    by simpa using (isHomogeneous_C _ _).mul hh, ?_, ?_⟩
  · rw [yEval_C_mul, hh']
    exact mul_ne_zero (Int.cast_ne_zero.mpr hn) (Int.cast_ne_zero.mpr hn')
  · rw [yEval_C_mul, yEval_C_mul, hg', hh']
    ring
end GroundTheory.Heights₂.Heights.LatticeModel
