-- Prove2me | solution 1 for PI.DvRows.det_ne_zero_of_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:34.346268+00:00
-- url     : https://prove2.me/submissions/c197cff7-58e0-4cf7-adac-907c0937b58d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Adapted
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pairing
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
namespace PI.DvRows
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {r : ℕ} (x y : Fin r → V)
    (P : Matrix (Fin r) (Fin r) K) (hy : LinearIndependent K y)
    (hxy : ∀ j, y j = ∑ c, P c j • x c) : P.det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  change P.mulVec c = 0 at hc
  apply hc0
  have hsum : ∑ j, c j • y j = 0 := by
    simp_rw [hxy, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ j, (c j * P l j) • x l = ((P.mulVec c) l) • x l := by
      intro l
      rw [← Finset.sum_smul]
      congr 1
      simp [Matrix.mulVec, dotProduct, mul_comm]
    simp_rw [this, hc]
    simp
  funext i
  exact (Fintype.linearIndependent_iff.1 hy) c hsum i
end PI.DvRows
