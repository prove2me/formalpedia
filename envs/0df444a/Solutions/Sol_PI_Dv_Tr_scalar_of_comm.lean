-- Prove2me | solution 1 for PI.Dv.Tr.scalar_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:30.274116+00:00
-- url     : https://prove2.me/submissions/8967deef-e2f4-4839-ac3a-3b89086c6039

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) (Z : Module.End K (T.W s))
    (h : ∀ g, Z * T.tau s g = T.tau s g * Z) : ∃ c : K, Z = c • 1 := by
  have hall : ∀ a : MonoidAlgebra K G, Z * (T.tau s).asAlgebraHom a = (T.tau s).asAlgebraHom a * Z := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => rw [Representation.asAlgebraHom_of, h]
    | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
    | smul r x hx => rw [map_smul, mul_smul_comm, smul_mul_assoc, hx]
  have hc : Z ∈ Set.center (Module.End K (T.W s)) := by
    rw [Semigroup.mem_center_iff]
    intro Y
    obtain ⟨a, rfl⟩ := T.irr s Y
    exact (hall a).symm
  obtain ⟨α, hα, hZ⟩ := Module.End.mem_center_iff.mp hc
  refine ⟨α, ?_⟩
  ext x
  rw [hZ]
  simp
end PI.Dv.Tr
