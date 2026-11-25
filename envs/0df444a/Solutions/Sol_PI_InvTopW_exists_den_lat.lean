-- Prove2me | solution 1 for PI.InvTopW.exists_den_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:50.479889+00:00
-- url     : https://prove2.me/submissions/c70aba79-f338-45b5-a8fd-2f6a3f3c205b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_PI_InvTopW_exists_nat_den
import Theorems.Thm_PI_InvTopW_algebraMap_mem_intOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.InvTopW
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ L, ∀ i, (d : E) * x i ∈ Formalism.UG.intOE E := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨d, hd, hds⟩ := exists_nat_den (S.biUnion fun v => Finset.univ.image v)
  refine ⟨d, hd, fun x hx i => ?_⟩
  let K : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {x | ∀ i, (d : E) * x i ∈ Formalism.UG.intOE E}
      add_mem' := by
        intro a b ha hb i
        rw [Pi.add_apply, mul_add]
        exact add_mem (ha i) (hb i)
      zero_mem' := by
        intro i
        rw [Pi.zero_apply, mul_zero]
        exact zero_mem _
      smul_mem' := by
        intro r a ha i
        rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
        exact mul_mem (algebraMap_mem_intOE r) (ha i) }
  have hSK : Submodule.span (𝓞 E) (S : Set (Fin n → E)) ≤ K := by
    rw [Submodule.span_le]
    intro v hv
    show ∀ j, (d : E) * v j ∈ Formalism.UG.intOE E
    intro j
    exact hds _ (Finset.mem_biUnion.2 ⟨v, Finset.mem_coe.1 hv,
      Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
  rw [← hS] at hx
  exact (show ∀ i, (d : E) * x i ∈ Formalism.UG.intOE E from hSK hx) i
end PI.InvTopW
