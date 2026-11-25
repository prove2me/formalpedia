-- Prove2me | solution 1 for PI.InvTopW.exists_good_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:47.499143+00:00
-- url     : https://prove2.me/submissions/045a53df-670b-442d-9898-1752604f85fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_PI_InvTopW_exists_den_lat
import Theorems.Thm_PI_InvTopW_exists_single_mem

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
    (L : Submodule (𝓞 E) (Fin n → E)) (hF : L.FG)
    (hS : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 1 ≤ c ∧ (∀ x ∈ L, ∀ i, (c : E) * x i ∈ Formalism.UG.intOE E) ∧
      ∀ j, (c : E) • Pi.single j (1 : E) ∈ L := by
  obtain ⟨d, hd, hdL⟩ := exists_den_lat L hF
  choose e he1 he2 using fun j => exists_single_mem L hS j
  refine ⟨d * ∏ j, e j, Nat.mul_pos hd (Finset.prod_pos fun j _ => he1 j), fun x hx i => ?_,
    fun j => ?_⟩
  · rw [Nat.cast_mul, mul_comm (d : E), mul_assoc]
    exact mul_mem (natCast_mem _ _) (hdL x hx i)
  · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem e (Finset.mem_univ j)
    rw [hm, show d * (e j * m) = d * m * e j by ring, Nat.cast_mul, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (he2 j) _
end PI.InvTopW
