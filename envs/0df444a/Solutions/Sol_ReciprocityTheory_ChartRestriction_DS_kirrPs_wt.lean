-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kirrPs_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:26.067523+00:00
-- url     : https://prove2.me/submissions/0847cffc-637f-4fc6-825d-8814841583df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (ν : Fin n → ℝ) :
    ∀ l, KirrLow ε l → kirrPs k (kirrWt ν l) ≤ kirrPs k ν
  | [], _ => le_rfl
  | p :: l, hl => by
    have ih := solution k ν l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    have hr : kirrPs k (root p.1 p.2) ≤ 0 := by
      unfold kirrPs root
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_filter,
        Finset.mem_univ, true_and]
      have h3 : (p.2 : ℕ) < p.1 := hp.1
      split_ifs with h1 h2 <;> first | (exfalso; omega) | norm_num
    have hadd : kirrPs k (kirrWt ν (p :: l)) = kirrPs k (kirrWt ν l) + kirrPs k (root p.1 p.2) := by
      simp [kirrPs, kirrWt, Finset.sum_add_distrib]
    linarith
end ReciprocityTheory.ChartRestriction.DS
