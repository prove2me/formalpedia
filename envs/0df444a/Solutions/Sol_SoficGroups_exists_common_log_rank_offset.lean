-- Prove2me | solution 1 for SoficGroups.exists_common_log_rank_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/dc7f6130-c0a1-47e9-96dd-6648dec811dd

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_common_rank_offset_one_sided_sharp
import Theorems.Thm_SoficGroups_log_one_sided_of_multiplicative

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (eta H : ℝ)
    (hx : ∀ i : ι, 0 < x i)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hH : 0 < H)
    (hcomparison : ∀ i : ι, (1 - eta) * x i ≤ y i) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount (fun i => Real.log (x i))
          (fun i => Real.log (y i)) H r ≤
        (Fintype.card ι : ℝ) * |Real.log (1 - eta)| / H := by
  classical
  obtain ⟨r, hr, hbound⟩ :=
    exists_common_rank_offset_one_sided_sharp
      (fun i => Real.log (x i))
      (fun i => Real.log (y i))
      (fun _ : ι => |Real.log (1 - eta)|)
      H hH
      (fun _ => abs_nonneg _)
      (fun i => log_one_sided_of_multiplicative
        (x i) (y i) eta (hx i) heta0 heta1 (hcomparison i))
  refine ⟨r, hr, hbound.trans_eq ?_⟩
  simp
  ring
end SoficGroups
