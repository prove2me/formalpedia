-- Prove2me | solution 1 for Research.shellSixIncidence_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:08:04.069604+00:00
-- url     : https://prove2.me/submissions/d12407ac-2e34-4d47-b572-c0f5c974dd48

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_shellSixOffsets_weighted_sum

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    Fintype.card ShellSixIncidence = 16786618 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    (∑ d : ShellSixOffset,
        (365 - d.val.1.natAbs) * (365 - d.val.2.natAbs)) =
        ∑ d ∈ shellSixOffsets,
          (365 - d.1.natAbs) * (365 - d.2.natAbs) := by
      symm
      exact Finset.sum_subtype shellSixOffsets (fun _ => Iff.rfl)
        (fun d => (365 - d.1.natAbs) * (365 - d.2.natAbs))
    _ = 16786618 := shellSixOffsets_weighted_sum
end Research
