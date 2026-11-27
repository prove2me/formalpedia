-- Prove2me | solution 1 for SizeRamsey.F17_arrows_matching4_c4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:48.679094+00:00
-- url     : https://prove2.me/submissions/cef16e5a-4103-4aed-a3e9-211d42a826fe

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
public import Theorems.Thm_SizeRamsey_Plan_leftCopy_injective
public import Theorems.Thm_SizeRamsey_Plan_rightCopy_injective
public import Theorems.Thm_SizeRamsey_Plan_copies_disjoint
public import Theorems.Thm_SizeRamsey_Plan_leftCopy_adj
public import Theorems.Thm_SizeRamsey_Plan_rightCopy_adj
public import Theorems.Thm_SizeRamsey_Plan_hasC4_map
public import Theorems.Thm_SizeRamsey_Plan_matching2_union
public import Theorems.Thm_SizeRamsey_k33MinusEdge_arrows_matching2_c4

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution :
    ArrowsMatching4C4 F17 := by
  intro R hR
  have hL : R.comap Plan.leftCopy ≤ k33MinusEdge := fun a b h =>
    (Plan.leftCopy_adj a b).1 (hR (SimpleGraph.comap_adj.1 h))
  have hRt : R.comap Plan.rightCopy ≤ k33MinusEdge := fun a b h =>
    (Plan.rightCopy_adj a b).1 (hR (SimpleGraph.comap_adj.1 h))
  have blueL : ∀ ⦃a b⦄, (k33MinusEdge \ R.comap Plan.leftCopy).Adj a b →
      (F17 \ R).Adj (Plan.leftCopy a) (Plan.leftCopy b) := fun a b h =>
    ⟨(Plan.leftCopy_adj a b).2 h.1, fun hr => h.2 (SimpleGraph.comap_adj.2 hr)⟩
  have blueR : ∀ ⦃a b⦄, (k33MinusEdge \ R.comap Plan.rightCopy).Adj a b →
      (F17 \ R).Adj (Plan.rightCopy a) (Plan.rightCopy b) := fun a b h =>
    ⟨(Plan.rightCopy_adj a b).2 h.1, fun hr => h.2 (SimpleGraph.comap_adj.2 hr)⟩
  rcases k33MinusEdge_arrows_matching2_c4 _ hL with hmL | hcL
  · rcases k33MinusEdge_arrows_matching2_c4 _ hRt with hmR | hcR
    · exact Or.inl (Plan.matching2_union Plan.leftCopy Plan.rightCopy
        Plan.leftCopy_injective Plan.rightCopy_injective Plan.copies_disjoint
        (fun _ _ h => SimpleGraph.comap_adj.1 h) (fun _ _ h => SimpleGraph.comap_adj.1 h)
        hmL hmR)
    · exact Or.inr (Plan.hasC4_map Plan.rightCopy Plan.rightCopy_injective blueR hcR)
  · exact Or.inr (Plan.hasC4_map Plan.leftCopy Plan.leftCopy_injective blueL hcL)
end SizeRamsey
