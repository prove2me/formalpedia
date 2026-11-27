-- Prove2me | solution 1 for SizeRamsey.Plan.square_supported_no_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:55.599508+00:00
-- url     : https://prove2.me/submissions/58120042-4dd8-4ea1-99e7-633792530687

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (h : SquareSupported G) {u v : V} (huv : G.Adj u v) :
    ¬ G.IsBridge s(u, v) := by
  rw [SimpleGraph.isBridge_iff, not_not]
  obtain ⟨f, ⟨hinj, -, h12, h23, h30⟩, rfl, rfl⟩ := h huv
  have hne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j hij => hinj.ne hij
  have hadj : ∀ i j : Fin 4, G.Adj (f i) (f j) → s(f i, f j) ≠ s(f 0, f 1) →
      (G.deleteEdges {s(f 0, f 1)}).Adj (f i) (f j) := fun i j ha hn =>
    SimpleGraph.deleteEdges_adj.mpr ⟨ha, by simpa using hn⟩
  have e30 : s(f 3, f 0) ≠ s(f 0, f 1) := by
    intro he; rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hne 3 0 (by decide) h1
    · exact hne 3 1 (by decide) h1
  have e23 : s(f 2, f 3) ≠ s(f 0, f 1) := by
    intro he; rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hne 2 0 (by decide) h1
    · exact hne 2 1 (by decide) h1
  have e12 : s(f 1, f 2) ≠ s(f 0, f 1) := by
    intro he; rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hne 1 0 (by decide) h1
    · exact hne 2 0 (by decide) h2
  exact ((hadj 3 0 h30 e30).symm.reachable.trans (hadj 2 3 h23 e23).symm.reachable).trans
    (hadj 1 2 h12 e12).symm.reachable
end SizeRamsey.Plan
