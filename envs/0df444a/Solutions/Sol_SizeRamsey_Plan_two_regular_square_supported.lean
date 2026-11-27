-- Prove2me | solution 1 for SizeRamsey.Plan.two_regular_square_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:08.533206+00:00
-- url     : https://prove2.me/submissions/91df5639-344e-4aba-998d-5ca9a539ee75

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_three_le_degree_of_adj
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_adj_at
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_ne_at

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
    (hcon : G.Connected) (hsq : SquareSupported G)
    (hdeg : ∀ v, G.degree v = 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 4) := by
  obtain ⟨v⟩ := hcon.nonempty
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp (by rw [hdeg v]; decide)
  obtain ⟨f, hf, -, -⟩ := hsq hw
  have hN : ∀ i y, G.Adj (f i) y → y = f (i + 1) ∨ y = f (i + 3) := by
    intro i y hy
    by_contra hc
    push Not at hc
    obtain ⟨h1, -, -, h3⟩ := IsC4Map.adj_at G hf i
    have := three_le_degree_of_adj G h1 h3.symm hy (IsC4Map.ne_at G hf i (by decide))
      hc.1.symm hc.2.symm
    rw [hdeg] at this
    omega
  have hsurj : Function.Surjective f := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨p⟩ := hcon.preconnected (f 0) x
    obtain ⟨⟨⟨a, b⟩, hab⟩, -, ha, hb⟩ :=
      p.exists_boundary_dart (Set.range f) ⟨0, rfl⟩ (fun ⟨i, hi⟩ => hx i hi)
    obtain ⟨i, rfl⟩ := ha
    rcases hN i b hab with h | h
    · exact hb ⟨_, h.symm⟩
    · exact hb ⟨_, h.symm⟩
  let e : Fin 4 ≃ V := Equiv.ofBijective f ⟨hf.1, hsurj⟩
  have hcyc : ∀ i j : Fin 4, (SimpleGraph.cycleGraph 4).Adj i j ↔ (j = i + 1 ∨ j = i + 3) := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [SimpleGraph.cycleGraph_adj] <;> decide
  have hadj : ∀ i j : Fin 4, G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph 4).Adj i j := by
    intro i j
    rw [hcyc]
    constructor
    · intro h
      rcases hN i _ h with h' | h'
      · exact Or.inl (hf.1 h')
      · exact Or.inr (hf.1 h')
    · obtain ⟨h1, -, -, h3⟩ := IsC4Map.adj_at G hf i
      rintro (rfl | rfl)
      · exact h1
      · exact h3.symm
  exact ⟨(⟨e, fun {i j} => hadj i j⟩ : SimpleGraph.cycleGraph 4 ≃g G).symm⟩
end SizeRamsey.Plan
