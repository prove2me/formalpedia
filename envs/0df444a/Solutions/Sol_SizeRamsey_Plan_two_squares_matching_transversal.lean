-- Prove2me | solution 1 for SizeRamsey.Plan.two_squares_matching_transversal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:30.627464+00:00
-- url     : https://prove2.me/submissions/9ba827ed-0980-4f9c-a7d1-806eafd3c14a

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Cubic

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} (G : SimpleGraph V)
    (l r : Fin 4 → V) (μ : Fin 4 ≃ Fin 4)
    (hl : Function.Injective l)
    (hr : Function.Injective r)
    (hdisj : ∀ i j, l i ≠ r j)
    (hcover : ∀ v,
      (∃ i, l i = v) ∨ ∃ j, r j = v)
    (hleft : ∀ i j,
      G.Adj (l i) (l j) ↔
        (SimpleGraph.cycleGraph 4).Adj i j)
    (hright : ∀ i j,
      G.Adj (r i) (r j) ↔
        (SimpleGraph.cycleGraph 4).Adj i j)
    (hcross : ∀ i j,
      G.Adj (l i) (r j) ↔ μ i = j) :
    c4Transversal G {l 0, r (μ 2)} := by
  intro f hf
  classical
  by_contra hno
  push Not at hno
  have hll : ∀ a b : Fin 4, (SimpleGraph.cycleGraph 4).Adj a b →
      a ≠ 0 → b ≠ 0 → a = 2 ∨ b = 2 := by decide
  have hcycle : ∀ a b c d k : Fin 4,
      (SimpleGraph.cycleGraph 4).Adj a b →
      (SimpleGraph.cycleGraph 4).Adj b c →
      (SimpleGraph.cycleGraph 4).Adj c d →
      (SimpleGraph.cycleGraph 4).Adj d a →
      a ≠ c → b ≠ d → a = k ∨ b = k ∨ c = k ∨ d = k := by decide
  have hrr : ∀ a b, G.Adj (r a) (l b) ↔ μ b = a := by
    intro a b
    rw [G.adj_comm, hcross]
  have h02 : f 0 ≠ f 2 := fun h => absurd (hf.1 h) (by decide)
  have h13 : f 1 ≠ f 3 := fun h => absurd (hf.1 h) (by decide)
  have hn0 := hno 0
  have hn1 := hno 1
  have hn2 := hno 2
  have hn3 := hno 3
  obtain ⟨hinj, h01, h12, h23, h30⟩ := hf
  rcases hcover (f 0) with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases hcover (f 1) with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
    rcases hcover (f 2) with ⟨c, hc⟩ | ⟨c, hc⟩ <;>
    rcases hcover (f 3) with ⟨d, hd⟩ | ⟨d, hd⟩
  all_goals
    simp only [← ha, ← hb, ← hc, ← hd, hleft, hright, hcross, hrr] at h01 h12 h23 h30
    simp only [← ha, ← hb, ← hc, ← hd, Finset.mem_insert, Finset.mem_singleton,
      not_or, ne_eq, hl.eq_iff, hr.eq_iff] at hn0 hn1 hn2 hn3 h02 h13
  · exact (hcycle a b c d 0 h01 h12 h23 h30 h02 h13).elim hn0.1
      (fun h => h.elim hn1.1 (fun h => h.elim hn2.1 hn3.1))
  · exact h02 (μ.injective (h30.trans h23.symm))
  · exact h13 (μ.injective (h12.trans h23.symm))
  · rcases hll a b h01 hn0.1 hn1.1 with ha2 | hb2
    · exact hn3.2 (h30.symm.trans (congrArg μ ha2))
    · exact hn2.2 (h12.symm.trans (congrArg μ hb2))
  · exact h02 (μ.injective (h01.trans h12.symm))
  · exact h02 (μ.injective (h01.trans h12.symm))
  · rcases hll d a h30 hn3.1 hn0.1 with hd2 | ha2
    · exact hn2.2 (h23.symm.trans (congrArg μ hd2))
    · exact hn1.2 (h01.symm.trans (congrArg μ ha2))
  · exact h13 (h01.symm.trans h30)
  · exact h13 (μ.injective (h01.trans h30.symm))
  · rcases hll b c h12 hn1.1 hn2.1 with hb2 | hc2
    · exact hn0.2 (h01.symm.trans (congrArg μ hb2))
    · exact hn3.2 (h23.symm.trans (congrArg μ hc2))
  · exact h02 (h01.symm.trans h12)
  · exact h02 (h01.symm.trans h12)
  · rcases hll c d h23 hn2.1 hn3.1 with hc2 | hd2
    · exact hn1.2 (h12.symm.trans (congrArg μ hc2))
    · exact hn0.2 (h30.symm.trans (congrArg μ hd2))
  · exact h13 (h12.symm.trans h23)
  · exact h02 (h30.symm.trans h23)
  · exact (hcycle a b c d (μ 2) h01 h12 h23 h30 h02 h13).elim hn0.2
      (fun h => h.elim hn1.2 (fun h => h.elim hn2.2 hn3.2))
end SizeRamsey.Plan
