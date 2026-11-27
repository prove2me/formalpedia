-- Prove2me | solution 1 for SizeRamsey.Plan.subcubic_chord_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:44.01616+00:00
-- url     : https://prove2.me/submissions/b41bbcc6-067e-4ab8-a6d0-05a5a4746891

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_two_le_degree_of_adj
public import Theorems.Thm_SizeRamsey_Plan_three_le_degree_of_adj
public import Theorems.Thm_SizeRamsey_Plan_four_le_degree_of_adj
public import Theorems.Thm_SizeRamsey_Plan_two_mul_edgeCount_induce
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_adj_at
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_ne_at
public import Theorems.Thm_SizeRamsey_Plan_erase_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_tau4_delete_vertices_le


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
    (hdeg : ∀ v, G.degree v ≤ 3)
    (f : Fin 4 → V) (hf : IsC4Map G f)
    (hac : G.Adj (f 0) (f 2)) :
    tau4 G ≤ tau4 (erase G {f 0,f 1,f 2}) + 1 ∧
    edgeCount (erase G {f 0,f 1,f 2}) +
      G.degree (f 1) + 3 = edgeCount G ∧
    2 ≤ G.degree (f 1) := by
  have hinj := hf.1
  have hfc := hf
  obtain ⟨-, h01, h12, h23, h30⟩ := hf
  have hne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j h => hinj.ne h
  have hd0 : G.degree (f 0) = 3 := le_antisymm (hdeg _)
    (three_le_degree_of_adj G h01 hac h30.symm (hne 1 2 (by decide)) (hne 1 3 (by decide))
      (hne 2 3 (by decide)))
  have hd2 : G.degree (f 2) = 3 := le_antisymm (hdeg _)
    (three_le_degree_of_adj G h12.symm h23 hac.symm (hne 1 3 (by decide)) (hne 1 0 (by decide))
      (hne 3 0 (by decide)))
  have hN : ∀ a : Fin 4, (a = 0 ∨ a = 2) → ∀ y, G.Adj (f a) y → ∃ j, j ≠ a ∧ y = f j := by
    rintro a (rfl | rfl) y hy
    · by_contra hc
      push Not at hc
      have := four_le_degree_of_adj G h01 hac h30.symm hy (hne 1 2 (by decide))
        (hne 1 3 (by decide)) (hc 1 (by decide)).symm (hne 2 3 (by decide))
        (hc 2 (by decide)).symm (hc 3 (by decide)).symm
      omega
    · by_contra hc
      push Not at hc
      have := four_le_degree_of_adj G h12.symm h23 hac.symm hy (hne 1 3 (by decide))
        (hne 1 0 (by decide)) (hc 1 (by decide)).symm (hne 3 0 (by decide))
        (hc 3 (by decide)).symm (hc 0 (by decide)).symm
      omega
  have key4 : ∀ a b c d : Fin 4, a ≠ 1 → b ≠ 1 → c ≠ 1 → d ≠ 1 → a ≠ b → a ≠ c → a ≠ d →
      b ≠ c → b ≠ d → c ≠ d → False := by intro a b c d; omega
  have key2 : ∀ iq ir : Fin 4, iq ≠ 1 → ir ≠ 1 → iq ≠ ir → ¬(iq = 0 ∨ iq = 2) →
      (ir = 0 ∨ ir = 2) := by intro a b; omega
  refine ⟨?_, ?_, two_le_degree_of_adj G h01.symm h12 (hne 0 2 (by decide))⟩
  · have hHit : HitsDeleted G {f 0, f 1, f 2} {f 1} := by
      intro g hg ⟨k, hk⟩
      by_contra hX
      push Not at hX
      have hX' : ∀ j, g j ≠ f 1 := fun j h => hX j (by simp [h])
      have hidx : ∀ j i, g j = f i → i ≠ 1 := fun j i h hi => hX' j (hi ▸ h)
      obtain ⟨g1, g2, g3, g4⟩ := IsC4Map.adj_at G hg k
      have n13 := IsC4Map.ne_at G hg k (a := 1) (b := 3) (by decide)
      have n12 := IsC4Map.ne_at G hg k (a := 1) (b := 2) (by decide)
      have n23 := IsC4Map.ne_at G hg k (a := 2) (b := 3) (by decide)
      have n02 := IsC4Map.ne_at G hg k (a := 0) (b := 2) (by decide)
      simp only [add_zero] at n02
      obtain ⟨a, ha, hka⟩ : ∃ a : Fin 4, (a = 0 ∨ a = 2) ∧ g k = f a := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with h | h | h
        · exact ⟨0, Or.inl rfl, h⟩
        · exact absurd h (hX' k)
        · exact ⟨2, Or.inr rfl, h⟩
      rw [hka] at g1 g4
      obtain ⟨iq, hqa, hq⟩ := hN a ha _ g1
      obtain ⟨ir, hra, hr⟩ := hN a ha _ g4.symm
      have hqr : iq ≠ ir := fun h => n13 (by rw [hq, hr, h])
      have hq1 := hidx _ _ hq
      have hr1 := hidx _ _ hr
      have ha1 : a ≠ 1 := by rcases ha with rfl | rfl <;> decide
      by_cases hqA : iq = 0 ∨ iq = 2
      · rw [hq] at g2
        obtain ⟨it, htq, ht⟩ := hN iq hqA _ g2
        have hta : it ≠ a := fun h => n02 (by rw [hka, ht, h])
        have htr : it ≠ ir := fun h => n23 (by rw [ht, hr, h])
        exact key4 a iq ir it ha1 hq1 hr1 (hidx _ _ ht) hqa.symm hra.symm hta.symm hqr
          htq.symm htr.symm
      · have hrA := key2 iq ir hq1 hr1 hqr hqA
        rw [hr] at g3
        obtain ⟨it, htr, ht⟩ := hN ir hrA _ g3.symm
        have hta : it ≠ a := fun h => n02 (by rw [hka, ht, h])
        have htq : it ≠ iq := fun h => n12 (by rw [ht, hq, h])
        exact key4 a iq ir it ha1 hq1 hr1 (hidx _ _ ht) hqa.symm hra.symm hta.symm hqr
          htq.symm htr.symm
    have := tau4_delete_vertices_le G {f 0, f 1, f 2} {f 1} (by simp) hHit
    simpa using this
  · have h1 := erase_edgeCount G {f 0, f 1, f 2}
    have h2 := two_mul_edgeCount_induce G {f 0, f 1, f 2}
    have m0 : f 0 ∉ ({f 1, f 2} : Finset V) := by
      simp [hne 0 1 (by decide), hne 0 2 (by decide)]
    have n12 := hne 1 2 (by decide)
    rw [Finset.sum_insert m0, Finset.sum_pair n12, hd0, hd2] at h1
    simp only [Finset.sum_insert m0, Finset.sum_pair n12, SimpleGraph.irrefl, h01, h12, hac,
      h01.symm, h12.symm, hac.symm, ite_true, ite_false] at h2
    omega
end SizeRamsey.Plan
