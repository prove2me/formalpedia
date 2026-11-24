-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.outside_component_attachment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:53.072088+00:00
-- url     : https://prove2.me/submissions/e8f8dccb-5225-4236-a330-ed785dee2682

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_mem_of_adj_closed
public import Theorems.Thm_SimpleGraph_Connected_exists_adj_finset_compl


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    (K : Finset α) (hK : K.Nonempty)
    (huniq : ∀ (z w : ↥((K : Set α)ᶜ)),
      (G.induce (K : Set α)ᶜ).Reachable z w →
      ∀ {a b : α}, a ∈ K → b ∈ K → G.Adj a z → G.Adj b w → a = b)
    (z : ↥((K : Set α)ᶜ)) :
    ∃ (c : α) (hc : c ∈ K), ∃ w : ↥((K : Set α)ᶜ),
      (G.induce (K : Set α)ᶜ).Reachable z w ∧ G.Adj c w ∧
      ∀ (v : α) (hv : v ∈ K) (hvc : v ≠ c),
        ¬ (G.induce ({c}ᶜ : Set α)).Reachable
          ⟨z, by simpa using (show (z : α) ≠ c from fun heq => z.property (heq.symm ▸ hc))⟩
          ⟨v, by simpa using hvc⟩ := by
  classical
  let C : Set α := {v | ∃ hv : v ∉ K,
    (G.induce (K : Set α)ᶜ).Reachable z ⟨v, hv⟩}
  have hzC : (z : α) ∈ C := ⟨z.property, Reachable.rfl⟩
  have hCK : ∀ v ∈ C, v ∉ K := fun v hv => hv.choose
  have hCproper : C.toFinset ≠ Finset.univ := by
    obtain ⟨k, hk⟩ := hK
    intro heq
    have hkC : k ∈ C := Set.mem_toFinset.mp (heq ▸ Finset.mem_univ k)
    exact hCK k hkC hk
  obtain ⟨c, hcC, w, hwC, hcw⟩ := hG.exists_adj_finset_compl
    (show C.toFinset.Nonempty from ⟨z, by simpa using hzC⟩) hCproper
  have hwC' : w ∈ C := by simpa using hwC
  obtain ⟨hwK, hzw⟩ := hwC'
  have hcK : c ∈ K := by
    by_contra hcK
    have hwr : (G.induce (K : Set α)ᶜ).Reachable
        (⟨w, hwK⟩ : ↥((K : Set α)ᶜ)) ⟨c, hcK⟩ :=
      (show (G.induce (K : Set α)ᶜ).Adj ⟨w, hwK⟩ ⟨c, hcK⟩ from hcw.symm).reachable
    exact hcC (by simpa using (show c ∈ C from ⟨hcK, hzw.trans hwr⟩))
  refine ⟨c, hcK, ⟨w, hwK⟩, hzw, hcw, ?_⟩
  intro v hv hvc hr
  have hclosed : ∀ u ∈ {y : ↥({c}ᶜ : Set α) | (y : α) ∈ C},
      ∀ t : ↥({c}ᶜ : Set α), (G.induce ({c}ᶜ : Set α)).Adj u t → (t : α) ∈ C := by
    intro u hu t hut
    obtain ⟨huK, hzu⟩ := hu
    by_cases htK : (t : α) ∈ K
    · have hct : c = (t : α) := huniq ⟨w, hwK⟩ ⟨u, huK⟩
        (hzw.symm.trans hzu) hcK htK hcw (show G.Adj t u from hut.symm)
      exact (t.property hct.symm).elim
    · exact ⟨htK, hzu.trans
        (show (G.induce (K : Set α)ᶜ).Adj ⟨u, huK⟩ ⟨t, htK⟩ from hut).reachable⟩
  have hvC := reachable_mem_of_adj_closed hclosed hr hzC
  exact hCK v hvC hv
end WrittenOnTheWallII.GraphConjecture84
