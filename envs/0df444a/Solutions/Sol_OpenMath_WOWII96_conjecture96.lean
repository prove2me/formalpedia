-- Prove2me | solution 1 for OpenMath.WOWII96.conjecture96
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:19.940503+00:00
-- url     : https://prove2.me/submissions/d29bad93-32d0-4d48-8d19-c1f1ea1a75be

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_OpenMath_WOWII96
public import Theorems.Thm_OpenMath_WOWII96_indepNum_le_one_of_local
public import Theorems.Thm_OpenMath_WOWII96_key
public import Theorems.Thm_OpenMath_card_le_indepNeighborsCard


set_option autoImplicit true
@[expose] public section
public section
open OpenMath OpenMath.WOWII96
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [Nontrivial α]
namespace OpenMath.WOWII96
theorem _root_.solution (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  intro minDistEven maxL
  obtain ⟨v, -, hv⟩ := mem_image.mp (min'_mem (univ.image (distEven G)) (by simp))
  have hmin : distEven G v = minDistEven := hv
  have hL : ∀ u, indepNeighborsCard G u ≤ maxL := fun u =>
    le_max' _ _ (mem_image_of_mem _ (mem_univ u))
  -- `maxL ≥ 1`: a nontrivial connected graph has an edge
  have hL1 : 1 ≤ maxL := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist a b
    have hnil : ¬ q.Nil := fun hn => hab hn.eq
    have : ({q.snd} : Finset α).card ≤ indepNeighborsCard G a :=
      card_le_indepNeighborsCard (by simpa using q.adj_snd hnil) (by simp)
    simp at this
    exact this.trans (hL a)
  rcases Nat.lt_or_ge maxL 2 with hlt | hge
  · -- every neighbourhood is a clique, so `G` is complete
    have hα := indepNum_le_one_of_local h (fun u => (hL u).trans (by omega))
    have : (maxL : ℝ) = 1 := by exact_mod_cast (by omega : maxL = 1)
    rw [this]
    have : (G.indepNum : ℝ) ≤ 1 := by exact_mod_cast hα
    linarith
  · have hk := key G h v maxL hge hL
    rw [hmin] at hk
    have hk' : (G.indepNum : ℝ) + minDistEven ≤ 1 + (minDistEven : ℝ) * maxL := by
      exact_mod_cast hk
    nlinarith
end OpenMath.WOWII96
