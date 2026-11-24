-- Prove2me | solution 1 for RandOnlineSetCover.InfoLB.observation_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:03:28.712135+00:00
-- url     : https://prove2.me/submissions/ee046d25-b1f2-45a4-bde9-7850da1a3af6

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_Inner

set_option autoImplicit false

open RandOnlineSetCover.InfoLB

/-- Consecutive path vertices are parent and child. -/
private lemma pathVertex_isChild {k : ℕ} (π : InnerPath k) (s : Fin (2 * k))
    (hs : s.val + 1 < 2 * k) :
    IsChild (pathVertex π s) (pathVertex π ⟨s.val + 1, hs⟩) :=
  ⟨⟨by simp [pathVertex], fun _ => rfl⟩, rfl⟩

/-- A nonempty subtree rooted at a path vertex has a path vertex on its boundary. -/
private lemma boundary_meets_path {k : ℕ} (π : InnerPath k) (t : Fin (2 * k))
    (H : Finset (BinaryVertex (2 * k))) (hH : IsRootedSubtree (pathVertex π t) H) :
    ∃ s : Fin (2 * k), pathVertex π s ∈ boundary (pathVertex π t) H := by
  classical
  by_cases h0 : H = ∅
  · refine ⟨t, ?_⟩
    unfold boundary
    rw [if_pos h0]
    exact Finset.mem_singleton_self _
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have htH : pathVertex π t ∈ H :=
      hH.2 x hx (pathVertex π t) ⟨le_refl _, fun _ => rfl⟩ (hH.1 x hx)
    set S := Finset.univ.filter fun s : Fin (2 * k) => pathVertex π s ∈ H
    obtain ⟨s, hsS, hmax⟩ := S.exists_max_image id ⟨t, by simp [S, htH]⟩
    have hsH : pathVertex π s ∈ H := (Finset.mem_filter.mp hsS).2
    by_cases hs : s.val + 1 = 2 * k
    · refine ⟨s, ?_⟩
      unfold boundary
      rw [if_neg h0, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inr ⟨hsH, hs⟩⟩
    · have hs' : s.val + 1 < 2 * k := by omega
      refine ⟨⟨s.val + 1, hs'⟩, ?_⟩
      unfold boundary
      rw [if_neg h0, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Or.inl ⟨fun hin => ?_, pathVertex π s, hsH,
        pathVertex_isChild π s hs'⟩⟩
      have := hmax ⟨s.val + 1, hs'⟩ (by simp [S, hin])
      simp [Fin.le_def] at this

theorem solution (k m : ℕ) (hk : 0 < k) (O : BatchOrder k)
    (χ : BinaryVertex (2 * k) → Fin m) (π : InnerPath k) :
    listOpt (innerRequests O χ π) ≤ (2 * k : ℕ) := by
  classical
  set C : Finset (Fin m) := Finset.univ.image fun t => χ (pathVertex π t)
  have hcov : Covers (innerRequests O χ π) C := by
    intro e he
    unfold innerRequests innerIndices at he
    simp only [List.mem_map, List.mem_flatMap, List.mem_ofFn] at he
    obtain ⟨⟨v, H⟩, ⟨w, ⟨t, rfl⟩, ⟨H', hH', hpair⟩⟩, rfl⟩ := he
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hR := (((O (pathVertex π t)).2.2 H').mp hH').1
    obtain ⟨s, hs⟩ := boundary_meets_path π t H' hR
    refine ⟨χ (pathVertex π s), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image_of_mem χ hs
  have hcard : C.card ≤ 2 * k :=
    (Finset.card_image_le).trans (by simp)
  unfold listOpt
  exact (iInf_le _ (⟨C, hcov⟩ : {C : Finset (Fin m) // Covers _ C})).trans
    (by exact_mod_cast hcard)
