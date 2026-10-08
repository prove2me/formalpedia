-- Prove2me | solution 1 for OptimumBranchings.Polytope.branching_vector_isVertex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:11:24.471053+00:00
-- url     : https://prove2.me/submissions/c27dcf25-2d66-4602-9f7f-79e7aaa4863e

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron

set_option autoImplicit false

namespace OptimumBranchings.Polytope.A3767

open OptimumBranchings.Polytope

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- every rear of an edge of `F` is a front of an edge of `F` -/
def Closed (G : Graph V E) (F : Finset E) : Prop :=
  ∀ e ∈ F, ∃ f ∈ F, G.front f = G.rear e

theorem no_closed (G : Graph V E) (B : Finset E) (hB : G.IsBranching B)
    (F : Finset E) (hFB : F ⊆ B) (hFne : F.Nonempty) (hFc : Closed G F) : False := by
  classical
  obtain ⟨hfor, hinj⟩ := hB
  set C := F.powerset.filter (fun H => H.Nonempty ∧ Closed G H) with hC
  have hCne : C.Nonempty := ⟨F, by simp [hC, hFne, hFc]⟩
  obtain ⟨H, hHC, hmin⟩ := C.exists_min_image Finset.card hCne
  simp only [hC, Finset.mem_filter, Finset.mem_powerset] at hHC
  obtain ⟨hHF, hHne, hHc⟩ := hHC
  have hHB : H ⊆ B := hHF.trans hFB
  have hsurj : ∀ e ∈ H, ∃ g ∈ H, G.rear g = G.front e := by
    intro e he
    by_contra hcon
    push Not at hcon
    have hmem : H.erase e ∈ C := by
      simp only [hC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨(Finset.erase_subset _ _).trans hHF, ?_, ?_⟩
      · obtain ⟨f, hf, hfe⟩ := hHc e he
        refine ⟨f, Finset.mem_erase.2 ⟨?_, hf⟩⟩
        rintro rfl
        exact G.front_ne_rear f hfe
      · intro g hg
        obtain ⟨hge, hgH⟩ := Finset.mem_erase.1 hg
        obtain ⟨f, hf, hfg⟩ := hHc g hgH
        refine ⟨f, Finset.mem_erase.2 ⟨?_, hf⟩, hfg⟩
        rintro rfl
        exact hcon g hgH hfg.symm
    have := hmin _ hmem
    have h2 := Finset.card_erase_lt_of_mem he
    omega
  have himg : H.image G.rear = H.image G.front := by
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨f, hf, hfe⟩ := hHc e he
      exact ⟨f, hf, hfe⟩
    · rintro ⟨e, he, rfl⟩
      exact hsurj e he
  have hfrontinj : Set.InjOn G.front H := fun e he f hf h => hinj e (hHB he) f (hHB hf) h
  have hcardf : (H.image G.front).card = H.card := Finset.card_image_of_injOn hfrontinj
  have hrearinj : Set.InjOn G.rear H := by
    rw [← Finset.card_image_iff, himg, hcardf]
  apply hfor H hHB hHne
  intro v
  unfold Graph.meetCount
  by_cases hv : ∃ e ∈ H, G.front e = v
  · right
    obtain ⟨e, he, rfl⟩ := hv
    have h1 : (H.filter (fun f => G.front f = G.front e)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨e, ?_⟩
      ext f
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hf, hfe⟩; exact hfrontinj hf he hfe
      · rintro rfl; exact ⟨he, rfl⟩
    obtain ⟨g, hg, hge⟩ := hsurj e he
    have h2 : (H.filter (fun f => G.rear f = G.front e)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨g, ?_⟩
      ext f
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hf, hfe⟩; exact hrearinj hf hg (hfe.trans hge.symm)
      · rintro rfl; exact ⟨hg, hge⟩
    omega
  · left
    push Not at hv
    have h1 : (H.filter (fun f => G.front f = v)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f hf; exact hv f hf
    have h2 : (H.filter (fun f => G.rear f = v)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f hf hfv
      obtain ⟨g, hg, hgf⟩ := hHc f hf
      exact hv g hg (hgf.trans hfv)
    omega

theorem main (G : Graph V E) (B : Finset E) (hB : G.IsBranching B) :
    incidenceVector B ∈ branchingPolyhedron G := by
  classical
  have hsum : ∀ s : Finset E,
      ∑ e ∈ s, incidenceVector B e = ((s.filter (· ∈ B)).card : ℝ) := by
    intro s; unfold incidenceVector; rw [Finset.sum_boole]
  refine ⟨?_, ?_, ?_⟩
  · intro e; unfold incidenceVector; split_ifs <;> norm_num
  · intro v
    rw [hsum]
    have : ((Finset.univ.filter (fun e => G.front e = v)).filter (· ∈ B)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hB.2 a ha.2 b hb.2 (ha.1.trans hb.1.symm)
    exact_mod_cast this
  · intro S hS
    rw [hsum]
    set F := (Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∈ S)).filter (· ∈ B)
      with hF
    by_contra hlt
    push Not at hlt
    have hcard : S.card ≤ F.card := by
      have h1 : ((S.card : ℤ) : ℝ) - 1 < ((F.card : ℤ) : ℝ) := by exact_mod_cast hlt
      have h2 : (S.card : ℤ) - 1 < F.card := by exact_mod_cast h1
      omega
    have hFB : F ⊆ B := fun e he => (Finset.mem_filter.1 he).2
    have hmemF : ∀ e, e ∈ F ↔ (G.front e ∈ S ∧ G.rear e ∈ S) ∧ e ∈ B := by
      intro e; simp [hF]
    have himg : F.image G.front = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hv
        exact ((hmemF e).1 he).1.1
      · rw [Finset.card_image_of_injOn]
        · exact hcard
        · intro a ha b hb h
          exact hB.2 a (hFB ha) b (hFB hb) h
    apply no_closed G B hB F hFB
    · rw [← Finset.card_pos]; omega
    · intro e he
      have : G.rear e ∈ F.image G.front := by rw [himg]; exact ((hmemF e).1 he).1.2
      obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 this
      exact ⟨f, hf, hfe⟩

theorem le_one_of_mem (G : Graph V E) (y : E → ℝ) (hy : y ∈ branchingPolyhedron G) (e : E) :
    y e ≤ 1 := by
  obtain ⟨h1, h2, -⟩ := hy
  have hs := h2 (G.front e)
  have : y e ≤ ∑ f ∈ Finset.univ.filter (fun f => G.front f = G.front e), y f :=
    Finset.single_le_sum (f := y) (fun f _ => h1 f) (by simp)
  linarith

theorem vertex (G : Graph V E) (B : Finset E) (hB : G.IsBranching B) :
    IsVertex (branchingPolyhedron G) (incidenceVector B) := by
  refine ⟨main G B hB, fun e => if e ∈ B then 1 else -1, ?_⟩
  intro y hy hne
  have h0 := hy.1
  have h1 := le_one_of_mem G y hy
  apply Finset.sum_lt_sum
  · intro e _
    by_cases he : e ∈ B
    · simp [incidenceVector, he]; linarith [h1 e]
    · simp [incidenceVector, he]; linarith [h0 e]
  · by_contra hcon
    push_neg at hcon
    apply hne
    funext e
    have := hcon e (Finset.mem_univ e)
    by_cases he : e ∈ B
    · simp [incidenceVector, he] at this ⊢; linarith [h1 e]
    · simp [incidenceVector, he] at this ⊢; linarith [h0 e]

end OptimumBranchings.Polytope.A3767

open OptimumBranchings.Polytope in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : OptimumBranchings.Polytope.Graph V E) (B : Finset E) (hB : G.IsBranching B) :
    IsVertex (branchingPolyhedron G) (incidenceVector B) := by
  exact OptimumBranchings.Polytope.A3767.vertex G B hB
