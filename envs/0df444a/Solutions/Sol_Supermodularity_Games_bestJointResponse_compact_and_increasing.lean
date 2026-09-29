-- Prove2me | solution 1 for Supermodularity.Games.bestJointResponse_compact_and_increasing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T00:55:22.43858+00:00
-- url     : https://prove2.me/submissions/bd9a900d-4023-44da-8fd1-ccd168e59043

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_BestJointResponse
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Games

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}

lemma bj_update_sup (x x' : ∀ i, Fin (m i) → ℝ) (i : ι) (a b : Fin (m i) → ℝ) :
    Function.update x i a ⊔ Function.update x' i b = Function.update (x ⊔ x') i (a ⊔ b) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Function.update_of_ne h]

lemma bj_update_inf (x x' : ∀ i, Fin (m i) → ℝ) (i : ι) (a b : Fin (m i) → ℝ) :
    Function.update x i a ⊓ Function.update x' i b = Function.update (x ⊓ x') i (a ⊓ b) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Function.update_of_ne h]

/-- The feasible section `{y | update x i y ∈ S}` of a compact `S` is compact. -/
lemma bj_section_compact (S : Set (∀ i, Fin (m i) → ℝ)) (hS : IsCompact S)
    (x : ∀ i, Fin (m i) → ℝ) (i : ι) : IsCompact {y : Fin (m i) → ℝ | Function.update x i y ∈ S} := by
  have hL : IsClosed {z : ∀ i, Fin (m i) → ℝ | ∀ j, j ≠ i → z j = x j} := by
    have : {z : ∀ i, Fin (m i) → ℝ | ∀ j, j ≠ i → z j = x j} =
        ⋂ j ∈ {j | j ≠ i}, {z | z j = x j} := by ext z; simp
    rw [this]
    exact isClosed_biInter fun j _ => isClosed_eq (continuous_apply j) continuous_const
  have heq : {y : Fin (m i) → ℝ | Function.update x i y ∈ S} =
      (fun z : ∀ i, Fin (m i) → ℝ => z i) '' (S ∩ {z | ∀ j, j ≠ i → z j = x j}) := by
    ext y
    constructor
    · intro hy
      exact ⟨Function.update x i y, ⟨hy, fun j hj => Function.update_of_ne hj _ _⟩,
        Function.update_self _ _ _⟩
    · rintro ⟨z, ⟨hzS, hzL⟩, rfl⟩
      have : Function.update x i (z i) = z := by
        funext j
        rcases eq_or_ne j i with rfl | h
        · simp
        · rw [Function.update_of_ne h, hzL j h]
      show Function.update x i (z i) ∈ S
      rw [this]; exact hzS
  rw [heq]
  exact (hS.inter_right hL).image (continuous_apply i)

lemma bj_mem_proj {S : Set (∀ i, Fin (m i) → ℝ)} {x : ∀ i, Fin (m i) → ℝ} {i : ι}
    {y : Fin (m i) → ℝ} (h : Function.update x i y ∈ S) : y ∈ proj S i := ⟨x, h⟩

lemma bj_mem_projOthers {S : Set (∀ i, Fin (m i) → ℝ)} {x : ∀ i, Fin (m i) → ℝ} {i : ι}
    {y : Fin (m i) → ℝ} (h : Function.update x i y ∈ S) : x ∈ projOthers S i := ⟨y, h⟩

/-- Properties of a single player's best responses at a feasible profile. -/
lemma bj_br (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S})
    (x : ∀ i, Fin (m i) → ℝ) (hx : x ∈ S) (i : ι) :
    (BestResponse S f i x).Nonempty ∧ IsCompact (BestResponse S f i x) ∧
      ∀ ⦃a b⦄, a ∈ BestResponse S f i x → b ∈ BestResponse S f i x →
        a ⊔ b ∈ BestResponse S f i x ∧ a ⊓ b ∈ BestResponse S f i x := by
  set Sec := {y : Fin (m i) → ℝ | Function.update x i y ∈ S} with hSec
  have hxi : x i ∈ Sec := by show Function.update x i (x i) ∈ S; rw [Function.update_eq_self]; exact hx
  obtain ⟨y0, hy0, hmax⟩ := (husc i x).exists_isMaxOn ⟨x i, hxi⟩ (bj_section_compact S hScompact x i)
  have hBR : BestResponse S f i x =
      Sec ∩ (fun y => f i (Function.update x i y)) ⁻¹' Set.Ici (f i (Function.update x i y0)) := by
    ext y
    simp only [BestResponse, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 y0 hy0⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun z hz => (isMaxOn_iff.mp hmax z hz).trans h2⟩
  refine ⟨⟨y0, ?_⟩, ?_, fun a b ha hb => ?_⟩
  · rw [hBR]; exact ⟨hy0, Set.mem_preimage.mpr (Set.mem_Ici.mpr le_rfl)⟩
  · obtain ⟨v, hv, hvEq⟩ := upperSemicontinuousOn_iff_preimage_Ici.mp (husc i x)
      (f i (Function.update x i y0))
    rw [hBR, hvEq]
    exact (bj_section_compact S hScompact x i).inter_right hv
  · obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have hsup : Function.update x i (a ⊔ b) ∈ S := by
      have := hgame.sublattice.supClosed ha1 hb1
      rwa [bj_update_sup, sup_idem] at this
    have hinf : Function.update x i (a ⊓ b) ∈ S := by
      have := hgame.sublattice.infClosed ha1 hb1
      rwa [bj_update_inf, inf_idem] at this
    have hsm := hgame.supermodular i x (bj_mem_projOthers hx') (bj_mem_proj ha1) (bj_mem_proj hb1)
    have e1 := ha2 (a ⊔ b) hsup
    have e2 := hb2 (a ⊓ b) hinf
    have e3 := ha2 b hb1
    have e4 := ha2 (a ⊓ b) hinf
    have e5 := hb2 (a ⊔ b) hsup
    have e6 := hb2 a ha1
    simp only at hsm
    refine ⟨⟨hsup, fun z hz => ?_⟩, ⟨hinf, fun z hz => ?_⟩⟩
    · have := ha2 z hz; linarith
    · have := ha2 z hz; linarith
  where hx' : Function.update x i (x i) ∈ S := by rw [Function.update_eq_self]; exact hx


/-- Topkis's monotonicity argument for one player. -/
lemma bj_incr (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S})
    {x x' : ∀ i, Fin (m i) → ℝ} (hx : x ∈ S) (hx' : x' ∈ S) (hle : x ≤ x') (i : ι)
    {A B : Fin (m i) → ℝ} (hA : A ∈ BestResponse S f i x) (hB : B ∈ BestResponse S f i x') :
    A ⊓ B ∈ BestResponse S f i x ∧ A ⊔ B ∈ BestResponse S f i x' := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    have := (bj_br S f hgame hScompact husc x hx i).2.2 hA hB
    exact ⟨this.2, this.1⟩
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  have hinf : Function.update x i (A ⊓ B) ∈ S := by
    have := hgame.sublattice.infClosed hA1 hB1
    rwa [bj_update_inf, inf_eq_left.mpr hle] at this
  have hsup : Function.update x' i (A ⊔ B) ∈ S := by
    have := hgame.sublattice.supClosed hA1 hB1
    rwa [bj_update_sup, sup_eq_right.mpr hle] at this
  have hsm := hgame.supermodular i x (bj_mem_projOthers hA1) (bj_mem_proj hA1) (bj_mem_proj hB1)
  have hid := hgame.increasing_differences i hlt
    ⟨Set.mk_mem_prod (bj_mem_proj hB1) (bj_mem_projOthers hA1),
      Set.mk_mem_prod (bj_mem_proj hB1) (bj_mem_projOthers hB1)⟩
    ⟨Set.mk_mem_prod (bj_mem_proj hsup) (bj_mem_projOthers hA1),
      Set.mk_mem_prod (bj_mem_proj hsup) (bj_mem_projOthers hB1)⟩
    (le_sup_right : B ≤ A ⊔ B)
  have o1 := hB2 (A ⊔ B) hsup
  have o2 := hA2 (A ⊓ B) hinf
  simp only at hsm hid
  refine ⟨⟨hinf, fun z hz => ?_⟩, ⟨hsup, fun z hz => ?_⟩⟩
  · have := hA2 z hz; linarith
  · have := hB2 z hz; linarith

theorem bj_main (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    (∀ x ∈ S, (BestJointResponse S f x).Nonempty ∧ IsCompact (BestJointResponse S f x) ∧
      IsSublattice (BestJointResponse S f x)) ∧
    ∀ ⦃x x' : ∀ i, Fin (m i) → ℝ⦄, x ∈ S → x' ∈ S → x ≤ x' →
      Supermodularity.Lattices.InducedSetOrder (BestJointResponse S f x)
        (BestJointResponse S f x') := by
  have hBJR : ∀ x, BestJointResponse S f x = Set.univ.pi (fun i => BestResponse S f i x) := by
    intro x; ext y; simp [BestJointResponse, Set.mem_univ_pi]
  refine ⟨fun x hx => ?_, fun x x' hx hx' hle => ?_⟩
  · have hbr := fun i => bj_br S f hgame hScompact husc x hx i
    rw [hBJR]
    refine ⟨Set.univ_pi_nonempty_iff.mpr fun i => (hbr i).1,
      isCompact_univ_pi fun i => (hbr i).2.1, ⟨fun a ha b hb => ?_, fun a ha b hb => ?_⟩⟩
    · intro i _
      exact ((hbr i).2.2 (ha i (Set.mem_univ i)) (hb i (Set.mem_univ i))).1
    · intro i _
      exact ((hbr i).2.2 (ha i (Set.mem_univ i)) (hb i (Set.mem_univ i))).2
  · intro a ha b hb
    rw [hBJR] at ha hb
    rw [hBJR, hBJR]
    refine ⟨fun i _ => ?_, fun i _ => ?_⟩
    · exact (bj_incr S f hgame hScompact husc hx hx' hle i (ha i (Set.mem_univ i))
        (hb i (Set.mem_univ i))).1
    · exact (bj_incr S f hgame hScompact husc hx hx' hle i (ha i (Set.mem_univ i))
        (hb i (Set.mem_univ i))).2

end Supermodularity.Games

open Supermodularity.Games

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hSne : S.Nonempty) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    (∀ x ∈ S, (BestJointResponse S f x).Nonempty ∧ IsCompact (BestJointResponse S f x) ∧
      IsSublattice (BestJointResponse S f x)) ∧
    ∀ ⦃x x' : ∀ i, Fin (m i) → ℝ⦄, x ∈ S → x' ∈ S → x ≤ x' →
      Supermodularity.Lattices.InducedSetOrder (BestJointResponse S f x)
        (BestJointResponse S f x') :=
  bj_main S f hgame hScompact husc
