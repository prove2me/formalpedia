-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.RankA.sum_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:56.706321+00:00
-- url     : https://prove2.me/submissions/948a20d2-69f0-4195-a40a-b16393d842f6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.RankA
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.PGsh.Up.RankA
theorem _root_.solution {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    [StrongRankCondition S] (e : m → Matrix ι ι S)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hsum : ∑ i, e i = 1)
    [∀ i, Module.Free S (LinearMap.range (e i).mulVecLin)]
    [∀ i, Module.Finite S (LinearMap.range (e i).mulVecLin)] :
    ∑ i, Module.finrank S (LinearMap.range (e i).mulVecLin) = Fintype.card ι := by
  let M : m → Submodule S (ι → S) := fun i => LinearMap.range (e i).mulVecLin
  have hmem : ∀ i j (y : M j), e i *ᵥ (y : ι → S) = if i = j then (y : ι → S) else 0 := by
    intro i j y
    obtain ⟨z, hz⟩ := y.2
    simp only [Matrix.mulVecLin_apply] at hz
    rw [← hz, mulVec_mulVec, horth]
    split_ifs with h
    · subst h; rfl
    · exact zero_mulVec _
  have hsum' : ∀ x : ι → S, ∑ i, e i *ᵥ x = x := by
    intro x
    rw [← Matrix.sum_mulVec, hsum, one_mulVec]
  let E : (ι → S) ≃ₗ[S] ((i : m) → M i) :=
    { toFun := fun x i => ⟨e i *ᵥ x, x, rfl⟩
      map_add' := fun x y => by ext i : 1; apply Subtype.ext; simp [mulVec_add]
      map_smul' := fun c x => by ext i : 1; apply Subtype.ext; simp [mulVec_smul]
      invFun := fun y => ∑ i, (y i : ι → S)
      left_inv := fun x => hsum' x
      right_inv := fun y => by
        ext i : 1; apply Subtype.ext
        simp only [Matrix.mulVec_sum, hmem, Finset.sum_ite_eq, Finset.mem_univ, if_true] }
  have h1 := E.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype] at h1
  exact h1.symm
end ReciprocityTheory.PGsh.Up.RankA
