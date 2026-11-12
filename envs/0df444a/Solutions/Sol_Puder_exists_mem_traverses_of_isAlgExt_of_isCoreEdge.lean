-- Prove2me | solution 1 for Puder.exists_mem_traverses_of_isAlgExt_of_isCoreEdge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:06:04.309617+00:00
-- url     : https://prove2.me/submissions/72b8914b-90a4-476e-ba54-0015e307607f

import Mathlib
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
import Theorems.Thm_Puder_isFreeFactor_of_le_of_mem_of_traverses
section
namespace Puder.Q284
variable {d : ℕ}
/-!
# q284 Blueprint: PP15 Claim 4.2, Lemma 4.1 and Takahasi from Claim 3.3(4) and Lemma 4.1's last step

Infrastructure on walks of words in Schreier coset graphs (stubs, proved in Parts), then the three
reductions, proved here from the stubs.
-/
/-- The walk of the (not necessarily reduced) list `L` from the coset `J` crosses the `x`-edge
leaving the coset `J g`. -/
def ListTraverses (J : Subgroup (FreeGroup (Fin d))) (L : List (Fin d × Bool))
    (g : FreeGroup (Fin d)) (x : Fin d) : Prop :=
  ∃ (p s : List (Fin d × Bool)) (b : Bool), L = p ++ (x, b) :: s ∧
    (if b then FreeGroup.mk p else FreeGroup.mk p * (FreeGroup.of x)⁻¹) * g⁻¹ ∈ J

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem exists_traverses_iff (J : Subgroup (FreeGroup (Fin d))) (w g : FreeGroup (Fin d))
    (x : Fin d) : (∃ i, Traverses J w i g x) ↔ ListTraverses J w.toWord g x := by
  constructor
  · rintro ⟨i, p, s, b, hw, -, hm⟩
    exact ⟨p, s, b, hw, hm⟩
  · rintro ⟨p, s, b, hw, hm⟩
    exact ⟨p.length, p, s, b, hw, rfl, hm⟩

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem mk_cancel_pair (L₁ L₂ : List (Fin d × Bool)) (z : Fin d) (c : Bool) :
    FreeGroup.mk (L₁ ++ (z, c) :: (z, !c) :: L₂) = FreeGroup.mk (L₁ ++ L₂) :=
  Quot.sound FreeGroup.Red.Step.not

theorem listTraverses_of_step (J : Subgroup (FreeGroup (Fin d))) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red.Step L L') (g : FreeGroup (Fin d)) (x : Fin d) :
    ListTraverses J L' g x → ListTraverses J L g x := by
  cases h with
  | @not L₁ L₂ z c =>
    rintro ⟨p, s, b, hL, hm⟩
    rcases List.append_eq_append_iff.mp hL with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hc⟩
    · refine ⟨L₁ ++ (z, c) :: (z, !c) :: a', s, b, by simp, ?_⟩
      rwa [mk_cancel_pair]
    · rcases List.cons_eq_append_iff.mp hc with ⟨rfl, rfl⟩ | ⟨c'', rfl, rfl⟩
      · refine ⟨p ++ (z, c) :: (z, !c) :: [], s, b, by simp, ?_⟩
        rwa [mk_cancel_pair, List.append_nil]
      · exact ⟨p, c'' ++ (z, c) :: (z, !c) :: L₂, b, by simp, hm⟩

theorem listTraverses_of_red (J : Subgroup (FreeGroup (Fin d))) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red L L') (g : FreeGroup (Fin d)) (x : Fin d) :
    ListTraverses J L' g x → ListTraverses J L g x := by
  induction h with
  | refl => exact id
  | tail _ hstep ih => exact fun h' => ih (listTraverses_of_step J hstep g x h')

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem cond_append_of_mem (J : Subgroup (FreeGroup (Fin d))) (L₁ a : List (Fin d × Bool))
    (h : FreeGroup.mk L₁ ∈ J) (g : FreeGroup (Fin d)) (x : Fin d) (b : Bool)
    (hm : (if b then FreeGroup.mk (L₁ ++ a) else FreeGroup.mk (L₁ ++ a) * (FreeGroup.of x)⁻¹)
      * g⁻¹ ∈ J) :
    (if b then FreeGroup.mk a else FreeGroup.mk a * (FreeGroup.of x)⁻¹) * g⁻¹ ∈ J := by
  rw [← FreeGroup.mul_mk] at hm
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_assoc] at hm ⊢
    exact (J.mul_mem_cancel_left h).mp hm
  · simp only [↓reduceIte, mul_assoc] at hm ⊢
    exact (J.mul_mem_cancel_left h).mp hm

theorem listTraverses_append_of_mem (J : Subgroup (FreeGroup (Fin d))) (L₁ L₂ : List (Fin d × Bool))
    (h : FreeGroup.mk L₁ ∈ J) (g : FreeGroup (Fin d)) (x : Fin d) :
    ListTraverses J (L₁ ++ L₂) g x → ListTraverses J L₁ g x ∨ ListTraverses J L₂ g x := by
  rintro ⟨p, s, b, hL, hm⟩
  rcases List.append_eq_append_iff.mp hL with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hc⟩
  · exact Or.inr ⟨a', s, b, rfl, cond_append_of_mem J L₁ a' h g x b hm⟩
  · rcases List.cons_eq_append_iff.mp hc with ⟨rfl, rfl⟩ | ⟨c'', rfl, rfl⟩
    · refine Or.inr ⟨[], s, b, rfl, cond_append_of_mem J _ [] h g x b ?_⟩
      simpa using hm
    · exact Or.inl ⟨p, c'', b, rfl, hm⟩

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem traverses_mul (J : Subgroup (FreeGroup (Fin d))) {a b : FreeGroup (Fin d)} (ha : a ∈ J)
    {i : ℕ} {g : FreeGroup (Fin d)} {x : Fin d} (h : Traverses J (a * b) i g x) :
    (∃ j, Traverses J a j g x) ∨ ∃ j, Traverses J b j g x := by
  have h1 : ListTraverses J (a * b).toWord g x := (exists_traverses_iff J _ g x).mp ⟨i, h⟩
  rw [FreeGroup.toWord_mul] at h1
  have h2 := listTraverses_of_red J FreeGroup.reduce.red g x h1
  have ha' : FreeGroup.mk a.toWord ∈ J := by rwa [FreeGroup.mk_toWord]
  rcases listTraverses_append_of_mem J _ _ ha' g x h2 with h3 | h3
  · exact Or.inl ((exists_traverses_iff J _ g x).mpr h3)
  · exact Or.inr ((exists_traverses_iff J _ g x).mpr h3)

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}
alias traverses_mul := Puder.Q284.PartW.traverses_mul

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem traverses_inv (J : Subgroup (FreeGroup (Fin d))) {a : FreeGroup (Fin d)} (ha : a ∈ J)
    {i : ℕ} {g : FreeGroup (Fin d)} {x : Fin d} (h : Traverses J a⁻¹ i g x) :
    ∃ j, Traverses J a j g x := by
  obtain ⟨p, s, b, hw, -, hm⟩ := h
  have hmk : a⁻¹ = FreeGroup.mk p * FreeGroup.mk [(x, b)] * FreeGroup.mk s := by
    rw [FreeGroup.mul_mk, FreeGroup.mul_mk, List.append_assoc, List.singleton_append, ← hw,
      FreeGroup.mk_toWord]
  have hword : a.toWord = FreeGroup.invRev s ++ (x, !b) :: FreeGroup.invRev p := by
    have := congrArg FreeGroup.invRev hw
    rw [← FreeGroup.toWord_inv, inv_inv] at this
    rw [this]; simp [FreeGroup.invRev]
  refine ⟨_, _, _, _, hword, rfl, ?_⟩
  rw [← FreeGroup.inv_mk]
  have ha' : a = (FreeGroup.mk p * FreeGroup.mk [(x, b)] * FreeGroup.mk s)⁻¹ := by
    rw [← hmk, inv_inv]
  cases b
  · have hx : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ := by
      rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hm ⊢
    rw [hx] at ha'
    have : (FreeGroup.mk s)⁻¹ * g⁻¹ = a * (FreeGroup.mk p * (FreeGroup.of x)⁻¹ * g⁻¹) := by
      rw [ha']; group
    rw [this]; exact J.mul_mem ha hm
  · have hx : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl
    simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true] at hm ⊢
    rw [hx] at ha'
    have : (FreeGroup.mk s)⁻¹ * (FreeGroup.of x)⁻¹ * g⁻¹ = a * (FreeGroup.mk p * g⁻¹) := by
      rw [ha']; group
    rw [this]; exact J.mul_mem ha hm

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}
alias traverses_inv := Puder.Q284.PartW.traverses_inv

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem traverses_lt_length (J : Subgroup (FreeGroup (Fin d))) {w : FreeGroup (Fin d)} {i : ℕ}
    {g : FreeGroup (Fin d)} {x : Fin d} (h : Traverses J w i g x) : i < w.toWord.length := by
  obtain ⟨p, s, b, hw, hp, -⟩ := h
  rw [hw]; simp; omega

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

alias traverses_lt_length := Puder.Q284.PartW.traverses_lt_length

end Puder.Q284
end

section
namespace Puder.Q284.PartT
open Puder Puder.Q284
variable {d : ℕ}

end Puder.Q284.PartT
end

section
namespace Puder.Q284
variable {d : ℕ}

/-- `π_1^X` of the subgraph of `Γ_X(J)` traced by the elements of `H`. -/
def tracedSubgroup (H J : Subgroup (FreeGroup (Fin d))) (hHJ : H ≤ J) : Subgroup (FreeGroup (Fin d)) where
  carrier := {g | g ∈ J ∧ ∀ (i : ℕ) (y : FreeGroup (Fin d)) (x : Fin d), Traverses J g i y x →
    ∃ h ∈ H, ∃ j : ℕ, Traverses J h j y x}
  mul_mem' := by
    rintro a b ⟨haJ, ha⟩ ⟨hbJ, hb⟩
    refine ⟨J.mul_mem haJ hbJ, fun i y x htr => ?_⟩
    rcases traverses_mul J haJ htr with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ha j y x hj
    · exact hb j y x hj
  one_mem' := by
    refine ⟨J.one_mem, fun i y x htr => ?_⟩
    have := traverses_lt_length J htr
    simp at this
  inv_mem' := by
    rintro a ⟨haJ, ha⟩
    refine ⟨J.inv_mem haJ, fun i y x htr => ?_⟩
    obtain ⟨j, hj⟩ := traverses_inv J haJ htr
    exact ha j y x hj

/-- PP15, Claim 4.2 (as used in Puder's Lemma 4.1): `η_{H→J}` is onto when `H ≤_alg J`. -/
theorem exists_mem_traverses_of_isAlgExt_of_isCoreEdge_dev (H J : Subgroup (FreeGroup (Fin d)))
    (halg : IsAlgExt H J) (g : FreeGroup (Fin d)) (x : Fin d) (hcore : IsCoreEdge J g x) :
    ∃ h ∈ H, ∃ i : ℕ, Traverses J h i g x := by
  set L := tracedSubgroup H J halg.1 with hL
  have hHL : H ≤ L := fun h hh => ⟨halg.1 hh, fun i y x htr => ⟨h, hh, i, htr⟩⟩
  have hLJ : L ≤ J := fun g hg => hg.1
  have hff : IsFreeFactor L J := by
    refine Puder.isFreeFactor_of_le_of_mem_of_traverses L J hLJ ?_
    intro g hgJ hg
    refine ⟨hgJ, fun i y x htr => ?_⟩
    obtain ⟨l, hl, j, hj⟩ := hg i y x htr
    exact hl.2 j y x hj
  have hLeq : L = J := by
    by_contra hne
    exact halg.2 L hHL (lt_of_le_of_ne hLJ hne) hff
  obtain ⟨k, hk, i, hki⟩ := hcore
  have hkL : k ∈ L := hLeq ▸ hk
  exact hkL.2 i g x hki

end Puder.Q284
end

section
open Puder
open Puder.Q284
variable {d : ℕ}
theorem solution (H J : Subgroup (FreeGroup (Fin d)))
    (halg : IsAlgExt H J) (g : FreeGroup (Fin d)) (x : Fin d) (hcore : IsCoreEdge J g x) :
    ∃ h ∈ H, ∃ i : ℕ, Traverses J h i g x := by
  exact Puder.Q284.exists_mem_traverses_of_isAlgExt_of_isCoreEdge_dev H J halg g x hcore
end
