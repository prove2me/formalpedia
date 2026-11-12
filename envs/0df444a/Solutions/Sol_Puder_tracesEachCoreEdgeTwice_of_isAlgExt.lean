-- Prove2me | solution 1 for Puder.tracesEachCoreEdgeTwice_of_isAlgExt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:06:05.549208+00:00
-- url     : https://prove2.me/submissions/f0d72e30-6e15-478c-b477-d5ac39c26d37

import Mathlib
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
import Theorems.Thm_Puder_exists_mem_traverses_of_isAlgExt_of_isCoreEdge
import Theorems.Thm_Puder_isPrimitiveIn_of_ncard_traverses_eq_one

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

theorem traverses_of_mem_closure (J : Subgroup (FreeGroup (Fin d))) (T : Set (FreeGroup (Fin d)))
    (hT : T ⊆ J) {h : FreeGroup (Fin d)} (hh : h ∈ Subgroup.closure T)
    {i : ℕ} {g : FreeGroup (Fin d)} {x : Fin d} (htr : Traverses J h i g x) :
    ∃ t ∈ T, ∃ j, Traverses J t j g x := by
  have hle : Subgroup.closure T ≤ J := (Subgroup.closure_le J).mpr hT
  induction hh using Subgroup.closure_induction generalizing i with
  | mem t ht => exact ⟨t, ht, i, htr⟩
  | one =>
    have := traverses_lt_length J htr
    simp at this
  | mul a b ha hb iha ihb =>
    rcases traverses_mul J (hle ha) htr with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact iha hj
    · exact ihb hj
  | inv a ha iha =>
    obtain ⟨j, hj⟩ := traverses_inv J (hle ha) htr
    exact iha hj

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}
alias traverses_of_mem_closure := Puder.Q284.PartW.traverses_of_mem_closure

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

theorem isFreeFactor_zpowers_of_isPrimitiveIn (N : Subgroup (FreeGroup (Fin d))) (w : FreeGroup (Fin d))
    (h : IsPrimitiveIn N w) : IsFreeFactor (Subgroup.zpowers w) N := by
  obtain ⟨ι, b, i, hb⟩ := h
  refine ⟨ι, b, {i}, ?_⟩
  rw [Set.image_singleton, hb, Subgroup.zpowers_eq_closure]

/-- Puder, Lemma 4.1. -/
theorem tracesEachCoreEdgeTwice_of_isAlgExt_dev (w : FreeGroup (Fin d))
    (N : Subgroup (FreeGroup (Fin d))) (hN : N.FG) (halg : IsAlgExt (Subgroup.zpowers w) N)
    (hne : Subgroup.zpowers w ≠ N) : TracesEachCoreEdgeTwice N w := by
  intro g x hcore
  have hwN : w ∈ N := halg.1 (Subgroup.mem_zpowers w)
  obtain ⟨h, hh, i, hi⟩ :=
    Puder.exists_mem_traverses_of_isAlgExt_of_isCoreEdge _ N halg g x hcore
  have hT : ({w} : Set (FreeGroup (Fin d))) ⊆ N := by simpa using hwN
  obtain ⟨t, ht, j, hj⟩ := traverses_of_mem_closure N {w} hT
    (by rwa [← Subgroup.zpowers_eq_closure]) hi
  rw [Set.mem_singleton_iff] at ht
  subst ht
  have hfin : {i : ℕ | Traverses N t i g x}.Finite :=
    (Set.finite_lt_nat t.toWord.length).subset fun i hi => traverses_lt_length N hi
  have hpos : 1 ≤ {i : ℕ | Traverses N t i g x}.ncard :=
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_ne_zero_of_mem (a := j) hj hfin))
  by_contra hlt
  have h1 : {i : ℕ | Traverses N t i g x}.ncard = 1 := by omega
  have hprim := Puder.isPrimitiveIn_of_ncard_traverses_eq_one N hN t hwN g x h1
  exact halg.2 _ le_rfl (lt_of_le_of_ne halg.1 hne) (isFreeFactor_zpowers_of_isPrimitiveIn N t hprim)

end Puder.Q284
end

section
open Puder
open Puder.Q284
variable {d : ℕ}
theorem solution (w : FreeGroup (Fin d))
    (N : Subgroup (FreeGroup (Fin d))) (hN : N.FG) (halg : IsAlgExt (Subgroup.zpowers w) N)
    (hne : Subgroup.zpowers w ≠ N) : TracesEachCoreEdgeTwice N w := by
  exact Puder.Q284.tracesEachCoreEdgeTwice_of_isAlgExt_dev w N hN halg hne
end
