-- Prove2me | solution 1 for Puder.setOf_isAlgExt_finite_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:06:05.194086+00:00
-- url     : https://prove2.me/submissions/109fa8ce-5dc3-4e99-a13c-adeffea0971a

import Mathlib
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
import Theorems.Thm_Puder_exists_mem_traverses_of_isAlgExt_of_isCoreEdge
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

end Puder.Q284
end

section
namespace Puder.Q284.PartT
open Puder Puder.Q284
variable {d : ℕ}
theorem core_step (J J' : Subgroup (FreeGroup (Fin d))) (V : Finset (FreeGroup (Fin d)))
    (hrel : ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ J → a * b⁻¹ ∈ J')
    {m a v a' m' : FreeGroup (Fin d)} (hm : m ∈ V) (hv : v ∈ V)
    (hav : a * v⁻¹ ∈ J) (hav' : a * v⁻¹ ∈ J') (hma : m * a⁻¹ ∈ J)
    (heq : a' * m'⁻¹ = a * m⁻¹) : a' * m'⁻¹ ∈ J ∧ a' * m'⁻¹ ∈ J' := by
  have h1 : m * v⁻¹ ∈ J := by
    have := J.mul_mem hma hav
    simpa [mul_assoc] using this
  have h2 := hrel m hm v hv h1
  rw [heq]
  refine ⟨by simpa using J.inv_mem hma, ?_⟩
  have := J'.mul_mem hav' (J'.inv_mem h2)
  simpa [mul_assoc] using this

theorem mk_letter (x : Fin d) (c : Bool) :
    FreeGroup.mk [(x, c)] = if c then FreeGroup.of x else (FreeGroup.of x)⁻¹ := by
  cases c
  · simp [FreeGroup.inv_mk, FreeGroup.invRev, FreeGroup.of]
  · rfl

theorem le_of_forall_mem_iff (T : Finset (FreeGroup (Fin d))) (V : Finset (FreeGroup (Fin d)))
    (hV : ∀ t ∈ T, ∀ j ≤ t.toWord.length, FreeGroup.mk (t.toWord.take j) ∈ V) (h1 : (1 : FreeGroup (Fin d)) ∈ V)
    (J J' : Subgroup (FreeGroup (Fin d)))
    (hJ : ∀ (y : FreeGroup (Fin d)) (x : Fin d), IsCoreEdge J y x → ∃ t ∈ T, ∃ j, Traverses J t j y x)
    (hrel : ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ J → a * b⁻¹ ∈ J') : J ≤ J' := by
  intro g hg
  set L := g.toWord with hLdef
  have key : ∀ k ≤ L.length, ∃ v ∈ V, FreeGroup.mk (L.take k) * v⁻¹ ∈ J ∧
      FreeGroup.mk (L.take k) * v⁻¹ ∈ J' := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, h1, by simp [← FreeGroup.one_eq_mk], by simp [← FreeGroup.one_eq_mk]⟩
    | succ k ih =>
      intro hk
      obtain ⟨v, hv, hvJ, hvJ'⟩ := ih (by omega)
      have hk' : k < L.length := by omega
      have hL : L = L.take k ++ L[k] :: L.drop (k+1) := by
        rw [← List.drop_eq_getElem_cons hk', List.take_append_drop]
      have htk : L.take (k+1) = L.take k ++ [L[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk']; rfl
      rw [htk]
      generalize L[k] = e at hL
      obtain ⟨x, b⟩ := e
      set p := FreeGroup.mk (L.take k) with hp
      have hlen : (L.take k).length = k := by simp; omega
      set y : FreeGroup (Fin d) := if b then p else p * (FreeGroup.of x)⁻¹ with hy
      have htr : Traverses J g k y x :=
        ⟨L.take k, L.drop (k+1), b, hL, hlen, by rw [← hp]; cases b <;> simp [hy]⟩
      obtain ⟨t, ht, j, q, s', b', hteq, hqlen, hmem⟩ := hJ y x ⟨g, hg, k, htr⟩
      have hu0 : FreeGroup.mk q ∈ V := by
        have := hV t ht j (by rw [hteq]; simp; omega)
        rwa [hteq, ← hqlen, List.take_left'] at this
        rfl
      have hu1 : FreeGroup.mk q * FreeGroup.mk [(x, b')] ∈ V := by
        have := hV t ht (j+1) (by rw [hteq]; simp; omega)
        rw [FreeGroup.mul_mk]
        convert this using 2
        rw [hteq, ← hqlen]
        clear this hteq hqlen hmem hu0
        induction q with
        | nil => simp
        | cons a q ih => simp [ih]
      rw [← FreeGroup.mul_mk, mk_letter, ← hp]
      rw [mk_letter] at hu1
      cases b <;> cases b' <;> simp only [if_true, if_false, Bool.false_eq_true, hy] at hu1 hmem ⊢
      · exact ⟨_, hu1, core_step J J' V hrel hu0 hv hvJ hvJ' (m := FreeGroup.mk q)
          (by simpa [mul_assoc] using hmem) (by group)⟩
      · exact ⟨_, hu0, core_step J J' V hrel hu1 hv hvJ hvJ'
          (m := FreeGroup.mk q * FreeGroup.of x) (by simpa [mul_assoc] using hmem) (by group)⟩
      · exact ⟨_, hu0, core_step J J' V hrel hu1 hv hvJ hvJ'
          (m := FreeGroup.mk q * (FreeGroup.of x)⁻¹) (by simpa [mul_assoc] using hmem) (by group)⟩
      · exact ⟨_, hu1, core_step J J' V hrel hu0 hv hvJ hvJ' (m := FreeGroup.mk q)
          (by simpa [mul_assoc] using hmem) (by group)⟩
  obtain ⟨v, hv, hvJ, hvJ'⟩ := key L.length le_rfl
  rw [List.take_length, hLdef, FreeGroup.mk_toWord] at hvJ hvJ'
  have hvJ1 : v * 1⁻¹ ∈ J := by simpa using J.mul_mem (J.inv_mem hvJ) hg
  have := hrel v hv 1 h1 hvJ1
  have hvJ'' : v ∈ J' := by simpa using this
  have := J'.mul_mem hvJ' hvJ''
  rwa [inv_mul_cancel_right] at this

end Puder.Q284.PartT
end

section
namespace Puder.Q284
variable {d : ℕ}
alias le_of_forall_mem_iff := Puder.Q284.PartT.le_of_forall_mem_iff

/-- Takahasi: a finitely generated subgroup has only finitely many algebraic extensions. -/
theorem setOf_isAlgExt_finite_of_fg_dev (H : Subgroup (FreeGroup (Fin d))) (hH : H.FG) :
    {J : Subgroup (FreeGroup (Fin d)) | IsAlgExt H J}.Finite := by
  classical
  obtain ⟨T, hT⟩ := hH
  set V : Finset (FreeGroup (Fin d)) :=
    insert 1 (T.biUnion fun t => (Finset.range (t.toWord.length + 1)).image
      fun j => FreeGroup.mk (t.toWord.take j)) with hVdef
  have hV : ∀ t ∈ T, ∀ j ≤ t.toWord.length, FreeGroup.mk (t.toWord.take j) ∈ V := by
    intro t ht j hj
    refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_image.mpr ⟨j, ?_, rfl⟩⟩)
    simp only [Finset.mem_range]; omega
  have h1 : (1 : FreeGroup (Fin d)) ∈ V := Finset.mem_insert_self _ _
  have hcov : ∀ J, IsAlgExt H J → ∀ (y : FreeGroup (Fin d)) (x : Fin d), IsCoreEdge J y x →
      ∃ t ∈ T, ∃ j, Traverses J t j y x := by
    intro J hJ y x hc
    obtain ⟨h, hh, i, hi⟩ := Puder.exists_mem_traverses_of_isAlgExt_of_isCoreEdge H J hJ y x hc
    have hTJ : (↑T : Set (FreeGroup (Fin d))) ⊆ J := fun t ht => hJ.1 (hT ▸ Subgroup.subset_closure ht)
    obtain ⟨t, ht, j, hj⟩ := traverses_of_mem_closure J (↑T) hTJ (by rwa [hT]) hi
    exact ⟨t, ht, j, hj⟩
  let f : Subgroup (FreeGroup (Fin d)) → Set (V × V) := fun J => {p | (p.1 : FreeGroup (Fin d)) * (p.2 : FreeGroup (Fin d))⁻¹ ∈ J}
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro J hJ J' hJ' hf
  have hrel : ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ J ↔ a * b⁻¹ ∈ J' := by
    intro a ha b hb
    have := congrArg (fun S : Set (V × V) => ((⟨a, ha⟩ : V), (⟨b, hb⟩ : V)) ∈ S) hf
    simpa [f] using this
  exact le_antisymm
    (le_of_forall_mem_iff T V hV h1 J J' (hcov J hJ) fun a ha b hb => (hrel a ha b hb).1)
    (le_of_forall_mem_iff T V hV h1 J' J (hcov J' hJ') fun a ha b hb => (hrel a ha b hb).2)

end Puder.Q284
end

section
open Puder
open Puder.Q284
variable {d : ℕ}
theorem solution (H : Subgroup (FreeGroup (Fin d))) (hH : H.FG) :
    {J : Subgroup (FreeGroup (Fin d)) | IsAlgExt H J}.Finite := by
  exact Puder.Q284.setOf_isAlgExt_finite_of_fg_dev H hH
end
