-- Prove2me | solution 1 for Puder.finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:17:52.236826+00:00
-- url     : https://prove2.me/submissions/71458207-95ef-47a1-bf2d-e36a983a34b4

import Mathlib
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
import Definitions.Def_StrongConv
section
section
section
namespace Puder.Q284
variable {d : ℕ}
/-!
# q284 Blueprint: PP15 Claim 4.2, Lemma 4.1 and Takahasi from Claim 3.3(4) and Lemma 4.1's last step

Infrastructure on walks of words in Schreier coset graphs (stubs, proved in Parts), then the three
reductions, proved here from the stubs.
-/

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}

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

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

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
end Puder.Q284
end
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-!
# q284 Blueprint: Schreier bases adapted to a set of edges; Claim 3.3(4) and Lemma 4.1's last step

For a subgroup `J ≤ F_d` and a coset-invariant set `P` of edges of its Schreier graph, the transversal
`tr J P g` is the element of the coset `J g` minimising (number of steps of its reduced walk outside `P`,
shortlex code of its reduced word). It is a Schreier transversal (prefix-closed), and the elements
`v x tr(v x)⁻¹` over the non-tree edges `(v, x)` form a basis of `J`, the coordinates of `g ∈ J`
being read off the walk of `g` (Reidemeister–Schreier).
-/
/-- The vertex (as a representative `g` of the coset `J g`) of the edge crossed at step `k` of the
walk of the list `L`: the `x`-edge leaving `J g`, where `L[k] = (x, b)`. -/
def vtx (L : List (Fin d × Bool)) (k : Fin L.length) : FreeGroup (Fin d) :=
  if L[k].2 then FreeGroup.mk (L.take k) else FreeGroup.mk (L.take k) * (FreeGroup.of L[k].1)⁻¹

open Classical in
/-- Number of steps of the reduced walk of `g` crossing an edge outside `P`. -/
noncomputable def nonCount (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d)) : ℕ :=
  (Finset.univ.filter fun k : Fin g.toWord.length => ¬ P (vtx g.toWord k) (g.toWord[k]).1).card

/-- Shortlex code of a word, in base `2d + 1` with nonzero digits, first letter most significant. -/
def code (L : List (Fin d × Bool)) : ℕ :=
  L.foldl (fun n a => n * (2 * d + 1) + (2 * (a.1 : ℕ) + if a.2 then 1 else 2)) 0

/-- The key minimised by the transversal. -/
noncomputable def key (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d)) : ℕ ×ₗ ℕ :=
  toLex (nonCount P g, code g.toWord)

/-- The transversal: the element of `J g` of least key. -/
noncomputable def tr (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (g : FreeGroup (Fin d)) : FreeGroup (Fin d) :=
  Function.argminOn (key P) {h | h * g⁻¹ ∈ J} ⟨g, by simp⟩

/-- `P` depends only on the coset of the vertex. -/
def CosetInv (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop) : Prop :=
  ∀ g g' x, g * g'⁻¹ ∈ J → P g x → P g' x

/-- The non-tree edges, indexed by their transversal vertex. -/
def Idx (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop) : Type :=
  {e : FreeGroup (Fin d) × Fin d // tr J P e.1 = e.1 ∧ tr J P (e.1 * FreeGroup.of e.2) ≠ e.1 * FreeGroup.of e.2}

/-- The Schreier generator of a non-tree edge. -/
noncomputable def basisElt (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (e : Idx J P) : FreeGroup (Fin d) :=
  e.1.1 * FreeGroup.of e.1.2 * (tr J P (e.1.1 * FreeGroup.of e.1.2))⁻¹

open Classical in
/-- The contribution of step `k` of the walk of `g` to its Schreier coordinates. -/
noncomputable def stepLabel (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (g : FreeGroup (Fin d)) (k : Fin g.toWord.length) : FreeGroup (Idx J P) :=
  if h : tr J P (tr J P (vtx g.toWord k)) = tr J P (vtx g.toWord k) ∧
      tr J P (tr J P (vtx g.toWord k) * FreeGroup.of (g.toWord[k]).1) ≠
        tr J P (vtx g.toWord k) * FreeGroup.of (g.toWord[k]).1 then
    (if (g.toWord[k]).2 then FreeGroup.of (⟨(tr J P (vtx g.toWord k), (g.toWord[k]).1), h⟩ : Idx J P)
      else (FreeGroup.of (⟨(tr J P (vtx g.toWord k), (g.toWord[k]).1), h⟩ : Idx J P))⁻¹)
  else 1

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
/-! ## Codes -/
/-- The digit of a letter in the shortlex code. -/
def digit (a : Fin d × Bool) : ℕ := 2 * (a.1 : ℕ) + if a.2 then 1 else 2

theorem digit_pos (a : Fin d × Bool) : 1 ≤ digit a := by
  unfold digit; split <;> omega

theorem digit_lt (a : Fin d × Bool) : digit a < 2 * d + 1 := by
  have := a.1.isLt
  unfold digit; split <;> omega

theorem digit_inj {a a' : Fin d × Bool} (h : digit a = digit a') : a = a' := by
  obtain ⟨x, b⟩ := a
  obtain ⟨x', b'⟩ := a'
  unfold digit at h
  cases b <;> cases b' <;> simp at h <;> first
    | (exfalso; omega)
    | (have : (x : ℕ) = x' := by omega
       simp [Fin.ext this])

theorem foldl_code (L : List (Fin d × Bool)) (n : ℕ) :
    L.foldl (fun n a => n * (2 * d + 1) + (2 * (a.1 : ℕ) + if a.2 then 1 else 2)) n =
      n * (2 * d + 1) ^ L.length + code L := by
  induction L generalizing n with
  | nil => simp [code]
  | cons a L ih =>
    simp only [code, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, ih (0 * (2 * d + 1) + _)]
    ring

theorem code_cons (a : Fin d × Bool) (L : List (Fin d × Bool)) :
    code (a :: L) = digit a * (2 * d + 1) ^ L.length + code L := by
  have := foldl_code L (0 * (2 * d + 1) + digit a)
  simp only [code, List.foldl_cons, digit] at this ⊢
  rw [this]; ring

theorem code_nil : code ([] : List (Fin d × Bool)) = 0 := rfl

theorem code_append (A B : List (Fin d × Bool)) :
    code (A ++ B) = code A * (2 * d + 1) ^ B.length + code B := by
  have := foldl_code B (code A)
  simp only [code, List.foldl_append] at this ⊢
  exact this

theorem code_lt (L : List (Fin d × Bool)) : code L < (2 * d + 1) ^ L.length := by
  induction L with
  | nil => simp [code_nil]
  | cons a L ih =>
    rw [code_cons, List.length_cons, pow_succ]
    have := digit_lt a
    have h2 : digit a * (2 * d + 1) ^ L.length + (2 * d + 1) ^ L.length ≤
        (2 * d + 1) ^ L.length * (2 * d + 1) := by
      rw [← Nat.succ_mul, mul_comm]; exact Nat.mul_le_mul_left _ this
    omega

theorem le_code_cons (a : Fin d × Bool) (L : List (Fin d × Bool)) :
    (2 * d + 1) ^ L.length ≤ code (a :: L) := by
  rw [code_cons]
  have := Nat.mul_le_mul_right ((2 * d + 1) ^ L.length) (digit_pos a)
  omega

theorem length_eq_of_code_eq {L L' : List (Fin d × Bool)} (h : code L = code L') :
    L.length = L'.length := by
  have key : ∀ L L' : List (Fin d × Bool), L.length < L'.length → code L < code L' := by
    intro L L' hl
    match L' with
    | [] => simp at hl
    | a :: L'' =>
      have h1 := code_lt L
      have h2 := le_code_cons a L''
      have h3 : (2 * d + 1) ^ L.length ≤ (2 * d + 1) ^ L''.length :=
        Nat.pow_le_pow_right (by omega) (by simp at hl; omega)
      omega
  rcases lt_trichotomy L.length L'.length with hl | hl | hl
  · exact absurd h (key L L' hl).ne
  · exact hl
  · exact absurd h (key L' L hl).ne'

theorem code_inj_aux : ∀ (L L' : List (Fin d × Bool)), L.length = L'.length →
    code L = code L' → L = L'
  | [], [], _, _ => rfl
  | a :: L, a' :: L', hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [code_cons, code_cons, hl] at h
    have hlt := code_lt L
    have hlt' := code_lt L'
    rw [hl] at hlt
    have hpos : 0 < (2 * d + 1) ^ L'.length := by positivity
    have hm := congrArg (· % (2 * d + 1) ^ L'.length) h
    have hd := congrArg (· / (2 * d + 1) ^ L'.length) h
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt,
      add_comm (digit a' * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt'] at hm
    rw [add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt,
      add_comm (digit a' * _), Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt'] at hd
    simp only [zero_add] at hd
    rw [digit_inj hd, code_inj_aux L L' hl hm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem code_inj {L L' : List (Fin d × Bool)} (h : code L = code L') : L = L' :=
  code_inj_aux L L' (length_eq_of_code_eq h) h

/-! ## Counting non-`P` steps -/
open Classical in
/-- Number of non-`P` steps of the walk of the list `L` started at the coset of `u`. -/
noncomputable def cntR (P : FreeGroup (Fin d) → Fin d → Prop) :
    FreeGroup (Fin d) → List (Fin d × Bool) → ℕ
  | _, [] => 0
  | u, a :: L =>
    (if P (if a.2 then u else u * (FreeGroup.of a.1)⁻¹) a.1 then 0 else 1) +
      cntR P (u * FreeGroup.mk [a]) L

theorem cntR_append (P : FreeGroup (Fin d) → Fin d → Prop) (A B : List (Fin d × Bool)) (u : FreeGroup (Fin d)) :
    cntR P u (A ++ B) = cntR P u A + cntR P (u * FreeGroup.mk A) B := by
  induction A generalizing u with
  | nil => simp [cntR, ← FreeGroup.one_eq_mk]
  | cons a A ih =>
    simp only [List.cons_append, cntR, ih, mul_assoc, FreeGroup.mul_mk, List.nil_append]
    ring

open Classical in
theorem cntR_coset (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (hP : CosetInv J P) (L : List (Fin d × Bool)) :
    ∀ u u' : FreeGroup (Fin d), u * u'⁻¹ ∈ J → cntR P u L = cntR P u' L := by
  induction L with
  | nil => intros; rfl
  | cons a L ih =>
    intro u u' h
    have hv : (if a.2 then u else u * (FreeGroup.of a.1)⁻¹) *
        (if a.2 then u' else u' * (FreeGroup.of a.1)⁻¹)⁻¹ ∈ J := by
      split
      · exact h
      · simpa [mul_assoc] using h
    have hv' := J.inv_mem hv
    rw [mul_inv_rev, inv_inv] at hv'
    have hiff : P (if a.2 then u else u * (FreeGroup.of a.1)⁻¹) a.1 ↔
        P (if a.2 then u' else u' * (FreeGroup.of a.1)⁻¹) a.1 :=
      ⟨hP _ _ _ hv, hP _ _ _ hv'⟩
    simp only [cntR]
    congr 1
    · exact if_congr hiff rfl rfl
    apply ih
    have : u * FreeGroup.mk [a] * (u' * FreeGroup.mk [a])⁻¹ = u * u'⁻¹ := by group
    rw [this]; exact h

theorem cntR_step (P : FreeGroup (Fin d) → Fin d → Prop) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red.Step L L') (u : FreeGroup (Fin d)) : cntR P u L' ≤ cntR P u L := by
  cases h with
  | @not L₁ L₂ z c =>
    rw [cntR_append, cntR_append]
    have : u * FreeGroup.mk L₁ * FreeGroup.mk [(z, c)] * FreeGroup.mk [(z, !c)] =
        u * FreeGroup.mk L₁ := by
      rw [mul_assoc (u * _), FreeGroup.mul_mk]
      have : FreeGroup.mk ([(z, c)] ++ [(z, !c)]) = 1 := by
        have := Puder.Q284.PartW.mk_cancel_pair [] [] z c
        rw [FreeGroup.one_eq_mk]; simpa using this
      rw [this, mul_one]
    simp only [cntR, this]
    omega

theorem cntR_red (P : FreeGroup (Fin d) → Fin d → Prop) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red L L') (u : FreeGroup (Fin d)) : cntR P u L' ≤ cntR P u L := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (cntR_step P hstep u).trans ih

open Classical in
theorem sum_eq_cntR (P : FreeGroup (Fin d) → Fin d → Prop) (L : List (Fin d × Bool)) :
    ∀ u : FreeGroup (Fin d),
      (∑ k : Fin L.length, if P (u * vtx L k) (L[k]).1 then 0 else 1) = cntR P u L := by
  induction L with
  | nil => intro u; simp [cntR]
  | cons a L ih =>
    intro u
    refine (Fin.sum_univ_succ (n := L.length)
      (fun k => if P (u * vtx (a :: L) k) ((a :: L)[k]).1 then 0 else 1)).trans ?_
    simp only [cntR]
    rw [← ih (u * FreeGroup.mk [a])]
    congr 1
    · refine if_congr (Iff.of_eq ?_) rfl rfl
      have hv : u * vtx (a :: L) 0 = if a.2 then u else u * (FreeGroup.of a.1)⁻¹ := by
        obtain ⟨x, b⟩ := a
        cases b <;> simp [vtx, ← FreeGroup.one_eq_mk]
      rw [hv]; rfl
    · apply Finset.sum_congr rfl
      intro k _
      refine if_congr (Iff.of_eq ?_) rfl rfl
      have hv : u * vtx (a :: L) k.succ = u * FreeGroup.mk [a] * vtx L k := by
        have : FreeGroup.mk (a :: List.take (↑k) L) =
            FreeGroup.mk [a] * FreeGroup.mk (List.take (↑k) L) := by
          rw [FreeGroup.mul_mk]; rfl
        have hk : (a :: L)[k.succ] = L[k] := rfl
        simp only [vtx, hk, Fin.val_succ, List.take_succ_cons, this]
        split <;> simp only [mul_assoc]
      rw [hv]; rfl

theorem nonCount_eq (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d)) :
    nonCount P g = cntR P 1 g.toWord := by
  rw [← sum_eq_cntR, nonCount, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_mul]
  by_cases h : P (vtx g.toWord k) (g.toWord[k]).1 <;> simp

theorem code_le_cons (a : Fin d × Bool) (L : List (Fin d × Bool)) : code L ≤ code (a :: L) := by
  rw [code_cons]; omega

theorem code_step {L L' : List (Fin d × Bool)} (h : FreeGroup.Red.Step L L') : code L' ≤ code L := by
  cases h with
  | @not L₁ L₂ z c =>
    rw [code_append, code_append]
    have h1 := (code_le_cons (z, !c) L₂).trans (code_le_cons (z, c) _)
    have h2 : (2 * d + 1) ^ L₂.length ≤ (2 * d + 1) ^ ((z, c) :: (z, !c) :: L₂).length :=
      Nat.pow_le_pow_right (by omega) (by simp only [List.length_cons]; omega)
    have h3 := Nat.mul_le_mul_left (code L₁) h2
    omega

theorem code_red {L L' : List (Fin d × Bool)} (h : FreeGroup.Red L L') : code L' ≤ code L := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (code_step hstep).trans ih

/-! ## The key -/
theorem key_le_iff (P : FreeGroup (Fin d) → Fin d → Prop) (a b : FreeGroup (Fin d)) :
    key P a ≤ key P b ↔ nonCount P a < nonCount P b ∨
      nonCount P a = nonCount P b ∧ code a.toWord ≤ code b.toWord := by
  unfold key; exact Prod.Lex.toLex_le_toLex

theorem key_inj (P : FreeGroup (Fin d) → Fin d → Prop) {a b : FreeGroup (Fin d)}
    (h : key P a = key P b) : a = b := by
  unfold key at h
  have h' := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  exact FreeGroup.toWord_injective (code_inj h'.2)

theorem key_tr_le (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    {g h : FreeGroup (Fin d)} (hh : h * g⁻¹ ∈ J) : key P (tr J P g) ≤ key P h :=
  Function.argminOn_le (key P) {h | h * g⁻¹ ∈ J} (a := h) hh

theorem argminOn_congr {α β : Type*} [LT β] [WellFoundedLT β] (f : α → β) {s t : Set α}
    (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    Function.argminOn f s hs = Function.argminOn f t ht := by
  subst h; rfl

/-! ## Part S1 -/
theorem tr_mem (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (g : FreeGroup (Fin d)) : tr J P g * g⁻¹ ∈ J :=
  Function.argminOn_mem (key P) {h | h * g⁻¹ ∈ J} ⟨g, by simp⟩

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S1: the transversal -/
alias tr_mem := Puder.Q284S.PartS1.tr_mem

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
theorem tr_congr (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    {g g' : FreeGroup (Fin d)} (h : g * g'⁻¹ ∈ J) : tr J P g = tr J P g' := by
  unfold tr
  apply argminOn_congr
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    have := J.mul_mem hx h
    simpa [mul_assoc] using this
  · intro hx
    have := J.mul_mem hx (J.inv_mem h)
    simpa [mul_assoc] using this

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
alias tr_congr := Puder.Q284S.PartS1.tr_congr

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
theorem tr_one (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop) :
    tr J P 1 = 1 := by
  apply key_inj P
  apply le_antisymm (key_tr_le J P (by simp))
  rw [key_le_iff]
  have h1 : nonCount P (1 : FreeGroup (Fin d)) = 0 := by
    rw [nonCount_eq, FreeGroup.toWord_one]; rfl
  have h2 : code (1 : FreeGroup (Fin d)).toWord = 0 := by
    rw [FreeGroup.toWord_one]; rfl
  rw [h1, h2]
  rcases Nat.eq_zero_or_pos (nonCount P (tr J P 1)) with h | h
  · exact Or.inr ⟨h.symm, Nat.zero_le _⟩
  · exact Or.inl h

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
alias tr_one := Puder.Q284S.PartS1.tr_one

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}

theorem toWord_mk_of_isReduced {L : List (Fin d × Bool)} (h : FreeGroup.IsReduced L) :
    (FreeGroup.mk L).toWord = L := by
  rw [FreeGroup.toWord_mk, h.reduce_eq]

theorem tr_take (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (hP : CosetInv J P) (g : FreeGroup (Fin d)) (k : ℕ) :
    tr J P (FreeGroup.mk ((tr J P g).toWord.take k)) = FreeGroup.mk ((tr J P g).toWord.take k) := by
  set t := tr J P g with ht
  set p := t.toWord.take k with hpdef
  set s := t.toWord.drop k with hsdef
  have hps : t.toWord = p ++ s := (List.take_append_drop k t.toWord).symm
  have hp : (FreeGroup.mk p).toWord = p :=
    toWord_mk_of_isReduced (FreeGroup.isReduced_toWord.infix (List.take_prefix k _).isInfix)
  set p' := tr J P (FreeGroup.mk p) with hp'def
  set A := p'.toWord with hA
  have hp'mem : p' * (FreeGroup.mk p)⁻¹ ∈ J := tr_mem J P _
  have hkey1 := (key_le_iff P _ _).mp (key_tr_le J P (g := FreeGroup.mk p)
    (h := FreeGroup.mk p) (by rw [mul_inv_cancel]; exact J.one_mem))
  have htmk : t = FreeGroup.mk p * FreeGroup.mk s := by
    rw [FreeGroup.mul_mk, ← hps, FreeGroup.mk_toWord]
  have hp'A : p' = FreeGroup.mk A := FreeGroup.mk_toWord.symm
  set g' := FreeGroup.mk (A ++ s) with hg'
  have hg'mem : g' * g⁻¹ ∈ J := by
    have e : g' * g⁻¹ = (p' * (FreeGroup.mk p)⁻¹) * (t * g⁻¹) := by
      rw [hg', ← FreeGroup.mul_mk, ← hp'A, htmk]; group
    rw [e]; exact J.mul_mem hp'mem (tr_mem J P g)
  have hkey2 := (key_le_iff P _ _).mp (key_tr_le J P hg'mem)
  -- counts
  have hnt : nonCount P t = cntR P 1 p + cntR P (FreeGroup.mk p) s := by
    rw [nonCount_eq, hps, cntR_append, one_mul]
  have hnp : nonCount P (FreeGroup.mk p) = cntR P 1 p := by rw [nonCount_eq, hp]
  have hnp' : nonCount P p' = cntR P 1 A := nonCount_eq P p'
  have hng' : nonCount P g' ≤ cntR P 1 A + cntR P (FreeGroup.mk p) s := by
    rw [nonCount_eq, hg', FreeGroup.toWord_mk]
    refine (cntR_red P FreeGroup.reduce.red 1).trans (le_of_eq ?_)
    rw [cntR_append, one_mul, ← hp'A]
    congr 1
    exact cntR_coset J P hP s _ _ hp'mem
  -- codes
  have hct : code t.toWord = code p * (2 * d + 1) ^ s.length + code s := by
    rw [hps, code_append]
  have hcp : code (FreeGroup.mk p).toWord = code p := by rw [hp]
  have hcg' : code g'.toWord ≤ code A * (2 * d + 1) ^ s.length + code s := by
    rw [← code_append, hg', FreeGroup.toWord_mk]
    exact code_red FreeGroup.reduce.red
  have hpos : 0 < (2 * d + 1) ^ s.length := by positivity
  have hA' : code (tr J P (FreeGroup.mk p)).toWord = code A := rfl
  rw [hnp, hnp', hcp, hA'] at hkey1
  rw [hnt, hct] at hkey2
  -- key p' = key (mk p)
  have hn : cntR P 1 A = cntR P 1 p := by
    rcases hkey1 with h | ⟨h, -⟩
    · exfalso; omega
    · exact h
  have hc : code A = code p := by
    rcases hkey1 with h | ⟨-, h⟩
    · exfalso; omega
    · rcases Nat.lt_or_ge (code A) (code p) with h' | h'
      · exfalso
        have := Nat.mul_lt_mul_of_pos_right h' hpos
        omega
      · omega
  have hAp : A = p := code_inj hc
  rw [hp'A, hAp]

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
alias tr_take := Puder.Q284S.PartS1.tr_take

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS2
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
variable (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
/-!
# q284 Part S2: the Schreier basis (Reidemeister–Schreier)
-/
local notation "G" => FreeGroup (Fin d)

theorem tr_tr (g : G) : tr J P (tr J P g) = tr J P g := tr_congr J P (tr_mem J P g)

theorem tr_mul_right (g h : G) : tr J P (tr J P g * h) = tr J P (g * h) := by
  apply tr_congr
  have := tr_mem J P g
  simpa [mul_assoc] using this

/-- Transversal elements. -/
abbrev T := {v : G // tr J P v = v}

/-- The label of the `x`-edge leaving the transversal vertex `w`. -/
noncomputable def lab (w : G) (x : Fin d) : FreeGroup (Idx J P) := by
  classical
  exact if h : tr J P w = w ∧ tr J P (w * FreeGroup.of x) ≠ w * FreeGroup.of x then
    FreeGroup.of (⟨(w, x), h⟩ : Idx J P) else 1

/-- The permutation of `T × FreeGroup ι` given by the letter `x`. -/
noncomputable def sig (x : Fin d) : Equiv.Perm (T J P × FreeGroup (Idx J P)) where
  toFun s := (⟨tr J P (s.1.1 * FreeGroup.of x), tr_tr J P _⟩, s.2 * lab J P s.1.1 x)
  invFun s := (⟨tr J P (s.1.1 * (FreeGroup.of x)⁻¹), tr_tr J P _⟩,
    s.2 * (lab J P (tr J P (s.1.1 * (FreeGroup.of x)⁻¹)) x)⁻¹)
  left_inv s := by
    obtain ⟨⟨v, hv⟩, u⟩ := s
    have h1 : tr J P (tr J P (v * FreeGroup.of x) * (FreeGroup.of x)⁻¹) = v := by
      rw [tr_mul_right]; simpa using hv
    ext1
    · exact Subtype.ext h1
    · simp only
      rw [h1]; simp
  right_inv s := by
    obtain ⟨⟨v, hv⟩, u⟩ := s
    have h1 : tr J P (tr J P (v * (FreeGroup.of x)⁻¹) * FreeGroup.of x) = v := by
      rw [tr_mul_right]; simpa using hv
    ext1
    · exact Subtype.ext h1
    · simp

/-- The right action of `F_d`. -/
noncomputable def A : G →* (Equiv.Perm (T J P × FreeGroup (Idx J P)))ᵐᵒᵖ :=
  FreeGroup.lift fun x => MulOpposite.op (sig J P x)

noncomputable def act (s : T J P × FreeGroup (Idx J P)) (g : G) : T J P × FreeGroup (Idx J P) :=
  (A J P g).unop s

theorem act_one (s) : act J P s 1 = s := by simp [act]

theorem act_mul (s) (g h : G) : act J P s (g * h) = act J P (act J P s g) h := by
  simp [act, map_mul, Equiv.Perm.mul_apply]

theorem act_of (s) (x : Fin d) : act J P s (FreeGroup.of x) = sig J P x s := by
  simp [act, A]

theorem act_inv_of (s) (x : Fin d) : act J P s (FreeGroup.of x)⁻¹ = (sig J P x).symm s := by
  simp [act, A, map_inv]

theorem mk_single (a : Fin d × Bool) :
    FreeGroup.mk [a] = if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹ := by
  obtain ⟨x, b⟩ := a
  cases b
  · simp [FreeGroup.inv_mk, FreeGroup.of, FreeGroup.invRev]
  · rfl

/-- Induction on words. -/
theorem ind {p : G → Prop} (h1 : p 1) (hm : ∀ a g, p g → p (FreeGroup.mk [a] * g)) (g : G) : p g := by
  rw [← FreeGroup.mk_toWord (x := g)]
  induction g.toWord with
  | nil => exact h1
  | cons a L ih =>
    have : FreeGroup.mk (a :: L) = FreeGroup.mk [a] * FreeGroup.mk L := by
      rw [FreeGroup.mul_mk]; rfl
    rw [this]; exact hm a _ ih

theorem act_single (s) (a : Fin d × Bool) :
    act J P s (FreeGroup.mk [a]) =
      if a.2 then (⟨⟨tr J P (s.1.1 * FreeGroup.of a.1), tr_tr J P _⟩, s.2 * lab J P s.1.1 a.1⟩)
      else (⟨tr J P (s.1.1 * (FreeGroup.of a.1)⁻¹), tr_tr J P _⟩,
        s.2 * (lab J P (tr J P (s.1.1 * (FreeGroup.of a.1)⁻¹)) a.1)⁻¹) := by
  rw [mk_single]
  obtain ⟨x, b⟩ := a
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, act_inv_of]; rfl
  · simp only [↓reduceIte, act_of]; rfl

theorem act_fst (g : G) : ∀ s, ((act J P s g).1 : G) = tr J P (s.1.1 * g) := by
  induction g using ind with
  | h1 => intro s; simp [act_one, s.1.2]
  | hm a g ih =>
    intro s
    rw [act_mul, ih, act_single]
    split_ifs with hb
    · simp only; rw [tr_mul_right, mk_single, if_pos hb, mul_assoc]
    · simp only; rw [tr_mul_right, mk_single, if_neg hb, mul_assoc]

theorem act_snd (g : G) : ∀ s, (act J P s g).2 = s.2 * (act J P (s.1, 1) g).2 := by
  induction g using ind with
  | h1 => intro s; simp [act_one]
  | hm a g ih =>
    intro s
    rw [act_mul, act_mul, ih, ih (act J P (s.1, 1) (FreeGroup.mk [a])), act_single, act_single]
    split_ifs <;> simp [mul_assoc]

/-- The cocycle. -/
noncomputable def C (v : T J P) (g : G) : FreeGroup (Idx J P) := (act J P (v, 1) g).2

theorem C_mul (v : T J P) (g h : G) :
    C J P v (g * h) = C J P v g * C J P (act J P (v, 1) g).1 h := by
  unfold C
  rw [act_mul, act_snd]

theorem C_single (v : T J P) (a : Fin d × Bool) :
    C J P v (FreeGroup.mk [a]) = if a.2 then lab J P v.1 a.1
      else (lab J P (tr J P (v.1 * (FreeGroup.of a.1)⁻¹)) a.1)⁻¹ := by
  unfold C; rw [act_single]; split_ifs <;> simp

/-- The vertex `1`. -/
def oneT : T J P := ⟨1, tr_one J P⟩

theorem vert_eq (v : T J P) (g : G) (w : T J P) (h : tr J P (v.1 * g) = w.1) :
    (act J P (v, 1) g).1 = w := Subtype.ext (by rw [act_fst]; exact h)

/-- The map `ψ`. -/
noncomputable def psi : FreeGroup (Idx J P) →* J :=
  FreeGroup.lift fun e => ⟨basisElt J P e, by
    have := tr_mem J P (e.1.1 * FreeGroup.of e.1.2)
    have := J.inv_mem this
    simpa [basisElt, mul_assoc] using this⟩

theorem psi_of (e : Idx J P) : (psi J P (FreeGroup.of e) : G) = basisElt J P e := by
  simp [psi]

theorem psi_lab (w : G) (hw : tr J P w = w) (x : Fin d) :
    (psi J P (lab J P w x) : G) = w * FreeGroup.of x * (tr J P (w * FreeGroup.of x))⁻¹ := by
  unfold lab
  split_ifs with h
  · exact psi_of J P ⟨(w, x), h⟩
  · have : tr J P (w * FreeGroup.of x) = w * FreeGroup.of x := by
      by_contra h'; exact h ⟨hw, h'⟩
    rw [this]; simp

theorem psi_C (g : G) : ∀ v : T J P, (psi J P (C J P v g) : G) = v.1 * g * (tr J P (v.1 * g))⁻¹ := by
  induction g using ind with
  | h1 => intro v; simp [C, act_one, v.2]
  | hm a g ih =>
    intro v
    rw [C_mul, map_mul, Subgroup.coe_mul, ih, act_fst, C_single, tr_mul_right]
    have key : (psi J P (if a.2 then lab J P v.1 a.1
        else (lab J P (tr J P (v.1 * (FreeGroup.of a.1)⁻¹)) a.1)⁻¹) : G) =
        v.1 * FreeGroup.mk [a] * (tr J P (v.1 * FreeGroup.mk [a]))⁻¹ := by
      rw [mk_single]
      split_ifs
      · rw [psi_lab J P _ v.2]
      · rw [map_inv, Subgroup.coe_inv, psi_lab J P _ (tr_tr J P _), tr_mul_right]
        simp [v.2, mul_assoc]
    rw [key]
    simp [mul_assoc]

/-- The inverse map `ρ`. -/
noncomputable def rho : J →* FreeGroup (Idx J P) where
  toFun g := C J P (oneT J P) g.1
  map_one' := by simp [C, act_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul]
    rw [C_mul]
    congr 2
    apply vert_eq
    simp only [oneT, one_mul]
    rw [tr_congr J P (g := g.1) (g' := 1) (by simpa using g.2), tr_one]

theorem C_oneT_fixed (hP : CosetInv J P) (v : G) (hv : tr J P v = v) : C J P (oneT J P) v = 1 := by
  have ht := tr_take J P hP v
  rw [hv] at ht
  set L := v.toWord
  have key : ∀ k, C J P (oneT J P) (FreeGroup.mk (L.take k)) = 1 := by
    intro k
    induction k with
    | zero => show C J P (oneT J P) 1 = 1; simp [C, act_one]
    | succ k ih =>
      by_cases hk : k < L.length
      · have hsplit : FreeGroup.mk (L.take (k + 1)) = FreeGroup.mk (L.take k) * FreeGroup.mk [L[k]] := by
          rw [FreeGroup.mul_mk, List.take_add_one, List.getElem?_eq_getElem hk]; rfl
        have hfix := ht (k + 1)
        rw [hsplit] at hfix ⊢
        rw [C_mul, ih, one_mul]
        have hv' : (act J P (oneT J P, 1) (FreeGroup.mk (L.take k))).1 = ⟨_, ht k⟩ :=
          vert_eq J P _ _ _ (by simp [oneT, ht k])
        rw [hv', C_single]
        rw [mk_single] at hfix
        split_ifs at hfix ⊢ with hb
        · unfold lab; rw [dif_neg]; simp [hfix]
        · simp only [hfix]
          unfold lab; rw [dif_neg]; · simp
          simp [ht k]
      · push Not at hk
        rw [List.take_of_length_le hk, List.take_of_length_le (by omega)] at *
        exact ih
  have := key L.length
  rwa [List.take_length, FreeGroup.mk_toWord] at this

theorem rho_psi (hP : CosetInv J P) : (rho J P).comp (psi J P) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro e
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  change C J P (oneT J P) (psi J P (FreeGroup.of e) : G) = _
  rw [psi_of]
  obtain ⟨⟨v, x⟩, hv, hne⟩ := e
  simp only [basisElt]
  rw [C_mul, C_mul, C_oneT_fixed J P hP v hv, one_mul]
  have h1 : (act J P (oneT J P, 1) v).1 = ⟨v, hv⟩ := vert_eq J P _ _ _ (by simp [oneT, hv])
  rw [h1]
  have h2 : C J P ⟨v, hv⟩ (FreeGroup.of x) = FreeGroup.of ⟨(v, x), hv, hne⟩ := by
    have := C_single J P ⟨v, hv⟩ (x, true)
    simp only [↓reduceIte] at this
    rw [show FreeGroup.mk [(x, true)] = FreeGroup.of x from rfl] at this
    rw [this]; unfold lab; rw [dif_pos ⟨hv, hne⟩]
  rw [h2]
  set w := tr J P (v * FreeGroup.of x)
  have h3 : (act J P (oneT J P, 1) (v * FreeGroup.of x)).1 = ⟨w, tr_tr J P _⟩ :=
    vert_eq J P _ _ _ (by simp [oneT, w])
  rw [h3]
  -- C_w (w⁻¹) = (C_1 w)⁻¹ = 1
  have h4 := C_mul J P ⟨w, tr_tr J P _⟩ w⁻¹ w
  rw [inv_mul_cancel] at h4
  have h5 : (act J P (⟨w, tr_tr J P _⟩, 1) w⁻¹).1 = oneT J P :=
    vert_eq J P _ _ _ (by simp [oneT, tr_one])
  rw [h5, C_oneT_fixed J P hP w (tr_tr J P _)] at h4
  have h6 : C J P ⟨w, tr_tr J P _⟩ 1 = 1 := by simp [C, act_one]
  rw [h6, mul_one] at h4
  rw [← h4, mul_one]

theorem psi_rho : (psi J P).comp (rho J P) = MonoidHom.id _ := by
  ext g
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  change (psi J P (C J P (oneT J P) g.1) : G) = g.1
  rw [psi_C]
  simp [oneT, tr_congr J P (g := g.1) (g' := 1) (by simpa using g.2), tr_one]

theorem stepLabel_eq (g : G) (k : Fin g.toWord.length) :
    stepLabel J P g k = if (g.toWord[k]).2 then lab J P (tr J P (vtx g.toWord k)) (g.toWord[k]).1
      else (lab J P (tr J P (vtx g.toWord k)) (g.toWord[k]).1)⁻¹ := by
  unfold stepLabel lab
  split_ifs <;> rfl

theorem rho_eq (g : G) :
    C J P (oneT J P) g = ((List.finRange g.toWord.length).map (stepLabel J P g)).prod := by
  set L := g.toWord with hL
  classical
  let s : ℕ → FreeGroup (Idx J P) := fun k => if h : k < L.length then stepLabel J P g ⟨k, h⟩ else 1
  have hs : (List.finRange L.length).map (stepLabel J P g) = (List.range L.length).map s := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro k _
    simp [s]
  have key : ∀ n, n ≤ L.length → C J P (oneT J P) (FreeGroup.mk (L.take n)) =
      ((List.range n).map s).prod := by
    intro n
    induction n with
    | zero => intro; show C J P (oneT J P) 1 = _; simp [C, act_one]
    | succ n ih =>
      intro hn
      have hk : n < L.length := hn
      have hsplit : FreeGroup.mk (L.take (n + 1)) = FreeGroup.mk (L.take n) * FreeGroup.mk [L[n]] := by
        rw [FreeGroup.mul_mk, List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      rw [hsplit, C_mul, ih (by omega), List.range_succ, List.map_append, List.prod_append]
      congr 1
      have hv' : (act J P (oneT J P, 1) (FreeGroup.mk (L.take n))).1 =
          ⟨tr J P (FreeGroup.mk (L.take n)), tr_tr J P _⟩ :=
        vert_eq J P _ _ _ (by simp [oneT])
      rw [hv', C_single]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, s, dif_pos hk]
      rw [stepLabel_eq]
      simp only [vtx]
      split_ifs <;> simp_all [tr_mul_right]
  have := key L.length le_rfl
  rw [List.take_length, hL, FreeGroup.mk_toWord] at this
  rw [this, hs]

end Puder.Q284S.PartS2
end

section
namespace Puder.Q284S.PartS2
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
theorem exists_basis (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (hP : CosetInv J P) :
    ∃ b : FreeGroupBasis (Idx J P) J, (∀ e, (b e : FreeGroup (Fin d)) = basisElt J P e) ∧
      ∀ (g : FreeGroup (Fin d)) (hg : g ∈ J),
        b.repr ⟨g, hg⟩ = ((List.finRange g.toWord.length).map (stepLabel J P g)).prod := by
  let E : FreeGroup (Idx J P) ≃* J :=
    MonoidHom.toMulEquiv (psi J P) (rho J P) (rho_psi J P hP) (psi_rho J P)
  refine ⟨FreeGroupBasis.ofRepr E.symm, ?_, ?_⟩
  · intro e
    change ((E.symm.symm (FreeGroup.of e) : J) : FreeGroup (Fin d)) = _
    rw [MulEquiv.symm_symm]
    exact psi_of J P e
  · intro g hg
    change rho J P ⟨g, hg⟩ = _
    exact rho_eq J P g

end Puder.Q284S.PartS2
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S2: the Schreier basis -/
alias exists_basis := Puder.Q284S.PartS2.exists_basis

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS3
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
/-!
# q284 Part S3: Claim 3.3(4)

If every edge traversed by an element of `J` that is also traversed by some element of `H`
forces membership in `H`, then `H` is a free factor of `J`: it is generated by the Schreier
basis elements of the non-tree edges lying in the image subgraph of `H`.
-/

end Puder.Q284S.PartS3
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S3: Claim 3.3(4) -/

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS4
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}

end Puder.Q284S.PartS4
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S4: the last step of Lemma 4.1 -/

end Puder.Q284S
end
end

section
open Filter
namespace Puder.Q284C
open Puder
variable {k : ℕ}
/-!
# q284 Blueprint: Puder's count of core graphs traced twice (proof of Proposition 4.3, (4.2)–(4.3))

A pair `(w, J)` with `|w| = t`, `rk J = m`, `w ∈ J` and the walk of `w` tracing every edge of `Γ_X(J)` twice is
encoded by the reduced word `L` of `w` and the map `f` sending each position `i ≤ t` of the walk to the first
position at which the walk visits the same vertex (coset). The encoded pairs satisfy `WalkOK`, a purely
combinatorial condition, and are counted by a branching argument.
-/
/-! ## The combinatorial model -/
/-- Tail vertex of the edge crossed at step `i` (letter `(x, true)` crosses the `x`-edge forwards). -/
def tail {t : ℕ} (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) (i : Fin t) : Fin (t + 1) :=
  if (L i).2 then f i.castSucc else f i.succ

/-- Head vertex of the edge crossed at step `i`. -/
def head {t : ℕ} (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) (i : Fin t) : Fin (t + 1) :=
  if (L i).2 then f i.succ else f i.castSucc

/-- The edge crossed at step `i`: its tail vertex and its label. -/
def edgeId {t : ℕ} (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) (i : Fin t) :
    Fin (t + 1) × Fin k :=
  (tail L f i, (L i).1)

/-- `L` is freely reduced. -/
def Reduced {t : ℕ} (L : Fin t → Fin k × Bool) : Prop :=
  ∀ (i : Fin t) (h : i.val + 1 < t), L ⟨i.val + 1, h⟩ ≠ ((L i).1, !(L i).2)

/-- The walk with letters `L` and vertex map `f` is a closed walk in a folded labelled graph of rank at most
`m` crossing each of its edges at least twice; `f` sends each position to the first position at the same
vertex. -/
def WalkOK {t : ℕ} (m : ℕ) (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) : Prop :=
  f 0 = 0 ∧ f (Fin.last t) = 0 ∧
  (∀ i, f i ≤ i ∧ f (f i) = f i) ∧
  (∀ i j, (L i).1 = (L j).1 → tail L f i = tail L f j → head L f i = head L f j) ∧
  (∀ i j, (L i).1 = (L j).1 → head L f i = head L f j → tail L f i = tail L f j) ∧
  (∀ i, 2 ≤ (Finset.univ.filter fun j => edgeId L f j = edgeId L f i).card) ∧
  (Finset.univ.image (edgeId L f)).card + 1 ≤ m + (Finset.univ.filter fun i => f i = i).card

/-- The growth rate `max(√(2k − 1), 2m − 1)`, written as in the published statement. -/
noncomputable def rate (k m : ℕ) : ℝ :=
  if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1

/-! ## Part G: the bridge from subgroups -/
/-- The prefix of length `i` of the reduced word of `w`. -/
def pre (w : FreeGroup (Fin k)) (i : ℕ) : FreeGroup (Fin k) := FreeGroup.mk (w.toWord.take i)

/-- The letters of `w`, when its reduced length is `t`. -/
def wL (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t) : Fin t → Fin k × Bool :=
  fun i => w.toWord[i.val]'(h ▸ i.isLt)

open Classical in
/-- First position (up to `t`) at which the walk of `w` visits the coset `J · pre w i`. -/
noncomputable def fJ (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) :
    Fin (t + 1) → Fin (t + 1) :=
  fun i => (Finset.univ.filter fun j : Fin (t + 1) => pre w j * (pre w i)⁻¹ ∈ J).min' ⟨i, by simp⟩

end Puder.Q284C
end

section
namespace Puder.Q284C.PartG
open Puder Puder.Q284 Puder.Q284S Puder.Q284C
variable {k : ℕ}
/-!
# q284 Part G: the bridge from subgroups to the combinatorial model

`reduced_wL`, `walkOK_fJ`, `fJ_injOn` of the Blueprint `Q284Cnt`.
-/
/-! ## Reducedness -/
theorem reduced_wL (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t) : Reduced (wL w t h) := by
  intro i hi heq
  have hR : FreeGroup.IsReduced w.toWord := FreeGroup.isReduced_toWord
  have hc := List.IsChain.getElem hR i.val (by omega)
  simp only [wL] at heq
  rw [heq] at hc
  have := hc rfl
  simp at this

end Puder.Q284C.PartG
end

section
open Filter
namespace Puder.Q284C
open Puder
variable {k : ℕ}
alias reduced_wL := Puder.Q284C.PartG.reduced_wL

end Puder.Q284C
end

section
namespace Puder.Q284C.PartG
open Puder Puder.Q284 Puder.Q284S Puder.Q284C
variable {k : ℕ}
/-! ## Relations in `J` -/
theorem rel_symm {J : Subgroup (FreeGroup (Fin k))} {a b : FreeGroup (Fin k)} (h : a * b⁻¹ ∈ J) :
    b * a⁻¹ ∈ J := by
  simpa using J.inv_mem h

theorem rel_trans {J : Subgroup (FreeGroup (Fin k))} {a b c : FreeGroup (Fin k)} (h1 : a * b⁻¹ ∈ J)
    (h2 : b * c⁻¹ ∈ J) : a * c⁻¹ ∈ J := by
  simpa [mul_assoc] using J.mul_mem h1 h2

/-! ## `fJ` -/
theorem fJ_mem (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) (i : Fin (t + 1)) :
    pre w (fJ J w t i) * (pre w i)⁻¹ ∈ J := by
  classical
  have := Finset.min'_mem (Finset.univ.filter fun j : Fin (t + 1) => pre w j * (pre w i)⁻¹ ∈ J)
    ⟨i, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  unfold fJ
  exact this

theorem fJ_le (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) {i j : Fin (t + 1)}
    (h : pre w j * (pre w i)⁻¹ ∈ J) : fJ J w t i ≤ j := by
  classical
  unfold fJ
  convert Finset.min'_le (Finset.univ.filter fun j : Fin (t + 1) => pre w j * (pre w i)⁻¹ ∈ J) j
    (by simpa using h)

theorem fJ_eq_iff (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) (i i' : Fin (t + 1)) :
    fJ J w t i = fJ J w t i' ↔ pre w i * (pre w i')⁻¹ ∈ J := by
  constructor
  · intro heq
    have h1 := fJ_mem J w t i
    have h2 := fJ_mem J w t i'
    rw [heq] at h1
    exact rel_trans (rel_symm h1) h2
  · intro hii
    apply le_antisymm
    · exact fJ_le J w t (rel_trans (fJ_mem J w t i') (rel_symm hii))
    · exact fJ_le J w t (rel_trans (fJ_mem J w t i) hii)

theorem fJ_le_self (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) (i : Fin (t + 1)) :
    fJ J w t i ≤ i :=
  fJ_le J w t (by simp)

theorem fJ_fJ (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) (i : Fin (t + 1)) :
    fJ J w t (fJ J w t i) = fJ J w t i :=
  (fJ_eq_iff J w t _ _).mpr (fJ_mem J w t i)

/-! ## Prefixes -/
theorem pre_zero (w : FreeGroup (Fin k)) : pre w 0 = 1 := by
  simp [pre, FreeGroup.one_eq_mk]

theorem pre_length (w : FreeGroup (Fin k)) : pre w w.toWord.length = w := by
  simp [pre, FreeGroup.mk_toWord]

theorem pre_succ (w : FreeGroup (Fin k)) (i : ℕ) (hi : i < w.toWord.length) :
    pre w (i + 1) = pre w i * FreeGroup.mk [w.toWord[i]] := by
  unfold pre
  rw [FreeGroup.mul_mk, List.take_add_one, List.getElem?_eq_getElem hi]
  rfl

/-! ## Steps -/
/-- The representative of the tail coset of step `i`. -/
def ev (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t) (i : Fin t) : FreeGroup (Fin k) :=
  if (wL w t h i).2 then pre w i else pre w i * (FreeGroup.of (wL w t h i).1)⁻¹

/-- The position at the tail of step `i`. -/
def tpos {t : ℕ} (L : Fin t → Fin k × Bool) (i : Fin t) : Fin (t + 1) :=
  if (L i).2 then i.castSucc else i.succ

/-- The position at the head of step `i`. -/
def hpos {t : ℕ} (L : Fin t → Fin k × Bool) (i : Fin t) : Fin (t + 1) :=
  if (L i).2 then i.succ else i.castSucc

theorem pre_succ' (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t) (i : Fin t) :
    pre w (i.val + 1) = pre w i *
      (if (wL w t h i).2 then FreeGroup.of (wL w t h i).1 else (FreeGroup.of (wL w t h i).1)⁻¹) := by
  rw [pre_succ w i.val (h ▸ i.isLt), Puder.Q284.PartT.mk_letter]
  rfl

theorem pre_tpos (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t) (i : Fin t) :
    pre w (tpos (wL w t h) i) = ev w t h i := by
  unfold tpos ev
  split_ifs with hb
  · rfl
  · rw [Fin.val_succ, pre_succ' w t h i, if_neg hb]

theorem pre_hpos (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t) (i : Fin t) :
    pre w (hpos (wL w t h) i) = ev w t h i * FreeGroup.of (wL w t h i).1 := by
  unfold hpos ev
  split_ifs with hb
  · rw [Fin.val_succ, pre_succ' w t h i, if_pos hb]
  · simp

theorem tail_eq (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t)
    (i : Fin t) : tail (wL w t h) (fJ J w t) i = fJ J w t (tpos (wL w t h) i) := by
  unfold tail tpos; split_ifs <;> rfl

theorem head_eq (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t)
    (i : Fin t) : head (wL w t h) (fJ J w t) i = fJ J w t (hpos (wL w t h) i) := by
  unfold head hpos; split_ifs <;> rfl

theorem tail_eq_iff (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ)
    (h : w.toWord.length = t) (i j : Fin t) :
    tail (wL w t h) (fJ J w t) i = tail (wL w t h) (fJ J w t) j ↔ ev w t h i * (ev w t h j)⁻¹ ∈ J := by
  rw [tail_eq, tail_eq, fJ_eq_iff, pre_tpos, pre_tpos]

theorem head_eq_iff (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ)
    (h : w.toWord.length = t) (i j : Fin t) :
    head (wL w t h) (fJ J w t) i = head (wL w t h) (fJ J w t) j ↔
      (ev w t h i * FreeGroup.of (wL w t h i).1) * (ev w t h j * FreeGroup.of (wL w t h j).1)⁻¹ ∈ J := by
  rw [head_eq, head_eq, fJ_eq_iff, pre_hpos, pre_hpos]

theorem traverses_iff (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ)
    (h : w.toWord.length = t) (n : ℕ) (g : FreeGroup (Fin k)) (x : Fin k) :
    Traverses J w n g x ↔ ∃ hn : n < t, (wL w t h ⟨n, hn⟩).1 = x ∧ ev w t h ⟨n, hn⟩ * g⁻¹ ∈ J := by
  constructor
  · rintro ⟨p, s, b, hw, hp, hm⟩
    have hn : n < t := by
      rw [← h, hw]; simp; omega
    have hget : w.toWord[n]'(h ▸ hn) = (x, b) := by
      simp only [hw]; subst hp; simp
    have htake : w.toWord.take n = p := by
      rw [hw, ← hp]; simp
    refine ⟨hn, ?_, ?_⟩
    · simp [wL, hget]
    · unfold ev pre; simp only [wL, hget, htake]; exact hm
  · rintro ⟨hn, hx, hm⟩
    have hn' : n < w.toWord.length := h ▸ hn
    refine ⟨w.toWord.take n, w.toWord.drop (n + 1), (w.toWord[n]'hn').2, ?_, ?_, ?_⟩
    · have : (x, (w.toWord[n]'hn').2) = w.toWord[n]'hn' := by
        rw [← hx]; rfl
      rw [this, ← List.drop_eq_getElem_cons hn', List.take_append_drop]
    · simp; omega
    · unfold ev at hm; simp only [wL] at hm hx; rw [hx] at hm; exact hm

/-! ## Determinism and counts of steps -/
theorem twice (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ)
    (h : w.toWord.length = t) (hw : w ∈ J) (htr : TracesEachCoreEdgeTwice J w) (i : Fin t) :
    2 ≤ (Finset.univ.filter fun j => edgeId (wL w t h) (fJ J w t) j = edgeId (wL w t h) (fJ J w t) i).card := by
  have hcore : IsCoreEdge J (ev w t h i) (wL w t h i).1 :=
    ⟨w, hw, i.val, (traverses_iff J w t h _ _ _).mpr ⟨i.isLt, rfl, by simp⟩⟩
  have h2 := htr _ _ hcore
  have hset : {n : ℕ | Traverses J w n (ev w t h i) (wL w t h i).1} =
      (((Finset.univ.filter fun j => edgeId (wL w t h) (fJ J w t) j = edgeId (wL w t h) (fJ J w t) i).map
        Fin.valEmbedding : Finset ℕ) : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.coe_map, Fin.valEmbedding_apply, Finset.coe_filter,
      Finset.mem_univ, true_and, Set.mem_image]
    rw [traverses_iff J w t h]
    constructor
    · rintro ⟨hn, hx, hm⟩
      refine ⟨⟨n, hn⟩, ?_, rfl⟩
      unfold edgeId
      rw [Prod.ext_iff]
      exact ⟨(tail_eq_iff J w t h _ _).mpr hm, hx⟩
    · rintro ⟨j, hj, rfl⟩
      unfold edgeId at hj
      rw [Prod.ext_iff] at hj
      exact ⟨j.isLt, hj.2, (tail_eq_iff J w t h _ _).mp hj.1⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_map] at h2
  exact h2

/-! ## Injectivity -/
theorem fJ_injOn (w : FreeGroup (Fin k)) (t : ℕ) (h : w.toWord.length = t) :
    Set.InjOn (fun J => fJ J w t) {J : Subgroup (FreeGroup (Fin k)) | w ∈ J ∧ TracesEachCoreEdgeTwice J w} := by
  classical
  have key : ∀ J J' : Subgroup (FreeGroup (Fin k)), w ∈ J → TracesEachCoreEdgeTwice J w →
      fJ J w t = fJ J' w t → J ≤ J' := by
    intro J J' hw htr heq
    refine le_of_forall_mem_iff {w} (Finset.univ.image fun i : Fin (t + 1) => pre w i) ?_ ?_ J J' ?_ ?_
    · intro t' ht' j hj
      rw [Finset.mem_singleton] at ht'
      subst ht'
      exact Finset.mem_image.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [pre_zero]⟩
    · intro y x hc
      have h2 := htr y x hc
      have hne : {i : ℕ | Traverses J w i y x}.Nonempty := by
        by_contra hem
        rw [Set.not_nonempty_iff_eq_empty] at hem
        rw [hem, Set.ncard_empty] at h2
        omega
      obtain ⟨j, hj⟩ := hne
      exact ⟨w, Finset.mem_singleton_self _, j, hj⟩
    · intro a ha b hb hab
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hb
      have := (fJ_eq_iff J w t i i').mpr hab
      rw [heq] at this
      exact (fJ_eq_iff J' w t i i').mp this
  intro J hJ J' hJ' heq
  exact le_antisymm (key J J' hJ.1 hJ.2 heq) (key J' J hJ'.1 hJ'.2 heq.symm)

/-! ## Children of tree edges (pure free-group combinatorics) -/
theorem toWord_mul_of (v : FreeGroup (Fin k)) (x : Fin k) (hv : v.toWord.getLast? ≠ some (x, false)) :
    (v * FreeGroup.of x).toWord = v.toWord ++ [(x, true)] := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of]
  apply FreeGroup.IsReduced.reduce_eq
  unfold FreeGroup.IsReduced
  rw [List.isChain_append]
  refine ⟨FreeGroup.isReduced_toWord, List.isChain_singleton _, ?_⟩
  intro a ha b hb hab
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
  subst hb
  rw [Option.mem_def] at ha
  cases hb2 : a.2
  · exfalso; apply hv; rw [ha, show a = (x, false) from Prod.ext hab hb2]
  · rfl

/-- The child vertex of the edge `(v, x)`: the endpoint whose reduced word ends with this edge. -/
def child (v : FreeGroup (Fin k)) (x : Fin k) : FreeGroup (Fin k) :=
  if v.toWord.getLast? = some (x, false) then v else v * FreeGroup.of x

/-- Recover the edge from its child. -/
def recov (c : FreeGroup (Fin k)) : Option (FreeGroup (Fin k) × Fin k) :=
  match c.toWord.getLast? with
  | some (y, true) => some (FreeGroup.mk c.toWord.dropLast, y)
  | some (y, false) => some (c, y)
  | none => none

theorem recov_child (v : FreeGroup (Fin k)) (x : Fin k) : recov (child v x) = some (v, x) := by
  unfold child
  split_ifs with hv
  · unfold recov; rw [hv]
  · unfold recov
    rw [toWord_mul_of v x hv]
    simp [FreeGroup.mk_toWord]

theorem child_ne_one (v : FreeGroup (Fin k)) (x : Fin k) : child v x ≠ 1 := by
  intro h1
  have := congrArg FreeGroup.toWord h1
  rw [FreeGroup.toWord_one] at this
  unfold child at this
  split_ifs at this with hv
  · rw [this] at hv; simp at hv
  · rw [toWord_mul_of v x hv] at this; simp at this

/-! ## The transversal -/
theorem tr_eq_iff (J : Subgroup (FreeGroup (Fin k))) (P : FreeGroup (Fin k) → Fin k → Prop)
    (g g' : FreeGroup (Fin k)) : tr J P g = tr J P g' ↔ g * g'⁻¹ ∈ J := by
  constructor
  · intro heq
    have h1 := tr_mem J P g
    have h2 := tr_mem J P g'
    rw [heq] at h1
    exact rel_trans (rel_symm h1) h2
  · exact tr_congr J P

theorem tr_tr (J : Subgroup (FreeGroup (Fin k))) (P : FreeGroup (Fin k) → Fin k → Prop)
    (g : FreeGroup (Fin k)) : tr J P (tr J P g) = tr J P g :=
  tr_congr J P (tr_mem J P g)

/-! ## Counting -/
theorem card_image_eq_of_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (F : α → β) (G : α → γ) (hFG : ∀ a ∈ s, ∀ b ∈ s, F a = F b ↔ G a = G b) :
    (s.image F).card = (s.image G).card := by
  classical
  apply Finset.card_bij (fun y hy => G (Classical.choose (Finset.mem_image.mp hy)))
  · intro y hy
    exact Finset.mem_image_of_mem G (Classical.choose_spec (Finset.mem_image.mp hy)).1
  · intro y1 hy1 y2 hy2 heq
    have s1 := Classical.choose_spec (Finset.mem_image.mp hy1)
    have s2 := Classical.choose_spec (Finset.mem_image.mp hy2)
    rw [← s1.2, ← s2.2]
    exact (hFG _ s1.1 _ s2.1).mpr heq
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨F a, Finset.mem_image_of_mem F ha, ?_⟩
    have s := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image_of_mem F ha))
    exact (hFG _ s.1 _ ha).mp s.2

theorem rank_bound (m : ℕ) (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ)
    (h : w.toWord.length = t) (hr : HasRank J m) :
    (Finset.univ.image (edgeId (wL w t h) (fJ J w t))).card + 1 ≤
      m + (Finset.univ.filter fun i => fJ J w t i = i).card := by
  classical
  set P : FreeGroup (Fin k) → Fin k → Prop := fun _ _ => True with hPdef
  have hP : CosetInv J P := fun _ _ _ _ _ => trivial
  set τ := tr J P with hτ
  set Ed : Finset (FreeGroup (Fin k) × Fin k) :=
    Finset.univ.image fun i : Fin t => (τ (ev w t h i), (wL w t h i).1) with hEd
  set Vs : Finset (FreeGroup (Fin k)) :=
    Finset.univ.image fun j : Fin (t + 1) => τ (pre w j) with hVs
  -- edges
  have hA : (Finset.univ.image (edgeId (wL w t h) (fJ J w t))).card = Ed.card := by
    apply card_image_eq_of_iff
    intro a _ b _
    unfold edgeId
    rw [Prod.ext_iff, Prod.ext_iff, tail_eq_iff, hτ, tr_eq_iff]
  -- vertices
  have hB : (Finset.univ.filter fun i => fJ J w t i = i).card = Vs.card := by
    have : (Finset.univ.filter fun i => fJ J w t i = i) = Finset.univ.image (fJ J w t) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi; exact ⟨i, hi⟩
      · rintro ⟨j, rfl⟩; exact fJ_fJ J w t j
    rw [this]
    apply card_image_eq_of_iff
    intro a _ b _
    rw [fJ_eq_iff, hτ, tr_eq_iff]
  rw [hA, hB]
  -- non-tree edges
  obtain ⟨bm⟩ := hr
  obtain ⟨b, -, -⟩ := exists_basis J P hP
  let eqv : Idx J P ≃ Fin m := Equiv.ofFreeGroupEquiv (b.repr.symm.trans bm.repr)
  let _ : Fintype (Idx J P) := Fintype.ofEquiv (Fin m) eqv.symm
  have hcardIdx : Fintype.card (Idx J P) = m := by
    rw [Fintype.card_congr eqv, Fintype.card_fin]
  have hEdtr : ∀ e ∈ Ed, τ e.1 = e.1 ∧ ∃ i : Fin t, e = (τ (ev w t h i), (wL w t h i).1) := by
    intro e he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨tr_tr J P _, i, rfl⟩
  have hNT : (Ed.filter fun e => τ (e.1 * FreeGroup.of e.2) ≠ e.1 * FreeGroup.of e.2).card ≤ m := by
    rw [← hcardIdx, ← Finset.card_univ]
    calc _ ≤ (Finset.univ.map (⟨Subtype.val, Subtype.val_injective⟩ :
            Idx J P ↪ FreeGroup (Fin k) × Fin k)).card := by
          apply Finset.card_le_card
          intro e he
          rw [Finset.mem_filter] at he
          rw [Finset.mem_map]
          exact ⟨⟨e, (hEdtr e he.1).1, he.2⟩, Finset.mem_univ _, rfl⟩
      _ = _ := Finset.card_map _
  -- tree edges
  have h1 : (1 : FreeGroup (Fin k)) ∈ Vs :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [pre_zero, hτ, tr_one]⟩
  have hT : (Ed.filter fun e => ¬ τ (e.1 * FreeGroup.of e.2) ≠ e.1 * FreeGroup.of e.2).card ≤
      (Vs.erase 1).card := by
    apply Finset.card_le_card_of_injOn (fun e => child e.1 e.2)
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter, not_not] at he
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨child_ne_one _ _, ?_⟩
      obtain ⟨-, i, rfl⟩ := hEdtr e he.1
      have htree := he.2
      simp only at htree ⊢
      unfold child
      split_ifs
      · exact Finset.mem_image.mpr ⟨tpos (wL w t h) i, Finset.mem_univ _, by rw [pre_tpos]⟩
      · refine Finset.mem_image.mpr ⟨hpos (wL w t h) i, Finset.mem_univ _, ?_⟩
        rw [pre_hpos, ← htree, hτ, tr_eq_iff]
        have := rel_symm (tr_mem J P (ev w t h i))
        simpa [mul_assoc] using this
    · intro e1 _ e2 _ heq
      have := congrArg recov heq
      simp only [recov_child] at this
      exact Option.some.inj this
  rw [Finset.card_erase_of_mem h1] at hT
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Ed) (fun e => τ (e.1 * FreeGroup.of e.2) ≠ e.1 * FreeGroup.of e.2)
  have hVpos : 0 < Vs.card := Finset.card_pos.mpr ⟨1, h1⟩
  omega

/-! ## The walk is admissible -/
theorem walkOK_fJ (m : ℕ) (J : Subgroup (FreeGroup (Fin k))) (w : FreeGroup (Fin k)) (t : ℕ)
    (h : w.toWord.length = t) (hr : HasRank J m) (hw : w ∈ J) (htr : TracesEachCoreEdgeTwice J w) :
    WalkOK m (wL w t h) (fJ J w t) := by
  refine ⟨?_, ?_, fun i => ⟨fJ_le_self J w t i, fJ_fJ J w t i⟩, ?_, ?_, twice J w t h hw htr,
    rank_bound m J w t h hr⟩
  · exact le_antisymm (fJ_le_self J w t 0) (Fin.zero_le _)
  · apply le_antisymm _ (Fin.zero_le _)
    apply fJ_le J w t
    have : ((Fin.last t : Fin (t + 1)) : ℕ) = w.toWord.length := by simp [h]
    rw [this, pre_length]
    simpa [pre_zero] using J.inv_mem hw
  · intro i j hx ht
    rw [tail_eq_iff] at ht
    rw [head_eq_iff, hx]
    simpa [mul_assoc] using ht
  · intro i j hx hh
    rw [head_eq_iff, hx] at hh
    rw [tail_eq_iff]
    simpa [mul_assoc] using hh

end Puder.Q284C.PartG
end

section
open Filter
namespace Puder.Q284C
open Puder
variable {k : ℕ}
alias walkOK_fJ := Puder.Q284C.PartG.walkOK_fJ

alias fJ_injOn := Puder.Q284C.PartG.fJ_injOn

end Puder.Q284C
end

section
namespace Puder.Q284C.PartF1
open Puder Puder.Q284C
variable {k : ℕ}
/-!
# q284 Part F1: the sum over words is bounded by the number of encoded pairs

`sum_ncard_le_card` of the Blueprint `Q284Cnt`.
-/
/-- The free-group letter of a generator or inverse generator. -/
def letter : Fin k ⊕ Fin k → Fin k × Bool
  | Sum.inl x => (x, true)
  | Sum.inr x => (x, false)

theorem letter_injective : Function.Injective (letter (k := k)) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp_all [letter]

theorem wordFree_map_some (L : List (Fin k ⊕ Fin k)) :
    StrongConv.wordFree (L.map some) = FreeGroup.mk (L.map letter) := by
  induction L with
  | nil => simp [StrongConv.wordFree]; rfl
  | cons a l ih =>
    have e : FreeGroup.mk ((a :: l).map letter) = FreeGroup.mk [letter a] * FreeGroup.mk (l.map letter) := by
      rw [FreeGroup.mul_mk]; rfl
    rw [e, ← ih]
    rcases a with x | x
    · simp [StrongConv.wordFree, letter]; rfl
    · simp [StrongConv.wordFree, letter]; rfl

theorem toWord_eq_of_length {t : ℕ} (i : Fin t → Fin k ⊕ Fin k)
    (h : (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t) :
    (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord = List.ofFn fun j => letter (i j) := by
  have e1 : (List.ofFn fun j => some (i j)) = (List.ofFn i).map some := by simp [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun j => letter (i j)) = (List.ofFn i).map letter := by simp [List.map_ofFn]; rfl
  rw [e1, wordFree_map_some, FreeGroup.toWord_mk, e2]
  rw [e1, wordFree_map_some, FreeGroup.toWord_mk] at h
  exact (FreeGroup.reduce.red).sublist.eq_of_length (by rw [h]; simp)

theorem wL_eq {t : ℕ} (i : Fin t → Fin k ⊕ Fin k)
    (h : (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t) :
    wL (StrongConv.wordFree (List.ofFn fun j => some (i j))) t h = fun j => letter (i j) := by
  funext j
  simp only [wL]
  have := toWord_eq_of_length i h
  simp [this]

open Classical in
theorem sum_ncard_le_card (k m t : ℕ) :
    (∑ i : Fin t → Fin k ⊕ Fin k with (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
      ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
          TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard : ℝ)) ≤
      ((Finset.univ.filter fun p : (Fin t → Fin k × Bool) × (Fin (t + 1) → Fin (t + 1)) =>
          Reduced p.1 ∧ WalkOK m p.1 p.2).card : ℝ) := by
  set S := (Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
    (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t) with hS
  let Lf : (Fin t → Fin k ⊕ Fin k) → Fin t → Fin k × Bool := fun i j => letter (i j)
  let T : (Fin t → Fin k ⊕ Fin k) → Finset ((Fin t → Fin k × Bool) × (Fin (t + 1) → Fin (t + 1))) :=
    fun i => (Finset.univ.filter fun f => WalkOK m (Lf i) f).image fun f => (Lf i, f)
  have hLf : Function.Injective Lf := by
    intro a b hab
    funext j
    exact letter_injective (congrFun hab j)
  -- each term is bounded
  have h1 : ∀ i ∈ S, {J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
      StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
        TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard ≤ (T i).card := by
    intro i hi
    have hlen : (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t := by
      simpa [hS] using hi
    have hT : (T i).card = (Finset.univ.filter fun f => WalkOK m (Lf i) f).card :=
      Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).2)
    rw [hT, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun J => fJ J (StrongConv.wordFree (List.ofFn fun j => some (i j))) t)
      ?_ ?_ (Set.toFinite _)
    · intro J hJ
      have := walkOK_fJ m J _ t hlen hJ.1 hJ.2.1 hJ.2.2
      rw [wL_eq i hlen] at this
      simpa using this
    · exact (fJ_injOn _ t hlen).mono fun J hJ => by simp only [Set.mem_ofPred_eq] at hJ ⊢; exact ⟨hJ.2.1, hJ.2.2⟩
  have h2 : ∑ i ∈ S, (T i).card = (S.biUnion T).card := by
    rw [Finset.card_biUnion]
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpa hpb
    simp only [T, Finset.mem_image] at hpa hpb
    obtain ⟨f, _, rfl⟩ := hpa
    obtain ⟨g, _, hg⟩ := hpb
    exact hab (hLf (Prod.mk.inj hg).1).symm
  have h3 : S.biUnion T ⊆ (Finset.univ.filter fun p : (Fin t → Fin k × Bool) × (Fin (t + 1) → Fin (t + 1)) =>
          Reduced p.1 ∧ WalkOK m p.1 p.2) := by
    intro p hp
    simp only [Finset.mem_biUnion, T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨i, hi, f, hf, rfl⟩ := hp
    have hlen : (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t := by
      simpa [hS] using hi
    have hr := reduced_wL _ t hlen
    rw [wL_eq i hlen] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr, hf⟩
  have key : ∑ i ∈ S, {J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧
      StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
        TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard ≤
      (Finset.univ.filter fun p : (Fin t → Fin k × Bool) × (Fin (t + 1) → Fin (t + 1)) =>
          Reduced p.1 ∧ WalkOK m p.1 p.2).card :=
    (Finset.sum_le_sum h1).trans (h2 ▸ Finset.card_le_card h3)
  exact_mod_cast key

end Puder.Q284C.PartF1
end

section
open Filter
namespace Puder.Q284C
open Puder
variable {k : ℕ}
/-! ## Part F: the sum and the asymptotics -/
alias sum_ncard_le_card := Puder.Q284C.PartF1.sum_ncard_le_card

end Puder.Q284C
end

section
namespace Puder.Q284C.PartF2
open Puder Puder.Q284C Filter
theorem boundedUnder_and_limsup_le (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (M : ℝ) (hM : 0 < M) (C D : ℕ)
    (hb : ∀ t, a t ≤ C * ((t : ℝ) + 2) ^ D * M ^ t) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => a t ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ => a t ^ (1 / (t : ℝ))) atTop ≤ M := by
  set u : ℕ → ℝ := fun t => ((C : ℝ) + 1) ^ (1 / (t : ℝ)) * ((t : ℝ) + 2) ^ ((D : ℝ) / t) * M
    with hu_def
  -- the upper sequence tends to M
  have h1 : Tendsto (fun t : ℕ => (1 / (t : ℝ))) atTop (nhds 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hC : Tendsto (fun t : ℕ => ((C : ℝ) + 1) ^ (1 / (t : ℝ))) atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := ((C : ℝ) + 1))).rpow h1 (Or.inl (by positivity))
    simpa using this
  have hD : Tendsto (fun t : ℕ => ((t : ℝ) + 2) ^ ((D : ℝ) / t)) atTop (nhds 1) := by
    have h := tendsto_rpow_div_mul_add (D : ℝ) 1 (-2) (by norm_num)
    have h2 : Tendsto (fun t : ℕ => (t : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have := h.comp h2
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp]
    congr 2
    ring
  have hu : Tendsto u atTop (nhds M) := by
    have := (hC.mul hD).mul_const M
    simpa [hu_def] using this
  -- eventual comparison
  have hle : ∀ᶠ t : ℕ in atTop, a t ^ (1 / (t : ℝ)) ≤ u t := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : t ≠ 0 := by omega
    have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht0
    have hb' : a t ≤ ((C : ℝ) + 1) * ((t : ℝ) + 2) ^ D * M ^ t := by
      refine (hb t).trans ?_
      gcongr
      linarith
    have hnn : (0 : ℝ) ≤ 1 / (t : ℝ) := by positivity
    calc a t ^ (1 / (t : ℝ)) ≤ (((C : ℝ) + 1) * ((t : ℝ) + 2) ^ D * M ^ t) ^ (1 / (t : ℝ)) :=
          Real.rpow_le_rpow (ha t) hb' hnn
      _ = u t := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
          rw [hu_def]
          simp only
          congr 1
          · congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            congr 1
            field_simp
          · rw [one_div, Real.pow_rpow_inv_natCast hM.le ht0]
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => a t ^ (1 / (t : ℝ))) := by
    obtain ⟨B, hB⟩ := hu.isBoundedUnder_le
    refine ⟨B, ?_⟩
    simp only [eventually_map] at hB ⊢
    filter_upwards [hB, hle] with t h1 h2
    exact h2.trans h1
  refine ⟨hbdd, ?_⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun t : ℕ => a t ^ (1 / (t : ℝ))) :=
    isCoboundedUnder_le_of_le atTop (fun t => Real.rpow_nonneg (ha t) _)
  calc limsup (fun t : ℕ => a t ^ (1 / (t : ℝ))) atTop ≤ limsup u atTop :=
        limsup_le_limsup hle hcob hu.isBoundedUnder_le
    _ = M := hu.limsup_eq

end Puder.Q284C.PartF2
end

section
open Filter
namespace Puder.Q284C
open Puder
variable {k : ℕ}
alias boundedUnder_and_limsup_le := Puder.Q284C.PartF2.boundedUnder_and_limsup_le

theorem rate_pos (k m : ℕ) (hk : 2 ≤ k) : 0 < rate k m := by
  unfold rate
  have : (0 : ℝ) < Real.sqrt (2 * k - 1) := Real.sqrt_pos.mpr (by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  split_ifs with h
  · exact this
  · have := not_le.mp h; linarith

end Puder.Q284C
end

section
open Finset
namespace Puder.Q284C.PartC1
open Puder Puder.Q284C
variable {k : ℕ}
/-!
# q284 Part C, helper 1: ends, degrees, the handshake lemma
-/
/-- The inverse letter. -/
def inv (e : Fin k × Bool) : Fin k × Bool := (e.1, !e.2)

theorem inv_ne (e : Fin k × Bool) : inv e ≠ e := by
  obtain ⟨x, b⟩ := e; cases b <;> simp [inv]

theorem inv_inv (e : Fin k × Bool) : inv (inv e) = e := by
  obtain ⟨x, b⟩ := e; simp [inv]

end Puder.Q284C.PartC1
end

section
open Finset
namespace Puder.Q284C.PartC1
open Puder Puder.Q284C
variable {k : ℕ}
variable {t : ℕ} (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1))
/-- Step `j` has the end `e` at vertex `u`. -/
def hasEnd (j : Fin t) (u : Fin (t + 1)) (e : Fin k × Bool) : Prop :=
  (L j).1 = e.1 ∧ (if e.2 then tail L f j = u else head L f j = u)

open Classical in
/-- The ends at `u`. -/
noncomputable def Ends (u : Fin (t + 1)) : Finset (Fin k × Bool) :=
  univ.filter fun e => ∃ j, hasEnd L f j u e

/-- The degree of `u`. -/
noncomputable def deg (u : Fin (t + 1)) : ℕ := (Ends L f u).card

theorem mem_Ends {u : Fin (t + 1)} {e : Fin k × Bool} : e ∈ Ends L f u ↔ ∃ j, hasEnd L f j u e := by
  classical
  unfold Ends; simp

theorem hasEnd_dep (i : Fin t) : hasEnd L f i (f i.castSucc) (L i) := by
  unfold hasEnd tail head
  cases h : (L i).2 <;> simp

theorem hasEnd_arr (i : Fin t) : hasEnd L f i (f i.succ) (inv (L i)) := by
  unfold hasEnd tail head inv
  cases h : (L i).2 <;> simp

theorem hasEnd_pos (j : Fin t) (u : Fin (t + 1)) (e : Fin k × Bool) :
    hasEnd L f j u e → u = f j.castSucc ∨ u = f j.succ := by
  unfold hasEnd tail head
  rintro ⟨-, h⟩
  split_ifs at h <;> simp_all

theorem hasEnd_vertex (hf : ∀ i, f (f i) = f i) {j : Fin t} {u : Fin (t + 1)} {e : Fin k × Bool}
    (h : hasEnd L f j u e) : f u = u := by
  rcases hasEnd_pos L f j u e h with rfl | rfl <;> exact hf _

end Puder.Q284C.PartC1
end

section
open Finset
namespace Puder.Q284C.PartC1
open Puder Puder.Q284C
variable {k : ℕ}
variable {t : ℕ} (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1))
variable {L f}
theorem edgeId_eq_of_hasEnd
    (hC : ∀ i j, (L i).1 = (L j).1 → head L f i = head L f j → tail L f i = tail L f j)
    {i j : Fin t} {u : Fin (t + 1)} {e : Fin k × Bool}
    (hj : hasEnd L f j u e) (hi : hasEnd L f i u e) : edgeId L f j = edgeId L f i := by
  obtain ⟨hj1, hj2⟩ := hj; obtain ⟨hi1, hi2⟩ := hi
  unfold edgeId
  have hl : (L j).1 = (L i).1 := hj1.trans hi1.symm
  cases he : e.2 <;> simp only [he, if_true, Bool.false_eq_true, if_false] at hj2 hi2
  · exact Prod.ext (hC j i hl (hj2.trans hi2.symm)) hl
  · exact Prod.ext (hj2.trans hi2.symm) hl

theorem hasEnd_of_edgeId_eq
    (hD : ∀ i j, (L i).1 = (L j).1 → tail L f i = tail L f j → head L f i = head L f j)
    {i j : Fin t} {u : Fin (t + 1)} {e : Fin k × Bool}
    (hij : edgeId L f j = edgeId L f i) (hi : hasEnd L f i u e) : hasEnd L f j u e := by
  obtain ⟨hi1, hi2⟩ := hi
  unfold edgeId at hij
  have ht := congrArg Prod.fst hij
  have hl := congrArg Prod.snd hij
  simp only at ht hl
  refine ⟨hl.trans hi1, ?_⟩
  cases he : e.2 <;> simp only [he, if_true, Bool.false_eq_true, if_false] at hi2 ⊢
  · rw [hD j i hl ht, hi2]
  · rw [ht, hi2]

theorem succ_eq_of_hasEnd
    (hD : ∀ i j, (L i).1 = (L j).1 → tail L f i = tail L f j → head L f i = head L f j)
    (hC : ∀ i j, (L i).1 = (L j).1 → head L f i = head L f j → tail L f i = tail L f j)
    {i j : Fin t} {u : Fin (t + 1)} {e : Fin k × Bool}
    (hj : hasEnd L f j u e) (hLi : L i = e) (hfi : f i.castSucc = u) :
    f i.succ = if e.2 then head L f j else tail L f j := by
  obtain ⟨hj1, hj2⟩ := hj
  have hl : (L i).1 = (L j).1 := by rw [hLi, hj1]
  cases he : e.2 <;> simp only [he, if_true, Bool.false_eq_true, if_false] at hj2 ⊢
  · have hh : head L f i = head L f j := by
      rw [hj2]; unfold head; rw [hLi, he]; simpa using hfi
    have := hC i j hl hh
    rw [← this]; unfold tail; rw [hLi, he]; simp
  · have ht : tail L f i = tail L f j := by
      rw [hj2]; unfold tail; rw [hLi, he]; simpa using hfi
    have := hD i j hl ht
    rw [← this]; unfold head; rw [hLi, he]; simp

end Puder.Q284C.PartC1
end

section
open Finset
namespace Puder.Q284C.PartC1
open Puder Puder.Q284C
variable {k : ℕ}
/-! ## The handshake lemma -/
theorem sum_card_fib {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : Finset (A × B)) :
    ∑ a, (univ.filter fun b => (a, b) ∈ S).card = S.card := by
  classical
  simp only [card_filter]
  rw [← Fintype.sum_prod_type' (f := fun a b => if (a, b) ∈ S then 1 else 0)]
  simp

theorem card_image_eq_of_iff {A B C : Type*} [Fintype A] [DecidableEq B] [DecidableEq C]
    (g : A → B) (h : A → C) (hgh : ∀ i j, g i = g j ↔ h i = h j) :
    (univ.image g).card = (univ.image h).card := by
  classical
  have h1 : (univ.image g).card = (univ.image fun i => (g i, h i)).card := by
    rw [show (univ.image g) = (univ.image fun i => (g i, h i)).image Prod.fst by
      rw [image_image]; rfl]
    apply card_image_of_injOn
    intro p hp q hq hpq
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hp hq
    obtain ⟨i, rfl⟩ := hp; obtain ⟨j, rfl⟩ := hq
    simp only at hpq
    exact Prod.ext hpq ((hgh i j).1 hpq)
  have h2 : (univ.image h).card = (univ.image fun i => (g i, h i)).card := by
    rw [show (univ.image h) = (univ.image fun i => (g i, h i)).image Prod.snd by
      rw [image_image]; rfl]
    apply card_image_of_injOn
    intro p hp q hq hpq
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hp hq
    obtain ⟨i, rfl⟩ := hp; obtain ⟨j, rfl⟩ := hq
    simp only at hpq
    exact Prod.ext ((hgh i j).2 hpq) hpq
  rw [h1, h2]

end Puder.Q284C.PartC1
end

section
open Finset
namespace Puder.Q284C.PartC1
open Puder Puder.Q284C
variable {k : ℕ}
variable {t : ℕ} {L : Fin t → Fin k × Bool} {f : Fin (t + 1) → Fin (t + 1)}
/-- The number of edges. -/
noncomputable def nE (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) : ℕ :=
  by classical exact (univ.image (edgeId L f)).card

theorem handshake
    (hD : ∀ i j, (L i).1 = (L j).1 → tail L f i = tail L f j → head L f i = head L f j)
    (hC : ∀ i j, (L i).1 = (L j).1 → head L f i = head L f j → tail L f i = tail L f j) :
    ∑ u, deg L f u = 2 * nE L f := by
  classical
  set hId : Fin t → Fin (t + 1) × Fin k := fun j => (head L f j, (L j).1)
  have hdeg : ∀ u, deg L f u = (univ.filter fun x => (u, x) ∈ univ.image (edgeId L f)).card +
      (univ.filter fun x => (u, x) ∈ univ.image hId).card := by
    intro u
    unfold deg
    simp only [card_filter]
    rw [show (Ends L f u).card = ∑ e, if e ∈ Ends L f u then 1 else 0 by
      rw [sum_boole]; simp]
    rw [Fintype.sum_prod_type, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_bool]
    simp only [mem_Ends, hasEnd, mem_image, mem_univ, true_and, edgeId, hId, Prod.mk.injEq]
    simp only [if_true, Bool.false_eq_true, if_false]
    congr 2 <;> apply propext <;> constructor <;> rintro ⟨j, h1, h2⟩ <;> exact ⟨j, h2, h1⟩
  have hcard : (univ.image hId).card = (univ.image (edgeId L f)).card := by
    apply card_image_eq_of_iff
    intro i j
    simp only [hId, edgeId, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hC i j h2 h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨hD i j h2 h1, h2⟩
  simp only [hdeg, sum_add_distrib, sum_card_fib, hcard]
  unfold nE; ring

/-! ## Degree bounds -/
theorem deg_eq_zero_of_not_vertex (hf : ∀ i, f (f i) = f i) {u : Fin (t + 1)} (hu : f u ≠ u) :
    deg L f u = 0 := by
  unfold deg; rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he; obtain ⟨j, hj⟩ := (mem_Ends L f).1 he
  exact hu (hasEnd_vertex L f hf hj)

theorem two_le_deg (hR : Reduced L) (hlast : f (Fin.last t) = 0) {u : Fin (t + 1)} (hu : f u = u)
    (hu0 : u ≠ 0) : 2 ≤ deg L f u := by
  have hul : u ≠ Fin.last t := by
    rintro rfl; exact hu0 (hu.symm.trans hlast)
  have hu1 : 1 ≤ u.val := by
    rcases Nat.eq_zero_or_pos u.val with h | h
    · exact absurd (Fin.ext h) hu0
    · exact h
  have hut : u.val < t := by
    have := Fin.val_lt_last hul; simpa using this
  set i : Fin t := ⟨u.val - 1, by omega⟩
  set j : Fin t := ⟨u.val, hut⟩
  have hi : i.succ = u := by ext; simp [i]; omega
  have hj : j.castSucc = u := by ext; simp [j]
  have h1 : inv (L i) ∈ Ends L f u := (mem_Ends L f).2 ⟨i, by
    have := hasEnd_arr L f i; rwa [hi, hu] at this⟩
  have h2 : L j ∈ Ends L f u := (mem_Ends L f).2 ⟨j, by
    have := hasEnd_dep L f j; rwa [hj, hu] at this⟩
  have hne : L j ≠ inv (L i) := by
    have := hR i (by simp [i]; omega)
    have hj' : (⟨i.val + 1, by simp [i]; omega⟩ : Fin t) = j := by ext; simp [i, j]; omega
    rw [hj'] at this; exact this
  unfold deg
  exact Finset.one_lt_card.2 ⟨_, h1, _, h2, hne.symm⟩

open Classical in
/-- The vertex set. -/
noncomputable def Vset (f : Fin (t + 1) → Fin (t + 1)) : Finset (Fin (t + 1)) :=
  univ.filter fun u => f u = u

open Classical in
/-- Total excess degree over the vertices other than the base. -/
noncomputable def excess (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) : ℕ :=
  ∑ u ∈ (Vset f).erase 0, (deg L f u - 2)

theorem deg0_add_excess {m : ℕ} (hR : Reduced L) (hW : WalkOK m L f) :
    deg L f 0 + excess L f ≤ 2 * m := by
  classical
  obtain ⟨h0, hlast, hf, hD, hC, -, hE⟩ := hW
  have hs : ∑ u, deg L f u = ∑ u ∈ Vset f, deg L f u := by
    unfold Vset
    rw [sum_filter_of_ne]
    intro u _ hne
    by_contra h
    exact hne (deg_eq_zero_of_not_vertex (fun i => (hf i).2) h)
  have h0V : (0 : Fin (t + 1)) ∈ Vset f := by unfold Vset; simp [h0]
  have hs2 : ∑ u ∈ Vset f, deg L f u = deg L f 0 + (excess L f + 2 * ((Vset f).card - 1)) := by
    rw [← add_sum_erase _ _ h0V]
    congr 1
    unfold excess
    rw [← card_erase_of_mem h0V, mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
    refine sum_congr rfl fun u hu => ?_
    have hu' : f u = u ∧ u ≠ 0 := by
      simp only [Vset, mem_erase, mem_filter, mem_univ, true_and] at hu; exact ⟨hu.2, hu.1⟩
    have := two_le_deg hR hlast hu'.1 hu'.2
    omega
  have hh := handshake hD hC
  rw [hs, hs2] at hh
  have hV1 : 1 ≤ (Vset f).card := card_pos.2 ⟨0, h0V⟩
  have hE' : nE L f + 1 ≤ m + (Vset f).card := by
    unfold nE Vset; convert hE
  omega

theorem deg_le_of_nonleaf {m : ℕ} (hR : Reduced L) (hW : WalkOK m L f) (h2 : 2 ≤ deg L f 0)
    (u : Fin (t + 1)) : deg L f u ≤ 2 * m := by
  classical
  have hx := deg0_add_excess hR hW
  by_cases hu0 : u = 0
  · subst hu0; omega
  by_cases hv : f u = u
  · have : deg L f u - 2 ≤ excess L f := by
      unfold excess
      exact single_le_sum (f := fun u => deg L f u - 2) (fun _ _ => Nat.zero_le _)
        (by simp [Vset, hu0, hv])
    omega
  · rw [deg_eq_zero_of_not_vertex (fun i => (hW.2.2.1 i).2) hv]; omega

open Classical in
/-- The junctions: the base and the vertices of degree at least three. -/
noncomputable def Jn (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) : Finset (Fin (t + 1)) :=
  univ.filter fun u => f u = u ∧ (u = 0 ∨ 3 ≤ deg L f u)

theorem Jn_bounds {m : ℕ} (hR : Reduced L) (hW : WalkOK m L f) :
    (Jn L f).card ≤ 2 * m + 1 ∧ ∑ u ∈ Jn L f, deg L f u ≤ 6 * m := by
  classical
  have hx := deg0_add_excess hR hW
  set J' := ((Vset f).erase 0).filter fun u => 3 ≤ deg L f u
  have hsub : Jn L f ⊆ insert 0 J' := by
    intro u hu
    simp only [Jn, mem_filter, mem_univ, true_and] at hu
    rcases hu with ⟨hv, h | h⟩
    · simp [h]
    · by_cases h0 : u = 0
      · simp [h0]
      · exact mem_insert_of_mem (by simp [J', Vset, h0, hv, h])
  have hJ'1 : J'.card ≤ excess L f := by
    calc J'.card = ∑ u ∈ J', 1 := card_eq_sum_ones _
      _ ≤ ∑ u ∈ J', (deg L f u - 2) := sum_le_sum fun u hu => by
          simp only [J', mem_filter] at hu; omega
      _ ≤ excess L f := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hJ'2 : ∑ u ∈ J', deg L f u ≤ 3 * excess L f := by
    calc ∑ u ∈ J', deg L f u ≤ ∑ u ∈ J', 3 * (deg L f u - 2) := sum_le_sum fun u hu => by
          simp only [J', mem_filter] at hu; omega
      _ = 3 * ∑ u ∈ J', (deg L f u - 2) := by rw [mul_sum]
      _ ≤ 3 * excess L f := Nat.mul_le_mul_left _
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _))
  have h0J' : (0 : Fin (t + 1)) ∉ J' := by simp [J']
  refine ⟨?_, ?_⟩
  · calc (Jn L f).card ≤ (insert 0 J').card := card_le_card hsub
      _ ≤ J'.card + 1 := card_insert_le _ _
      _ ≤ 2 * m + 1 := by omega
  · calc ∑ u ∈ Jn L f, deg L f u ≤ ∑ u ∈ insert 0 J', deg L f u :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ = deg L f 0 + ∑ u ∈ J', deg L f u := sum_insert h0J'
      _ ≤ 6 * m := by omega

end Puder.Q284C.PartC1
end

section
open Finset
namespace Puder.Q284C.PartC2
open Puder Puder.Q284C Puder.Q284C.PartC1
variable {k : ℕ}
variable {t : ℕ} (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1))
/-!
# q284 Part C, helper 2: step types (first, second and later crossings)
-/
/-- Step `i` is the first crossing of its edge. -/
def isN (i : Fin t) : Prop := ∀ j : Fin t, j < i → edgeId L f j ≠ edgeId L f i

open Classical in
/-- Step `i` is the second crossing of its edge. -/
def isS (i : Fin t) : Prop := (univ.filter fun j => j < i ∧ edgeId L f j = edgeId L f i).card = 1

open Classical in
noncomputable def Nset : Finset (Fin t) := univ.filter (isN L f)

open Classical in
noncomputable def Sset : Finset (Fin t) := univ.filter (isS L f)

open Classical in
noncomputable def Lset : Finset (Fin t) := univ.filter fun i => ¬ isN L f i ∧ ¬ isS L f i

end Puder.Q284C.PartC2
end

section
open Finset
namespace Puder.Q284C.PartC2
open Puder Puder.Q284C Puder.Q284C.PartC1
variable {k : ℕ}
variable {t : ℕ} {L : Fin t → Fin k × Bool} {f : Fin (t + 1) → Fin (t + 1)}
theorem exists_isN (i : Fin t) : ∃ j, isN L f j ∧ edgeId L f j = edgeId L f i := by
  classical
  set X := univ.filter fun j => edgeId L f j = edgeId L f i
  have hX : X.Nonempty := ⟨i, by simp [X]⟩
  refine ⟨X.min' hX, ?_, (mem_filter.1 (X.min'_mem hX)).2⟩
  intro j hj he
  have hjX : j ∈ X := by simp only [X, mem_filter, mem_univ, true_and]; rw [he]; exact (mem_filter.1 (X.min'_mem hX)).2
  exact absurd (X.min'_le j hjX) (not_le.2 hj)

theorem isN_inj {i j : Fin t} (hi : isN L f i) (hj : isN L f j) (h : edgeId L f i = edgeId L f j) :
    i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (hj i hij)
  · exact hij
  · exact absurd h.symm (hi j hij)

theorem card_Nset : (Nset L f).card = nE L f := by
  classical
  unfold nE
  have himg : (Nset L f).image (edgeId L f) = univ.image (edgeId L f) := by
    apply Subset.antisymm (image_subset_image (subset_univ _))
    intro e he
    obtain ⟨i, -, rfl⟩ := mem_image.1 he
    obtain ⟨j, hj, hje⟩ := exists_isN (L := L) (f := f) i
    exact mem_image.2 ⟨j, by simp [Nset, hj], hje⟩
  rw [← himg, card_image_of_injOn]
  intro i hi j hj h
  simp only [Nset, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
  exact isN_inj hi hj h

theorem isS_inj {i j : Fin t} (hi : isS L f i) (hj : isS L f j) (h : edgeId L f i = edgeId L f j) :
    i = j := by
  classical
  have key : ∀ a b : Fin t, isS L f a → isS L f b → edgeId L f a = edgeId L f b → ¬ a < b := by
    intro a b ha hb hab hlt
    obtain ⟨c, hc⟩ := card_eq_one.1 ha
    have hcm : c ∈ univ.filter fun j => j < a ∧ edgeId L f j = edgeId L f a := by rw [hc]; simp
    simp only [mem_filter, mem_univ, true_and] at hcm
    have h2 : 2 ≤ (univ.filter fun j => j < b ∧ edgeId L f j = edgeId L f b).card := by
      apply one_lt_card.2
      refine ⟨a, by simp [hlt, hab], c, by simp [hcm.1.trans hlt, hcm.2, hab], ?_⟩
      exact ne_of_gt hcm.1
    unfold isS at hb; omega
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd hij (key i j hi hj h)
  · exact hij
  · exact absurd hij (key j i hj hi h.symm)

theorem card_Sset (h2 : ∀ i, 2 ≤ (univ.filter fun j => edgeId L f j = edgeId L f i).card) :
    (Sset L f).card = nE L f := by
  classical
  unfold nE
  have himg : (Sset L f).image (edgeId L f) = univ.image (edgeId L f) := by
    apply Subset.antisymm (image_subset_image (subset_univ _))
    intro e he
    obtain ⟨i, -, rfl⟩ := mem_image.1 he
    set X := univ.filter fun j => edgeId L f j = edgeId L f i
    have hX : X.Nonempty := ⟨i, by simp [X]⟩
    set j1 := X.min' hX
    have hj1 : j1 ∈ X := X.min'_mem hX
    have hX' : (X.erase j1).Nonempty := by
      rw [← card_pos, card_erase_of_mem hj1]
      have : 2 ≤ X.card := by convert h2 i
      omega
    set j2 := (X.erase j1).min' hX'
    have hj2 : j2 ∈ X.erase j1 := (X.erase j1).min'_mem hX'
    have hj2X : j2 ∈ X := mem_of_mem_erase hj2
    have hj2e : edgeId L f j2 = edgeId L f i := (mem_filter.1 hj2X).2
    have hj1e : edgeId L f j1 = edgeId L f i := (mem_filter.1 hj1).2
    have hlt : j1 < j2 := lt_of_le_of_ne (X.min'_le j2 hj2X) (ne_of_mem_erase hj2).symm
    refine mem_image.2 ⟨j2, ?_, hj2e⟩
    simp only [Sset, mem_filter, mem_univ, true_and, isS]
    rw [card_eq_one]
    refine ⟨j1, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hjl, hje⟩
      by_contra hne
      have : j ∈ X.erase j1 := mem_erase.2 ⟨hne, by simp [X, hje.trans hj2e]⟩
      exact absurd ((X.erase j1).min'_le j this) (not_le.2 hjl)
    · rintro rfl; exact ⟨hlt, hj1e.trans hj2e.symm⟩
  rw [← himg, card_image_of_injOn]
  intro i hi j hj h
  simp only [Sset, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
  exact isS_inj hi hj h

theorem not_isS_of_isN {i : Fin t} (h : isN L f i) : ¬ isS L f i := by
  classical
  unfold isS
  rw [card_eq_one]
  rintro ⟨c, hc⟩
  have hcm : c ∈ univ.filter fun j => j < i ∧ edgeId L f j = edgeId L f i := by rw [hc]; simp
  simp only [mem_filter, mem_univ, true_and] at hcm
  exact h c hcm.1 hcm.2

theorem card_Lset (h2 : ∀ i, 2 ≤ (univ.filter fun j => edgeId L f j = edgeId L f i).card) :
    (Lset L f).card + 2 * nE L f ≤ t := by
  classical
  have hd1 : Disjoint (Nset L f) (Sset L f) := by
    rw [disjoint_left]; intro i hi hi'
    simp only [Nset, Sset, mem_filter, mem_univ, true_and] at hi hi'
    exact not_isS_of_isN hi hi'
  have hd2 : Disjoint (Nset L f ∪ Sset L f) (Lset L f) := by
    rw [disjoint_left]; intro i hi hi'
    simp only [Nset, Sset, Lset, mem_union, mem_filter, mem_univ, true_and] at hi hi'
    tauto
  have := card_le_univ (Nset L f ∪ Sset L f ∪ Lset L f)
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_Nset, card_Sset h2] at this
  simp at this; omega

/-- Injectively labelling steps departing a set of vertices by their departure ends. -/
theorem card_le_sum_deg
    (hC : ∀ i j, (L i).1 = (L j).1 → head L f i = head L f j → tail L f i = tail L f j)
    (X : Finset (Fin t)) (J : Finset (Fin (t + 1)))
    (hX : ∀ i ∈ X, f i.castSucc ∈ J)
    (hinj : ∀ i ∈ X, ∀ j ∈ X, edgeId L f i = edgeId L f j → i = j) :
    X.card ≤ ∑ u ∈ J, deg L f u := by
  classical
  unfold deg
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun i => (⟨f i.castSucc, L i⟩ : Σ _ : Fin (t + 1), Fin k × Bool))
  · intro i hi
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe]
    exact ⟨hX i hi, (mem_Ends L f).2 ⟨i, hasEnd_dep L f i⟩⟩
  · intro i hi j hj h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : L i = L j := eq_of_heq h2
    apply hinj i hi j hj
    have hj' := hasEnd_dep L f j
    rw [← h1, ← h2'] at hj'
    exact edgeId_eq_of_hasEnd hC (hasEnd_dep L f i) hj'

/-- A step entering a brand-new position is a first crossing. -/
theorem isN_of_new (hD : ∀ i j, (L i).1 = (L j).1 → tail L f i = tail L f j → head L f i = head L f j)
    (hf : ∀ i, f i ≤ i) {i : Fin t} (h : f i.succ = i.succ) : isN L f i := by
  intro j hj he
  have := hasEnd_of_edgeId_eq hD he (hasEnd_arr L f i)
  rw [h] at this
  rcases hasEnd_pos L f j _ _ this with h' | h'
  · have := hf j.castSucc
    have h1 : (i.succ : Fin (t + 1)).val = (f j.castSucc).val := congrArg Fin.val h'
    simp at h1; rw [Fin.le_def] at this; simp at this
    rw [Fin.lt_def] at hj; omega
  · have := hf j.succ
    have h1 : (i.succ : Fin (t + 1)).val = (f j.succ).val := congrArg Fin.val h'
    simp at h1; rw [Fin.le_def] at this; simp at this
    rw [Fin.lt_def] at hj; omega

open Classical in
/-- The first crossings that end at an old vertex. -/
noncomputable def Qset (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) : Finset (Fin t) :=
  univ.filter fun i => isN L f i ∧ f i.succ ≠ i.succ

theorem card_Qset {m : ℕ} (hW : WalkOK m L f) : (Qset L f).card ≤ m := by
  classical
  obtain ⟨h0, hlast, hf, hD, hC, h2, hE⟩ := hW
  set Nnew := univ.filter fun i : Fin t => f i.succ = i.succ
  have hsub : Nnew ⊆ Nset L f := by
    intro i hi
    simp only [Nnew, mem_filter, mem_univ, true_and] at hi
    simp only [Nset, mem_filter, mem_univ, true_and]
    exact isN_of_new hD (fun i => (hf i).1) hi
  have hQ : Qset L f = Nset L f \ Nnew := by
    ext i; simp [Qset, Nset, Nnew]
  have hV : (Vset f).erase 0 = Nnew.image Fin.succ := by
    ext u
    simp only [Vset, mem_erase, mem_filter, mem_univ, true_and, mem_image, Nnew]
    constructor
    · rintro ⟨hu0, hu⟩
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hu0
      exact ⟨i, hu, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Fin.succ_ne_zero i, hi⟩
  have hcV : Nnew.card = (Vset f).card - 1 := by
    have h0V : (0 : Fin (t + 1)) ∈ Vset f := by unfold Vset; simp [h0]
    rw [← card_erase_of_mem h0V, hV, card_image_of_injective _ (Fin.succ_injective _)]
  have hE' : nE L f + 1 ≤ m + (Vset f).card := by unfold nE Vset; convert hE
  rw [hQ, card_sdiff_of_subset hsub, card_Nset, hcV]
  omega

end Puder.Q284C.PartC2
end

section
open Finset
namespace Puder.Q284C.PartC3
/-!
# q284 Part C, helper 3: the branching (tree of choices) lemma and subset counts
-/
/-- The branching of `S` at step `i` along `p`. -/
def br {β α : Type*} [DecidableEq α] {t : ℕ} (S : Finset β) (val : Fin t → β → α) (p : β) (i : Fin t) : ℕ :=
  haveI := Classical.decEq β
  ((S.filter fun q => ∀ j < i, val j q = val j p).image (val i)).card

theorem card_le_of_branch {β α : Type*} [DecidableEq α] :
    ∀ (t : ℕ) (S : Finset β) (val : Fin t → β → α) (B : ℕ),
      (∀ p ∈ S, ∀ q ∈ S, (∀ i, val i p = val i q) → p = q) →
      (∀ p ∈ S, ∏ i, br S val p i ≤ B) → S.card ≤ B := by
  classical
  intro t
  induction t with
  | zero =>
    intro S val B hinj hB
    rcases S.eq_empty_or_nonempty with h | ⟨p, hp⟩
    · simp [h]
    · have h1 : S.card ≤ 1 := card_le_one.2 fun a ha b hb => hinj a ha b hb (fun i => i.elim0)
      have := hB p hp
      simp at this
      omega
  | succ t ih =>
    intro S val B hinj hB
    set A0 := S.image (val 0)
    set val' : Fin t → β → α := fun i => val i.succ
    have hbr0 : ∀ p, br S val p 0 = A0.card := by
      intro p
      unfold br
      congr 2
      ext q; simp
    have hbrs : ∀ p ∈ S, ∀ i : Fin t,
        br S val p i.succ = br (S.filter fun q => val 0 q = val 0 p) val' p i := by
      intro p hp i
      unfold br
      congr 2
      ext q
      simp only [mem_filter, val']
      constructor
      · rintro ⟨hq, h⟩
        refine ⟨⟨hq, h 0 (Fin.succ_pos _)⟩, fun j hj => h j.succ (Fin.succ_lt_succ_iff.2 hj)⟩
      · rintro ⟨⟨hq, h0⟩, h⟩
        refine ⟨hq, fun j hj => ?_⟩
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact h0
        · exact h j' (Fin.succ_lt_succ_iff.1 hj)
    rw [card_eq_sum_card_image (val 0) S]
    by_cases hA : A0.card = 0
    · have : S.image (val 0) = ∅ := card_eq_zero.1 hA
      rw [this]; simp
    have hpos : 0 < A0.card := Nat.pos_of_ne_zero hA
    calc ∑ a ∈ A0, (S.filter fun q => val 0 q = a).card ≤ ∑ a ∈ A0, B / A0.card := by
          apply sum_le_sum
          intro a ha
          obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
          apply ih (S.filter fun q => val 0 q = val 0 p) val' (B / A0.card)
          · intro x hx y hy hxy
            simp only [mem_filter] at hx hy
            apply hinj x hx.1 y hy.1
            intro i
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
            · rw [hx.2, hy.2]
            · exact hxy i'
          · intro x hx
            simp only [mem_filter] at hx
            rw [Nat.le_div_iff_mul_le hpos]
            have := hB x hx.1
            rw [Fin.prod_univ_succ, hbr0] at this
            rw [mul_comm]
            have heq : ∏ i : Fin t, br S val x i.succ =
                ∏ i : Fin t, br (S.filter fun q => val 0 q = val 0 p) val' x i := by
              apply prod_congr rfl
              intro i _
              rw [hbrs x hx.1 i, hx.2]
            rw [heq] at this
            exact this
      _ = A0.card * (B / A0.card) := by rw [sum_const, smul_eq_mul]
      _ ≤ B := Nat.mul_div_le B A0.card

theorem card_le_of_branch_real {β α : Type*} [DecidableEq α] (t : ℕ) (S : Finset β)
    (val : Fin t → β → α) (B : ℝ) (hB0 : 0 ≤ B)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, (∀ i, val i p = val i q) → p = q)
    (hB : ∀ p ∈ S, ((∏ i, br S val p i : ℕ) : ℝ) ≤ B) : (S.card : ℝ) ≤ B := by
  have := card_le_of_branch t S val ⌊B⌋₊ hinj fun p hp => Nat.le_floor (hB p hp)
  calc (S.card : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast this
    _ ≤ B := Nat.floor_le hB0

/-- Subsets of size at most `a` of an `n`-element type number at most `(n + 1) ^ a`. -/
theorem card_small_subsets (A : Type*) [Fintype A] [DecidableEq A] (a : ℕ) :
    ((univ : Finset (Finset A)).filter fun s => s.card ≤ a).card ≤ (Fintype.card A + 1) ^ a := by
  classical
  let Φ : (Fin a → Option A) → Finset A := fun g => (univ.image g).eraseNone
  have hsurj : ((univ : Finset (Finset A)).filter fun s => s.card ≤ a) ⊆ univ.image Φ := by
    intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    simp only [mem_image, mem_univ, true_and]
    let l := s.toList
    have hl : l.length ≤ a := by simp [l, hs]
    refine ⟨fun i => l[i.val]?, ?_⟩
    ext x
    simp only [Φ, mem_eraseNone, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      have := List.mem_of_getElem? hi
      simpa [l] using this
    · intro hx
      have hxl : x ∈ l := by simp [l, hx]
      obtain ⟨n, hn, hnx⟩ := List.getElem_of_mem hxl
      exact ⟨⟨n, by omega⟩, by simp [hn, hnx]⟩
  calc _ ≤ (univ.image Φ).card := card_le_card hsurj
    _ ≤ (univ : Finset (Fin a → Option A)).card := card_image_le
    _ = (Fintype.card A + 1) ^ a := by simp

end Puder.Q284C.PartC3
end

section
open Finset
namespace Puder.Q284C.PartC4
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC3
variable {k : ℕ}
/-!
# q284 Part C, helper 4: the branching at each step of a fibre
-/
/-- Walks of length `t`. -/
abbrev Walk (k t : ℕ) := (Fin t → Fin k × Bool) × (Fin (t + 1) → Fin (t + 1))

/-- What step `i` records: its letter and the vertex it reaches. -/
def val {t : ℕ} (i : Fin t) (p : Walk k t) : (Fin k × Bool) × Fin (t + 1) := (p.1 i, p.2 i.succ)

end Puder.Q284C.PartC4
end

section
open Finset
namespace Puder.Q284C.PartC4
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC3
variable {k : ℕ}
variable {t : ℕ}
open Classical in
/-- Ends at `u` seen before step `i`. -/
noncomputable def KEnds (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) (i : Fin t)
    (u : Fin (t + 1)) : Finset (Fin k × Bool) :=
  univ.filter fun e => ∃ j < i, hasEnd L f j u e

open Classical in
/-- Ends at the current vertex seen before step `i`, other than the arrival end. -/
noncomputable def Kx (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) (i : Fin t) :
    Finset (Fin k × Bool) :=
  (KEnds L f i (f i.castSucc)).filter fun e => ∀ j : Fin t, j.val + 1 = i.val → e ≠ inv (L j)

open Classical in
/-- First crossings departing a junction. -/
noncomputable def Rset (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) : Finset (Fin t) :=
  univ.filter fun i => isN L f i ∧ f i.castSucc ∈ Jn L f

/-- `q` agrees with `p` before step `i`. -/
def Agree (p q : Walk k t) (i : Fin t) : Prop := ∀ j < i, val j q = val j p

theorem agree_L {p q : Walk k t} {i : Fin t} (h : Agree p q i) {j : Fin t} (hj : j < i) :
    q.1 j = p.1 j :=
  congrArg Prod.fst (h j hj)

theorem agree_f {p q : Walk k t} {i : Fin t} (h : Agree p q i) (hp0 : p.2 0 = 0) (hq0 : q.2 0 = 0)
    {a : Fin (t + 1)} (ha : a.val ≤ i.val) : q.2 a = p.2 a := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨j, rfl⟩
  · rw [hp0, hq0]
  · have hj : j < i := by rw [Fin.lt_def]; simp at ha; omega
    exact congrArg Prod.snd (h j hj)

theorem agree_tail_head {p q : Walk k t} {i : Fin t} (h : Agree p q i) (hp0 : p.2 0 = 0)
    (hq0 : q.2 0 = 0) {j : Fin t} (hj : j < i) :
    tail q.1 q.2 j = tail p.1 p.2 j ∧ head q.1 q.2 j = head p.1 p.2 j := by
  have hj' : j.val < i.val := hj
  have h1 := agree_L h hj
  have h2 := agree_f h hp0 hq0 (a := j.castSucc) (by simp; omega)
  have h3 := agree_f h hp0 hq0 (a := j.succ) (by simp; omega)
  unfold tail head; rw [h1, h2, h3]; exact ⟨rfl, rfl⟩

theorem agree_hasEnd {p q : Walk k t} {i : Fin t} (h : Agree p q i) (hp0 : p.2 0 = 0)
    (hq0 : q.2 0 = 0) {j : Fin t} (hj : j < i) (u : Fin (t + 1)) (e : Fin k × Bool) :
    hasEnd q.1 q.2 j u e ↔ hasEnd p.1 p.2 j u e := by
  obtain ⟨ht, hh⟩ := agree_tail_head h hp0 hq0 hj
  unfold hasEnd; rw [agree_L h hj, ht, hh]

theorem agree_KEnds {p q : Walk k t} {i : Fin t} (h : Agree p q i) (hp0 : p.2 0 = 0)
    (hq0 : q.2 0 = 0) (u : Fin (t + 1)) : KEnds q.1 q.2 i u = KEnds p.1 p.2 i u := by
  classical
  unfold KEnds; ext e; simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, h'⟩; exact ⟨j, hj, (agree_hasEnd h hp0 hq0 hj u e).1 h'⟩
  · rintro ⟨j, hj, h'⟩; exact ⟨j, hj, (agree_hasEnd h hp0 hq0 hj u e).2 h'⟩

theorem KEnds_sub_Ends {p q : Walk k t} {i : Fin t} (h : Agree p q i) (hp0 : p.2 0 = 0)
    (hq0 : q.2 0 = 0) (u : Fin (t + 1)) : KEnds p.1 p.2 i u ⊆ Ends q.1 q.2 u := by
  classical
  intro e he
  simp only [KEnds, mem_filter, mem_univ, true_and] at he
  obtain ⟨j, hj, hje⟩ := he
  exact (mem_Ends _ _).2 ⟨j, (agree_hasEnd h hp0 hq0 hj u e).2 hje⟩

theorem agree_refl (p : Walk k t) (i : Fin t) : Agree p p i := fun _ _ => rfl

theorem val_eq_of_mem_K {m : ℕ} {p q q' : Walk k t} {i : Fin t}
    (hp : WalkOK m p.1 p.2) (hq : WalkOK m q.1 q.2) (hq' : WalkOK m q'.1 q'.2)
    (ha : Agree p q i) (ha' : Agree p q' i) (hL : q.1 i = q'.1 i)
    (hK : q.1 i ∈ KEnds p.1 p.2 i (p.2 i.castSucc)) : val i q = val i q' := by
  classical
  simp only [KEnds, mem_filter, mem_univ, true_and] at hK
  obtain ⟨j, hj, hje⟩ := hK
  have hi : i.castSucc.val ≤ i.val := by simp
  have hfq : q.2 i.castSucc = p.2 i.castSucc := agree_f ha hp.1 hq.1 hi
  have hfq' : q'.2 i.castSucc = p.2 i.castSucc := agree_f ha' hp.1 hq'.1 hi
  have e1 := succ_eq_of_hasEnd hq.2.2.2.1 hq.2.2.2.2.1
    ((agree_hasEnd ha hp.1 hq.1 hj _ _).2 hje) rfl hfq
  have e2 := succ_eq_of_hasEnd hq'.2.2.2.1 hq'.2.2.2.2.1
    ((agree_hasEnd ha' hp.1 hq'.1 hj _ _).2 hje) hL.symm hfq'
  obtain ⟨t1, h1⟩ := agree_tail_head ha hp.1 hq.1 hj
  obtain ⟨t2, h2⟩ := agree_tail_head ha' hp.1 hq'.1 hj
  unfold val
  refine Prod.ext hL ?_
  simp only
  rw [e1, e2, t1, h1, t2, h2]

theorem isN_iff {m : ℕ} {p q : Walk k t} {i : Fin t} (hp0 : p.2 0 = 0) (hq : WalkOK m q.1 q.2)
    (ha : Agree p q i) : isN q.1 q.2 i ↔ q.1 i ∉ KEnds p.1 p.2 i (p.2 i.castSucc) := by
  classical
  have hfq : q.2 i.castSucc = p.2 i.castSucc := agree_f ha hp0 hq.1 (by simp)
  rw [← agree_KEnds ha hp0 hq.1, ← hfq]
  simp only [KEnds, mem_filter, mem_univ, true_and, not_exists, not_and]
  constructor
  · intro hN j hj hje
    exact hN j hj (edgeId_eq_of_hasEnd hq.2.2.2.2.1 hje (hasEnd_dep q.1 q.2 i))
  · intro h j hj he
    exact h j hj (hasEnd_of_edgeId_eq hq.2.2.2.1 he (hasEnd_dep q.1 q.2 i))

theorem ne_arr {p q : Walk k t} {i : Fin t} (hR : Reduced q.1) (ha : Agree p q i) {j : Fin t}
    (hj : j.val + 1 = i.val) : q.1 i ≠ inv (p.1 j) := by
  have hji : j < i := by rw [Fin.lt_def]; omega
  rw [← agree_L ha hji]
  have := hR j (by omega)
  have hi : (⟨j.val + 1, by omega⟩ : Fin t) = i := Fin.ext hj
  rw [hi] at this; exact this

theorem arr_mem_K {p : Walk k t} {i j : Fin t} (hj : j.val + 1 = i.val) :
    inv (p.1 j) ∈ KEnds p.1 p.2 i (p.2 i.castSucc) := by
  classical
  simp only [KEnds, mem_filter, mem_univ, true_and]
  refine ⟨j, by rw [Fin.lt_def]; omega, ?_⟩
  have := hasEnd_arr p.1 p.2 j
  rwa [show j.succ = i.castSucc from Fin.ext (by simp; omega)] at this

theorem card_Kx_add_one {p : Walk k t} (hp0 : p.2 0 = 0) {i j : Fin t} (hj : j.val + 1 = i.val) :
    (Kx p.1 p.2 i).card + 1 ≤ deg p.1 p.2 (p.2 i.castSucc) := by
  classical
  have harr : inv (p.1 j) ∈ Ends p.1 p.2 (p.2 i.castSucc) :=
    KEnds_sub_Ends (agree_refl p i) hp0 hp0 _ (arr_mem_K hj)
  have hsub : Kx p.1 p.2 i ⊆ (Ends p.1 p.2 (p.2 i.castSucc)).erase (inv (p.1 j)) := by
    intro e he
    simp only [Kx, mem_filter] at he
    exact mem_erase.2 ⟨he.2 j hj, KEnds_sub_Ends (agree_refl p i) hp0 hp0 _ he.1⟩
  have h1 := card_le_card hsub
  rw [card_erase_of_mem harr] at h1
  unfold deg
  have : 1 ≤ (Ends p.1 p.2 (p.2 i.castSucc)).card := card_pos.2 ⟨_, harr⟩
  omega

open Classical in
/-- The branching budget at step `i`. -/
noncomputable def cfun (m : ℕ) (L : Fin t → Fin k × Bool) (f : Fin (t + 1) → Fin (t + 1)) (i : Fin t) :
    ℕ :=
  if i ∈ Rset L f then 2 * k * (t + 1) else if f i.castSucc ∈ Jn L f then 2 * m - 1
  else if (Kx L f i).Nonempty then 1 else if i ∈ Qset L f then (2 * k - 1) * (t + 1) else 2 * k - 1

theorem card_erase_letters (a : Fin k × Bool) : (univ.erase a).card = 2 * k - 1 := by
  rw [card_erase_of_mem (mem_univ _), card_univ]; simp; omega

theorem br_le {m : ℕ} (S : Finset (Walk k t)) (p : Walk k t) (hpS : p ∈ S)
    (hS : ∀ q ∈ S, Reduced q.1 ∧ WalkOK m q.1 q.2 ∧ Jn q.1 q.2 = Jn p.1 p.2 ∧
      Rset q.1 q.2 = Rset p.1 p.2 ∧ Qset q.1 q.2 = Qset p.1 p.2)
    (hdeg : ∀ u, deg p.1 p.2 u ≤ 2 * m) (i : Fin t) : br S val p i ≤ cfun m p.1 p.2 i := by
  classical
  obtain ⟨hpR, hpW, -, -, -⟩ := hS p hpS
  have hp0 := hpW.1
  unfold br cfun
  set T := S.filter fun q => ∀ j < i, val j q = val j p with hT
  have hTa : ∀ q ∈ T, q ∈ S ∧ Agree p q i := fun q hq => by
    rw [hT, mem_filter] at hq; exact hq
  have hpT : p ∈ T := by rw [hT, mem_filter]; exact ⟨hpS, fun _ _ => rfl⟩
  set u := p.2 i.castSucc with hu
  set K := KEnds p.1 p.2 i u with hK
  have hKx : (∀ q ∈ T, q.1 i ∈ K) → (T.image (val i)).card ≤ (Kx p.1 p.2 i).card := by
    intro hall
    apply card_le_card_of_injOn Prod.fst
    · intro v hv
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hv
      obtain ⟨hqS, hqa⟩ := hTa q hq
      show q.1 i ∈ Kx p.1 p.2 i
      simp only [Kx, mem_filter]
      exact ⟨hall q hq, fun j hj => ne_arr (hS q hqS).1 hqa hj⟩
    · intro v hv v' hv' hvv
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hv
      obtain ⟨q', hq', rfl⟩ := mem_image.1 hv'
      obtain ⟨hqS, hqa⟩ := hTa q hq
      obtain ⟨hqS', hqa'⟩ := hTa q' hq'
      exact val_eq_of_mem_K hpW (hS q hqS).2.1 (hS q' hqS').2.1 hqa hqa' hvv (hall q hq)
  have hJ0 : (0 : Fin (t + 1)) ∈ Jn p.1 p.2 := by simp [Jn, hp0]
  by_cases hR : i ∈ Rset p.1 p.2
  · rw [if_pos hR]
    calc (T.image (val i)).card ≤ (univ : Finset ((Fin k × Bool) × Fin (t + 1))).card := card_le_univ _
      _ = 2 * k * (t + 1) := by simp [Fintype.card_prod, Fintype.card_bool]; ring
  rw [if_neg hR]
  by_cases hJ : u ∈ Jn p.1 p.2
  · rw [if_pos hJ]
    have hi1 : ∃ j : Fin t, j.val + 1 = i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exfalso; apply hR
        simp only [Rset, mem_filter, mem_univ, true_and]
        refine ⟨fun j hj => absurd hj (by rw [Fin.lt_def]; omega), hJ⟩
      · exact ⟨⟨i.val - 1, by omega⟩, by simp; omega⟩
    obtain ⟨j, hj⟩ := hi1
    have hall : ∀ q ∈ T, q.1 i ∈ K := by
      intro q hq
      obtain ⟨hqS, hqa⟩ := hTa q hq
      obtain ⟨-, hqW, hqJ, hqRs, -⟩ := hS q hqS
      have hnN : ¬ isN q.1 q.2 i := by
        intro hN
        apply hR
        rw [← hqRs]
        simp only [Rset, mem_filter, mem_univ, true_and]
        refine ⟨hN, ?_⟩
        rw [hqJ, agree_f hqa hp0 hqW.1 (by simp)]
        exact hJ
      by_contra hK'
      exact hnN ((isN_iff hp0 hqW hqa).2 hK')
    have h1 := hKx hall
    have h6 : (Kx p.1 p.2 i).card + 1 ≤ deg p.1 p.2 u := card_Kx_add_one hp0 hj
    have := hdeg u
    omega
  · rw [if_neg hJ]
    have hi1 : ∃ j : Fin t, j.val + 1 = i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exfalso; apply hJ
        have : i.castSucc = 0 := Fin.ext (by simp [h])
        rw [hu, this, hp0]; exact hJ0
      · exact ⟨⟨i.val - 1, by omega⟩, by simp; omega⟩
    obtain ⟨j, hj⟩ := hi1
    have huv : p.2 u = u := (hpW.2.2.1 _).2
    have hule : u.val ≤ i.val := by
      have := (hpW.2.2.1 i.castSucc).1; rw [Fin.le_def] at this; simpa using this
    have hdq : ∀ q ∈ T, deg q.1 q.2 u ≤ 2 := by
      intro q hq
      obtain ⟨hqS, hqa⟩ := hTa q hq
      obtain ⟨-, hqW, hqJ, -, -⟩ := hS q hqS
      by_contra h3
      apply hJ
      rw [← hqJ]
      simp only [Jn, mem_filter, mem_univ, true_and]
      exact ⟨by rw [agree_f hqa hp0 hqW.1 hule, huv], Or.inr (by omega)⟩
    by_cases hne : (Kx p.1 p.2 i).Nonempty
    · rw [if_pos hne]
      obtain ⟨e0, he0⟩ := hne
      have he0' := he0
      simp only [Kx, mem_filter] at he0'
      have hall : ∀ q ∈ T, q.1 i ∈ K := by
        intro q hq
        by_contra hK'
        obtain ⟨hqS, hqa⟩ := hTa q hq
        obtain ⟨hqR, hqW, -, -, -⟩ := hS q hqS
        have hfq : q.2 i.castSucc = u := agree_f hqa hp0 hqW.1 (by simp)
        have h3 : 2 < deg q.1 q.2 u := by
          unfold deg
          rw [two_lt_card]
          refine ⟨inv (p.1 j), KEnds_sub_Ends hqa hp0 hqW.1 _ (arr_mem_K hj), e0,
            KEnds_sub_Ends hqa hp0 hqW.1 _ he0'.1, q.1 i, ?_, ?_, ?_, ?_⟩
          · rw [← hfq]; exact (mem_Ends _ _).2 ⟨i, hasEnd_dep _ _ i⟩
          · exact (he0'.2 j hj).symm
          · exact (ne_arr hqR hqa hj).symm
          · rintro rfl; exact hK' he0'.1
        have := hdq q hq; omega
      have h1 := hKx hall
      have h6 : (Kx p.1 p.2 i).card + 1 ≤ deg p.1 p.2 u := card_Kx_add_one hp0 hj
      have := hdq p hpT
      omega
    · rw [if_neg hne]
      have hallN : ∀ q ∈ T, isN q.1 q.2 i ∧ q.1 i ≠ inv (p.1 j) := by
        intro q hq
        obtain ⟨hqS, hqa⟩ := hTa q hq
        obtain ⟨hqR, hqW, -, -, -⟩ := hS q hqS
        refine ⟨(isN_iff hp0 hqW hqa).2 fun hK' => hne ⟨q.1 i, ?_⟩, ne_arr hqR hqa hj⟩
        simp only [Kx, mem_filter]
        exact ⟨hK', fun j' hj' => by
          have : j' = j := Fin.ext (by omega)
          subst this; exact ne_arr hqR hqa hj⟩
      by_cases hQ : i ∈ Qset p.1 p.2
      · rw [if_pos hQ]
        calc (T.image (val i)).card ≤ ((univ.erase (inv (p.1 j))) ×ˢ (univ : Finset (Fin (t + 1)))).card := by
              apply card_le_card
              intro v hv
              obtain ⟨q, hq, rfl⟩ := mem_image.1 hv
              simp only [mem_product, mem_erase, mem_univ, and_true, val]
              exact (hallN q hq).2
          _ = (2 * k - 1) * (t + 1) := by rw [card_product, card_erase_letters]; simp
      · rw [if_neg hQ]
        calc (T.image (val i)).card ≤ ((univ.erase (inv (p.1 j))) ×ˢ ({i.succ} : Finset (Fin (t + 1)))).card := by
              apply card_le_card
              intro v hv
              obtain ⟨q, hq, rfl⟩ := mem_image.1 hv
              obtain ⟨hqS, hqa⟩ := hTa q hq
              obtain ⟨-, -, -, -, hqQ⟩ := hS q hqS
              simp only [mem_product, mem_erase, mem_univ, and_true, val, mem_singleton]
              refine ⟨(hallN q hq).2, ?_⟩
              by_contra hne'
              apply hQ
              rw [← hqQ]
              simp only [Qset, mem_filter, mem_univ, true_and]
              exact ⟨(hallN q hq).1, hne'⟩
          _ = 2 * k - 1 := by rw [card_product, card_erase_letters]; simp

end Puder.Q284C.PartC4
end

section
open Finset
namespace Puder.Q284C.PartC5
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC3 Puder.Q284C.PartC4
variable {k : ℕ}
/-!
# q284 Part C, helper 5: the count of walks whose base is not a leaf
-/
theorem le_rate_both (k m : ℕ) :
    (2 * m - 1 : ℝ) ≤ rate k m ∧ Real.sqrt (2 * k - 1) ≤ rate k m := by
  unfold rate; split_ifs with h
  · exact ⟨h, le_rfl⟩
  · exact ⟨le_rfl, (not_le.1 h).le⟩

theorem pow_le_rate {m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) (E t : ℕ) (h : 2 * E ≤ t) :
    (((2 * m - 1 : ℕ) : ℝ)) ^ (t - 2 * E) * (((2 * k - 1 : ℕ) : ℝ)) ^ E ≤ rate k m ^ t := by
  obtain ⟨h1, h2⟩ := le_rate_both k m
  have ca : (((2 * m - 1 : ℕ) : ℝ)) = 2 * m - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have cb : (((2 * k - 1 : ℕ) : ℝ)) = 2 * k - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : (0 : ℝ) ≤ 2 * m - 1 := by linarith
  have hs0 : (0 : ℝ) ≤ 2 * k - 1 := by linarith
  rw [ca, cb]
  have hsq : (2 * k - 1 : ℝ) ^ E = Real.sqrt (2 * k - 1) ^ (2 * E) := by
    rw [pow_mul, Real.sq_sqrt hs0]
  rw [hsq, show t = (t - 2 * E) + 2 * E by omega, pow_add, Nat.add_sub_cancel]
  apply mul_le_mul (pow_le_pow_left₀ ha0 h1 _) (pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 _)
    (pow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg (ha0.trans h1) _)

end Puder.Q284C.PartC5
end

section
open Finset
namespace Puder.Q284C.PartC5
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC3 Puder.Q284C.PartC4
variable {k : ℕ}
variable {t : ℕ}
theorem prod_cfun_le {m : ℕ} (hm : 1 ≤ m) (hk : 2 ≤ k) (L : Fin t → Fin k × Bool)
    (f : Fin (t + 1) → Fin (t + 1)) (hR : Reduced L) (hW : WalkOK m L f) :
    ∏ i, cfun m L f i ≤ (2 * k * (t + 1)) ^ (6 * m) * (2 * m - 1) ^ (6 * m + (t - 2 * nE L f)) *
      (2 * k - 1) ^ nE L f * (t + 1) ^ m := by
  classical
  obtain ⟨h0, hlast, hf, hD, hC, h2, hE⟩ := hW
  set R := Rset L f with hRdef
  set J2 := univ.filter fun i : Fin t => i ∉ R ∧ f i.castSucc ∈ Jn L f
  set N3 := univ.filter fun i : Fin t => i ∉ R ∧ f i.castSucc ∉ Jn L f ∧ ¬ (Kx L f i).Nonempty
  set Q := Qset L f
  have a1 : 1 ≤ 2 * k * (t + 1) := by
    have : 1 ≤ 2 * k := by omega
    exact le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  have a2 : 1 ≤ 2 * m - 1 := by omega
  have a3 : 1 ≤ 2 * k - 1 := by omega
  have hpt : ∀ i ∈ univ, cfun m L f i ≤
      (if i ∈ R then 2 * k * (t + 1) else 1) * (if i ∈ J2 then 2 * m - 1 else 1) *
      (if i ∈ N3 then 2 * k - 1 else 1) * (if i ∈ Q then t + 1 else 1) := by
    intro i _
    unfold cfun
    simp only [J2, N3, mem_filter, mem_univ, true_and, ← hRdef]
    split_ifs <;> simp_all
    all_goals first
      | omega
      | exact Nat.le_mul_of_pos_right _ (by omega)
      | (have := Nat.le_mul_of_pos_right (2 * m - 1) (show 0 < t + 1 by omega); omega)
  have hprod := prod_le_prod (fun i _ => Nat.zero_le _) hpt
  rw [prod_mul_distrib, prod_mul_distrib, prod_mul_distrib] at hprod
  simp only [prod_ite_mem, univ_inter, prod_const] at hprod
  refine hprod.trans ?_
  -- cardinality bounds
  have hJb := (Jn_bounds hR ⟨h0, hlast, hf, hD, hC, h2, hE⟩).2
  have hRc : R.card ≤ 6 * m := by
    refine le_trans (card_le_sum_deg hC R (Jn L f) (fun i hi => ?_) (fun i hi j hj h => ?_)) hJb
    · simp only [R, Rset, mem_filter] at hi; exact hi.2.2
    · simp only [R, Rset, mem_filter] at hi hj; exact isN_inj hi.2.1 hj.2.1 h
  have hJ2 : J2.card ≤ 6 * m + (t - 2 * nE L f) := by
    have hsub : J2 ⊆ (Sset L f).filter (fun i => f i.castSucc ∈ Jn L f) ∪ Lset L f := by
      intro i hi
      simp only [J2, mem_filter, mem_univ, true_and] at hi
      have hnN : ¬ isN L f i := fun hN => hi.1 (by simp [R, Rset, hN, hi.2])
      by_cases hS : isS L f i
      · exact mem_union_left _ (by simp [Sset, hS, hi.2])
      · exact mem_union_right _ (by simp [Lset, hS, hnN])
    have h1 : ((Sset L f).filter (fun i => f i.castSucc ∈ Jn L f)).card ≤ 6 * m := by
      refine le_trans (card_le_sum_deg hC _ (Jn L f) (fun i hi => ?_) (fun i hi j hj h => ?_)) hJb
      · exact (mem_filter.1 hi).2
      · simp only [Sset, mem_filter, mem_univ, true_and] at hi hj; exact isS_inj hi.1 hj.1 h
    have h3 := card_Lset (L := L) (f := f) h2
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega
  have hN3 : N3.card ≤ nE L f := by
    rw [← card_Nset (L := L) (f := f)]
    apply card_le_card
    intro i hi
    simp only [N3, mem_filter, mem_univ, true_and] at hi
    simp only [Nset, mem_filter, mem_univ, true_and]
    obtain ⟨-, hJ, hne⟩ := hi
    have hi1 : ∃ j : Fin t, j.val + 1 = i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exfalso; apply hJ
        have : i.castSucc = 0 := Fin.ext (by simp [h])
        rw [this, h0]; simp [Jn, h0]
      · exact ⟨⟨i.val - 1, by omega⟩, by simp; omega⟩
    obtain ⟨j, hj⟩ := hi1
    refine (isN_iff (p := (L, f)) (q := (L, f)) h0 ⟨h0, hlast, hf, hD, hC, h2, hE⟩
      (agree_refl _ i)).2 fun hK => hne ⟨L i, ?_⟩
    simp only [Kx, mem_filter]
    refine ⟨hK, fun j' hj' => ?_⟩
    have : j' = j := Fin.ext (by omega)
    subst this
    exact ne_arr (p := (L, f)) (q := (L, f)) hR (agree_refl _ i) hj
  have hQ : Q.card ≤ m := card_Qset ⟨h0, hlast, hf, hD, hC, h2, hE⟩
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right a1 hRc)
    (Nat.pow_le_pow_right a2 hJ2)) (Nat.pow_le_pow_right a3 hN3)) (Nat.pow_le_pow_right (by omega) hQ)

end Puder.Q284C.PartC5
end

section
open Finset
namespace Puder.Q284C.PartC5
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC3 Puder.Q284C.PartC4
variable {k : ℕ}
open Classical in
/-- Walks whose base vertex has degree at least two. -/
noncomputable def NL (k m t : ℕ) : Finset (Walk k t) :=
  univ.filter fun p => Reduced p.1 ∧ WalkOK m p.1 p.2 ∧ 2 ≤ deg p.1 p.2 0

theorem card_NL_le {m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) (t : ℕ) :
    ((NL k m t).card : ℝ) ≤ ((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) : ℕ) *
      ((t : ℝ) + 2) ^ (16 * m + 1) * rate k m ^ t := by
  classical
  set W := NL k m t
  let Dm : Walk k t → Finset (Fin (t + 1)) × Finset (Fin t) × Finset (Fin t) :=
    fun p => (Jn p.1 p.2, Rset p.1 p.2, Qset p.1 p.2)
  let small : (A : Type) → [Fintype A] → ℕ → Finset (Finset A) :=
    fun A _ a => (univ : Finset (Finset A)).filter fun s => s.card ≤ a
  set DD := small (Fin (t + 1)) (2 * m + 1) ×ˢ small (Fin t) (6 * m) ×ˢ small (Fin t) m
  have hmaps : Set.MapsTo Dm W DD := by
    intro p hp
    simp only [W, NL, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
    obtain ⟨hR, hW, -⟩ := hp
    obtain ⟨h0, hlast, hf, hD, hC, h2, hE⟩ := hW
    have hJb := Jn_bounds hR ⟨h0, hlast, hf, hD, hC, h2, hE⟩
    simp only [DD, small, Dm, coe_product, Set.mem_prod, coe_filter, mem_univ, true_and,
      Set.mem_ofPred_eq]
    refine ⟨hJb.1, ?_, card_Qset ⟨h0, hlast, hf, hD, hC, h2, hE⟩⟩
    refine le_trans (card_le_sum_deg hC _ (Jn p.1 p.2) (fun i hi => ?_) (fun i hi j hj h => ?_)) hJb.2
    · simp only [Rset, mem_filter] at hi; exact hi.2.2
    · simp only [Rset, mem_filter] at hi hj; exact isN_inj hi.2.1 hj.2.1 h
  set Bf : ℝ := ((2 * k * (t + 1)) ^ (6 * m) * (2 * m - 1) ^ (6 * m) * (t + 1) ^ m : ℕ) * rate k m ^ t
  have hrate0 : 0 ≤ rate k m := (rate_pos k m hk).le
  have hBf0 : 0 ≤ Bf := by positivity
  have hfib : ∀ D ∈ DD, ((W.filter fun p => Dm p = D).card : ℝ) ≤ Bf := by
    intro D _
    apply card_le_of_branch_real t _ val Bf hBf0
    · intro p hp q hq hpq
      simp only [W, NL, mem_filter, mem_univ, true_and] at hp hq
      have h1 : p.1 = q.1 := funext fun i => congrArg Prod.fst (hpq i)
      have h2 : p.2 = q.2 := by
        funext a
        rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨j, rfl⟩
        · rw [hp.1.2.1.1, hq.1.2.1.1]
        · exact congrArg Prod.snd (hpq j)
      exact Prod.ext h1 h2
    · intro p hp
      have hp' := hp
      simp only [W, NL, mem_filter, mem_univ, true_and] at hp'
      obtain ⟨⟨hR, hW, h2⟩, hDp⟩ := hp'
      have hdeg := deg_le_of_nonleaf hR hW h2
      have hbr : ∏ i, br (W.filter fun p => Dm p = D) val p i ≤ ∏ i, cfun m p.1 p.2 i := by
        apply prod_le_prod'
        intro i _
        apply br_le _ p hp _ hdeg i
        intro q hq
        simp only [W, NL, mem_filter, mem_univ, true_and] at hq
        obtain ⟨⟨hqR, hqW, -⟩, hDq⟩ := hq
        rw [← hDp] at hDq
        simp only [Dm, Prod.mk.injEq] at hDq
        exact ⟨hqR, hqW, hDq.1, hDq.2.1, hDq.2.2⟩
      have hc := prod_cfun_le hm hk p.1 p.2 hR hW
      have h2E : 2 * nE p.1 p.2 ≤ t := by
        have := card_Lset (L := p.1) (f := p.2) hW.2.2.2.2.2.1; omega
      have hr := pow_le_rate (m := m) hk hm (nE p.1 p.2) t h2E
      calc ((∏ i, br (W.filter fun p => Dm p = D) val p i : ℕ) : ℝ)
          ≤ (((2 * k * (t + 1)) ^ (6 * m) * (2 * m - 1) ^ (6 * m + (t - 2 * nE p.1 p.2)) *
              (2 * k - 1) ^ nE p.1 p.2 * (t + 1) ^ m : ℕ) : ℝ) := by
            exact_mod_cast hbr.trans hc
        _ = ((2 * k * (t + 1)) ^ (6 * m) * (2 * m - 1) ^ (6 * m) * (t + 1) ^ m : ℕ) *
              ((((2 * m - 1 : ℕ) : ℝ)) ^ (t - 2 * nE p.1 p.2) *
                (((2 * k - 1 : ℕ) : ℝ)) ^ nE p.1 p.2) := by
            push_cast [pow_add]; ring
        _ ≤ Bf := by
            apply mul_le_mul_of_nonneg_left hr (by positivity)
  rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  calc ∑ D ∈ DD, ((W.filter fun p => Dm p = D).card : ℝ) ≤ ∑ D ∈ DD, Bf := sum_le_sum hfib
    _ = DD.card * Bf := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (((t + 2) ^ (2 * m + 1) * (t + 1) ^ (6 * m) * (t + 1) ^ m : ℕ) : ℝ) * Bf := by
        apply mul_le_mul_of_nonneg_right _ hBf0
        have h1 := card_small_subsets (Fin (t + 1)) (2 * m + 1)
        have h2 := card_small_subsets (Fin t) (6 * m)
        have h3 := card_small_subsets (Fin t) m
        simp only [Fintype.card_fin] at h1 h2 h3
        have : DD.card ≤ (t + 2) ^ (2 * m + 1) * (t + 1) ^ (6 * m) * (t + 1) ^ m := by
          simp only [DD, card_product]
          rw [mul_assoc]
          exact Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
        exact_mod_cast this
    _ ≤ ((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) : ℕ) * ((t : ℝ) + 2) ^ (16 * m + 1) *
          rate k m ^ t := by
        simp only [Bf]
        have ht : ((t : ℝ) + 1) ≤ (t : ℝ) + 2 := by linarith
        have ht0 : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
        set X : ℝ := (2 * (k : ℝ)) ^ (6 * m) * (((2 * m - 1 : ℕ) : ℝ)) ^ (6 * m) * rate k m ^ t *
          ((t : ℝ) + 2) ^ (2 * m + 1)
        have hX : 0 ≤ X := by positivity
        have e1 : ((((t + 2) ^ (2 * m + 1) * (t + 1) ^ (6 * m) * (t + 1) ^ m : ℕ) : ℝ) *
            ((((2 * k * (t + 1)) ^ (6 * m) * (2 * m - 1) ^ (6 * m) * (t + 1) ^ m : ℕ) : ℝ) *
              rate k m ^ t)) = X * (((t : ℝ) + 1) ^ (6 * m) * ((t : ℝ) + 1) ^ m *
              ((t : ℝ) + 1) ^ (6 * m) * ((t : ℝ) + 1) ^ m) := by
          simp only [X]; push_cast; simp only [mul_pow]; ring
        have e2 : (((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) : ℕ) : ℝ) * ((t : ℝ) + 2) ^ (16 * m + 1) *
            rate k m ^ t = X * (((t : ℝ) + 2) ^ (6 * m) * ((t : ℝ) + 2) ^ m *
              ((t : ℝ) + 2) ^ (6 * m) * ((t : ℝ) + 2) ^ m) := by
          simp only [X]
          rw [show 16 * m + 1 = (2 * m + 1) + 6 * m + m + 6 * m + m by ring]
          simp only [pow_add]; push_cast; ring
        rw [e1, e2]
        apply mul_le_mul_of_nonneg_left _ hX
        gcongr

end Puder.Q284C.PartC5
end

section
open Finset
namespace Puder.Q284C.PartC6
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC4
variable {k : ℕ}
variable {t : ℕ}
/-!
# q284 Part C, helper 6: peeling a leaf base edge
-/
/-- Letters of the walk with its first and last steps removed. -/
def peelL (L : Fin (t + 2) → Fin k × Bool) : Fin t → Fin k × Bool := fun i => L ⟨i.val + 1, by omega⟩

/-- Vertex map of the walk with its first and last steps removed. -/
def peelF (f : Fin (t + 2 + 1) → Fin (t + 2 + 1)) : Fin (t + 1) → Fin (t + 1) :=
  fun a => ⟨min ((f ⟨a.val + 1, by omega⟩).val - 1) t, by omega⟩

/-- The peeled walk. -/
def peel (p : Walk k (t + 2)) : Walk k t := (peelL p.1, peelF p.2)

end Puder.Q284C.PartC6
end

section
open Finset
namespace Puder.Q284C.PartC6
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC4
variable {k : ℕ}
variable {t : ℕ}
variable {L : Fin (t + 2) → Fin k × Bool} {f : Fin (t + 2 + 1) → Fin (t + 2 + 1)}
theorem peelF_val' (hf : ∀ i, f i ≤ i) (a : Fin (t + 1)) (b : Fin (t + 2 + 1)) (hb : b.val = a.val + 1) :
    (peelF f a).val = (f b).val - 1 := by
  have hb' : b = ⟨a.val + 1, by omega⟩ := Fin.ext hb
  rw [hb']
  have h1 := hf ⟨a.val + 1, by omega⟩
  rw [Fin.le_def] at h1
  have h2 : (f ⟨a.val + 1, by omega⟩).val ≤ a.val + 1 := h1
  have := a.isLt
  show min ((f ⟨a.val + 1, by omega⟩).val - 1) t = (f ⟨a.val + 1, by omega⟩).val - 1
  omega

theorem peelF_val (hf : ∀ i, f i ≤ i) (a : Fin (t + 1)) :
    (peelF f a).val = (f ⟨a.val + 1, by omega⟩).val - 1 :=
  peelF_val' hf a _ rfl

theorem interior_ne_zero {m : ℕ} (hR : Reduced L) (_hW : WalkOK m L f) (hleaf : deg L f 0 ≤ 1)
    (a : Fin (t + 2 + 1)) (ha1 : 0 < a.val) (ha2 : a.val < t + 2) : 1 ≤ (f a).val := by
  classical
  by_contra h0
  have hfa : f a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
  set jj : Fin (t + 2) := ⟨a.val - 1, by omega⟩
  set aa : Fin (t + 2) := ⟨a.val, ha2⟩
  have h1 : inv (L jj) ∈ Ends L f 0 := (mem_Ends L f).2 ⟨jj, by
    have := hasEnd_arr L f jj
    rwa [show jj.succ = a from Fin.ext (by simp [jj]; omega), hfa] at this⟩
  have h2 : L aa ∈ Ends L f 0 := (mem_Ends L f).2 ⟨aa, by
    have := hasEnd_dep L f aa
    rwa [show aa.castSucc = a from Fin.ext (by simp [aa]), hfa] at this⟩
  have hne : L aa ≠ inv (L jj) := by
    have := hR jj (by simp [jj]; omega)
    rwa [show (⟨jj.val + 1, by simp [jj]; omega⟩ : Fin (t + 2)) = aa from
      Fin.ext (by simp [jj, aa]; omega)] at this
  have : 2 ≤ deg L f 0 := Finset.one_lt_card.2 ⟨_, h1, _, h2, hne.symm⟩
  omega

theorem last_letter {m : ℕ} (hW : WalkOK m L f) (hleaf : deg L f 0 ≤ 1) :
    L ⟨t + 1, by omega⟩ = inv (L 0) := by
  have h1 : L 0 ∈ Ends L f 0 := (mem_Ends L f).2 ⟨0, by
    have := hasEnd_dep L f 0
    rwa [show (0 : Fin (t + 2)).castSucc = 0 from rfl, hW.1] at this⟩
  have h2 : inv (L ⟨t + 1, by omega⟩) ∈ Ends L f 0 := (mem_Ends L f).2 ⟨⟨t + 1, by omega⟩, by
    have := hasEnd_arr L f ⟨t + 1, by omega⟩
    rwa [show (⟨t + 1, by omega⟩ : Fin (t + 2)).succ = Fin.last (t + 2) from rfl, hW.2.1] at this⟩
  have := card_le_one.1 hleaf _ h1 _ h2
  rw [this, inv_inv]

theorem f_one {m : ℕ} (hR : Reduced L) (hW : WalkOK m L f) (hleaf : deg L f 0 ≤ 1) :
    f 1 = 1 := by
  have h := interior_ne_zero hR hW hleaf 1 (by simp) (by simp)
  have h2 := (hW.2.2.1 1).1
  rw [Fin.le_def] at h2
  ext; simp at h2 ⊢; omega

theorem f_penult {m : ℕ} (hR : Reduced L) (hW : WalkOK m L f) (hleaf : deg L f 0 ≤ 1) :
    f ⟨t + 1, by omega⟩ = 1 := by
  have hl := last_letter hW hleaf
  set z : Fin (t + 2) := ⟨t + 1, by omega⟩
  have hz : hasEnd L f z 0 (L 0) := by
    have := hasEnd_arr L f z
    rwa [show z.succ = Fin.last (t + 2) from rfl, hW.2.1, hl, inv_inv] at this
  have := succ_eq_of_hasEnd hW.2.2.2.1 hW.2.2.2.2.1 hz (i := 0) rfl hW.1
  rw [show (0 : Fin (t + 2)).succ = 1 from rfl, f_one hR hW hleaf] at this
  rw [this]
  unfold head tail
  rw [hl]
  cases h : (L 0).2 <;> simp [inv, h] <;> rfl

theorem tail_peel_val (hf : ∀ i, f i ≤ i) (i : Fin t) :
    (tail (peelL L) (peelF f) i).val = (tail L f ⟨i.val + 1, by omega⟩).val - 1 := by
  unfold tail peelL
  split_ifs <;> rw [peelF_val hf] <;> rfl

theorem head_peel_val (hf : ∀ i, f i ≤ i) (i : Fin t) :
    (head (peelL L) (peelF f) i).val = (head L f ⟨i.val + 1, by omega⟩).val - 1 := by
  unfold head peelL
  split_ifs <;> rw [peelF_val hf] <;> rfl

theorem tail_ge {m : ℕ} (hR : Reduced L) (hW : WalkOK m L f) (hleaf : deg L f 0 ≤ 1) (i : Fin t) :
    1 ≤ (tail L f ⟨i.val + 1, by omega⟩).val ∧ 1 ≤ (head L f ⟨i.val + 1, by omega⟩).val := by
  have h1 := interior_ne_zero hR hW hleaf ⟨i.val + 1, by omega⟩ (by simp) (by simp)
  have h2 := interior_ne_zero hR hW hleaf ⟨i.val + 2, by omega⟩ (by simp) (by simp)
  unfold tail head
  split_ifs
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

theorem walkOK_peel {m : ℕ} (hR : Reduced L) (hW : WalkOK m L f) (hleaf : deg L f 0 ≤ 1) :
    Reduced (peelL L) ∧ WalkOK m (peelL L) (peelF f) := by
  classical
  have hW' := hW
  obtain ⟨h0, hlast, hf, hD, hC, h2, hE⟩ := hW'
  have hfle : ∀ i, f i ≤ i := fun i => (hf i).1
  have hint := interior_ne_zero hR hW hleaf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hR ⟨i.val + 1, by omega⟩ (by show i.val + 1 + 1 < t + 2; omega)
    exact this
  · ext; rw [peelF_val hfle]; simp [f_one hR hW hleaf]
  · ext; rw [peelF_val hfle]
    have := f_penult hR hW hleaf
    simp only [Fin.val_last]
    rw [this]; simp
  · intro a
    have ha := hint ⟨a.val + 1, by omega⟩ (by simp) (by have := a.isLt; simp; omega)
    refine ⟨?_, ?_⟩
    · rw [Fin.le_def, peelF_val hfle]
      have := hfle ⟨a.val + 1, by omega⟩; rw [Fin.le_def] at this; simp at this; have := a.isLt; omega
    · ext
      rw [peelF_val' hfle (peelF f a) (f ⟨a.val + 1, by omega⟩) (by rw [peelF_val hfle]; omega),
        (hf _).2, peelF_val hfle]
  · intro i j hl ht
    have ti := tail_ge hR hW hleaf i
    have tj := tail_ge hR hW hleaf j
    have ht' : tail L f ⟨i.val + 1, by omega⟩ = tail L f ⟨j.val + 1, by omega⟩ := by
      have := congrArg Fin.val ht
      rw [tail_peel_val hfle, tail_peel_val hfle] at this
      ext; omega
    have := hD _ _ hl ht'
    ext; rw [head_peel_val hfle, head_peel_val hfle, this]
  · intro i j hl hh
    have ti := tail_ge hR hW hleaf i
    have tj := tail_ge hR hW hleaf j
    have hh' : head L f ⟨i.val + 1, by omega⟩ = head L f ⟨j.val + 1, by omega⟩ := by
      have := congrArg Fin.val hh
      rw [head_peel_val hfle, head_peel_val hfle] at this
      ext; omega
    have := hC _ _ hl hh'
    ext; rw [tail_peel_val hfle, tail_peel_val hfle, this]
  · -- each edge crossed at least twice
    intro i
    have key : ∀ j : Fin t, edgeId (peelL L) (peelF f) j = edgeId (peelL L) (peelF f) i ↔
        edgeId L f ⟨j.val + 1, by omega⟩ = edgeId L f ⟨i.val + 1, by omega⟩ := by
      intro j
      have ti := tail_ge hR hW hleaf i
      have tj := tail_ge hR hW hleaf j
      unfold edgeId
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have := congrArg Fin.val h1
        rw [tail_peel_val hfle, tail_peel_val hfle] at this
        ext; omega
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        ext; rw [tail_peel_val hfle, tail_peel_val hfle, h1]
    have hsub : (univ.filter fun j' : Fin (t + 2) => edgeId L f j' = edgeId L f ⟨i.val + 1, by omega⟩) ⊆
        (univ.filter fun j : Fin t => edgeId (peelL L) (peelF f) j = edgeId (peelL L) (peelF f) i).image
          (fun j => (⟨j.val + 1, by omega⟩ : Fin (t + 2))) := by
      intro j' hj'
      simp only [mem_filter, mem_univ, true_and] at hj'
      simp only [mem_image, mem_filter, mem_univ, true_and]
      have hti := tail_ge hR hW hleaf i
      -- j' is neither the first nor the last step
      have hnot : ∀ (z : Fin (t + 2)) (e : Fin k × Bool), hasEnd L f z 0 e → j' ≠ z := by
        rintro z e hz rfl
        have := hasEnd_of_edgeId_eq hD hj'.symm hz
        rcases hasEnd_pos L f _ _ _ this with h | h
        · have := hint (⟨i.val + 1, by omega⟩ : Fin (t + 2)).castSucc (by simp) (by simp)
          rw [← h] at this
          simp at this
        · have := hint (⟨i.val + 1, by omega⟩ : Fin (t + 2)).succ (by simp) (by simp)
          rw [← h] at this
          simp at this
      have hz0 : j' ≠ 0 := hnot 0 (L 0) (by
        have := hasEnd_dep L f 0; rwa [show (0 : Fin (t + 2)).castSucc = 0 from rfl, h0] at this)
      have hzl : j' ≠ ⟨t + 1, by omega⟩ := hnot ⟨t + 1, by omega⟩ _ (by
        have := hasEnd_arr L f ⟨t + 1, by omega⟩
        rwa [show (⟨t + 1, by omega⟩ : Fin (t + 2)).succ = Fin.last (t + 2) from rfl, hlast] at this)
      have hj0 : j'.val ≠ 0 := fun h => hz0 (Fin.ext h)
      have hjl : j'.val ≠ t + 1 := fun h => hzl (Fin.ext h)
      refine ⟨⟨j'.val - 1, by omega⟩, ?_, ?_⟩
      · rw [key]
        rw [show (⟨j'.val - 1 + 1, by omega⟩ : Fin (t + 2)) = j' from Fin.ext (by simp; omega)]
        exact hj'
      · ext; simp; omega
    have := (h2 ⟨i.val + 1, by omega⟩).trans ((card_le_card hsub).trans card_image_le)
    exact this
  · -- the rank condition
    have hEi : (univ.image (edgeId (peelL L) (peelF f))).card + 1 ≤ (univ.image (edgeId L f)).card := by
      let φ : Fin (t + 2 + 1) × Fin k → Fin (t + 1) × Fin k :=
        fun q => (⟨min (q.1.val - 1) t, by omega⟩, q.2)
      let mid := univ.image fun j : Fin t => edgeId L f ⟨j.val + 1, by omega⟩
      have h1 : univ.image (edgeId (peelL L) (peelF f)) = mid.image φ := by
        rw [image_image]
        congr 1
        funext j
        simp only [Function.comp, φ, edgeId]
        refine Prod.ext ?_ rfl
        ext
        simp only
        rw [tail_peel_val hfle]
        have := tail_peel_val (L := L) hfle j
        have h3 := (tail (peelL L) (peelF f) j).isLt
        omega
      have h0m : edgeId L f 0 ∉ mid := by
        simp only [mid, mem_image, mem_univ, true_and, not_exists]
        intro j hj
        have hz : hasEnd L f 0 0 (L 0) := by
          have := hasEnd_dep L f 0; rwa [show (0 : Fin (t + 2)).castSucc = 0 from rfl, h0] at this
        have := hasEnd_of_edgeId_eq hD hj hz
        rcases hasEnd_pos L f _ _ _ this with h | h
        · have := hint (⟨j.val + 1, by omega⟩ : Fin (t + 2)).castSucc (by simp) (by simp)
          rw [← h] at this
          simp at this
        · have := hint (⟨j.val + 1, by omega⟩ : Fin (t + 2)).succ (by simp) (by simp)
          rw [← h] at this
          simp at this
      have hsub : insert (edgeId L f 0) mid ⊆ univ.image (edgeId L f) := by
        intro e he
        rcases mem_insert.1 he with rfl | he
        · exact mem_image_of_mem _ (mem_univ _)
        · obtain ⟨j, -, rfl⟩ := mem_image.1 he
          exact mem_image_of_mem _ (mem_univ _)
      have := card_le_card hsub
      rw [card_insert_of_notMem h0m] at this
      rw [h1]
      exact le_trans (Nat.add_le_add_right card_image_le 1) this
    have hVi : (univ.filter fun u => f u = u).card ≤ (univ.filter fun u => peelF f u = u).card + 1 := by
      have hsub : (univ.filter fun u => f u = u) ⊆
          insert 0 ((univ.filter fun u => peelF f u = u).image
            (fun a : Fin (t + 1) => (⟨a.val + 1, by omega⟩ : Fin (t + 2 + 1)))) := by
        intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu
        by_cases hu0 : u.val = 0
        · exact mem_insert.2 (Or.inl (Fin.ext hu0))
        have hul : u.val ≠ t + 2 := by
          intro h
          have : u = Fin.last (t + 2) := Fin.ext h
          rw [this, hlast] at hu
          exact absurd (congrArg Fin.val hu) (by simp)
        refine mem_insert_of_mem (mem_image.2 ⟨⟨u.val - 1, by omega⟩, ?_, Fin.ext (by simp; omega)⟩)
        simp only [mem_filter, mem_univ, true_and]
        ext
        rw [peelF_val hfle]
        simp only
        rw [show (⟨u.val - 1 + 1, by omega⟩ : Fin (t + 2 + 1)) = u from Fin.ext (by simp; omega), hu]
      exact (card_le_card hsub).trans ((card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1))
    omega

theorem peel_first_ne (hR : Reduced L) (ht : 0 < t) :
    peelL L ⟨0, ht⟩ ≠ inv (L 0) := by
  have := hR 0 (by simp)
  exact this

theorem peel_inj {m : ℕ} {p q : Walk k (t + 2)} (hpR : Reduced p.1) (hpW : WalkOK m p.1 p.2)
    (hpl : deg p.1 p.2 0 ≤ 1) (hqR : Reduced q.1) (hqW : WalkOK m q.1 q.2) (hql : deg q.1 q.2 0 ≤ 1)
    (h0 : p.1 0 = q.1 0) (hpq : peel p = peel q) : p = q := by
  have hL : peelL p.1 = peelL q.1 := congrArg Prod.fst hpq
  have hF : peelF p.2 = peelF q.2 := congrArg Prod.snd hpq
  refine Prod.ext ?_ ?_
  · funext i
    by_cases hi0 : i.val = 0
    · rw [show i = 0 from Fin.ext hi0, h0]
    by_cases hil : i.val = t + 1
    · rw [show i = ⟨t + 1, by omega⟩ from Fin.ext hil, last_letter hpW hpl, last_letter hqW hql, h0]
    · have := congrFun hL ⟨i.val - 1, by omega⟩
      simp only [peelL] at this
      rwa [show (⟨i.val - 1 + 1, by omega⟩ : Fin (t + 2)) = i from Fin.ext (by simp; omega)] at this
  · funext a
    by_cases ha0 : a.val = 0
    · rw [show a = 0 from Fin.ext ha0, hpW.1, hqW.1]
    by_cases hal : a.val = t + 2
    · rw [show a = Fin.last (t + 2) from Fin.ext hal, hpW.2.1, hqW.2.1]
    · have := congrArg Fin.val (congrFun hF ⟨a.val - 1, by omega⟩)
      rw [peelF_val (fun i => (hpW.2.2.1 i).1), peelF_val (fun i => (hqW.2.2.1 i).1)] at this
      rw [show (⟨a.val - 1 + 1, by omega⟩ : Fin (t + 2 + 1)) = a from Fin.ext (by simp; omega)] at this
      have h1 := interior_ne_zero hpR hpW hpl a (by omega) (by omega)
      have h2 := interior_ne_zero hqR hqW hql a (by omega) (by omega)
      ext; omega

end Puder.Q284C.PartC6
end

section
open Finset
namespace Puder.Q284C.PartC7
open Puder Puder.Q284C Puder.Q284C.PartC1 Puder.Q284C.PartC2 Puder.Q284C.PartC4
  Puder.Q284C.PartC5 Puder.Q284C.PartC6
variable {k : ℕ}
/-!
# q284 Part C, helper 7: the recursion over leaf peels and the final count
-/
open Classical in
/-- Walks whose first letter is not `c`. -/
noncomputable def Wc (k m : ℕ) (c : Option (Fin k × Bool)) (t : ℕ) : Finset (Walk k t) :=
  univ.filter fun p => Reduced p.1 ∧ WalkOK m p.1 p.2 ∧ ∀ h : 0 < t, c ≠ some (p.1 ⟨0, h⟩)

theorem card_Wc_rec {m : ℕ} (c : Option (Fin k × Bool)) (t : ℕ) :
    (Wc k m c (t + 2)).card ≤ (NL k m (t + 2)).card +
      ∑ b ∈ univ.filter (fun b => c ≠ some b), (Wc k m (some (inv b)) t).card := by
  classical
  set Lf := (Wc k m c (t + 2)).filter fun p => ¬ 2 ≤ deg p.1 p.2 0
  have hsub : Wc k m c (t + 2) ⊆ NL k m (t + 2) ∪ Lf := by
    intro p hp
    by_cases h : 2 ≤ deg p.1 p.2 0
    · simp only [Wc, mem_filter, mem_univ, true_and] at hp
      exact mem_union_left _ (by simp [NL, hp.1, hp.2.1, h])
    · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
  have hL : Lf.card ≤ ∑ b ∈ univ.filter (fun b => c ≠ some b), (Wc k m (some (inv b)) t).card := by
    rw [← card_sigma]
    apply card_le_card_of_injOn (fun p => (⟨p.1 0, peel p⟩ : Σ _ : Fin k × Bool, Walk k t))
    · intro p hp
      simp only [Lf, Wc, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
      obtain ⟨⟨hR, hW, hc⟩, hl⟩ := hp
      have hl' : deg p.1 p.2 0 ≤ 1 := by omega
      obtain ⟨hR', hW'⟩ := walkOK_peel hR hW hl'
      simp only [coe_sigma, Set.mem_sigma_iff, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Wc]
      refine ⟨hc (by omega), hR', hW', fun ht h => ?_⟩
      exact peel_first_ne (L := p.1) hR ht (Option.some_injective _ h).symm
    · intro p hp q hq hpq
      simp only [Lf, Wc, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      simp only [Sigma.mk.injEq] at hpq
      exact peel_inj hp.1.1 hp.1.2.1 (by omega) hq.1.1 hq.1.2.1 (by omega) hpq.1 (eq_of_heq hpq.2)
  calc _ ≤ (NL k m (t + 2) ∪ Lf).card := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left hL _

theorem Wc_one_sub {m : ℕ} (c : Option (Fin k × Bool)) : Wc k m c 1 ⊆ NL k m 1 := by
  classical
  intro p hp
  simp only [Wc, NL, mem_filter, mem_univ, true_and] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_⟩
  have h1 : p.1 0 ∈ Ends p.1 p.2 0 := (mem_Ends _ _).2 ⟨0, by
    have := hasEnd_dep p.1 p.2 0
    rwa [show (0 : Fin 1).castSucc = 0 from rfl, hp.2.1.1] at this⟩
  have h2 : inv (p.1 0) ∈ Ends p.1 p.2 0 := (mem_Ends _ _).2 ⟨0, by
    have := hasEnd_arr p.1 p.2 0
    rwa [show (0 : Fin 1).succ = Fin.last 1 from rfl, hp.2.1.2.1] at this⟩
  exact one_lt_card.2 ⟨_, h1, _, h2, (inv_ne _).symm⟩

theorem card_Wc_zero {m : ℕ} (c : Option (Fin k × Bool)) : (Wc k m c 0).card ≤ 1 := by
  classical
  refine (card_le_univ _).trans ?_
  simp [Walk]

theorem one_le_rate (hk : 2 ≤ k) (m : ℕ) : 1 ≤ rate k m := by
  have h := (le_rate_both k m).2
  have : (1 : ℝ) ≤ Real.sqrt (2 * k - 1) := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  linarith

theorem sq_rate (hk : 2 ≤ k) (m : ℕ) : (2 * k - 1 : ℝ) ≤ rate k m ^ 2 := by
  have h := (le_rate_both k m).2
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [Real.sq_sqrt (by linarith)] at this

theorem card_filter_ne (a : Fin k × Bool) (hk : 1 ≤ k) :
    ((univ.filter fun b : Fin k × Bool => some a ≠ some b).card : ℝ) = 2 * k - 1 := by
  classical
  have : (univ.filter fun b : Fin k × Bool => some a ≠ some b) = univ.erase a := by
    ext b; simp [eq_comm]
  rw [this, card_erase_letters]
  rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem card_Wc_some_le {m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    ∀ (t : ℕ) (a : Fin k × Bool), ((Wc k m (some a) t).card : ℝ) ≤
      (((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) : ℕ) + 1 : ℝ) * ((t : ℝ) + 1) *
        ((t : ℝ) + 2) ^ (16 * m + 1) * rate k m ^ t := by
  obtain ⟨C1, hC1e⟩ : ∃ C1 : ℝ, C1 = (((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  rw [← hC1e]
  have hC1 : 0 ≤ C1 := by rw [hC1e]; exact Nat.cast_nonneg _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C1 + 1 := ⟨_, rfl⟩
  rw [← hK]
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = 16 * m + 1 := ⟨_, rfl⟩
  rw [← hD]
  have hr1 := one_le_rate hk m
  have hr0 : 0 ≤ rate k m := by linarith
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro a
  match t, ih with
  | 0, _ =>
    have := card_Wc_zero (k := k) (m := m) (some a)
    have h1 : ((Wc k m (some a) 0).card : ℝ) ≤ 1 := by exact_mod_cast this
    refine h1.trans ?_
    simp only [Nat.cast_zero, zero_add, pow_zero, mul_one]
    have : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
    nlinarith
  | 1, _ =>
    have h1 := card_le_card (Wc_one_sub (k := k) (m := m) (some a))
    have h2 := card_NL_le (m := m) hk hm 1
    rw [← hC1e, ← hD] at h2
    have h3 : ((Wc k m (some a) 1).card : ℝ) ≤ ((NL k m 1).card : ℝ) := by exact_mod_cast h1
    refine h3.trans (h2.trans ?_)
    have hp : (0 : ℝ) ≤ ((1 : ℕ) + 2 : ℝ) ^ D * rate k m ^ 1 := by positivity
    rw [hK]
    push_cast at hp ⊢
    nlinarith
  | t' + 2, ih =>
    have hrec := card_Wc_rec (k := k) (m := m) (some a) t'
    have hNL := card_NL_le (m := m) hk hm (t' + 2)
    rw [← hC1e, ← hD] at hNL
    have hsum : (∑ b ∈ univ.filter (fun b => some a ≠ some b), ((Wc k m (some (inv b)) t').card : ℝ)) ≤
        (2 * k - 1) * (K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ D * rate k m ^ t') := by
      rw [← card_filter_ne a (by omega), ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun b _ => ih t' (by omega) (inv b)
    have h1 : ((Wc k m (some a) (t' + 2)).card : ℝ) ≤ ((NL k m (t' + 2)).card : ℝ) +
        ∑ b ∈ univ.filter (fun b => some a ≠ some b), ((Wc k m (some (inv b)) t').card : ℝ) := by
      exact_mod_cast hrec
    refine h1.trans ?_
    set ρ := rate k m
    set X : ℝ := ((t' : ℝ) + 4) ^ D * ρ ^ t'
    have hX : 0 ≤ X := by positivity
    have hpow : ((t' : ℝ) + 2) ^ D ≤ ((t' : ℝ) + 4) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) D
    have hsq := sq_rate hk m
    have e1 : (((t' + 2 : ℕ) : ℝ) + 2) ^ D = ((t' : ℝ) + 4) ^ D := by push_cast; ring_nf
    have e2 : ρ ^ (t' + 2) = ρ ^ t' * ρ ^ 2 := pow_add _ _ _
    have hρt : 0 ≤ ρ ^ t' := pow_nonneg hr0 _
    have hk1 : (0 : ℝ) ≤ 2 * k - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    -- the two pieces
    have A1 : C1 * (((t' + 2 : ℕ) : ℝ) + 2) ^ D * ρ ^ (t' + 2) ≤ K * X * ρ ^ 2 := by
      rw [e1, e2]
      calc C1 * ((t' : ℝ) + 4) ^ D * (ρ ^ t' * ρ ^ 2) = C1 * (X * ρ ^ 2) := by simp only [X]; ring
        _ ≤ K * (X * ρ ^ 2) := by
            exact mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (mul_nonneg hX (sq_nonneg ρ))
        _ = K * X * ρ ^ 2 := by ring
    have A2 : (2 * k - 1) * (K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ D * ρ ^ t') ≤
        ρ ^ 2 * (K * ((t' : ℝ) + 1) * X) := by
      have hK0 : 0 ≤ K := by rw [hK]; linarith
      have hB : 0 ≤ K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ D * ρ ^ t' := by positivity
      calc (2 * k - 1) * (K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ D * ρ ^ t')
          ≤ ρ ^ 2 * (K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ D * ρ ^ t') :=
            mul_le_mul_of_nonneg_right hsq hB
        _ ≤ ρ ^ 2 * (K * ((t' : ℝ) + 1) * ((t' : ℝ) + 4) ^ D * ρ ^ t') := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg ρ)
            apply mul_le_mul_of_nonneg_right _ hρt
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ρ ^ 2 * (K * ((t' : ℝ) + 1) * X) := by simp only [X]; ring
    have hK0 : 0 ≤ K := by rw [hK]; linarith
    have fin : K * X * ρ ^ 2 + ρ ^ 2 * (K * ((t' : ℝ) + 1) * X) ≤
        K * (((t' + 2 : ℕ) : ℝ) + 1) * (((t' + 2 : ℕ) : ℝ) + 2) ^ D * ρ ^ (t' + 2) := by
      rw [e1, e2]
      have : 0 ≤ K * X * ρ ^ 2 := by positivity
      have e3 : K * (((t' + 2 : ℕ) : ℝ) + 1) * ((t' : ℝ) + 4) ^ D * (ρ ^ t' * ρ ^ 2) =
          K * X * ρ ^ 2 * ((t' : ℝ) + 3) := by simp only [X]; push_cast; ring
      rw [e3]
      nlinarith
    have := add_le_add (hNL.trans A1) (hsum.trans A2)
    linarith [fin, this]

end Puder.Q284C.PartC7
end

section
open Finset
namespace Puder.Q284C.PartC
open Puder Puder.Q284C
variable {k : ℕ}
/-!
# q284 Part C: the count of walks (Puder, proof of Proposition 4.3, (4.2)–(4.3))
-/
open Classical in
theorem card_walkOK_le (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    ∃ C D : ℕ, ∀ t : ℕ,
      ((Finset.univ.filter fun p : (Fin t → Fin k × Bool) × (Fin (t + 1) → Fin (t + 1)) =>
          Reduced p.1 ∧ WalkOK m p.1 p.2).card : ℝ) ≤ C * ((t : ℝ) + 2) ^ D * rate k m ^ t := by
  refine ⟨(2 * k + 1) * ((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) + 1), 16 * m + 2, fun t => ?_⟩
  have hF : (Finset.univ.filter fun p : (Fin t → Fin k × Bool) × (Fin (t + 1) → Fin (t + 1)) =>
      Reduced p.1 ∧ WalkOK m p.1 p.2) = PartC7.Wc k m none t := by
    ext p; simp [PartC7.Wc]
  rw [hF]
  have hS := PartC7.card_Wc_some_le (k := k) (m := m) hk hm
  obtain ⟨C1, hC1e⟩ : ∃ C1 : ℝ, C1 = (((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hC1 : 0 ≤ C1 := by rw [hC1e]; exact Nat.cast_nonneg _
  rw [← hC1e] at hS
  have hCe : (((2 * k + 1) * ((2 * k) ^ (6 * m) * (2 * m - 1) ^ (6 * m) + 1) : ℕ) : ℝ) =
      (2 * k + 1) * (C1 + 1) := by rw [hC1e]; push_cast; ring
  rw [hCe]
  have hr1 := PartC7.one_le_rate hk m
  have hr0 : 0 ≤ rate k m := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  match t with
  | 0 =>
    have := PartC7.card_Wc_zero (k := k) (m := m) none
    have h1 : ((PartC7.Wc k m none 0).card : ℝ) ≤ 1 := by exact_mod_cast this
    refine h1.trans ?_
    simp only [Nat.cast_zero, zero_add, pow_zero, mul_one]
    have : (1 : ℝ) ≤ 2 ^ (16 * m + 2) := one_le_pow₀ (by norm_num)
    nlinarith
  | 1 =>
    have h1 := card_le_card (PartC7.Wc_one_sub (k := k) (m := m) none)
    have h2 := PartC5.card_NL_le (m := m) hk hm 1
    rw [← hC1e] at h2
    have h3 : ((PartC7.Wc k m none 1).card : ℝ) ≤ ((PartC5.NL k m 1).card : ℝ) := by exact_mod_cast h1
    refine h3.trans (h2.trans ?_)
    push_cast
    have hp : (0 : ℝ) ≤ (1 + 2 : ℝ) ^ (16 * m + 1) * rate k m := by positivity
    have e : (1 + 2 : ℝ) ^ (16 * m + 2) = 3 * (1 + 2 : ℝ) ^ (16 * m + 1) := by
      rw [pow_succ]; ring
    rw [e]
    simp only [pow_one]
    have key : C1 ≤ (2 * (k : ℝ) + 1) * (C1 + 1) * 3 := by nlinarith
    have := mul_le_mul_of_nonneg_right key hp
    linarith
  | t' + 2 =>
    have hrec := PartC7.card_Wc_rec (k := k) (m := m) none t'
    have hNL := PartC5.card_NL_le (m := m) hk hm (t' + 2)
    rw [← hC1e] at hNL
    have hfilt : (univ.filter fun b : Fin k × Bool => (none : Option (Fin k × Bool)) ≠ some b) = univ := by
      ext b; simp
    rw [hfilt] at hrec
    set ρ := rate k m
    set K : ℝ := C1 + 1
    have hsum : (∑ b : Fin k × Bool, ((PartC7.Wc k m (some (PartC1.inv b)) t').card : ℝ)) ≤
        (2 * k) * (K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ (16 * m + 1) * ρ ^ t') := by
      have : ((univ : Finset (Fin k × Bool)).card : ℝ) = 2 * k := by
        rw [card_univ]; simp; ring
      rw [← this, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun b _ => hS t' (PartC1.inv b)
    have h1 : ((PartC7.Wc k m none (t' + 2)).card : ℝ) ≤ ((PartC5.NL k m (t' + 2)).card : ℝ) +
        ∑ b : Fin k × Bool, ((PartC7.Wc k m (some (PartC1.inv b)) t').card : ℝ) := by
      exact_mod_cast hrec
    refine h1.trans ?_
    set Y : ℝ := ((t' : ℝ) + 4) ^ (16 * m + 1) * ρ ^ t'
    have hY : 0 ≤ Y := by positivity
    have hρt : 0 ≤ ρ ^ t' := pow_nonneg hr0 _
    have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hr1
    have hK0 : 0 ≤ K := by simp only [K]; linarith
    have e1 : (((t' + 2 : ℕ) : ℝ) + 2) = (t' : ℝ) + 4 := by push_cast; ring
    have e2 : ρ ^ (t' + 2) = ρ ^ t' * ρ ^ 2 := pow_add _ _ _
    have hpow : ((t' : ℝ) + 2) ^ (16 * m + 1) ≤ ((t' : ℝ) + 4) ^ (16 * m + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hT : (1 : ℝ) ≤ (t' : ℝ) + 4 := by have : (0 : ℝ) ≤ t' := Nat.cast_nonneg _; linarith
    -- piece one
    have A1 : C1 * (((t' + 2 : ℕ) : ℝ) + 2) ^ (16 * m + 1) * ρ ^ (t' + 2) ≤
        K * ((t' : ℝ) + 4) * Y * ρ ^ 2 := by
      rw [e1, e2]
      have : C1 * ((t' : ℝ) + 4) ^ (16 * m + 1) * (ρ ^ t' * ρ ^ 2) = C1 * (Y * ρ ^ 2) := by
        simp only [Y]; ring
      rw [this]
      have hYr : 0 ≤ Y * ρ ^ 2 := by positivity
      have : C1 * (Y * ρ ^ 2) ≤ K * (Y * ρ ^ 2) :=
        mul_le_mul_of_nonneg_right (by simp only [K]; linarith) hYr
      have : K * (Y * ρ ^ 2) ≤ K * ((t' : ℝ) + 4) * (Y * ρ ^ 2) := by
        have := mul_le_mul_of_nonneg_left hT (mul_nonneg hK0 hYr)
        nlinarith
      nlinarith
    -- piece two
    have A2 : (2 * k) * (K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ (16 * m + 1) * ρ ^ t') ≤
        (2 * k) * (K * ((t' : ℝ) + 4) * Y * ρ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have ht1 : (t' : ℝ) + 1 ≤ (t' : ℝ) + 4 := by linarith
      calc K * ((t' : ℝ) + 1) * ((t' : ℝ) + 2) ^ (16 * m + 1) * ρ ^ t'
          ≤ K * ((t' : ℝ) + 4) * ((t' : ℝ) + 4) ^ (16 * m + 1) * ρ ^ t' := by gcongr
        _ = K * ((t' : ℝ) + 4) * Y * 1 := by simp only [Y]; ring
        _ ≤ K * ((t' : ℝ) + 4) * Y * ρ ^ 2 := by
            apply mul_le_mul_of_nonneg_left hρ2; positivity
    have fin : K * ((t' : ℝ) + 4) * Y * ρ ^ 2 + (2 * k) * (K * ((t' : ℝ) + 4) * Y * ρ ^ 2) =
        (2 * k + 1) * K * (((t' + 2 : ℕ) : ℝ) + 2) ^ (16 * m + 2) * ρ ^ (t' + 2) := by
      rw [e1, e2]; simp only [Y]; ring
    have := add_le_add (hNL.trans A1) (hsum.trans A2)
    linarith [fin, this]

end Puder.Q284C.PartC
end

section
open Filter
namespace Puder.Q284C
open Puder
variable {k : ℕ}
/-! ## Part C: the count -/
alias card_walkOK_le := Puder.Q284C.PartC.card_walkOK_le

/-! ## The statement -/
theorem finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le_dev (k m : ℕ) (hk : 2 ≤ k)
    (hm1 : 1 ≤ m) (hm : m ≤ k) :
    (∀ w : FreeGroup (Fin k),
        {J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ w ∈ J ∧ TracesEachCoreEdgeTwice J w}.Finite) ∧
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
              TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard : ℝ)) ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
              TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard : ℝ)) ^ (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  refine ⟨fun w => ?_, ?_⟩
  · have hinj : Set.InjOn (fun J => fJ J w w.toWord.length)
        {J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ w ∈ J ∧ TracesEachCoreEdgeTwice J w} :=
      (fJ_injOn w _ rfl).mono fun J (hJ : HasRank J m ∧ w ∈ J ∧ TracesEachCoreEdgeTwice J w) =>
        (show w ∈ J ∧ TracesEachCoreEdgeTwice J w from ⟨hJ.2.1, hJ.2.2⟩)
    exact Set.Finite.of_finite_image (Set.toFinite _) hinj
  · obtain ⟨C, D, hCD⟩ := card_walkOK_le k m hk hm1
    have := boundedUnder_and_limsup_le _ (fun t => Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
      (rate k m) (rate_pos k m hk) C D (fun t => (sum_ncard_le_card k m t).trans (hCD t))
    exact this

end Puder.Q284C
end

section
open Filter
open Puder
open Puder.Q284C
open Puder
variable {k : ℕ}
theorem solution (k m : ℕ) (hk : 2 ≤ k)
    (hm1 : 1 ≤ m) (hm : m ≤ k) :
    (∀ w : FreeGroup (Fin k),
        {J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ w ∈ J ∧ TracesEachCoreEdgeTwice J w}.Finite) ∧
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
              TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard : ℝ)) ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t,
          ({J : Subgroup (FreeGroup (Fin k)) | HasRank J m ∧ StrongConv.wordFree (List.ofFn fun j => some (i j)) ∈ J ∧
              TracesEachCoreEdgeTwice J (StrongConv.wordFree (List.ofFn fun j => some (i j)))}.ncard : ℝ)) ^ (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  exact Puder.Q284C.finite_and_limsup_sum_ncard_tracesEachCoreEdgeTwice_reduced_rpow_le_dev k m hk hm1 hm
end
