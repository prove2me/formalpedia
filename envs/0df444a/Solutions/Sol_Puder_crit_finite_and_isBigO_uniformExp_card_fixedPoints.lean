-- Prove2me | solution 1 for Puder.crit_finite_and_isBigO_uniformExp_card_fixedPoints
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T11:13:08.89021+00:00
-- url     : https://prove2.me/submissions/5c2959ec-9c09-4b95-8d39-3db9767ea5a3

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
import Theorems.Thm_Puder_isPrimitiveIn_of_isPrimitiveIn_top
import Theorems.Thm_Puder_isAlgExt_zpowers_of_mem_crit
import Theorems.Thm_Puder_exists_mem_traverses_of_isAlgExt_of_isCoreEdge
import Theorems.Thm_Puder_setOf_isAlgExt_finite_of_fg
section
/-!
# Quotients of the cycle of a word, after Puder–Parzanchevski (JAMS 2015), §§3, 5–7

A word `K` over the letters `(i, true) = x_i`, `(i, false) = x_i⁻¹` is drawn on a cycle with
vertices `Fin K.length`; the edge at position `p` joins `p` and its cyclic successor and carries
the letter `K[p]`. A partition of the vertices is fold-free (`FF`) when the quotient graph is a
core graph without folding. All definitions here are bundle-ready (no proofs are needed to state
them).
-/

namespace Puder.PP

variable {d : ℕ}

/-- The cyclic successor on `Fin n`. -/
def cnxt {n : ℕ} (p : Fin n) : Fin n :=
  ⟨((p : ℕ) + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt p.2)⟩

/-- The generator on the edge at position `p`. -/
def lab (K : List (Fin d × Bool)) (p : Fin K.length) : Fin d := (K[p]).1

/-- The tail of the edge at position `p`: an `x_i` edge runs from `p` to `p + 1`, an `x_i⁻¹` edge
from `p + 1` to `p`. -/
def tl (K : List (Fin d × Bool)) (p : Fin K.length) : Fin K.length :=
  if (K[p]).2 then p else cnxt p

/-- The head of the edge at position `p`. -/
def hd (K : List (Fin d × Bool)) (p : Fin K.length) : Fin K.length :=
  if (K[p]).2 then cnxt p else p

/-- Partitions of the vertices of the cycle. -/
abbrev Part (K : List (Fin d × Bool)) : Type :=
  Finpartition (Finset.univ : Finset (Fin K.length))

/-- The partition is fold-free: two edges with the same generator have tails in the same block iff
they have heads in the same block. -/
def FF (K : List (Fin d × Bool)) (P : Part K) : Prop :=
  ∀ e e' : Fin K.length, lab K e = lab K e' →
    (P.part (tl K e) = P.part (tl K e') ↔ P.part (hd K e) = P.part (hd K e'))

/-- The edge of the quotient graph of `P` under the cycle edge at position `p`. -/
def qedge (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) :
    Fin d × Finset (Fin K.length) × Finset (Fin K.length) :=
  (lab K p, P.part (tl K p), P.part (hd K p))

/-- The edges of the quotient graph of `P`. -/
def E (K : List (Fin d × Bool)) (P : Part K) :
    Finset (Fin d × Finset (Fin K.length) × Finset (Fin K.length)) :=
  Finset.univ.image (qedge K P)

/-- The number of blocks of `Q'` inside the set `B` (a block of a coarser partition). -/
def vfib (K : List (Fin d × Bool)) (Q' : Part K) (B : Finset (Fin K.length)) : ℕ :=
  (Q'.parts.filter (· ⊆ B)).card

/-- The number of edges of the quotient of `Q'` lying over the edge `ε` of the quotient of `Q`. -/
def efib (K : List (Fin d × Bool)) (Q' Q : Part K)
    (ε : Fin d × Finset (Fin K.length) × Finset (Fin K.length)) : ℕ :=
  ((Finset.univ.filter fun p => qedge K Q p = ε).image (qedge K Q')).card

/-- PP15 Lemma 6.4: `L_{Q',Q}`, the expected number of injective lifts of the quotient of `Q'` to
a random `N`-sheeted covering of the quotient of `Q`, as a function of `x = 1/N`:
`∏_B (N)_{v_B} / ∏_ε (N)_{e_ε}`. -/
noncomputable def Lx (K : List (Fin d × Bool)) (Q' Q : Part K) (x : ℝ) : ℝ :=
  x ^ (((E K Q').card : ℤ) - (Q'.parts.card : ℤ)) *
    (∏ B ∈ Q.parts, ∏ i ∈ Finset.range (vfib K Q' B), (1 - (i : ℝ) * x)) /
    (∏ ε ∈ E K Q, ∏ i ∈ Finset.range (efib K Q' Q ε), (1 - (i : ℝ) * x))

/-- The expected number of fixed points of `w(σ)` for `σ` uniform in `S_N^d`. -/
noncomputable def Fix (w : FreeGroup (Fin d)) (N : ℕ) : ℝ :=
  StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ))

/-- PP15 Lemma 6.2: `Φ`, the expected number of lifts of the cycle to a random `N`-sheeted
covering of the quotient graph of `Q`: a covering assigns a permutation of the `N` sheets to each
edge of the quotient, and a lift assigns a sheet to each vertex of the cycle. -/
noncomputable def Psi (K : List (Fin d × Bool)) (Q : Part K) (N : ℕ) : ℝ :=
  StrongConv.uniformExp (fun σ : {ε // ε ∈ E K Q} → Equiv.Perm (Fin N) =>
    ((Finset.univ.filter fun f : Fin K.length → Fin N =>
      ∀ p : Fin K.length,
        σ ⟨qedge K Q p, Finset.mem_image_of_mem _ (Finset.mem_univ p)⟩ (f (tl K p)) =
          f (hd K p)).card : ℝ))

/-- The element of `F_d` read along the first `p` edges of the cycle. -/
def pfx (K : List (Fin d × Bool)) (p : ℕ) : FreeGroup (Fin d) := FreeGroup.mk (K.take p)

/-- `π₁` of the quotient graph of `P` at the block of vertex `0`, as a subgroup of `F_d`. -/
def J (K : List (Fin d × Bool)) (P : Part K) : Subgroup (FreeGroup (Fin d)) :=
  Subgroup.closure ({FreeGroup.mk K} ∪
    {g | ∃ p q : Fin K.length, P.part p = P.part q ∧ g = pfx K p * (pfx K q)⁻¹})

/-- `Q` is the fold-free partition generated from `Q'` by identifying `m` pairs of vertices
(PP15 Definition 3.? of the `X`-distance `ρ_X`: `ρ_X ≤ m`). -/
def Gen (K : List (Fin d × Bool)) (Q' Q : Part K) (m : ℕ) : Prop :=
  ∃ s : Fin m → Fin K.length × Fin K.length, FF K Q ∧ Q' ≤ Q ∧
    (∀ i, Q.part (s i).1 = Q.part (s i).2) ∧
    ∀ Q'' : Part K, FF K Q'' → Q' ≤ Q'' → (∀ i, Q''.part (s i).1 = Q''.part (s i).2) → Q ≤ Q''

/-! ## Exploring the quotient along the cycle -/

/-- The edge at position `p` is traversed for the first time at step `p`. -/
def New (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : Prop :=
  ∀ q : Fin K.length, q < p → qedge K P q ≠ qedge K P p

/-- Step `p` arrives at a block not visited before (and does not wrap around). -/
def Disc (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : Prop :=
  (p : ℕ) + 1 < K.length ∧ ∀ q : Fin K.length, (q : ℕ) ≤ p → P.part q ≠ P.part (cnxt p)

/-- Step `p` traverses a new edge and arrives at a block already visited. -/
def Rec (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : Prop :=
  New K P p ∧ ¬ Disc K P p

/-- The first position in the block of `p`. -/
def first (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : Fin K.length :=
  (P.part p).min' ⟨p, P.mem_part (Finset.mem_univ p)⟩

/-- The closed walk of step `p`: along the cycle to the end of step `p`, then back along the
cycle from the first position of the block reached. -/
def gam (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : FreeGroup (Fin d) :=
  pfx K ((p : ℕ) + 1) * (pfx K (first K P (cnxt p)))⁻¹

end Puder.PP
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartE
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
/-!
# Part E: the two expansions (PP15 Lemmas 6.2–6.4; Hanany–Puder §6.1)

A fibered counting lemma (`sum_card_hom`) on a general labelled graph: pairs (edge permutations,
sheet assignment) are counted by the fibered kernel of the sheet assignment.
-/
theorem card_perm_extend {α D : Type*} [Fintype α] [DecidableEq α] [Fintype D]
    (ι κ : D ↪ α) :
    Fintype.card {σ : Perm α // ∀ d, σ (ι d) = κ d} =
      (Fintype.card α - Fintype.card D).factorial := by
  let e : {x // x ∈ Set.range ι} ≃ {x // x ∈ Set.range κ} :=
    (Equiv.ofInjective ι ι.injective).symm.trans (Equiv.ofInjective κ κ.injective)
  let σ₀ : Perm α := e.extendSubtype
  have h0 : ∀ d, σ₀ (ι d) = κ d := by
    intro d
    have := e.extendSubtype_apply_of_mem (ι d) ⟨d, rfl⟩
    simp only [σ₀, this, e, Equiv.trans_apply]
    rw [show (⟨ι d, ⟨d, rfl⟩⟩ : {x // x ∈ Set.range ι}) = Equiv.ofInjective ι ι.injective d from rfl,
      Equiv.symm_apply_apply]
    rfl
  let E1 : {σ : Perm α // ∀ d, σ (ι d) = κ d} ≃
      {τ : Perm α // ∀ a, ¬ (a ∉ Set.range ι) → τ a = a} :=
    { toFun := fun σ => ⟨σ₀⁻¹ * σ.1, by
        rintro a ha
        obtain ⟨d, rfl⟩ := not_not.1 ha
        simp [Perm.mul_apply, σ.2 d, ← h0 d]⟩
      invFun := fun τ => ⟨σ₀ * τ.1, by
        intro d
        simp [Perm.mul_apply, τ.2 (ι d) (by simp), h0 d]⟩
      left_inv := fun σ => by ext; simp
      right_inv := fun τ => by ext; simp }
  rw [Fintype.card_congr (E1.trans (Perm.subtypeEquivSubtypePerm _).symm), Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_range]

/-- Functions injective on each fibre of `c`. -/
theorem card_fiberwise_inj {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (c : α → β) (N : ℕ)
    [Fintype {g : α → Fin N // ∀ a a', c a = c a' → g a = g a' → a = a'}] :
    Fintype.card {g : α → Fin N // ∀ a a', c a = c a' → g a = g a' → a = a'} =
      ∏ b, N.descFactorial (Fintype.card {a // c a = b}) := by
  let e : {g : α → Fin N // ∀ a a', c a = c a' → g a = g a' → a = a'} ≃
      (∀ b, ({a // c a = b} ↪ Fin N)) :=
    { toFun := fun g b => ⟨fun a => g.1 a.1, fun a a' h =>
        Subtype.ext (g.2 _ _ (a.2.trans a'.2.symm) h)⟩
      invFun := fun h => ⟨fun a => h (c a) ⟨a, rfl⟩, by
        intro a a' hc hh
        have aux : ∀ b b' (hbb : b = b') (a : α) (ha : c a = b),
            h b ⟨a, ha⟩ = h b' ⟨a, ha.trans hbb⟩ := by
          rintro b _ rfl a ha; rfl
        have h3 : h (c a) ⟨a, rfl⟩ = h (c a) ⟨a', hc.symm⟩ :=
          hh.trans (aux (c a') (c a) hc.symm a' rfl)
        exact congrArg Subtype.val ((h (c a)).injective h3)⟩
      left_inv := fun g => Subtype.ext (funext fun a => rfl)
      right_inv := fun h => by
        funext b
        apply Function.Embedding.ext
        rintro ⟨a, rfl⟩
        rfl }
  rw [Fintype.card_congr e, Fintype.card_pi]
  refine prod_congr rfl fun b _ => ?_
  rw [Fintype.card_embedding_eq, Fintype.card_fin]

end Puder.PP.PartE
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartE
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {V Ed L : Type*} [Fintype V] [DecidableEq V] [Fintype Ed] [Fintype L] [DecidableEq L]
  {N : ℕ} (lam : Ed → L) (tl hd : Ed → V) (Q : Finpartition (univ : Finset V))
/-- The block of `x`, as an element of the set of parts. -/
def blk (P : Finpartition (univ : Finset V)) (x : V) : P.parts :=
  ⟨P.part x, P.part_mem.2 (mem_univ x)⟩

/-- A chosen representative of a part. -/
noncomputable def rep (P : Finpartition (univ : Finset V)) (A : P.parts) : V :=
  (P.nonempty_of_mem_parts A.2).choose

theorem rep_mem (P : Finpartition (univ : Finset V)) (A : P.parts) : rep P A ∈ A.1 :=
  (P.nonempty_of_mem_parts A.2).choose_spec

theorem blk_rep (P : Finpartition (univ : Finset V)) (A : P.parts) : blk P (rep P A) = A :=
  Subtype.ext ((P.part_eq_iff_mem A.2).2 (rep_mem P A))

theorem blk_eq_iff (P : Finpartition (univ : Finset V)) (x x' : V) :
    blk P x = blk P x' ↔ P.part x = P.part x' := Subtype.ext_iff

theorem part_eq_part_iff (P : Finpartition (univ : Finset V)) (x x' : V) :
    P.part x = P.part x' ↔ x' ∈ P.part x := by
  rw [eq_comm, P.part_eq_iff_mem (P.part_mem.2 (mem_univ x))]

theorem finpartition_eq_of (P P' : Finpartition (univ : Finset V))
    (h : ∀ x x', x' ∈ P.part x ↔ x' ∈ P'.part x) : P = P' := by
  have hpart : ∀ x, P.part x = P'.part x := fun x => Finset.ext (h x)
  ext t
  constructor
  · intro ht
    obtain ⟨x, -, rfl⟩ := P.part_surjOn (Finset.mem_coe.2 ht)
    rw [hpart]; exact P'.part_mem.2 (mem_univ x)
  · intro ht
    obtain ⟨x, -, rfl⟩ := P'.part_surjOn (Finset.mem_coe.2 ht)
    rw [← hpart]; exact P.part_mem.2 (mem_univ x)

/-- Refinement, pointwise. -/
def Le (P Q : Finpartition (univ : Finset V)) : Prop :=
  ∀ x x', P.part x = P.part x' → Q.part x = Q.part x'

theorem le_iff (P Q : Finpartition (univ : Finset V)) : P ≤ Q ↔ Le P Q := by
  constructor
  · intro h x x' hx
    obtain ⟨c, hc, hle⟩ := h (P.part_mem.2 (mem_univ x))
    have h1 : x ∈ c := hle (P.mem_part (mem_univ x))
    have h2 : x' ∈ c := hle ((part_eq_part_iff P x x').1 hx)
    rw [Q.part_eq_of_mem hc h1, Q.part_eq_of_mem hc h2]
  · intro h b hb
    obtain ⟨x, -, rfl⟩ := P.part_surjOn (Finset.mem_coe.2 hb)
    refine ⟨Q.part x, Q.part_mem.2 (mem_univ x), fun y hy => ?_⟩
    exact (part_eq_part_iff Q x y).1 (h x y ((part_eq_part_iff P x y).2 hy))

theorem sub_of_le {P : Finpartition (univ : Finset V)} (hle : Le P Q) (x : V) :
    P.part x ⊆ Q.part x := fun y hy =>
  (part_eq_part_iff Q x y).1 (hle x y ((part_eq_part_iff P x y).2 hy))

/-- `f` is a lift: every edge `e` is mapped by `σ_{lam e}` from `f (tl e)` to `f (hd e)`. -/
def GHom (σ : L → Perm (Fin N)) (f : V → Fin N) : Prop :=
  ∀ e, σ (lam e) (f (tl e)) = f (hd e)

/-- Fold-freeness for an abstract labelled graph. -/
def GFF (P : Finpartition (univ : Finset V)) : Prop :=
  ∀ e e', lam e = lam e' → (P.part (tl e) = P.part (tl e') ↔ P.part (hd e) = P.part (hd e'))

/-- The number of quotient edges of label `l`. -/
def QE (P : Finpartition (univ : Finset V)) (l : L) : ℕ :=
  ((univ.filter fun e => lam e = l).image fun e => (P.part (tl e), P.part (hd e))).card

theorem QE_le (P : Finpartition (univ : Finset V)) (l : L) :
    QE lam tl hd P l ≤ Fintype.card Ed :=
  card_image_le.trans (card_le_univ _)

/-- The fibered kernel of `f` over `Q` is `P`. -/
def KerIs (P : Finpartition (univ : Finset V)) (f : V → Fin N) : Prop :=
  ∀ x x', P.part x = P.part x' ↔ (Q.part x = Q.part x' ∧ f x = f x')

/-- The labelling determines the `Q`-blocks of both ends. -/
def H1 : Prop :=
  ∀ e e', lam e = lam e' → Q.part (tl e) = Q.part (tl e') ∧ Q.part (hd e) = Q.part (hd e')

theorem sum_kerIs (f : V → Fin N) :
    ∑ P : Finpartition (univ : Finset V), (if KerIs Q P f then 1 else 0) = 1 := by
  let s : Setoid V := ⟨fun x x' => Q.part x = Q.part x' ∧ f x = f x',
    ⟨fun x => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩⟩
  let P₀ : Finpartition (univ : Finset V) := Finpartition.ofSetoid s
  have h0 : KerIs Q P₀ f := by
    intro x x'
    rw [part_eq_part_iff, Finpartition.mem_part_ofSetoid_iff_rel]
    exact Iff.rfl
  rw [sum_eq_single P₀]
  · rw [if_pos h0]
  · intro P _ hP
    rw [if_neg]
    intro hk; apply hP
    apply finpartition_eq_of
    intro x x'
    rw [← part_eq_part_iff, ← part_eq_part_iff, hk, h0]
  · intro h; exact absurd (mem_univ _) h

theorem kerIs_le {P : Finpartition (univ : Finset V)} {f : V → Fin N} (hk : KerIs Q P f) :
    Le P Q := fun x x' h => ((hk x x').1 h).1

theorem ff_of_hom (h1 : H1 lam tl hd Q) {σ : L → Perm (Fin N)} {f : V → Fin N}
    {P : Finpartition (univ : Finset V)}
    (hf : GHom lam tl hd σ f) (hk : KerIs Q P f) : GFF lam tl hd P := by
  intro e e' hl
  obtain ⟨ht, hh⟩ := h1 e e' hl
  rw [hk (tl e) (tl e'), hk (hd e) (hd e'), ← hf e, ← hf e', hl]
  simp only [ht, hh, true_and]
  exact (σ (lam e')).injective.eq_iff.symm

/-- The `Q`-block containing a block of `P`. -/
noncomputable def cc (P : Finpartition (univ : Finset V)) (A : P.parts) : Q.parts :=
  blk Q (rep P A)

theorem cc_blk {P : Finpartition (univ : Finset V)} (hle : Le P Q) (x : V) :
    cc Q P (blk P x) = blk Q x :=
  Subtype.ext (hle _ _ ((blk_eq_iff P _ _).1 (blk_rep P (blk P x))))

/-- Injectivity on the blocks of `P` inside each block of `Q`. -/
def FibInj (P : Finpartition (univ : Finset V)) (g : P.parts → Fin N) : Prop :=
  ∀ A A' : P.parts, cc Q P A = cc Q P A' → g A = g A' → A = A'

/-- Compatibility of a sheet assignment on blocks with `σ`. -/
def Compat (P : Finpartition (univ : Finset V)) (σ : L → Perm (Fin N)) (g : P.parts → Fin N) :
    Prop :=
  ∀ e, σ (lam e) (g (blk P (tl e))) = g (blk P (hd e))

theorem card_hom_kerIs (P : Finpartition (univ : Finset V)) (hle : Le P Q)
    (σ : L → Perm (Fin N)) :
    (univ.filter fun f : V → Fin N => GHom lam tl hd σ f ∧ KerIs Q P f).card =
      (univ.filter fun g : P.parts → Fin N => FibInj Q P g ∧ Compat lam tl hd P σ g).card := by
  symm
  refine card_bij' (fun g _ => fun x => g (blk P x))
    (fun f _ => fun A => f (rep P A)) ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨hfi, hc⟩ := (mem_filter.1 hg).2
    refine mem_filter.2 ⟨mem_univ _, hc, fun x x' => ⟨fun h => ?_, ?_⟩⟩
    · exact ⟨hle _ _ h, congrArg g ((blk_eq_iff P x x').2 h)⟩
    · rintro ⟨hq, hg'⟩
      refine (blk_eq_iff P x x').1 (hfi _ _ ?_ hg')
      rw [cc_blk Q hle, cc_blk Q hle]
      exact (blk_eq_iff Q _ _).2 hq
  · intro f hf
    obtain ⟨hh, hk⟩ := (mem_filter.1 hf).2
    have h1 : ∀ x, f (rep P (blk P x)) = f x := fun x =>
      ((hk _ _).1 ((blk_eq_iff P _ _).1 (blk_rep P (blk P x)))).2
    refine mem_filter.2 ⟨mem_univ _, ?_, fun e => ?_⟩
    · intro A A' hq hfe
      have h2 : P.part (rep P A) = P.part (rep P A') :=
        (hk _ _).2 ⟨(blk_eq_iff Q _ _).1 hq, hfe⟩
      exact (blk_rep P A).symm.trans (((blk_eq_iff P _ _).2 h2).trans (blk_rep P A'))
    · show σ (lam e) (f (rep P (blk P (tl e)))) = f (rep P (blk P (hd e)))
      rw [h1, h1]
      exact hh e
  · intro g _
    funext A
    show g (blk P (rep P A)) = g A
    rw [blk_rep]
  · intro f hf
    have hk := (mem_filter.1 hf).2.2
    funext x
    exact ((hk _ _).1 ((blk_eq_iff P _ _).1 (blk_rep P (blk P x)))).2

/-- The quotient edges of label `l`, as pairs of blocks. -/
def QD (P : Finpartition (univ : Finset V)) (l : L) : Finset (P.parts × P.parts) :=
  (univ.filter fun e => lam e = l).image fun e => (blk P (tl e), blk P (hd e))

theorem card_QD (P : Finpartition (univ : Finset V)) (l : L) :
    (QD lam tl hd P l).card = QE lam tl hd P l := by
  unfold QD QE
  have hinj : Function.Injective (Prod.map (Subtype.val : P.parts → Finset V)
      (Subtype.val : P.parts → Finset V)) := fun a b h =>
    Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  rw [← card_image_of_injective _ hinj, image_image]
  rfl

theorem QD_fst_iff {P : Finpartition (univ : Finset V)} (hP : GFF lam tl hd P) {l : L}
    {x y : P.parts × P.parts} (hx : x ∈ QD lam tl hd P l) (hy : y ∈ QD lam tl hd P l) :
    x.1 = y.1 ↔ x.2 = y.2 := by
  obtain ⟨e, he, rfl⟩ := mem_image.1 hx
  obtain ⟨e', he', rfl⟩ := mem_image.1 hy
  simp only [blk_eq_iff]
  exact hP e e' ((mem_filter.1 he).2.trans (mem_filter.1 he').2.symm)

theorem QD_cc {P : Finpartition (univ : Finset V)} (hle : Le P Q) (h1 : H1 lam tl hd Q) {l : L}
    {x y : P.parts × P.parts} (hx : x ∈ QD lam tl hd P l) (hy : y ∈ QD lam tl hd P l) :
    cc Q P x.1 = cc Q P y.1 ∧ cc Q P x.2 = cc Q P y.2 := by
  obtain ⟨e, he, rfl⟩ := mem_image.1 hx
  obtain ⟨e', he', rfl⟩ := mem_image.1 hy
  have := h1 e e' ((mem_filter.1 he).2.trans (mem_filter.1 he').2.symm)
  show cc Q P (blk P (tl e)) = cc Q P (blk P (tl e')) ∧
    cc Q P (blk P (hd e)) = cc Q P (blk P (hd e'))
  rw [cc_blk Q hle, cc_blk Q hle, cc_blk Q hle, cc_blk Q hle]
  exact ⟨(blk_eq_iff Q _ _).2 this.1, (blk_eq_iff Q _ _).2 this.2⟩

theorem card_perm_compat_l {P : Finpartition (univ : Finset V)} (hle : Le P Q)
    (h1 : H1 lam tl hd Q) (hP : GFF lam tl hd P)
    (g : P.parts → Fin N) (hg : FibInj Q P g) (l : L) :
    (univ.filter fun τ : Perm (Fin N) =>
        ∀ e, lam e = l → τ (g (blk P (tl e))) = g (blk P (hd e))).card =
      (N - QE lam tl hd P l).factorial := by
  let D := QD lam tl hd P l
  let ι : D ↪ Fin N := ⟨fun x => g x.1.1, by
    intro x y h
    have h1' : x.1.1 = y.1.1 := hg _ _ (QD_cc lam tl hd Q hle h1 x.2 y.2).1 h
    exact Subtype.ext (Prod.ext h1' ((QD_fst_iff lam tl hd hP x.2 y.2).1 h1'))⟩
  let κ : D ↪ Fin N := ⟨fun x => g x.1.2, by
    intro x y h
    have h1' : x.1.2 = y.1.2 := hg _ _ (QD_cc lam tl hd Q hle h1 x.2 y.2).2 h
    exact Subtype.ext (Prod.ext ((QD_fst_iff lam tl hd hP x.2 y.2).2 h1') h1')⟩
  have := card_perm_extend ι κ
  rw [Fintype.card_subtype, Fintype.card_fin, Fintype.card_coe, card_QD] at this
  rw [← this]
  congr 1
  ext τ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro h ⟨x, hx⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hx
    exact h e (mem_filter.1 he).2
  · intro h e he
    exact h ⟨_, mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, he⟩, rfl⟩⟩

theorem card_compat {P : Finpartition (univ : Finset V)} (hle : Le P Q)
    (h1 : H1 lam tl hd Q) (hP : GFF lam tl hd P)
    (g : P.parts → Fin N) (hg : FibInj Q P g) :
    (univ.filter fun σ : L → Perm (Fin N) => Compat lam tl hd P σ g).card =
      ∏ l, (N - QE lam tl hd P l).factorial := by
  have : (univ.filter fun σ : L → Perm (Fin N) => Compat lam tl hd P σ g) =
      Fintype.piFinset fun l => univ.filter fun τ : Perm (Fin N) =>
        ∀ e, lam e = l → τ (g (blk P (tl e))) = g (blk P (hd e)) := by
    ext σ
    rw [mem_filter, Fintype.mem_piFinset]
    constructor
    · intro h l; exact mem_filter.2 ⟨mem_univ _, fun e he => by subst he; exact h.2 e⟩
    · intro h; exact ⟨mem_univ _, fun e => (mem_filter.1 (h _)).2 e rfl⟩
  rw [this, Fintype.card_piFinset]
  exact prod_congr rfl fun l _ => card_perm_compat_l lam tl hd Q hle h1 hP g hg l

theorem card_fibInj (P : Finpartition (univ : Finset V)) :
    (univ.filter fun g : P.parts → Fin N => FibInj Q P g).card =
      ∏ B : Q.parts, N.descFactorial (Fintype.card {A : P.parts // cc Q P A = B}) := by
  rw [← Fintype.card_subtype]
  exact @card_fiberwise_inj _ _ _ _ _ (cc Q P) N (Subtype.fintype (FibInj Q P))

theorem sum_card_hom (h1 : H1 lam tl hd Q) :
    ∑ σ : L → Perm (Fin N), (univ.filter (GHom lam tl hd σ)).card =
      ∑ P ∈ (univ : Finset (Finpartition (univ : Finset V))).filter
          (fun P => Le P Q ∧ GFF lam tl hd P),
        (∏ B : Q.parts, N.descFactorial (Fintype.card {A : P.parts // cc Q P A = B})) *
          ∏ l, (N - QE lam tl hd P l).factorial := by
  calc _ = ∑ σ : L → Perm (Fin N), ∑ P : Finpartition (univ : Finset V),
        (univ.filter fun f : V → Fin N => GHom lam tl hd σ f ∧ KerIs Q P f).card := by
        refine sum_congr rfl fun σ _ => ?_
        simp_rw [card_eq_sum_ones, sum_filter]
        rw [sum_comm]
        refine sum_congr rfl fun f _ => ?_
        by_cases h : GHom lam tl hd σ f
        · rw [if_pos h]; simp only [h, true_and]; exact (sum_kerIs Q f).symm
        · rw [if_neg h]; symm; apply sum_eq_zero; intro P _; rw [if_neg (fun hh => h hh.1)]
    _ = ∑ P : Finpartition (univ : Finset V), ∑ σ : L → Perm (Fin N),
        (univ.filter fun f : V → Fin N => GHom lam tl hd σ f ∧ KerIs Q P f).card := sum_comm
    _ = ∑ P ∈ (univ : Finset (Finpartition (univ : Finset V))).filter
          (fun P => Le P Q ∧ GFF lam tl hd P),
        ∑ σ : L → Perm (Fin N),
        (univ.filter fun f : V → Fin N => GHom lam tl hd σ f ∧ KerIs Q P f).card := by
        rw [sum_filter]
        refine sum_congr rfl fun P _ => ?_
        split_ifs with hP
        · rfl
        · apply sum_eq_zero; intro σ _
          rw [card_eq_zero, filter_eq_empty_iff]
          rintro f - ⟨hf, hk⟩
          exact hP ⟨kerIs_le Q hk, ff_of_hom lam tl hd Q h1 hf hk⟩
    _ = _ := by
        refine sum_congr rfl fun P hP => ?_
        obtain ⟨hle, hP⟩ := (mem_filter.1 hP).2
        have h3 : ∀ σ : L → Perm (Fin N),
            (univ.filter fun f : V → Fin N => GHom lam tl hd σ f ∧ KerIs Q P f).card =
              ∑ g ∈ univ.filter (fun g : P.parts → Fin N => FibInj Q P g),
                if Compat lam tl hd P σ g then 1 else 0 := fun σ => by
          rw [card_hom_kerIs lam tl hd Q P hle σ, ← filter_filter, card_filter]
        simp_rw [h3]
        rw [sum_comm]
        rw [sum_congr rfl (fun g hg => by
          rw [← card_filter, card_compat lam tl hd Q hle h1 hP g (mem_filter.1 hg).2]),
          sum_const, smul_eq_mul, card_fibInj]

theorem sum_card_fib (P : Finpartition (univ : Finset V)) :
    ∑ B : Q.parts, Fintype.card {A : P.parts // cc Q P A = B} = P.parts.card := by
  rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv (cc Q P)), Fintype.card_coe]

theorem card_fib_eq {P : Finpartition (univ : Finset V)} (hle : Le P Q) (B : Q.parts) :
    Fintype.card {A : P.parts // cc Q P A = B} = (P.parts.filter (· ⊆ B.1)).card := by
  rw [Fintype.card_subtype]
  refine card_bij (fun A _ => A.1) ?_ ?_ ?_
  · intro A hA
    have hA' : Q.part (rep P A) = B.1 := congrArg Subtype.val (mem_filter.1 hA).2
    refine mem_filter.2 ⟨A.2, ?_⟩
    have h2 : P.part (rep P A) = A.1 := congrArg Subtype.val (blk_rep P A)
    rw [← hA', ← h2]
    exact sub_of_le Q hle _
  · intro A _ A' _ h
    exact Subtype.ext h
  · intro A hA
    obtain ⟨hA1, hA2⟩ := mem_filter.1 hA
    refine ⟨⟨A, hA1⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    exact Subtype.ext (Q.part_eq_of_mem B.2 (hA2 (rep_mem P ⟨A, hA1⟩)))

end Puder.PP.PartE
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartE
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
/-! ## The real-number form of a term -/
theorem descFactorial_eq_real (N k : ℕ) (hN : 0 < N) :
    (N.descFactorial k : ℝ) = (N : ℝ) ^ k * ∏ i ∈ range k, (1 - (i : ℝ) * (1 / N)) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, prod_range_succ]
    by_cases hk : k ≤ N
    · rw [Nat.cast_mul, Nat.cast_sub hk, ih]
      field_simp
      ring
    · have h0 : N.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at ih
      rcases ih with ih | ih
      · exact absurd (pow_eq_zero_iff'.1 ih).1 hN'
      · rw [h0, ih]; simp

theorem term_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (N : ℕ) (hN : 0 < N) (v : ι → ℕ)
    (e : κ → ℕ) (he : ∀ j, e j ≤ N) :
    (((∏ b, N.descFactorial (v b)) * ∏ j, (N - e j).factorial : ℕ) : ℝ) /
        ((N.factorial : ℝ) ^ Fintype.card κ) =
      ((1 : ℝ) / N) ^ (((∑ j, e j : ℕ) : ℤ) - ((∑ b, v b : ℕ) : ℤ)) *
        (∏ b, ∏ i ∈ range (v b), (1 - (i : ℝ) * (1 / N))) /
        ∏ j, ∏ i ∈ range (e j), (1 - (i : ℝ) * (1 / N)) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hQ : ∀ j, ∏ i ∈ range (e j), (1 - (i : ℝ) * (1 / N)) ≠ 0 := by
    intro j
    refine prod_ne_zero_iff.2 fun i hi => ?_
    have h1 : (i : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (mem_range.1 hi) (he j)
    have h2 : (i : ℝ) * (1 / N) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; exact h1
    linarith
  have hfac : ((N.factorial : ℝ)) ^ Fintype.card κ =
      ∏ j, ((N - e j).factorial : ℝ) * (N.descFactorial (e j) : ℝ) := by
    rw [← Finset.card_univ, ← prod_const]
    refine prod_congr rfl fun j _ => ?_
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial (he j)]
  have hfpos : ∀ j, ((N - e j).factorial : ℝ) ≠ 0 := fun j => by positivity
  rw [hfac, prod_mul_distrib, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]
  simp_rw [descFactorial_eq_real N _ hN]
  rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum,
    zpow_sub₀ (by simpa using hN'), zpow_natCast, zpow_natCast, one_div_pow, one_div_pow]
  have h1 : ∏ j, ((N - e j).factorial : ℝ) ≠ 0 := prod_ne_zero_iff.2 fun j _ => hfpos j
  have h2 : ∏ j, ∏ i ∈ range (e j), (1 - (i : ℝ) * (1 / N)) ≠ 0 :=
    prod_ne_zero_iff.2 fun j _ => hQ j
  field_simp

end Puder.PP.PartE
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartE
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {d N : ℕ}
/-! ## Fixed points of a word as closed walks -/
/-- The permutation by which a letter moves a walk one step forward. -/
def rho (σ : Fin d → Perm (Fin N)) (x : Fin d × Bool) : Perm (Fin N) :=
  if x.2 then σ x.1 else (σ x.1)⁻¹

/-- The walk product of the first `p` letters (first letter applied first). -/
def pre (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (p : ℕ) : Perm (Fin N) :=
  ((K.take p).map (rho σ)).reverse.prod

theorem pre_zero (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) : pre σ K 0 = 1 := by
  simp [pre]

theorem pre_succ (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (p : ℕ)
    (hp : p < K.length) : pre σ K (p + 1) = rho σ K[p] * pre σ K p := by
  rw [pre, pre, List.take_add_one, List.getElem?_eq_getElem hp]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]

theorem step_iff (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (h : Fin K.length → Fin N)
    (p : Fin K.length) :
    σ (lab K p) (h (tl K p)) = h (hd K p) ↔ h (cnxt p) = rho σ K[p] (h p) := by
  unfold rho tl hd lab
  by_cases hb : (K[p]).2 = true
  · rw [if_pos hb, if_pos hb, if_pos hb, eq_comm]
  · rw [if_neg hb, if_neg hb, if_neg hb, Perm.eq_inv_iff_eq]

theorem card_cycle (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (hn : 0 < K.length) :
    (univ.filter (GHom (lab K) (tl K) (hd K) σ)).card =
      (univ.filter fun y : Fin N => pre σ K K.length y = y).card := by
  have hfw : ∀ h : Fin K.length → Fin N, GHom (lab K) (tl K) (hd K) σ h →
      ∀ k (hk : k < K.length), h ⟨k, hk⟩ = pre σ K k (h ⟨0, hn⟩) := by
    intro h hs k
    induction k with
    | zero => intro hk; simp [pre_zero]
    | succ k ih =>
      intro hk
      have h1 := (step_iff σ K h ⟨k, by omega⟩).1 (hs _)
      have h2 : cnxt (⟨k, by omega⟩ : Fin K.length) = ⟨k + 1, hk⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hk)
      rw [h2] at h1
      rw [h1, ih (by omega), pre_succ σ K k (by omega), Perm.mul_apply]
      rfl
  obtain ⟨m, hm⟩ : ∃ m, K.length = m + 1 := ⟨K.length - 1, by omega⟩
  have hclose : ∀ h : Fin K.length → Fin N, GHom (lab K) (tl K) (hd K) σ h →
      pre σ K K.length (h ⟨0, hn⟩) = h ⟨0, hn⟩ := by
    intro h hs
    have h1 := (step_iff σ K h ⟨m, by omega⟩).1 (hs _)
    have h2 : cnxt (⟨m, by omega⟩ : Fin K.length) = ⟨0, hn⟩ :=
      Fin.ext (by simp only [cnxt]; rw [← hm, Nat.mod_self])
    rw [h2] at h1
    have h3 := hfw h hs m (by omega)
    rw [congrArg (pre σ K) hm, pre_succ σ K m (by omega), Perm.mul_apply, ← h3, h1]
    rfl
  refine card_bij' (fun h _ => h ⟨0, hn⟩) (fun y _ => fun p => pre σ K p y) ?_ ?_ ?_ ?_
  · intro h hh
    exact mem_filter.2 ⟨mem_univ _, hclose h (mem_filter.1 hh).2⟩
  · intro y hy
    have hy := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, fun p => (step_iff σ K (fun p : Fin K.length => pre σ K p y) p).2 ?_⟩
    by_cases hp : (p : ℕ) + 1 < K.length
    · have h2 : cnxt p = ⟨(p : ℕ) + 1, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
      rw [h2]
      show pre σ K ((p : ℕ) + 1) y = _
      rw [pre_succ σ K p p.2, Perm.mul_apply]
      rfl
    · have hp' : (p : ℕ) + 1 = K.length := by omega
      have h2 : cnxt p = ⟨0, hn⟩ := Fin.ext (by simp only [cnxt]; rw [hp', Nat.mod_self])
      rw [h2]
      show pre σ K 0 y = _
      rw [pre_zero, Perm.one_apply]
      conv_lhs => rw [← hy, ← hp']
      rw [pre_succ σ K p p.2, Perm.mul_apply]
      rfl
  · intro h hh
    funext p
    exact (hfw h (mem_filter.1 hh).2 p p.2).symm
  · intro y _
    simp [pre_zero]

theorem lift_inv_mk (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) :
    FreeGroup.lift σ⁻¹ (FreeGroup.mk K) = (pre σ K K.length)⁻¹ := by
  rw [FreeGroup.lift_mk, pre, List.take_length, List.prod_inv_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rcases x with ⟨i, b⟩
  cases b <;> simp [rho]

theorem card_fix_inv (W : Perm (Fin N)) :
    (univ.filter fun y : Fin N => W⁻¹ y = y).card = (univ.filter fun y : Fin N => W y = y).card := by
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and]
  rw [Perm.inv_eq_iff_eq, eq_comm]

theorem fix_card (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (hn : 0 < K.length) :
    (univ.filter fun x : Fin N => FreeGroup.lift σ⁻¹ (FreeGroup.mk K) x = x).card =
      (univ.filter (GHom (lab K) (tl K) (hd K) σ)).card := by
  rw [lift_inv_mk, card_fix_inv, card_cycle σ K hn]

end Puder.PP.PartE
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartE
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {d : ℕ}
/-! ## The cycle of `K` -/
theorem top_part (K : List (Fin d × Bool)) (x : Fin K.length) :
    (⊤ : Part K).part x = univ := by
  have hne : (univ : Finset (Fin K.length)) ≠ ⊥ := Finset.ne_empty_of_mem (mem_univ x)
  have h : Finpartition.indiscrete hne ≤ ⊤ := le_top
  obtain ⟨c, hc, hle⟩ := h (show univ ∈ (Finpartition.indiscrete hne).parts from
    Finset.mem_singleton_self _)
  have hcu : c = univ := Finset.univ_subset_iff.1 hle
  exact Finpartition.part_eq_of_mem _ (hcu ▸ hc) (mem_univ x)

/-- `QE` in terms of `qedge`, when the labelling refines the generators. -/
theorem qe_eq (K : List (Fin d × Bool)) (Q' : Part K) {L : Type*} [DecidableEq L]
    (lam : Fin K.length → L)
    (h0 : ∀ p q, lam p = lam q → lab K p = lab K q) (l : L) :
    QE lam (tl K) (hd K) Q' l = ((univ.filter fun p => lam p = l).image (qedge K Q')).card := by
  unfold QE
  rcases (univ.filter fun p => lam p = l).eq_empty_or_nonempty with h | ⟨p0, hp0⟩
  · rw [h]; rfl
  · have : (univ.filter fun p => lam p = l).image (qedge K Q') =
        ((univ.filter fun p => lam p = l).image
          fun e => (Q'.part (tl K e), Q'.part (hd K e))).image (fun x => (lab K p0, x)) := by
      rw [image_image]
      refine image_congr fun p hp => ?_
      have := h0 p p0 ((mem_filter.1 hp).2.trans (mem_filter.1 hp0).2.symm)
      simp [qedge, this]
    rw [this, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]

theorem sum_qe (K : List (Fin d × Bool)) (Q' : Part K) {L : Type*} [Fintype L] [DecidableEq L]
    (lam : Fin K.length → L)
    (h2 : ∀ p q, qedge K Q' p = qedge K Q' q → lam p = lam q) :
    ∑ l, ((univ.filter fun p => lam p = l).image (qedge K Q')).card = (E K Q').card := by
  rw [← card_biUnion]
  · congr 1
    ext ε
    simp only [E, mem_biUnion, mem_univ, true_and, mem_image, mem_filter]
    constructor
    · rintro ⟨l, p, -, hp⟩; exact ⟨p, hp⟩
    · rintro ⟨p, hp⟩; exact ⟨lam p, p, rfl, hp⟩
  · intro l _ l' _ hne
    rw [Function.onFun, disjoint_left]
    intro ε h h'
    obtain ⟨p, hp, rfl⟩ := mem_image.1 h
    obtain ⟨q, hq, hqp⟩ := mem_image.1 h'
    exact hne ((mem_filter.1 hp).2.symm.trans ((h2 q p hqp).symm.trans (mem_filter.1 hq).2))

/-- Assembling `Lx` from the generic term. -/
theorem lx_eq (K : List (Fin d × Bool)) (Q' Q : Part K) (hle : Le Q' Q) {L : Type*} [Fintype L]
    (e : L → ℕ) (x : ℝ) (hsum : ∑ l, e l = (E K Q').card)
    (hprod : ∏ l, ∏ i ∈ range (e l), (1 - (i : ℝ) * x) =
      ∏ ε ∈ E K Q, ∏ i ∈ range (efib K Q' Q ε), (1 - (i : ℝ) * x)) :
    x ^ (((∑ l, e l : ℕ) : ℤ) -
          ((∑ B : Q.parts, Fintype.card {A : Q'.parts // cc Q Q' A = B} : ℕ) : ℤ)) *
        (∏ B : Q.parts, ∏ i ∈ range (Fintype.card {A : Q'.parts // cc Q Q' A = B}),
          (1 - (i : ℝ) * x)) /
        (∏ l, ∏ i ∈ range (e l), (1 - (i : ℝ) * x)) = Lx K Q' Q x := by
  rw [hprod, hsum, sum_card_fib]
  unfold Lx
  congr 2
  simp_rw [card_fib_eq Q hle]
  exact Finset.prod_coe_sort Q.parts
    (fun B => ∏ i ∈ range (vfib K Q' B), (1 - (i : ℝ) * x))

theorem card_perms {L : Type*} [Fintype L] [DecidableEq L] (N : ℕ) :
    (Fintype.card (L → Perm (Fin N)) : ℝ) = (N.factorial : ℝ) ^ Fintype.card L := by
  rw [Fintype.card_pi, prod_const, card_univ, Fintype.card_perm, Fintype.card_fin, Nat.cast_pow]

theorem psi_eq_sum (K : List (Fin d × Bool)) (hK : K ≠ []) (Q : Part K) (hQ : FF K Q) (N : ℕ)
    (hN : K.length ≤ N) :
    Psi K Q N = ∑ Q' ∈ (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ Q),
      Lx K Q' Q (1 / N) := by
  have hn : 0 < K.length := List.length_pos_iff.2 hK
  have hN0 : 0 < N := lt_of_lt_of_le hn hN
  let lam : Fin K.length → {ε // ε ∈ E K Q} := fun p =>
    ⟨qedge K Q p, Finset.mem_image_of_mem _ (Finset.mem_univ p)⟩
  have hlam : ∀ p q, lam p = lam q ↔ qedge K Q p = qedge K Q q := fun p q => Subtype.ext_iff
  have h1 : H1 lam (tl K) (hd K) Q := by
    intro e e' h
    have := (hlam e e').1 h
    simp only [qedge, Prod.mk.injEq] at this
    exact this.2
  have h0 : ∀ p q, lam p = lam q → lab K p = lab K q := by
    intro p q h
    have := (hlam p q).1 h
    simp only [qedge, Prod.mk.injEq] at this
    exact this.1
  have hmain := sum_card_hom (N := N) lam (tl K) (hd K) Q h1
  have hL : Psi K Q N = ((∑ σ : {ε // ε ∈ E K Q} → Perm (Fin N),
      (univ.filter (GHom lam (tl K) (hd K) σ)).card : ℕ) : ℝ) /
        (Fintype.card ({ε // ε ∈ E K Q} → Perm (Fin N)) : ℝ) := by
    unfold Psi StrongConv.uniformExp
    rw [Nat.cast_sum]
    congr 1
    refine sum_congr rfl fun σ _ => ?_
    exact congrArg Nat.cast (congrArg Finset.card (by
      ext f; simp only [mem_filter, mem_univ, true_and]; exact Iff.rfl))
  rw [hL, hmain, Nat.cast_sum, sum_div, card_perms]
  have hfilt : (univ : Finset (Part K)).filter (fun P => Le P Q ∧ GFF lam (tl K) (hd K) P) =
      (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ Q) := by
    ext P
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hle, hff⟩
      refine ⟨fun e e' hl => ?_, (le_iff P Q).2 hle⟩
      constructor
      · intro ht
        have h3 : qedge K Q e = qedge K Q e' := by
          have h4 := hle _ _ ht
          simp only [qedge, Prod.mk.injEq]
          exact ⟨hl, h4, (hQ e e' hl).1 h4⟩
        exact (hff e e' ((hlam e e').2 h3)).1 ht
      · intro hh
        have h3 : qedge K Q e = qedge K Q e' := by
          have h4 := hle _ _ hh
          simp only [qedge, Prod.mk.injEq]
          exact ⟨hl, (hQ e e' hl).2 h4, h4⟩
        exact (hff e e' ((hlam e e').2 h3)).2 hh
    · rintro ⟨hff, hle⟩
      exact ⟨(le_iff P Q).1 hle, fun e e' hl => hff e e' (h0 e e' hl)⟩
  rw [hfilt]
  refine sum_congr rfl fun P hP => ?_
  have hle : Le P Q := (le_iff P Q).1 (mem_filter.1 hP).2.2
  rw [term_eq N hN0 _ _ (fun l => (QE_le lam (tl K) (hd K) P l).trans
    (by rw [Fintype.card_fin]; exact hN))]
  refine lx_eq K P Q hle _ _ ?_ ?_
  · simp_rw [qe_eq K P lam h0]
    refine sum_qe K P lam fun p q h => (hlam p q).2 ?_
    simp only [qedge, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, hle _ _ h.2.1, hle _ _ h.2.2⟩
  · have h5 : ∀ l : {ε // ε ∈ E K Q}, QE lam (tl K) (hd K) P l = efib K P Q l.1 := by
      intro l
      rw [qe_eq K P lam h0]
      unfold efib
      congr 2
      ext p
      simp only [mem_filter, mem_univ, true_and]
      exact Subtype.ext_iff
    simp_rw [h5]
    exact Finset.prod_coe_sort (E K Q)
      (fun ε => ∏ i ∈ range (efib K P Q ε), (1 - (i : ℝ) * (1 / N)))

theorem fix_eq_sum (K : List (Fin d × Bool)) (hK : K ≠ []) (N : ℕ) (hN : K.length ≤ N) :
    Fix (FreeGroup.mk K) N = ∑ Q' ∈ (univ : Finset (Part K)).filter (FF K), Lx K Q' ⊤ (1 / N) := by
  have hn : 0 < K.length := List.length_pos_iff.2 hK
  have hN0 : 0 < N := lt_of_lt_of_le hn hN
  have h1 : H1 (lab K) (tl K) (hd K) (⊤ : Part K) := by
    intro e e' _
    simp only [top_part, and_self]
  have hmain := sum_card_hom (N := N) (lab K) (tl K) (hd K) (⊤ : Part K) h1
  have hL : Fix (FreeGroup.mk K) N = ((∑ σ : Fin d → Perm (Fin N),
      (univ.filter (GHom (lab K) (tl K) (hd K) σ)).card : ℕ) : ℝ) /
        (Fintype.card (Fin d → Perm (Fin N)) : ℝ) := by
    unfold Fix StrongConv.uniformExp
    rw [← Equiv.sum_comp (Equiv.inv (Fin d → Perm (Fin N))), Nat.cast_sum]
    congr 1
    refine sum_congr rfl fun σ _ => ?_
    exact congrArg Nat.cast (fix_card σ K hn)
  rw [hL, hmain, Nat.cast_sum, sum_div, card_perms]
  have hfilt : (univ : Finset (Part K)).filter
      (fun P => Le P (⊤ : Part K) ∧ GFF (lab K) (tl K) (hd K) P) =
      (univ : Finset (Part K)).filter (FF K) := by
    ext P
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨(le_iff P ⊤).1 le_top, h⟩⟩
  rw [hfilt]
  refine sum_congr rfl fun P hP => ?_
  have hle : Le P (⊤ : Part K) := (le_iff P ⊤).1 le_top
  rw [term_eq N hN0 _ _ (fun l => (QE_le (lab K) (tl K) (hd K) P l).trans
    (by rw [Fintype.card_fin]; exact hN))]
  have h0 : ∀ p q, lab K p = lab K q → lab K p = lab K q := fun _ _ h => h
  have h5 : ∀ j : Fin d, QE (lab K) (tl K) (hd K) P j = efib K P ⊤ (j, univ, univ) := by
    intro j
    rw [qe_eq K P (lab K) h0]
    unfold efib
    congr 2
    ext p
    simp [qedge, top_part]
  refine lx_eq K P ⊤ hle _ _ ?_ ?_
  · simp_rw [qe_eq K P (lab K) h0]
    refine sum_qe K P (lab K) fun p q h => ?_
    simp only [qedge, Prod.mk.injEq] at h
    exact h.1
  · have hE : E K (⊤ : Part K) =
        (univ.image (lab K)).image (fun j => (j, (univ : Finset (Fin K.length)),
          (univ : Finset (Fin K.length)))) := by
      rw [image_image]
      refine image_congr fun p _ => ?_
      simp [qedge, top_part]
    rw [hE, prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    simp_rw [h5]
    symm
    refine prod_subset (subset_univ _) fun j _ hj => ?_
    have : efib K P ⊤ (j, univ, univ) = 0 := by
      rw [← h5, qe_eq K P (lab K) h0, card_eq_zero, image_eq_empty, filter_eq_empty_iff]
      intro p _ hp
      exact hj (mem_image.2 ⟨p, mem_univ _, hp⟩)
    rw [this, range_zero, prod_empty]

end Puder.PP.PartE
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-!
# Blueprint: Puder–Parzanchevski Theorem 1.8 and Puder's §5.5 coefficient bound

Every `sorry` below is a stub proved in a Part file `M34Part<X>.lean` under
`namespace Puder.PP.Part<X>` with the statement copied verbatim. See PLAN.md for the mathematics.
-/
/-! ## Part E: the two expansions (PP15 Lemmas 6.2–6.4; Hanany–Puder §6.1) -/
alias fix_eq_sum := Puder.PP.PartE.fix_eq_sum

alias psi_eq_sum := Puder.PP.PartE.psi_eq_sum

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
variable {K : List (Fin d × Bool)}
/-!
# Part X: the exploration of a quotient of the cycle (`ex_card`, `ex_gen`, `ff_bot`, `ex_pos`)
-/
theorem mem_part (P : Part K) (a b : Fin K.length) : a ∈ P.part b ↔ P.part a = P.part b :=
  P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)

theorem first_mem (P : Part K) (p : Fin K.length) : first K P p ∈ P.part p :=
  Finset.min'_mem _ _

theorem part_first (P : Part K) (p : Fin K.length) : P.part (first K P p) = P.part p :=
  (mem_part P _ _).1 (first_mem P p)

theorem first_le (P : Part K) {p q : Fin K.length} (h : P.part q = P.part p) :
    first K P p ≤ q :=
  Finset.min'_le _ _ ((mem_part P _ _).2 h)

theorem first_congr (P : Part K) {p q : Fin K.length} (h : P.part p = P.part q) :
    first K P p = first K P q :=
  le_antisymm (first_le P ((part_first P q).trans h.symm)) (first_le P ((part_first P p).trans h))

theorem first_zero (P : Part K) (h : 0 < K.length) : first K P ⟨0, h⟩ = ⟨0, h⟩ :=
  Fin.ext (Nat.le_zero.1 (first_le P (rfl : P.part ⟨0, h⟩ = P.part ⟨0, h⟩)))

theorem cnxt_val_of_lt {n : ℕ} {p : Fin n} (h : (p : ℕ) + 1 < n) : ((cnxt p : Fin n) : ℕ) = p + 1 :=
  Nat.mod_eq_of_lt h

theorem cnxt_val_of_eq {n : ℕ} {p : Fin n} (h : (p : ℕ) + 1 = n) : ((cnxt p : Fin n) : ℕ) = 0 := by
  show ((p : ℕ) + 1) % n = 0
  rw [h, Nat.mod_self]

theorem cnxt_inj {n : ℕ} {p q : Fin n} (h : cnxt p = cnxt q) : p = q := by
  have h' := congrArg Fin.val h
  have hp := p.2
  have hq := q.2
  by_cases h1 : (p : ℕ) + 1 < n <;> by_cases h2 : (q : ℕ) + 1 < n
  · rw [cnxt_val_of_lt h1, cnxt_val_of_lt h2] at h'
    exact Fin.ext (by omega)
  · rw [cnxt_val_of_lt h1, cnxt_val_of_eq (by omega)] at h'
    omega
  · rw [cnxt_val_of_eq (by omega), cnxt_val_of_lt h2] at h'
    omega
  · exact Fin.ext (by omega)

theorem tl_hd_cases (K : List (Fin d × Bool)) (p : Fin K.length) :
    ((K[p]).2 = true ∧ tl K p = p ∧ hd K p = cnxt p) ∨
      ((K[p]).2 = false ∧ tl K p = cnxt p ∧ hd K p = p) := by
  unfold tl hd
  rcases Bool.eq_false_or_eq_true (K[p]).2 with h | h
  · left
    exact ⟨h, if_pos h, if_pos h⟩
  · right
    exact ⟨h, if_neg (by rw [h]; simp), if_neg (by rw [h]; simp)⟩

theorem pfx_succ (K : List (Fin d × Bool)) (p : Fin K.length) :
    pfx K ((p : ℕ) + 1) =
      pfx K p * (if (K[p]).2 then FreeGroup.of (lab K p) else (FreeGroup.of (lab K p))⁻¹) := by
  have h1 : K.take ((p : ℕ) + 1) = K.take p ++ [K[p]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem p.2]
    rfl
  unfold pfx
  rw [h1, ← FreeGroup.mul_mk]
  congr 1
  have h2 : K[p] = ((K[p]).1, (K[p]).2) := rfl
  rw [h2]
  rcases Bool.eq_false_or_eq_true (K[p]).2 with h | h
  · rw [h]
    rfl
  · rw [h]
    simp only [Bool.false_eq_true, if_false]
    rfl

/-- The prefix at the tail of the edge at `p`. -/
def Tg (K : List (Fin d × Bool)) (p : Fin K.length) : FreeGroup (Fin d) :=
  if (K[p]).2 then pfx K p else pfx K ((p : ℕ) + 1)

/-- The prefix at the head of the edge at `p`. -/
def Hg (K : List (Fin d × Bool)) (p : Fin K.length) : FreeGroup (Fin d) :=
  if (K[p]).2 then pfx K ((p : ℕ) + 1) else pfx K p

theorem Hg_eq (K : List (Fin d × Bool)) (p : Fin K.length) :
    Hg K p = Tg K p * FreeGroup.of (lab K p) := by
  unfold Hg Tg
  rw [pfx_succ]
  rcases Bool.eq_false_or_eq_true (K[p]).2 with h | h
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, inv_mul_cancel_right]

/-- The walk to the tail of edge `p` and back along the first position of its block. -/
def Xt (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : FreeGroup (Fin d) :=
  Tg K p * (pfx K (first K P (tl K p)))⁻¹

/-- The walk to the head of edge `p` and back along the first position of its block. -/
def Xh (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : FreeGroup (Fin d) :=
  Hg K p * (pfx K (first K P (hd K p)))⁻¹

/-- The walk to position `p` and back along the first position of its block. -/
def Xlo (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) : FreeGroup (Fin d) :=
  pfx K p * (pfx K (first K P p))⁻¹

theorem key (P : Part K) {p q : Fin K.length} (h : qedge K P p = qedge K P q) :
    (Xt K P p)⁻¹ * Xh K P p = (Xt K P q)⁻¹ * Xh K P q := by
  simp only [qedge, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold Xt Xh
  rw [Hg_eq, Hg_eq, first_congr P h2, first_congr P h3, h1]
  group

theorem Xt_Xh_cases (P : Part K) (p : Fin K.length) :
    ((K[p]).2 = true ∧ Xt K P p = Xlo K P p ∧ Xh K P p = gam K P p) ∨
      ((K[p]).2 = false ∧ Xt K P p = gam K P p ∧ Xh K P p = Xlo K P p) := by
  rcases Bool.eq_false_or_eq_true (K[p]).2 with h | h
  · left
    refine ⟨h, ?_, ?_⟩
    · simp only [Xt, Xlo, Tg, tl, h, ↓reduceIte]
    · simp only [Xh, gam, Hg, hd, h, ↓reduceIte]
  · right
    refine ⟨h, ?_, ?_⟩
    · simp only [Xt, gam, Tg, tl, h, Bool.false_eq_true, ↓reduceIte]
    · simp only [Xh, Xlo, Hg, hd, h, Bool.false_eq_true, ↓reduceIte]

/-! ## Counting -/
theorem card_new (P : Part K) : (univ.filter (New K P)).card = (E K P).card := by
  unfold E
  rw [← Finset.card_image_of_injOn (f := qedge K P)]
  · congr 1
    ext e
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨p, -, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image
        (univ.filter fun q => qedge K P q = qedge K P p) (fun q => q) ⟨p, by simp⟩
      have hq' := (mem_filter.1 hq).2
      refine ⟨q, ?_, hq'⟩
      intro r hr hrq
      have := hmin r (by simp [hrq.trans hq'])
      exact absurd hr (not_lt.2 this)
  · intro p hp q hq h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact hq p h1 h
    · exact hp q h1 h.symm

theorem disc_new (P : Part K) {p : Fin K.length} (hD : Disc K P p) : New K P p := by
  intro q hq he
  simp only [qedge, Prod.mk.injEq] at he
  obtain ⟨-, h2, h3⟩ := he
  have hqp : (q : ℕ) < p := hq
  have hc : ((cnxt q : Fin K.length) : ℕ) = q + 1 := cnxt_val_of_lt (by omega)
  have hc' : ((cnxt q : Fin K.length) : ℕ) ≤ p := by omega
  rcases tl_hd_cases K p with ⟨-, ht, hh⟩ | ⟨-, ht, hh⟩ <;>
    rcases tl_hd_cases K q with ⟨-, ht', hh'⟩ | ⟨-, ht', hh'⟩ <;>
    rw [ht, ht'] at h2 <;> rw [hh, hh'] at h3
  · exact hD.2 _ hc' h3
  · exact hD.2 _ hqp.le h3
  · exact hD.2 _ hqp.le h2
  · exact hD.2 _ hc' h2

theorem disc_iff (P : Part K) (p : Fin K.length) :
    Disc K P p ↔ (p : ℕ) + 1 < K.length ∧ first K P (cnxt p) = cnxt p := by
  constructor
  · intro hD
    refine ⟨hD.1, le_antisymm (first_le P rfl) ?_⟩
    by_contra hlt
    have hlt' : ((first K P (cnxt p) : Fin K.length) : ℕ) < (cnxt p : Fin K.length) :=
      not_le.1 hlt
    rw [cnxt_val_of_lt hD.1] at hlt'
    exact hD.2 _ (by omega) (part_first P _)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun q hq he => ?_⟩
    have h3 : ((first K P (cnxt p) : Fin K.length) : ℕ) ≤ q := first_le P he
    rw [h2, cnxt_val_of_lt h1] at h3
    omega

theorem card_min (P : Part K) :
    (univ.filter fun j => first K P j = j).card = P.parts.card := by
  rw [← Finset.card_image_of_injOn (f := P.part)]
  · congr 1
    ext t
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, -, rfl⟩
      exact P.part_mem.2 (mem_univ _)
    · intro ht
      obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts ht
      have h1 : P.part a = t := P.part_eq_of_mem ht ha
      exact ⟨first K P a, first_congr P (part_first P a), (part_first P a).trans h1⟩
  · intro j hj j' hj' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
    rw [← hj, ← hj']
    exact first_congr P h

theorem card_disc (P : Part K) (hn : 0 < K.length) :
    (univ.filter (Disc K P)).card + 1 = P.parts.card := by
  rw [← card_min P]
  have h0 : (⟨0, hn⟩ : Fin K.length) ∈ univ.filter fun j => first K P j = j := by
    simp [first_zero]
  have himg : (univ.filter (Disc K P)).image cnxt =
      (univ.filter fun j => first K P j = j).erase ⟨0, hn⟩ := by
    ext j
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [disc_iff] at hp
      refine ⟨fun h => ?_, hp.2⟩
      have := congrArg Fin.val h
      rw [cnxt_val_of_lt hp.1] at this
      simp at this
    · rintro ⟨hj0, hj⟩
      have hjpos : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
      have hjl := j.2
      have hpl : (j : ℕ) - 1 + 1 < K.length := by omega
      have hc : cnxt (⟨(j : ℕ) - 1, by omega⟩ : Fin K.length) = j := by
        apply Fin.ext
        rw [cnxt_val_of_lt hpl]
        show (j : ℕ) - 1 + 1 = j
        omega
      refine ⟨⟨(j : ℕ) - 1, by omega⟩, ?_, hc⟩
      rw [disc_iff, hc]
      exact ⟨hpl, hj⟩
  have hcard : ((univ.filter (Disc K P)).image cnxt).card = (univ.filter (Disc K P)).card :=
    Finset.card_image_of_injective _ fun _ _ h => cnxt_inj h
  rw [← hcard, himg, Finset.card_erase_of_mem h0]
  have := Finset.card_pos.2 ⟨_, h0⟩
  omega

theorem card_rec (P : Part K) :
    (univ.filter (Rec K P)).card + (univ.filter (Disc K P)).card = (univ.filter (New K P)).card := by
  have h1 : univ.filter (Rec K P) = (univ.filter (New K P)).filter fun p => ¬ Disc K P p := by
    ext p
    simp [Rec]
  have h2 : univ.filter (Disc K P) = (univ.filter (New K P)).filter fun p => Disc K P p := by
    ext p
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨disc_new P h, h⟩, fun h => h.2⟩
  rw [h1, h2, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-! ## Generators -/
theorem gam_last (P : Part K) {p : Fin K.length} (h : (p : ℕ) + 1 = K.length) :
    gam K P p = FreeGroup.mk K := by
  have hn : 0 < K.length := by omega
  have hc : cnxt p = ⟨0, hn⟩ := Fin.ext (cnxt_val_of_eq h)
  unfold gam
  rw [hc, first_zero, h]
  simp [pfx]

theorem gam_mem_J (P : Part K) (p : Fin K.length) : gam K P p ∈ J K P := by
  by_cases h : (p : ℕ) + 1 < K.length
  · refine Subgroup.subset_closure (Or.inr ⟨cnxt p, first K P (cnxt p), (part_first P _).symm, ?_⟩)
    unfold gam
    rw [cnxt_val_of_lt h]
  · have hp := p.2
    rw [gam_last P (by omega)]
    exact Subgroup.subset_closure (Or.inl rfl)

theorem Xlo_mem (P : Part K) (H : Subgroup (FreeGroup (Fin d))) (p : Fin K.length)
    (hih : ∀ q : Fin K.length, q < p → gam K P q ∈ H) (j : Fin K.length) (hj : j ≤ p) :
    Xlo K P j ∈ H := by
  have hjl := j.2
  by_cases h0 : (j : ℕ) = 0
  · have hn : 0 < K.length := by omega
    have : j = ⟨0, hn⟩ := Fin.ext h0
    rw [this]
    unfold Xlo
    rw [first_zero]
    simp
  · have hjp : (j : ℕ) ≤ p := hj
    have hpl : (j : ℕ) - 1 + 1 < K.length := by omega
    have hc : cnxt (⟨(j : ℕ) - 1, by omega⟩ : Fin K.length) = j := by
      apply Fin.ext
      rw [cnxt_val_of_lt hpl]
      show (j : ℕ) - 1 + 1 = j
      omega
    have hq := hih ⟨(j : ℕ) - 1, by omega⟩ (by
      show (j : ℕ) - 1 < p
      omega)
    have he : gam K P ⟨(j : ℕ) - 1, by omega⟩ = Xlo K P j := by
      unfold gam Xlo
      rw [hc]
      show pfx K ((j : ℕ) - 1 + 1) * _ = _
      rw [Nat.sub_add_cancel (by omega)]
    rwa [he] at hq

theorem gam_mem_H (P : Part K) (p : Fin K.length) :
    gam K P p ∈ Subgroup.closure (gam K P '' {p | Rec K P p}) := by
  induction p using WellFoundedLT.induction with
  | ind p ih =>
    by_cases hN : New K P p
    · by_cases hD : Disc K P p
      · rw [disc_iff] at hD
        unfold gam
        rw [hD.2, cnxt_val_of_lt hD.1, mul_inv_cancel]
        exact one_mem _
      · exact Subgroup.subset_closure ⟨p, ⟨hN, hD⟩, rfl⟩
    · unfold New at hN
      push Not at hN
      obtain ⟨q, hqp, he⟩ := hN
      have hk := key P he
      have hloq : Xlo K P q ∈ Subgroup.closure (gam K P '' {p | Rec K P p}) :=
        Xlo_mem P _ p ih q hqp.le
      have hlop : Xlo K P p ∈ Subgroup.closure (gam K P '' {p | Rec K P p}) :=
        Xlo_mem P _ p ih p le_rfl
      have hgq := ih q hqp
      have hmem : (Xt K P q)⁻¹ * Xh K P q ∈ Subgroup.closure (gam K P '' {p | Rec K P p}) := by
        rcases Xt_Xh_cases P q with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [h1, h2]
        · exact mul_mem (inv_mem hloq) hgq
        · exact mul_mem (inv_mem hgq) hloq
      rw [hk] at hmem
      rcases Xt_Xh_cases P p with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
      · have : gam K P p = Xt K P p * ((Xt K P p)⁻¹ * Xh K P p) := by
          rw [h2]
          group
        rw [this]
        exact mul_mem (h1 ▸ hlop) hmem
      · have : gam K P p = Xh K P p * ((Xt K P p)⁻¹ * Xh K P p)⁻¹ := by
          rw [h1]
          group
        rw [this]
        exact mul_mem (h2 ▸ hlop) (inv_mem hmem)

end Puder.PP.PartX
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
theorem ex_card (K : List (Fin d × Bool)) (hK : K ≠ []) (P : Part K) :
    (univ.filter (Rec K P)).card + P.parts.card = (E K P).card + 1 := by
  have h1 := card_rec P
  have h2 := card_disc P (List.length_pos_iff.2 hK)
  have h3 := card_new P
  omega

end Puder.PP.PartX
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part X: exploration of a quotient along the cycle -/
alias ex_card := Puder.PP.PartX.ex_card

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
theorem ex_gen (K : List (Fin d × Bool)) (hK : K ≠ []) (P : Part K) :
    J K P = Subgroup.closure (gam K P '' {p | Rec K P p}) := by
  have hn : 0 < K.length := List.length_pos_iff.2 hK
  apply le_antisymm
  · unfold J
    rw [Subgroup.closure_le]
    rintro g (hg | ⟨p, q, hpq, rfl⟩)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg, ← gam_last P (p := ⟨K.length - 1, by omega⟩) (by
        show K.length - 1 + 1 = K.length
        omega)]
      exact gam_mem_H P _
    · have h1 : Xlo K P p ∈ Subgroup.closure (gam K P '' {p | Rec K P p}) :=
        Xlo_mem P _ p (fun q _ => gam_mem_H P q) p le_rfl
      have h2 : Xlo K P q ∈ Subgroup.closure (gam K P '' {p | Rec K P p}) :=
        Xlo_mem P _ q (fun r _ => gam_mem_H P r) q le_rfl
      have : pfx K p * (pfx K q)⁻¹ = Xlo K P p * (Xlo K P q)⁻¹ := by
        unfold Xlo
        rw [first_congr P hpq]
        group
      rw [SetLike.mem_coe, this]
      exact mul_mem h1 (inv_mem h2)
  · rw [Subgroup.closure_le]
    rintro _ ⟨p, -, rfl⟩
    exact gam_mem_J P p

end Puder.PP.PartX
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias ex_gen := Puder.PP.PartX.ex_gen

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
/-! ## Cyclically reduced words -/
theorem getElem_fin_eq (K : List (Fin d × Bool)) (c : Fin K.length) (m : ℕ) (hm : m < K.length)
    (hc : (c : ℕ) = m) : K[c] = K[m] := by
  subst hc
  rfl

theorem adj {K : List (Fin d × Bool)} (hred : FreeGroup.IsCyclicallyReduced K)
    (p : Fin K.length) : (K[p]).1 = (K[cnxt p]).1 → (K[p]).2 = (K[cnxt p]).2 := by
  have hp := p.2
  by_cases h : (p : ℕ) + 1 < K.length
  · have h1 := List.isChain_iff_getElem.1 hred.1 p h
    rw [getElem_fin_eq K (cnxt p) _ h (cnxt_val_of_lt h)]
    exact h1
  · have hn : 0 < K.length := by omega
    rw [getElem_fin_eq K (cnxt p) _ hn (cnxt_val_of_eq (by omega))]
    have h1 : K[(p : ℕ)] ∈ K.getLast? := by
      rw [List.getLast?_eq_getElem?, Option.mem_def]
      have : K.length - 1 = p := by omega
      rw [this]
      exact List.getElem?_eq_getElem p.2
    have h2 : K[0] ∈ K.head? := by
      rw [List.head?_eq_getElem?, Option.mem_def]
      exact List.getElem?_eq_getElem hn
    exact hred.2 _ h1 _ h2

theorem part_bot (K : List (Fin d × Bool)) (p : Fin K.length) :
    (⊥ : Part K).part p = {p} :=
  Finpartition.part_eq_of_mem _ (Finpartition.mem_bot_iff.2 ⟨p, mem_univ _, rfl⟩)
    (mem_singleton_self p)

theorem bot_inj_tl {K : List (Fin d × Bool)} (hred : FreeGroup.IsCyclicallyReduced K)
    {e e' : Fin K.length} (hl : lab K e = lab K e') (h : tl K e = tl K e') : e = e' := by
  rcases tl_hd_cases K e with ⟨s, ht, -⟩ | ⟨s, ht, -⟩ <;>
    rcases tl_hd_cases K e' with ⟨s', ht', -⟩ | ⟨s', ht', -⟩ <;> rw [ht, ht'] at h
  · exact h
  · subst h
    have := adj hred e' hl.symm
    rw [s, s'] at this
    cases this
  · subst h
    have := adj hred e hl
    rw [s, s'] at this
    cases this
  · exact cnxt_inj h

theorem bot_inj_hd {K : List (Fin d × Bool)} (hred : FreeGroup.IsCyclicallyReduced K)
    {e e' : Fin K.length} (hl : lab K e = lab K e') (h : hd K e = hd K e') : e = e' := by
  rcases tl_hd_cases K e with ⟨s, -, ht⟩ | ⟨s, -, ht⟩ <;>
    rcases tl_hd_cases K e' with ⟨s', -, ht'⟩ | ⟨s', -, ht'⟩ <;> rw [ht, ht'] at h
  · exact cnxt_inj h
  · subst h
    have := adj hred e hl
    rw [s, s'] at this
    cases this
  · subst h
    have := adj hred e' hl.symm
    rw [s, s'] at this
    cases this
  · exact h

theorem ff_bot (K : List (Fin d × Bool)) (hK : K ≠ []) (hred : FreeGroup.IsCyclicallyReduced K) :
    FF K ⊥ ∧ (E K (⊥ : Part K)).card = K.length := by
  constructor
  · intro e e' hl
    simp only [part_bot, singleton_inj]
    constructor
    · intro h
      rw [bot_inj_tl hred hl h]
    · intro h
      rw [bot_inj_hd hred hl h]
  · unfold E
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro e e' h
    simp only [qedge, Prod.mk.injEq, part_bot, singleton_inj] at h
    exact bot_inj_tl hred h.1 h.2.1

/-- A cyclically reduced nonempty word has a record step in every quotient. -/
theorem rec_pos (K : List (Fin d × Bool)) (hK : K ≠ []) (hred : FreeGroup.IsCyclicallyReduced K)
    (P : Part K) : 0 < (univ.filter (Rec K P)).card := by
  by_contra h0
  have h1 : univ.filter (Rec K P) = ∅ := Finset.card_eq_zero.1 (by omega)
  have h2 : {p | Rec K P p} = (∅ : Set (Fin K.length)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    have : p ∈ univ.filter (Rec K P) := by simp [hp]
    rw [h1] at this
    simp at this
  have h3 : FreeGroup.mk K ∈ J K P := Subgroup.subset_closure (Or.inl rfl)
  rw [ex_gen K hK P, h2, Set.image_empty, Subgroup.closure_empty, Subgroup.mem_bot,
    FreeGroup.one_eq_mk] at h3
  have h4 := FreeGroup.reduce.sound h3
  rw [hred.1.reduce_eq] at h4
  exact hK (by simpa using h4)

/-- A cyclically reduced word has no quotient that is a tree. -/
theorem ex_pos (K : List (Fin d × Bool)) (hK : K ≠ []) (hred : FreeGroup.IsCyclicallyReduced K)
    (P : Part K) (hP : FF K P) : P.parts.card ≤ (E K P).card := by
  have h1 := ex_card K hK P
  have h2 := rec_pos K hK hred P
  omega

end Puder.PP.PartX
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias ex_pos := Puder.PP.PartX.ex_pos

alias ff_bot := Puder.PP.PartX.ff_bot

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
/-!
# Part X, continued: counting the fold-free quotients by rank (`ex_count`)
-/

end Puder.PP.PartX
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
variable {K : List (Fin d × Bool)}

end Puder.PP.PartX
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}

end Puder.PP.PartX
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartH
variable {d : ℕ}
/-!
# Part H: finitely generated free groups

Free groups are residually finite and (when finitely generated) Hopfian; rank is unique;
the stubs `h_basis_of_gen`, `h_fin_of_gen`, `h_free_subgroup`, `fg_a`, `fg_b`,
`isPrimitiveIn_zpowers`.
-/
/-! ## Residual finiteness and the Hopfian property -/
/-- A partial injection of a finite type, given as a relation, extends to a permutation. -/
theorem exists_perm_of_rel {V : Type*} [Finite V] (R : V → V → Prop)
    (hf : ∀ a b c, R a b → R a c → b = c) (hi : ∀ a b c, R a c → R b c → a = b) :
    ∃ σ : Equiv.Perm V, ∀ a b, R a b → σ a = b := by
  have := Fintype.ofFinite V
  have hbij : Function.Bijective (fun a : {a // ∃ b, R a b} =>
      (⟨a.2.choose, a.1, a.2.choose_spec⟩ : {b // ∃ a, R a b})) := by
    constructor
    · intro a a' h
      have h' : a.2.choose = a'.2.choose := congr_arg Subtype.val h
      apply Subtype.ext
      have h2 := a'.2.choose_spec
      rw [← h'] at h2
      exact hi _ _ _ a.2.choose_spec h2
    · rintro ⟨b, a, h⟩
      refine ⟨⟨a, b, h⟩, Subtype.ext ?_⟩
      exact hf a _ _ (Exists.choose_spec (⟨b, h⟩ : ∃ b, R a b)) h
  refine ⟨(Equiv.ofBijective _ hbij).extendSubtype, ?_⟩
  intro a b h
  rw [Equiv.extendSubtype_apply_of_mem _ a ⟨b, h⟩]
  exact hf a _ _ (Exists.choose_spec (⟨b, h⟩ : ∃ b, R a b)) h

/-- A word acts along a path: if each letter moves `v (i+1)` to `v i`, the word moves the end of
the path to its start. -/
theorem lift_path {α : Type*} {V : Type*} (f : α → Equiv.Perm V) (M : List (α × Bool)) (v : ℕ → V)
    (h : ∀ i (hi : i < M.length),
      (if M[i].2 = true then f M[i].1 else (f M[i].1)⁻¹) (v (i + 1)) = v i) :
    FreeGroup.lift f (FreeGroup.mk M) (v M.length) = v 0 := by
  induction M generalizing v with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons a M ih =>
    have h1 := ih (fun i => v (i + 1)) (fun i hi => by
      have h' := h (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at h'
      exact h')
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [show FreeGroup.mk (a :: M) = FreeGroup.mk [a] * FreeGroup.mk M from by
      rw [FreeGroup.mul_mk]; rfl]
    rw [map_mul, Equiv.Perm.mul_apply, List.length_cons, h1]
    rw [← h0]
    congr 1
    rcases a with ⟨x, b⟩
    cases b <;> simp [FreeGroup.lift_mk]

/-- Free groups are residually finite: a non-trivial element survives in some finite permutation
representation. -/
theorem exists_perm_rep {α : Type*} (g : FreeGroup α) (hg : g ≠ 1) :
    ∃ (n : ℕ) (π : FreeGroup α →* Equiv.Perm (Fin n)), π g ≠ 1 := by
  set L := g.toWord with hL
  set ℓ := L.length with hℓ
  have hgL : FreeGroup.mk L = g := FreeGroup.mk_toWord
  have hℓ0 : ℓ ≠ 0 := by
    intro h0
    apply hg
    rw [← hgL, List.length_eq_zero_iff.1 h0]
    rfl
  have hred : ∀ i (h : i + 1 < ℓ), L[i].1 = L[i + 1].1 → L[i].2 = L[i + 1].2 := by
    have hr : FreeGroup.IsReduced L := FreeGroup.isReduced_toWord
    unfold FreeGroup.IsReduced at hr
    rw [List.isChain_iff_getElem] at hr
    exact fun i h => hr i h
  let R : α → Fin (ℓ + 1) → Fin (ℓ + 1) → Prop := fun x a b =>
    ∃ i, ∃ hi : i < ℓ, L[i].1 = x ∧
      ((L[i].2 = true ∧ a.val = i + 1 ∧ b.val = i) ∨ (L[i].2 = false ∧ a.val = i ∧ b.val = i + 1))
  have hbad : ∀ i (h : i + 1 < ℓ), L[i].1 = L[i + 1].1 → L[i].2 = true → L[i + 1].2 = false →
      False := by
    intro i h h1 h2 h3
    have := hred i h h1
    rw [h2, h3] at this
    exact Bool.noConfusion this
  have hbad' : ∀ i (h : i + 1 < ℓ), L[i].1 = L[i + 1].1 → L[i].2 = false → L[i + 1].2 = true →
      False := by
    intro i h h1 h2 h3
    have := hred i h h1
    rw [h2, h3] at this
    exact Bool.noConfusion this
  have hRf : ∀ x a b c, R x a b → R x a c → b = c := by
    rintro x a b c ⟨i, hi, hx, h⟩ ⟨j, hj, hx', h'⟩
    apply Fin.ext
    rcases h with ⟨hb, ha, hb'⟩ | ⟨hb, ha, hb'⟩ <;> rcases h' with ⟨hc, ha', hc'⟩ | ⟨hc, ha', hc'⟩
    · omega
    · obtain rfl : j = i + 1 := by omega
      exact (hbad i hj (hx.trans hx'.symm) hb hc).elim
    · obtain rfl : i = j + 1 := by omega
      exact (hbad j hi (hx'.trans hx.symm) hc hb).elim
    · omega
  have hRi : ∀ x a b c, R x a c → R x b c → a = b := by
    rintro x a b c ⟨i, hi, hx, h⟩ ⟨j, hj, hx', h'⟩
    apply Fin.ext
    rcases h with ⟨hb, ha, hb'⟩ | ⟨hb, ha, hb'⟩ <;> rcases h' with ⟨hc, ha', hc'⟩ | ⟨hc, ha', hc'⟩
    · omega
    · obtain rfl : i = j + 1 := by omega
      exact (hbad' j hi (hx'.trans hx.symm) hc hb).elim
    · obtain rfl : j = i + 1 := by omega
      exact (hbad' i hj (hx.trans hx'.symm) hb hc).elim
    · omega
  choose f hf using fun x => exists_perm_of_rel (R x) (hRf x) (hRi x)
  let v : ℕ → Fin (ℓ + 1) := fun i => if h : i < ℓ + 1 then ⟨i, h⟩ else 0
  have hv : ∀ i, i < ℓ + 1 → (v i).val = i := by
    intro i hi
    simp only [v, dif_pos hi]
  have key := lift_path f L v (by
    intro i hi
    have hi' : i < ℓ := hi
    by_cases hb : L[i].2 = true
    · rw [if_pos hb]
      exact hf _ _ _ ⟨i, hi', rfl, Or.inl ⟨hb, hv _ (by omega), hv _ (by omega)⟩⟩
    · rw [if_neg hb, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact (hf _ _ _ ⟨i, hi', rfl,
        Or.inr ⟨by simpa using hb, hv _ (by omega), hv _ (by omega)⟩⟩).symm)
  refine ⟨ℓ + 1, FreeGroup.lift f, ?_⟩
  intro h1
  rw [hgL, h1, Equiv.Perm.one_apply] at key
  have := congr_arg Fin.val key
  rw [hv _ (by omega), hv _ (by omega)] at this
  exact hℓ0 this

/-- **Hopfian property**: a surjective endomorphism of a finitely generated free group is
injective. -/
theorem hopfian {α : Type*} [Finite α] (φ : FreeGroup α →* FreeGroup α)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  obtain ⟨n, π, hπ⟩ := exists_perm_rep g hne
  have : Finite (FreeGroup α →* Equiv.Perm (Fin n)) := Finite.of_equiv _ FreeGroup.lift
  have hinj : Function.Injective (fun h : FreeGroup α →* Equiv.Perm (Fin n) => h.comp φ) :=
    fun h1 h2 h => (MonoidHom.cancel_right hφ).1 h
  obtain ⟨h, hh⟩ := Finite.surjective_of_injective hinj π
  apply hπ
  rw [← hh]
  simp [hg]

/-- The elements of a basis generate. -/
theorem basis_closure {ι G : Type*} [Group G] (b : FreeGroupBasis ι G) :
    Subgroup.closure (Set.range b) = ⊤ := by
  have : Set.range b = (b.repr.symm.toMonoidHom) '' Set.range FreeGroup.of := by
    rw [← Set.range_comp]; rfl
  rw [this, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top]
  exact b.repr.symm.surjective

theorem h_basis_of_gen {G : Type} [Group G] {r : ℕ} (b : FreeGroupBasis (Fin r) G) (g : Fin r → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) : ∃ b' : FreeGroupBasis (Fin r) G, ∀ i, b' i = g i := by
  have hs : Function.Surjective (FreeGroup.lift g) :=
    FreeGroup.lift_surjective_iff_closure_range_eq_top.2 hg
  have hi : Function.Injective (b.repr.toMonoidHom.comp (FreeGroup.lift g)) :=
    hopfian _ (b.repr.surjective.comp hs)
  have hi' : Function.Injective (FreeGroup.lift g) := fun x y h => hi (by simp [h])
  refine ⟨FreeGroupBasis.ofRepr (MulEquiv.ofBijective (FreeGroup.lift g) ⟨hi', hs⟩).symm, ?_⟩
  intro i
  change FreeGroup.lift g (FreeGroup.of i) = g i
  simp

end Puder.PP.PartH
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part H: finitely generated free groups -/
alias h_basis_of_gen := Puder.PP.PartH.h_basis_of_gen

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartH
variable {d : ℕ}
theorem h_fin_of_gen {G : Type} [Group G] {ι : Type} (b : FreeGroupBasis ι G) {m : ℕ} (g : Fin m → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) : ∃ r, r ≤ m ∧ Nonempty (ι ≃ Fin r) := by
  let F : (ι → Multiplicative (ZMod 2)) → (Fin m → Multiplicative (ZMod 2)) :=
    fun c j => b.lift c (g j)
  have hF : Function.Injective F := by
    intro c1 c2 h
    apply b.lift.injective
    apply MonoidHom.eq_of_eqOn_dense hg
    rintro _ ⟨j, rfl⟩
    exact congr_fun h j
  obtain ⟨a, ha⟩ : ∃ a : Multiplicative (ZMod 2), a ≠ 1 := ⟨Multiplicative.ofAdd 1, by decide⟩
  have hG : Function.Injective
      (fun i : ι => (fun j => if j = i then a else 1 : ι → Multiplicative (ZMod 2))) := by
    intro i i' h
    have h1 := congr_fun h i
    by_contra hne
    simp only [if_true, if_neg hne] at h1
    exact ha h1
  have : Finite ι := Finite.of_injective _ (hF.comp hG)
  have := Fintype.ofFinite ι
  have hc := Fintype.card_le_of_injective F hF
  have h2 : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Fintype.card_congr Multiplicative.toAdd, ZMod.card]
  rw [Fintype.card_fun, Fintype.card_fun, h2, Fintype.card_fin] at hc
  exact ⟨Fintype.card ι, (Nat.pow_le_pow_iff_right (by norm_num)).1 hc, ⟨Fintype.equivFin ι⟩⟩

end Puder.PP.PartH
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias h_fin_of_gen := Puder.PP.PartH.h_fin_of_gen

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartH
variable {d : ℕ}
/-- Any basis of a group having a basis of `n` elements is indexed by a type with `n` elements. -/
theorem basis_equiv_fin {G : Type} [Group G] {ι : Type} (b : FreeGroupBasis ι G) {n : ℕ}
    (b' : FreeGroupBasis (Fin n) G) : Nonempty (ι ≃ Fin n) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := h_fin_of_gen b b' (basis_closure b')
  obtain ⟨r', hr', ⟨e'⟩⟩ := h_fin_of_gen b' (b.reindex e) (basis_closure _)
  have h := Fintype.card_congr e'
  simp only [Fintype.card_fin] at h
  obtain rfl : r = n := by omega
  exact ⟨e⟩

theorem h_free_subgroup {α : Type} (H : Subgroup (FreeGroup α)) :
    ∃ (ι : Type), Nonempty (FreeGroupBasis ι H) :=
  ⟨IsFreeGroup.Generators H, ⟨IsFreeGroup.basis H⟩⟩

end Puder.PP.PartH
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias h_free_subgroup := Puder.PP.PartH.h_free_subgroup

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartH
variable {d : ℕ}
/-- A basis of `H` together with `g` generates `H' = ⟨H, g⟩`. -/
theorem closure_sum_eq_top (H H' : Subgroup (FreeGroup (Fin d))) {m : ℕ}
    (g : Fin m → FreeGroup (Fin d)) (h : H' = Subgroup.closure (↑H ∪ Set.range g)) {κ : Type}
    (c : FreeGroupBasis κ H) (f : κ ⊕ Fin m → H')
    (hl : ∀ k, (f (Sum.inl k) : FreeGroup (Fin d)) = c k)
    (hr : ∀ j, (f (Sum.inr j) : FreeGroup (Fin d)) = g j) :
    Subgroup.closure (Set.range f) = ⊤ := by
  set K := (Subgroup.closure (Set.range f)).map H'.subtype with hK
  have hfK : ∀ s, (f s : FreeGroup (Fin d)) ∈ K := fun s =>
    ⟨f s, Subgroup.subset_closure ⟨s, rfl⟩, rfl⟩
  have hHK : H ≤ K := by
    intro x hx
    have hx' : (⟨x, hx⟩ : H) ∈ Subgroup.closure (Set.range c) := by
      rw [basis_closure]; trivial
    have : ∀ y : H, y ∈ Subgroup.closure (Set.range c) → (y : FreeGroup (Fin d)) ∈ K := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        rw [← hl]; exact hfK _
      | one => exact K.one_mem
      | mul a b _ _ ha hb => exact K.mul_mem ha hb
      | inv a _ ha => exact K.inv_mem ha
    exact this _ hx'
  have hle : H' ≤ K := by
    intro x hx
    rw [h] at hx
    refine (Subgroup.closure_le K).2 ?_ hx
    rintro y (hy | ⟨j, rfl⟩)
    · exact hHK hy
    · rw [← hr]; exact hfK _
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := hle x.2
  have : y = x := Subtype.ext hxy
  rwa [← this]

theorem fg_a (H H' : Subgroup (FreeGroup (Fin d))) (r r' m : ℕ) (hH : HasRank H r)
    (hH' : HasRank H' r') (g : Fin m → FreeGroup (Fin d))
    (h : H' = Subgroup.closure (↑H ∪ Set.range g)) :
    r' ≤ r + m ∧ (r' = r + m → ∀ w, IsPrimitiveIn H w → IsPrimitiveIn H' w) := by
  obtain ⟨bH⟩ := hH
  obtain ⟨bH'⟩ := hH'
  have hHle : H ≤ H' := by
    intro x hx
    rw [h]; exact Subgroup.subset_closure (Or.inl hx)
  have hg : ∀ j, g j ∈ H' := by
    intro j
    rw [h]; exact Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
  have key : ∀ (c : FreeGroupBasis (Fin r) H), ∃ f' : Fin (r + m) → H',
      Subgroup.closure (Set.range f') = ⊤ ∧
        ∀ i : Fin r, (f' (Fin.castAdd m i) : FreeGroup (Fin d)) = c i := by
    intro c
    let f : Fin r ⊕ Fin m → H' :=
      Sum.elim (fun i => ⟨c i, hHle (c i).2⟩) (fun j => ⟨g j, hg j⟩)
    refine ⟨f ∘ finSumFinEquiv.symm, ?_, ?_⟩
    · rw [(Equiv.surjective _).range_comp]
      exact closure_sum_eq_top H H' g h c f (fun _ => rfl) (fun _ => rfl)
    · intro i
      simp [f]
  constructor
  · obtain ⟨f', hf', -⟩ := key bH
    obtain ⟨k, hk, ⟨e⟩⟩ := h_fin_of_gen bH' f' hf'
    have := Fintype.card_congr e
    simp only [Fintype.card_fin] at this
    omega
  · rintro rfl w ⟨ι, c, i, rfl⟩
    obtain ⟨e⟩ := basis_equiv_fin c bH
    obtain ⟨f', hf', hf'2⟩ := key (c.reindex e)
    obtain ⟨b'', hb''⟩ := h_basis_of_gen bH' f' hf'
    exact ⟨Fin (r + m), b'', Fin.castAdd m (e i), by rw [hb'', hf'2]; simp⟩

end Puder.PP.PartH
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias fg_a := Puder.PP.PartH.fg_a

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartH
variable {d : ℕ}
theorem fg_b (H H' : Subgroup (FreeGroup (Fin d))) (r' : ℕ) (hH' : HasRank H' r') (hle : H ≤ H')
    (w : FreeGroup (Fin d)) (hw : w ∈ H) (hp : IsPrimitiveIn H' w) : IsPrimitiveIn H w := by
  obtain ⟨bH'⟩ := hH'
  obtain ⟨ι, c, i, rfl⟩ := hp
  obtain ⟨e⟩ := basis_equiv_fin c bH'
  let c' := c.reindex e
  let ρ : H' ≃* FreeGroup (Fin r') := c'.repr
  let J : Subgroup (FreeGroup (Fin r')) := (H.subgroupOf H').map ρ.toMonoidHom
  have hρ : ρ (c i) = FreeGroup.of (e i) := by
    have : c i = c' (e i) := by simp [c']
    rw [this]; exact c'.repr_apply_coe _
  have htop : IsPrimitiveIn (⊤ : Subgroup (FreeGroup (Fin r'))) (FreeGroup.of (e i)) :=
    ⟨Fin r', (FreeGroupBasis.ofFreeGroup (Fin r')).map Subgroup.topEquiv.symm, e i, by simp⟩
  have hJ : FreeGroup.of (e i) ∈ J := ⟨c i, by simpa [Subgroup.mem_subgroupOf] using hw, hρ⟩
  obtain ⟨ι2, c2, i2, h2⟩ := Puder.isPrimitiveIn_of_isPrimitiveIn_top htop J hJ
  let E : J ≃* H :=
    ((ρ.subgroupMap (H.subgroupOf H')).symm).trans (Subgroup.subgroupOfEquivOfLe hle)
  refine ⟨ι2, c2.map E, i2, ?_⟩
  rw [FreeGroupBasis.map_apply]
  have hmem : c i ∈ H.subgroupOf H' := by simpa [Subgroup.mem_subgroupOf] using hw
  have : c2 i2 = ρ.subgroupMap (H.subgroupOf H') ⟨c i, hmem⟩ := by
    apply Subtype.ext
    rw [h2]
    exact hρ.symm
  rw [this]
  change ((Subgroup.subgroupOfEquivOfLe hle) ((ρ.subgroupMap (H.subgroupOf H')).symm
    (ρ.subgroupMap (H.subgroupOf H') ⟨c i, hmem⟩)) : FreeGroup (Fin d)) = c i
  rw [MulEquiv.symm_apply_apply]
  rfl

end Puder.PP.PartH
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias fg_b := Puder.PP.PartH.fg_b

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartH
variable {d : ℕ}
theorem isPrimitiveIn_zpowers (w : FreeGroup (Fin d)) (hw : w ≠ 1) :
    IsPrimitiveIn (Subgroup.zpowers w) w ∧ HasRank (Subgroup.zpowers w) 1 := by
  let w' : Subgroup.zpowers w := ⟨w, Subgroup.mem_zpowers w⟩
  let ψ : FreeGroup (Fin 1) →* Subgroup.zpowers w := FreeGroup.lift (fun _ => w')
  have hpow : ∀ x : FreeGroup (Fin 1), ∃ n : ℤ, x = FreeGroup.of 0 ^ n := fun x =>
    ⟨FreeGroup.equivIntOfUnique x, (FreeGroup.equivIntOfUnique.left_inv x).symm⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, rfl⟩ := hpow x
    simp only [ψ, map_zpow, FreeGroup.lift_apply_of] at hx
    have h1 : w ^ n = 1 := by simpa [w'] using congr_arg Subtype.val hx
    have hn : n = 0 := by
      by_contra hn
      exact hw (zpow_left_injective hn (by simpa using h1))
    rw [hn, zpow_zero]
  have hsurj : Function.Surjective ψ := by
    rintro ⟨y, n, rfl⟩
    refine ⟨FreeGroup.of 0 ^ n, ?_⟩
    apply Subtype.ext
    simp [ψ, w']
  let b : FreeGroupBasis (Fin 1) (Subgroup.zpowers w) :=
    FreeGroupBasis.ofRepr (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm
  have hb : b 0 = w' := by
    change ψ (FreeGroup.of 0) = w'
    simp [ψ]
  exact ⟨⟨Fin 1, b, 0, by rw [hb]⟩, ⟨b⟩⟩

end Puder.PP.PartH
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias isPrimitiveIn_zpowers := Puder.PP.PartH.isPrimitiveIn_zpowers

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartT
variable {d : ℕ}
variable {V A : Type} [AddCommGroup A] (τ : Fin d → Equiv.Perm V) (c : Fin d → V → A)
/-!
# Part T: `π₁` of a fold-free quotient (`gt_inj`, `gt_rank`)

Words are read in the quotient graph of `P` through permutations of `V × A` (`V` the blocks, `A` an
abelian group of weights), which commute with the translations of `A`.
-/
/-! ## Generic part: weighted permutation action -/
/-- The lift of `τ j` to `V × A`, adding the weight `c j B`. -/
def that (j : Fin d) : Equiv.Perm (V × A) where
  toFun x := (τ j x.1, x.2 + c j x.1)
  invFun x := ((τ j).symm x.1, x.2 - c j ((τ j).symm x.1))
  left_inv x := by simp
  right_inv x := by simp

/-- Translation of the second coordinate. -/
def trl (t : A) : Equiv.Perm (V × A) where
  toFun x := (x.1, x.2 + t)
  invFun x := (x.1, x.2 - t)
  left_inv x := by simp
  right_inv x := by simp

/-- The representation. -/
def rho : FreeGroup (Fin d) →* Equiv.Perm (V × A) := FreeGroup.lift (fun j => (that τ c j)⁻¹)

/-- End point of the walk reading `g` from `(base, 0)`. -/
def en (base : V) (g : FreeGroup (Fin d)) : V × A := (rho τ c g)⁻¹ (base, 0)

theorem that_comm (j : Fin d) (t : A) : Commute (that τ c j) (trl (V := V) t) := by
  ext x <;> simp [that, trl, Equiv.Perm.mul_apply, add_right_comm]

theorem rho_comm (g : FreeGroup (Fin d)) (t : A) : Commute (rho τ c g) (trl (V := V) t) := by
  induction g using FreeGroup.induction_on with
  | C1 => simp
  | of j => simpa [rho] using (that_comm τ c j t).inv_left
  | inv_of j h => rw [map_inv]; exact h.inv_left
  | mul g h hg hh => rw [map_mul]; exact hg.mul_left hh

theorem rho_tr (g : FreeGroup (Fin d)) (x : V × A) (t : A) :
    rho τ c g (x.1, x.2 + t) = ((rho τ c g x).1, (rho τ c g x).2 + t) := by
  have h := congrArg (fun σ : Equiv.Perm (V × A) => σ x) (rho_comm τ c g t).eq
  simpa [Equiv.Perm.mul_apply, trl] using h

theorem en_mul (base : V) (g h : FreeGroup (Fin d)) :
    en τ c base (g * h) = (rho τ c h)⁻¹ (en τ c base g) := by
  simp [en, mul_inv_rev, Equiv.Perm.mul_apply]

theorem en_one (base : V) : en τ c base 1 = (base, 0) := by simp [en]

theorem en_mul_inv (base : V) (g h : FreeGroup (Fin d)) :
    en τ c base (g * h⁻¹) = rho τ c h (en τ c base g) := by
  rw [en_mul, map_inv, inv_inv]

theorem en_L (base : V) (g h : FreeGroup (Fin d)) (X : V) (a a' : A)
    (hg : en τ c base g = (X, a)) (hh : en τ c base h = (X, a')) :
    en τ c base (g * h⁻¹) = (base, a - a') := by
  rw [en_mul_inv, hg]
  have h1 : rho τ c h (X, a') = (base, 0) := by
    rw [← hh, en]; simp
  have := rho_tr τ c h (X, a') (a - a')
  simp only [h1] at this
  simpa using this

theorem en_Linv (base : V) (g h : FreeGroup (Fin d))
    (hgh : (en τ c base (g * h⁻¹)).1 = base) : (en τ c base g).1 = (en τ c base h).1 := by
  rw [en_mul_inv] at hgh
  have h1 : en τ c base g = (rho τ c h)⁻¹ (base, 0 + (rho τ c h (en τ c base g)).2) := by
    rw [Equiv.Perm.eq_inv_iff_eq]
    exact Prod.ext hgh (by simp)
  rw [← map_inv] at h1
  have := rho_tr τ c h⁻¹ (base, 0) (rho τ c h (en τ c base g)).2
  simp only at this
  rw [this] at h1
  rw [h1]
  simp [en]

theorem en_M (base : V) (g h : FreeGroup (Fin d)) (hg : (en τ c base g).1 = base) :
    en τ c base (g * h) = ((en τ c base h).1, (en τ c base h).2 + (en τ c base g).2) := by
  rw [en_mul]
  have h1 : en τ c base g = (base, 0 + (en τ c base g).2) := Prod.ext hg (by simp)
  rw [h1, ← map_inv]
  have := rho_tr τ c h⁻¹ (base, 0) (en τ c base g).2
  simp only at this
  rw [this]
  simp [en]

theorem en_step_true (base : V) (g : FreeGroup (Fin d)) (i : Fin d) :
    en τ c base (g * FreeGroup.mk [(i, true)]) = that τ c i (en τ c base g) := by
  rw [en_mul]; simp [rho]

theorem en_step_false (base : V) (g : FreeGroup (Fin d)) (i : Fin d) :
    en τ c base (g * FreeGroup.mk [(i, false)]) = (that τ c i)⁻¹ (en τ c base g) := by
  rw [en_mul]; simp [rho]

end Puder.PP.PartT
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartT
variable {d : ℕ}
theorem exists_perm {α : Type} [Fintype α] (R : α → α → Prop)
    (h1 : ∀ a b b', R a b → R a b' → b = b') (h2 : ∀ a a' b, R a b → R a' b → a = a') :
    ∃ σ : Equiv.Perm α, ∀ a b, R a b → σ a = b := by
  let f : {a // ∃ b, R a b} → {b // ∃ a, R a b} := fun a => ⟨a.2.choose, a.1, a.2.choose_spec⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' h
      have h' : a.2.choose = a'.2.choose := congrArg Subtype.val h
      exact Subtype.ext (h2 _ _ _ a.2.choose_spec (h' ▸ a'.2.choose_spec))
    · rintro ⟨b, a, hab⟩
      refine ⟨⟨a, b, hab⟩, Subtype.ext ?_⟩
      exact h1 a _ _ (Exists.choose_spec (⟨b, hab⟩ : ∃ b, R a b)) hab
  let e := Equiv.ofBijective f hf
  refine ⟨e.extendSubtype, fun a b hab => ?_⟩
  rw [e.extendSubtype_apply_of_mem a ⟨b, hab⟩]
  exact h1 a _ _ (Exists.choose_spec (⟨b, hab⟩ : ∃ b, R a b)) hab

/-! ## The quotient graph -/
theorem exists_tau (K : List (Fin d × Bool)) (P : Part K) (hP : FF K P) :
    ∃ τ : Fin d → Equiv.Perm (Finset (Fin K.length)),
      ∀ e : Fin K.length, τ (lab K e) (P.part (tl K e)) = P.part (hd K e) := by
  have : ∀ j : Fin d, ∃ σ : Equiv.Perm (Finset (Fin K.length)),
      ∀ B B', (∃ e, lab K e = j ∧ P.part (tl K e) = B ∧ P.part (hd K e) = B') → σ B = B' := by
    intro j
    apply exists_perm
    · rintro B B1 B2 ⟨e, he, rfl, rfl⟩ ⟨e', he', h, rfl⟩
      exact ((hP e e' (he.trans he'.symm)).1 h.symm)
    · rintro B1 B2 B ⟨e, he, rfl, rfl⟩ ⟨e', he', rfl, h⟩
      exact ((hP e e' (he.trans he'.symm)).2 h.symm)
  choose τ hτ using this
  exact ⟨τ, fun e => hτ _ _ _ ⟨e, rfl, rfl, rfl⟩⟩

/-- The weight: the indicator of the record edges. -/
noncomputable def wt (K : List (Fin d × Bool)) (P : Part K)
    (τ : Fin d → Equiv.Perm (Finset (Fin K.length))) (j : Fin d) (B : Finset (Fin K.length)) :
    Fin K.length → ZMod 2 :=
  fun p0 => if Rec K P p0 ∧ qedge K P p0 = (j, B, τ j B) then 1 else 0

/-- Weight of the step at position `q`. -/
noncomputable def cc (K : List (Fin d × Bool)) (P : Part K) (q : Fin K.length) :
    Fin K.length → ZMod 2 :=
  fun p0 => if Rec K P p0 ∧ qedge K P p0 = qedge K P q then 1 else 0

/-- Accumulated weight of the first `p` steps. -/
noncomputable def W (K : List (Fin d × Bool)) (P : Part K) (p : ℕ) : Fin K.length → ZMod 2 :=
  ∑ q ∈ Finset.range p, if h : q < K.length then cc K P ⟨q, h⟩ else 0

theorem neg_eq_self {n : ℕ} (a : Fin n → ZMod 2) : -a = a := by
  funext i
  have : ∀ x : ZMod 2, -x = x := by decide
  exact this _

theorem walk (K : List (Fin d × Bool)) (hn : 0 < K.length) (P : Part K)
    (τ : Fin d → Equiv.Perm (Finset (Fin K.length)))
    (hτ : ∀ e : Fin K.length, τ (lab K e) (P.part (tl K e)) = P.part (hd K e))
    (p : ℕ) (hp : p ≤ K.length) :
    en τ (wt K P τ) (P.part ⟨0, hn⟩) (pfx K p) =
      (P.part ⟨p % K.length, Nat.mod_lt _ hn⟩, W K P p) := by
  induction p with
  | zero =>
    simp only [pfx, List.take_zero, W, Finset.range_zero, Finset.sum_empty, Nat.zero_mod]
    exact en_one _ _ _
  | succ p ih =>
    have hp' : p < K.length := hp
    let pp : Fin K.length := ⟨p, hp'⟩
    have hpfx : pfx K (p + 1) = pfx K p * FreeGroup.mk [(lab K pp, (K[pp]).2)] := by
      simp only [pfx, FreeGroup.mul_mk]
      congr 1
      rw [List.take_add_one]
      simp [hp', lab, pp]
    have hW : W K P (p + 1) = W K P p + cc K P pp := by
      simp [W, Finset.sum_range_succ, hp', pp]
    have hcc : wt K P τ (lab K pp) (P.part (tl K pp)) = cc K P pp := by
      funext p0
      unfold wt cc qedge
      rw [hτ pp]
    have hmod : (⟨p % K.length, Nat.mod_lt _ hn⟩ : Fin K.length) = pp :=
      Fin.ext (Nat.mod_eq_of_lt hp')
    have hc : (⟨(p + 1) % K.length, Nat.mod_lt _ hn⟩ : Fin K.length) = cnxt pp := rfl
    rw [hpfx, hW, hc]
    have ih' := ih (le_of_lt hp')
    rw [hmod] at ih'
    cases hb : (K[pp]).2 with
    | true =>
      rw [en_step_true, ih']
      have htl : tl K pp = pp := by unfold tl; rw [if_pos hb]
      have hhd : hd K pp = cnxt pp := by unfold hd; rw [if_pos hb]
      have h := hτ pp
      rw [htl, hhd] at h
      rw [htl] at hcc
      simp [that, h, hcc]
    | false =>
      rw [en_step_false, ih']
      have htl : tl K pp = cnxt pp := by unfold tl; rw [if_neg (by rw [hb]; simp)]
      have hhd : hd K pp = pp := by unfold hd; rw [if_neg (by rw [hb]; simp)]
      have h := hτ pp
      rw [htl, hhd] at h
      rw [htl] at hcc
      have h' : (τ (lab K pp)).symm (P.part pp) = P.part (cnxt pp) := by
        rw [← h]; simp
      have hinv : (that τ (wt K P τ) (lab K pp))⁻¹ (P.part pp, W K P p) =
          ((τ (lab K pp)).symm (P.part pp),
            W K P p - wt K P τ (lab K pp) ((τ (lab K pp)).symm (P.part pp))) := rfl
      rw [hinv, h', hcc, sub_eq_add_neg, neg_eq_self]

theorem pfx_length (K : List (Fin d × Bool)) : pfx K K.length = FreeGroup.mk K := by
  simp [pfx]

theorem pfx_zero (K : List (Fin d × Bool)) : pfx K 0 = 1 := by
  simp [pfx, FreeGroup.one_eq_mk]

/-- Every element of `J K P` returns to the base block. -/
theorem J_stab (K : List (Fin d × Bool)) (hn : 0 < K.length) (P : Part K)
    (τ : Fin d → Equiv.Perm (Finset (Fin K.length)))
    (hτ : ∀ e : Fin K.length, τ (lab K e) (P.part (tl K e)) = P.part (hd K e))
    (g : FreeGroup (Fin d)) (hg : g ∈ J K P) :
    (en τ (wt K P τ) (P.part ⟨0, hn⟩) g).1 = P.part ⟨0, hn⟩ := by
  unfold J at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨p, q, hpq, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← pfx_length, walk K hn P τ hτ _ le_rfl]
      simp
    · have h1 := walk K hn P τ hτ p (le_of_lt p.2)
      have h2 := walk K hn P τ hτ q (le_of_lt q.2)
      have e1 : (⟨(p : ℕ) % K.length, Nat.mod_lt _ hn⟩ : Fin K.length) = p :=
        Fin.ext (Nat.mod_eq_of_lt p.2)
      have e2 : (⟨(q : ℕ) % K.length, Nat.mod_lt _ hn⟩ : Fin K.length) = q :=
        Fin.ext (Nat.mod_eq_of_lt q.2)
      rw [e1] at h1
      rw [e2, ← hpq] at h2
      rw [en_L _ _ _ _ _ _ _ _ h1 h2]
  | one => rw [en_one]
  | mul x y _ _ hx hy => rw [en_M _ _ _ _ _ hx]; exact hy
  | inv x _ hx =>
    have h1 : en τ (wt K P τ) (P.part ⟨0, hn⟩) x = (P.part ⟨0, hn⟩, (en τ (wt K P τ) (P.part ⟨0, hn⟩) x).2) :=
      Prod.ext hx rfl
    have := en_L τ (wt K P τ) (P.part ⟨0, hn⟩) 1 x _ _ _ (en_one _ _ _) h1
    rw [one_mul] at this
    rw [this]

theorem gt_inj (K : List (Fin d × Bool)) (hK : K ≠ []) (P : Part K) (hP : FF K P)
    (p q : Fin K.length) (h : pfx K p * (pfx K q)⁻¹ ∈ J K P) : P.part p = P.part q := by
  have hn : 0 < K.length := List.length_pos_of_ne_nil hK
  obtain ⟨τ, hτ⟩ := exists_tau K P hP
  have h0 := en_Linv _ _ _ _ _ (J_stab K hn P τ hτ _ h)
  rw [walk K hn P τ hτ p (le_of_lt p.2), walk K hn P τ hτ q (le_of_lt q.2)] at h0
  have e1 : (⟨(p : ℕ) % K.length, Nat.mod_lt _ hn⟩ : Fin K.length) = p :=
    Fin.ext (Nat.mod_eq_of_lt p.2)
  have e2 : (⟨(q : ℕ) % K.length, Nat.mod_lt _ hn⟩ : Fin K.length) = q :=
    Fin.ext (Nat.mod_eq_of_lt q.2)
  simpa [e1, e2] using h0

end Puder.PP.PartT
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part T: `π₁` of a fold-free quotient -/
alias gt_inj := Puder.PP.PartT.gt_inj

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartT
variable {d : ℕ}
/-! ## The rank -/
theorem W_zero (K : List (Fin d × Bool)) (P : Part K) (p0 : Fin K.length) (hp0 : New K P p0)
    (k : ℕ) (hk : k ≤ p0) : W K P k p0 = 0 := by
  simp only [W, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  have hq' : q < (p0 : ℕ) := lt_of_lt_of_le (Finset.mem_range.1 hq) hk
  have hqn : q < K.length := hq'.trans p0.2
  rw [dif_pos hqn]
  simp only [cc]
  rw [if_neg]
  rintro ⟨-, h⟩
  exact hp0 ⟨q, hqn⟩ hq' h.symm

theorem W_one (K : List (Fin d × Bool)) (P : Part K) (p0 : Fin K.length) (hp0 : Rec K P p0) :
    W K P ((p0 : ℕ) + 1) p0 = 1 := by
  have h0 := W_zero K P p0 hp0.1 p0 le_rfl
  have : W K P ((p0 : ℕ) + 1) = W K P p0 + cc K P p0 := by
    simp [W, Finset.sum_range_succ]
  rw [this, Pi.add_apply, h0, zero_add]
  simp [cc, hp0]

theorem first_le (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) :
    ((first K P (cnxt p) : Fin K.length) : ℕ) ≤ (p : ℕ) + 1 := by
  have h1 : first K P (cnxt p) ≤ cnxt p :=
    Finset.min'_le _ _ (P.mem_part (Finset.mem_univ _))
  have h2 : ((cnxt p : Fin K.length) : ℕ) ≤ (p : ℕ) + 1 := Nat.mod_le _ _
  exact le_trans h1 h2

theorem first_le_rec (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length)
    (hp : ¬ Disc K P p) : ((first K P (cnxt p) : Fin K.length) : ℕ) ≤ (p : ℕ) := by
  by_cases h : (p : ℕ) + 1 < K.length
  · have : ¬ ∀ q : Fin K.length, (q : ℕ) ≤ p → P.part q ≠ P.part (cnxt p) := fun h' => hp ⟨h, h'⟩
    push Not at this
    obtain ⟨q, hq, hpq⟩ := this
    have hmem : q ∈ P.part (cnxt p) := hpq ▸ P.mem_part (Finset.mem_univ q)
    have h1 : first K P (cnxt p) ≤ q := Finset.min'_le _ _ hmem
    exact le_trans h1 hq
  · have h1 : first K P (cnxt p) ≤ cnxt p :=
      Finset.min'_le _ _ (P.mem_part (Finset.mem_univ _))
    have h2 : ((cnxt p : Fin K.length) : ℕ) = 0 := by
      have : (p : ℕ) + 1 = K.length := by have := p.2; omega
      simp [cnxt, this]
    have h3 : ((first K P (cnxt p) : Fin K.length) : ℕ) ≤ ((cnxt p : Fin K.length) : ℕ) := h1
    omega

theorem part_first (K : List (Fin d × Bool)) (P : Part K) (p : Fin K.length) :
    P.part (first K P p) = P.part p :=
  P.part_eq_of_mem (P.part_mem.2 (Finset.mem_univ p)) (Finset.min'_mem _ _)

theorem en_gam (K : List (Fin d × Bool)) (hn : 0 < K.length) (P : Part K)
    (τ : Fin d → Equiv.Perm (Finset (Fin K.length)))
    (hτ : ∀ e : Fin K.length, τ (lab K e) (P.part (tl K e)) = P.part (hd K e))
    (p : Fin K.length) :
    en τ (wt K P τ) (P.part ⟨0, hn⟩) (gam K P p) =
      (P.part ⟨0, hn⟩, W K P ((p : ℕ) + 1) - W K P (first K P (cnxt p))) := by
  have h1 := walk K hn P τ hτ ((p : ℕ) + 1) p.2
  have h2 := walk K hn P τ hτ (first K P (cnxt p)) (le_of_lt (first K P (cnxt p)).2)
  have e2 : (⟨((first K P (cnxt p) : Fin K.length) : ℕ) % K.length, Nat.mod_lt _ hn⟩ :
      Fin K.length) = first K P (cnxt p) := Fin.ext (Nat.mod_eq_of_lt (first K P (cnxt p)).2)
  have e1 : (⟨((p : ℕ) + 1) % K.length, Nat.mod_lt _ hn⟩ : Fin K.length) = cnxt p := rfl
  rw [e1] at h1
  rw [e2, part_first] at h2
  exact en_L _ _ _ _ _ _ _ _ h1 h2

theorem gt_rank (K : List (Fin d × Bool)) (hK : K ≠ []) (P : Part K) (hP : FF K P) :
    HasRank (J K P) ((E K P).card + 1 - P.parts.card) := by
  have hn : 0 < K.length := List.length_pos_of_ne_nil hK
  obtain ⟨τ, hτ⟩ := exists_tau K P hP
  set base := P.part ⟨0, hn⟩ with hbase
  -- the homomorphism Θ
  let Θ : J K P →* Multiplicative (Fin K.length → ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (en τ (wt K P τ) base g.1).2
      map_one' := by
        show Multiplicative.ofAdd (en τ (wt K P τ) base 1).2 = 1
        rw [en_one]; rfl
      map_mul' := by
        intro g h
        show Multiplicative.ofAdd (en τ (wt K P τ) base (g.1 * h.1)).2 = _
        rw [en_M _ _ _ _ _ (J_stab K hn P τ hτ _ g.2), ← ofAdd_add, add_comm] }
  have hgen := Puder.PP.ex_gen K hK P
  have hmem : ∀ p, Rec K P p → gam K P p ∈ J K P := by
    intro p hp
    rw [hgen]
    exact Subgroup.subset_closure ⟨p, hp, rfl⟩
  have hΘ : ∀ p (hp : Rec K P p),
      Multiplicative.toAdd (Θ ⟨gam K P p, hmem p hp⟩) =
        W K P ((p : ℕ) + 1) - W K P (first K P (cnxt p)) := by
    intro p hp
    show (en τ (wt K P τ) base (gam K P p)).2 = _
    rw [en_gam K hn P τ hτ p]
  have hΘ0 : ∀ p (hp : Rec K P p) p0, Rec K P p0 → p < p0 →
      Multiplicative.toAdd (Θ ⟨gam K P p, hmem p hp⟩) p0 = 0 := by
    intro p hp p0 hp0 hlt
    have hlt' : (p : ℕ) < p0 := hlt
    rw [hΘ p hp, Pi.sub_apply, W_zero K P p0 hp0.1 _ hlt',
      W_zero K P p0 hp0.1 _ ((first_le K P p).trans hlt'), sub_zero]
  have hΘ1 : ∀ p (hp : Rec K P p),
      Multiplicative.toAdd (Θ ⟨gam K P p, hmem p hp⟩) p = 1 := by
    intro p hp
    rw [hΘ p hp, Pi.sub_apply, W_one K P p hp,
      W_zero K P p hp.1 _ (first_le_rec K P p hp.2), sub_zero]
  -- generators
  let S := {p : Fin K.length // Rec K P p}
  let m := Fintype.card S
  let e : Fin m ≃ S := (Fintype.equivFin S).symm
  let g : Fin m → J K P := fun i => ⟨gam K P (e i).1, hmem _ (e i).2⟩
  have hg : Subgroup.closure (Set.range g) = ⊤ := by
    apply Subgroup.map_injective (J K P).subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    conv_rhs => rw [hgen]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨(e i).1, (e i).2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨g (e.symm ⟨p, hp⟩), ⟨_, rfl⟩, by simp [g]⟩
  obtain ⟨ι, ⟨b0⟩⟩ := Puder.PP.h_free_subgroup (J K P)
  obtain ⟨r, hrm, ⟨eι⟩⟩ := Puder.PP.h_fin_of_gen b0 g hg
  let b : FreeGroupBasis (Fin r) (J K P) := b0.reindex eι
  -- homomorphisms to ZMod 2
  let ψ : (S → ZMod 2) → ((Fin K.length → ZMod 2) →+ ZMod 2) := fun v =>
    AddMonoidHom.mk' (fun a => ∑ s : S, v s * a s.1)
      (by intro a a'; simp [mul_add, Finset.sum_add_distrib])
  let φ : (S → ZMod 2) → (J K P →* Multiplicative (ZMod 2)) := fun v =>
    (AddMonoidHom.toMultiplicative (ψ v)).comp Θ
  have hφ : ∀ v (x : J K P), Multiplicative.toAdd (φ v x) =
      ∑ s : S, v s * Multiplicative.toAdd (Θ x) s.1 := fun v x => rfl
  let F : (S → ZMod 2) → (Fin r → ZMod 2) := fun v i => Multiplicative.toAdd (φ v (b i))
  have hF : Function.Injective F := by
    intro v v' hvv
    have hφeq : φ v = φ v' := by
      apply b.ext_hom
      intro i
      exact Multiplicative.toAdd.injective (congrFun hvv i)
    have key : ∀ k : ℕ, ∀ s : S, (s.1 : ℕ) = k → v s = v' s := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro s hs
        have h1 : Multiplicative.toAdd (φ v ⟨gam K P s.1, hmem _ s.2⟩) =
            Multiplicative.toAdd (φ v' ⟨gam K P s.1, hmem _ s.2⟩) := by rw [hφeq]
        rw [hφ, hφ, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
        rw [Finset.sum_eq_single s] at h1
        · rw [hΘ1 s.1 s.2, mul_one, mul_one] at h1
          exact sub_eq_zero.1 h1
        · intro t _ hts
          rcases lt_or_gt_of_ne (fun h => hts (Subtype.ext h) : t.1 ≠ s.1) with hlt | hgt
          · rw [ih t.1 (by rw [← hs]; exact hlt) t rfl, sub_self]
          · rw [hΘ0 s.1 s.2 t.1 t.2 hgt, mul_zero, mul_zero, sub_self]
        · intro h; exact absurd (Finset.mem_univ s) h
    funext s
    exact key _ s rfl
  have hcard := Fintype.card_le_of_injective F hF
  have hmr : m ≤ r := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hrm' : r = m := le_antisymm hrm hmr
  have hm : m = (E K P).card + 1 - P.parts.card := by
    have h1 := Puder.PP.ex_card K hK P
    have h2 : m = (univ.filter (Rec K P)).card := Fintype.card_subtype _
    omega
  rw [← hm, ← hrm']
  exact ⟨b⟩

end Puder.PP.PartT
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias gt_rank := Puder.PP.PartT.gt_rank

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartG
variable {d : ℕ}
/-!
# Part G: generation and critical subgroups

The kernel partition `kp K H` of a subgroup `H`, its Galois property `j_le_iff`, and the stubs
`gt_gen`, `gt_crit`, `crit_finite`, `j_bot`.
-/
/-! ## Right cosets -/
/-- `a` and `b` lie in the same right coset of `H`. -/
def RC (H : Subgroup (FreeGroup (Fin d))) (a b : FreeGroup (Fin d)) : Prop := a * b⁻¹ ∈ H

theorem RC.refl (H : Subgroup (FreeGroup (Fin d))) (a : FreeGroup (Fin d)) : RC H a a := by
  simp [RC, H.one_mem]

theorem RC.symm {H : Subgroup (FreeGroup (Fin d))} {a b : FreeGroup (Fin d)} (h : RC H a b) :
    RC H b a := by
  have := H.inv_mem h
  simpa [RC] using this

theorem RC.trans {H : Subgroup (FreeGroup (Fin d))} {a b c : FreeGroup (Fin d)} (h : RC H a b)
    (h' : RC H b c) : RC H a c := by
  have := H.mul_mem h h'
  simpa [RC, mul_assoc] using this

theorem RC.mul_right {H : Subgroup (FreeGroup (Fin d))} {a b : FreeGroup (Fin d)} (h : RC H a b)
    (c : FreeGroup (Fin d)) : RC H (a * c) (b * c) := by
  simpa [RC, mul_assoc] using h

theorem RC.mono {H H' : Subgroup (FreeGroup (Fin d))} {a b : FreeGroup (Fin d)} (h : RC H a b)
    (hle : H ≤ H') : RC H' a b := hle h

theorem RC.mul_left {H : Subgroup (FreeGroup (Fin d))} {a b j : FreeGroup (Fin d)} (h : RC H a b)
    (hj : j ∈ H) : RC H a (j * b) := by
  have := H.mul_mem h (H.inv_mem hj)
  simpa [RC, mul_assoc] using this

/-! ## Partitions -/
theorem part_eq_iff {K : List (Fin d × Bool)} (P : Part K) (p q : Fin K.length) :
    P.part p = P.part q ↔ q ∈ P.part p :=
  eq_comm.trans (P.mem_part_iff_part_eq_part (mem_univ q) (mem_univ p)).symm

/-- The order on partitions in terms of `part`. -/
theorem le_iff_part {K : List (Fin d × Bool)} (P Q : Part K) :
    P ≤ Q ↔ ∀ p q : Fin K.length, P.part p = P.part q → Q.part p = Q.part q := by
  constructor
  · intro h p q hpq
    obtain ⟨c, hc, hsub⟩ := h (P.part_mem.2 (mem_univ p))
    have hp : p ∈ c := hsub (P.mem_part (mem_univ p))
    have hq : q ∈ c := hsub ((part_eq_iff P p q).1 hpq)
    rw [Q.part_eq_of_mem hc hp, Q.part_eq_of_mem hc hq]
  · intro h B hB
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hB
    refine ⟨Q.part a, Q.part_mem.2 (mem_univ a), fun b hb => ?_⟩
    have : P.part a = P.part b := by rw [P.part_eq_of_mem hB ha, P.part_eq_of_mem hB hb]
    exact (part_eq_iff Q a b).1 (h a b this)

/-- The setoid of the kernel partition. -/
def kpSetoid (K : List (Fin d × Bool)) (H : Subgroup (FreeGroup (Fin d))) :
    Setoid (Fin K.length) where
  r p q := RC H (pfx K p) (pfx K q)
  iseqv := ⟨fun _ => RC.refl _ _, RC.symm, RC.trans⟩

/-- The kernel partition of a subgroup `H`: `p ~ q` iff `pfx K p * (pfx K q)⁻¹ ∈ H`. -/
noncomputable def kp (K : List (Fin d × Bool)) (H : Subgroup (FreeGroup (Fin d))) : Part K :=
  Finpartition.ofSetoid (kpSetoid K H)

theorem kp_part (K : List (Fin d × Bool)) (H : Subgroup (FreeGroup (Fin d)))
    (p q : Fin K.length) :
    (kp K H).part p = (kp K H).part q ↔ pfx K p * (pfx K q)⁻¹ ∈ H := by
  rw [part_eq_iff]
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-! ## Prefixes along the cycle -/
theorem mk_true (x : Fin d) : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl

theorem mk_false (x : Fin d) : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ := rfl

theorem mk_cons (a : Fin d × Bool) (L : List (Fin d × Bool)) :
    FreeGroup.mk (a :: L) = FreeGroup.mk [a] * FreeGroup.mk L := by
  rw [FreeGroup.mul_mk]; rfl

theorem pfx_succ (K : List (Fin d × Bool)) (p : ℕ) (hp : p < K.length) :
    pfx K (p + 1) = pfx K p * FreeGroup.mk [K[p]] := by
  unfold pfx
  rw [FreeGroup.mul_mk, List.take_succ_eq_append_getElem hp]

theorem pfx_wrap (K : List (Fin d × Bool)) (H : Subgroup (FreeGroup (Fin d)))
    (hH : FreeGroup.mk K ∈ H) (p : Fin K.length) :
    RC H (pfx K ((p : ℕ) + 1)) (pfx K (cnxt p)) := by
  by_cases h : (p : ℕ) + 1 < K.length
  · have : ((cnxt p : Fin K.length) : ℕ) = p + 1 := Nat.mod_eq_of_lt h
    rw [this]
    exact RC.refl _ _
  · have h1 : (p : ℕ) + 1 = K.length := by have := p.2; omega
    have : ((cnxt p : Fin K.length) : ℕ) = 0 := by simp [cnxt, h1]
    rw [this, h1]
    have e1 : pfx K K.length = FreeGroup.mk K := by unfold pfx; rw [List.take_length]
    have e0 : pfx K 0 = 1 := rfl
    rw [e1, e0]
    simpa [RC] using hH

/-- The head of an edge is the tail times the generator, up to the wrap-around element. -/
theorem edge_rel (K : List (Fin d × Bool)) (H : Subgroup (FreeGroup (Fin d)))
    (hH : FreeGroup.mk K ∈ H) (p : Fin K.length) :
    RC H (pfx K (hd K p)) (pfx K (tl K p) * FreeGroup.of (lab K p)) := by
  have hs := pfx_succ K p p.2
  have hw := pfx_wrap K H hH p
  unfold hd tl lab
  simp only [Fin.getElem_fin]
  rcases hK : K[(p : ℕ)] with ⟨x, b⟩
  rw [hK] at hs
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [mk_false] at hs
    have h1 := hw.symm.mul_right (FreeGroup.of x)
    rw [hs] at h1
    have e : pfx K p * (FreeGroup.of x)⁻¹ * FreeGroup.of x = pfx K p := by group
    rw [e] at h1
    exact h1.symm
  · simp only [if_true]
    rw [mk_true] at hs
    rw [← hs]
    exact hw.symm

/-- The kernel partition of a subgroup containing `mk K` is fold-free. -/
theorem kp_ff (K : List (Fin d × Bool)) (H : Subgroup (FreeGroup (Fin d)))
    (hH : FreeGroup.mk K ∈ H) : FF K (kp K H) := by
  intro e e' hl
  rw [kp_part, kp_part]
  have he := edge_rel K H hH e
  have he' := edge_rel K H hH e'
  rw [hl] at he
  constructor
  · intro h
    exact he.trans ((RC.mul_right h _).trans he'.symm)
  · intro h
    have := (he.symm.trans h).trans he'
    simpa [RC, mul_assoc] using this

/-! ## The subgroup `J K P` -/
theorem j_mem_mk (K : List (Fin d × Bool)) (P : Part K) : FreeGroup.mk K ∈ J K P :=
  Subgroup.subset_closure (Or.inl rfl)

theorem j_gen (K : List (Fin d × Bool)) (P : Part K) (p q : Fin K.length)
    (h : P.part p = P.part q) : pfx K p * (pfx K q)⁻¹ ∈ J K P :=
  Subgroup.subset_closure (Or.inr ⟨p, q, h, rfl⟩)

/-- Galois property of the kernel partition. -/
theorem j_le_iff (K : List (Fin d × Bool)) (P : Part K) (H : Subgroup (FreeGroup (Fin d))) :
    J K P ≤ H ↔ FreeGroup.mk K ∈ H ∧ P ≤ kp K H := by
  constructor
  · intro h
    refine ⟨h (j_mem_mk K P), (le_iff_part _ _).2 fun p q hpq => ?_⟩
    rw [kp_part]
    exact h (j_gen K P p q hpq)
  · rintro ⟨hH, hle⟩
    unfold J
    rw [Subgroup.closure_le]
    rintro g (hg | ⟨p, q, hpq, rfl⟩)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]; exact hH
    · exact (kp_part K H p q).1 ((le_iff_part _ _).1 hle p q hpq)

theorem j_mono (K : List (Fin d × Bool)) (P Q : Part K) (h : P ≤ Q) : J K P ≤ J K Q :=
  (j_le_iff K P (J K Q)).2 ⟨j_mem_mk K Q, (le_iff_part _ _).2 fun p q hpq => by
    rw [kp_part]
    exact j_gen K Q p q ((le_iff_part _ _).1 h p q hpq)⟩

theorem j_bot (K : List (Fin d × Bool)) (hK : K ≠ []) :
    J K (⊥ : Part K) = Subgroup.zpowers (FreeGroup.mk K) := by
  rw [Subgroup.zpowers_eq_closure]
  apply le_antisymm
  · unfold J
    rw [Subgroup.closure_le]
    rintro g (hg | ⟨p, q, hpq, rfl⟩)
    · exact Subgroup.subset_closure hg
    · have hq : q ∈ (⊥ : Part K).part p := (part_eq_iff _ p q).1 hpq
      have hp : p ∈ (⊥ : Part K).part p := (⊥ : Part K).mem_part (mem_univ p)
      have hm := (⊥ : Part K).part_mem.2 (mem_univ p)
      rw [Finpartition.mem_bot_iff] at hm
      obtain ⟨a, -, ha⟩ := hm
      rw [← ha] at hp hq
      rw [Finset.mem_singleton] at hp hq
      rw [hp, hq, mul_inv_cancel]
      exact Subgroup.one_mem _
  · exact Subgroup.closure_mono Set.subset_union_left

theorem gt_gen (K : List (Fin d × Bool)) (hK : K ≠ []) (Q' Q : Part K) (m : ℕ)
    (h : Gen K Q' Q m) : ∃ g : Fin m → FreeGroup (Fin d),
      J K Q = Subgroup.closure (↑(J K Q') ∪ Set.range g) := by
  obtain ⟨s, -, hle, hs, hmin⟩ := h
  refine ⟨fun i => pfx K (s i).1 * (pfx K (s i).2)⁻¹, ?_⟩
  set H : Subgroup (FreeGroup (Fin d)) := Subgroup.closure
    (↑(J K Q') ∪ Set.range fun i => pfx K (s i).1 * (pfx K (s i).2)⁻¹) with hHdef
  have h1 : J K Q' ≤ H := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have h2 := (j_le_iff K Q' H).1 h1
  apply le_antisymm
  · refine (j_le_iff K Q H).2 ⟨h2.1, hmin _ (kp_ff K H h2.1) h2.2 fun i => ?_⟩
    rw [kp_part]
    exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  · rw [hHdef, Subgroup.closure_le]
    rintro g (hg | ⟨i, rfl⟩)
    · exact j_mono K Q' Q hle hg
    · exact j_gen K Q _ _ (hs i)

end Puder.PP.PartG
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part G: generation, critical subgroups -/
alias gt_gen := Puder.PP.PartG.gt_gen

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartG
variable {d : ℕ}
theorem crit_finite (w : FreeGroup (Fin d)) : (Crit w).Finite :=
  (Puder.setOf_isAlgExt_finite_of_fg (Subgroup.zpowers w)
    ⟨{w}, by rw [Subgroup.zpowers_eq_closure]; simp⟩).subset
    fun _ hJ => Puder.isAlgExt_zpowers_of_mem_crit hJ

/-! ## Words all of whose steps run along edges of the cycle -/
/-- The `x`-edge leaving the coset `Jc y` is the image of an edge of the cycle. -/
def CE (K : List (Fin d × Bool)) (Jc : Subgroup (FreeGroup (Fin d))) (y : FreeGroup (Fin d))
    (x : Fin d) : Prop :=
  ∃ q : Fin K.length, lab K q = x ∧ RC Jc (pfx K (tl K q)) y

/-- The tail of the edge traversed by the letter `(x, b)` read from `t`. -/
def tailOf (t : FreeGroup (Fin d)) (x : Fin d) (b : Bool) : FreeGroup (Fin d) :=
  if b then t else t * (FreeGroup.of x)⁻¹

theorem tailOf_mul (j t : FreeGroup (Fin d)) (x : Fin d) (b : Bool) :
    tailOf (j * t) x b = j * tailOf t x b := by
  cases b <;> simp [tailOf, mul_assoc]

/-- Every step of the walk of `L` from the coset of `t` runs along the image of a cycle edge. -/
def GoodFrom (K : List (Fin d × Bool)) (Jc : Subgroup (FreeGroup (Fin d))) :
    FreeGroup (Fin d) → List (Fin d × Bool) → Prop
  | _, [] => True
  | t, (x, b) :: c => CE K Jc (tailOf t x b) x ∧ GoodFrom K Jc (t * FreeGroup.mk [(x, b)]) c

end Puder.PP.PartG
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartG
variable {d : ℕ}
variable {K : List (Fin d × Bool)} {Jc : Subgroup (FreeGroup (Fin d))}
theorem goodFrom_append (A B : List (Fin d × Bool)) (t : FreeGroup (Fin d)) :
    GoodFrom K Jc t (A ++ B) ↔ GoodFrom K Jc t A ∧ GoodFrom K Jc (t * FreeGroup.mk A) B := by
  induction A generalizing t with
  | nil =>
    have : t * FreeGroup.mk ([] : List (Fin d × Bool)) = t := mul_one t
    rw [this]
    simp [GoodFrom]
  | cons a A ih =>
    obtain ⟨x, b⟩ := a
    have : t * FreeGroup.mk ((x, b) :: A) = t * FreeGroup.mk [(x, b)] * FreeGroup.mk A := by
      rw [mk_cons, mul_assoc]
    rw [this]
    simp only [List.cons_append, GoodFrom, ih, and_assoc]

theorem goodFrom_shift {L : List (Fin d × Bool)} {t j : FreeGroup (Fin d)}
    (h : GoodFrom K Jc t L) (hj : j ∈ Jc) : GoodFrom K Jc (j * t) L := by
  induction L generalizing t with
  | nil => trivial
  | cons a L ih =>
    obtain ⟨x, b⟩ := a
    obtain ⟨⟨q, hq, hqr⟩, h2⟩ := h
    refine ⟨⟨q, hq, ?_⟩, ?_⟩
    · rw [tailOf_mul]; exact hqr.mul_left hj
    · rw [mul_assoc]; exact ih h2

theorem mk_mul_not (x : Fin d) (b : Bool) :
    FreeGroup.mk [(x, b)] * FreeGroup.mk [(x, !b)] = 1 := by
  cases b
  · show (FreeGroup.of x)⁻¹ * FreeGroup.of x = 1
    group
  · show FreeGroup.of x * (FreeGroup.of x)⁻¹ = 1
    group

theorem goodFrom_step {L₁ L₂ : List (Fin d × Bool)} {t : FreeGroup (Fin d)}
    (hs : FreeGroup.Red.Step L₁ L₂) (h : GoodFrom K Jc t L₁) : GoodFrom K Jc t L₂ := by
  cases hs with
  | @not A B x b =>
    rw [goodFrom_append] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2.2.2
    rw [mul_assoc, mk_mul_not, mul_one] at h2
    exact h2

theorem goodFrom_red {L₁ L₂ : List (Fin d × Bool)} {t : FreeGroup (Fin d)}
    (hs : FreeGroup.Red L₁ L₂) (h : GoodFrom K Jc t L₁) : GoodFrom K Jc t L₂ := by
  have hs' : Relation.ReflTransGen FreeGroup.Red.Step L₁ L₂ := hs
  clear hs
  induction hs' with
  | refl => exact h
  | tail _ hstep ih => exact goodFrom_step hstep ih

theorem goodFrom_invRev {L : List (Fin d × Bool)} {t : FreeGroup (Fin d)}
    (h : GoodFrom K Jc t L) : GoodFrom K Jc (t * FreeGroup.mk L) (FreeGroup.invRev L) := by
  induction L generalizing t with
  | nil => simp [FreeGroup.invRev, GoodFrom]
  | cons a c ih =>
    obtain ⟨x, b⟩ := a
    have e : FreeGroup.invRev ((x, b) :: c) = FreeGroup.invRev c ++ [(x, !b)] := by
      simp [FreeGroup.invRev]
    have hm : t * FreeGroup.mk ((x, b) :: c) = t * FreeGroup.mk [(x, b)] * FreeGroup.mk c := by
      rw [mk_cons, mul_assoc]
    rw [e, goodFrom_append, hm]
    refine ⟨ih h.2, ?_⟩
    rw [← FreeGroup.inv_mk, mul_inv_cancel_right]
    refine ⟨?_, trivial⟩
    have : tailOf (t * FreeGroup.mk [(x, b)]) x (!b) = tailOf t x b := by
      cases b
      · rw [mk_false]; simp [tailOf]
      · rw [mk_true]; simp [tailOf]
    rw [this]
    exact h.1

theorem goodFrom_K (hH : FreeGroup.mk K ∈ Jc) :
    ∀ (c a : List (Fin d × Bool)), K = a ++ c → GoodFrom K Jc (FreeGroup.mk a) c := by
  intro c
  induction c with
  | nil => intro a _; trivial
  | cons e c ih =>
    obtain ⟨x, b⟩ := e
    intro a h
    have hlen : a.length < K.length := by rw [h]; simp
    have hget : K[a.length] = (x, b) := by simp [h]
    have hpq : pfx K a.length = FreeGroup.mk a := by
      unfold pfx
      rw [h]; simp
    have hps := pfx_succ K a.length hlen
    rw [hget, hpq] at hps
    have hw : RC Jc (pfx K (a.length + 1)) (pfx K (cnxt (⟨a.length, hlen⟩ : Fin K.length))) :=
      pfx_wrap K Jc hH ⟨a.length, hlen⟩
    refine ⟨⟨⟨a.length, hlen⟩, ?_, ?_⟩, ?_⟩
    · show (K[a.length]).1 = x
      rw [hget]
    · have htl : tl K (⟨a.length, hlen⟩ : Fin K.length) =
          if b then ⟨a.length, hlen⟩ else cnxt ⟨a.length, hlen⟩ := by
        show (if (K[a.length]).2 then _ else _) = _
        rw [hget]
      rw [htl]
      cases b
      · simp only [Bool.false_eq_true, if_false]
        rw [hps] at hw
        exact hw.symm
      · simp only [if_true]
        show RC Jc (pfx K a.length) (FreeGroup.mk a)
        rw [hpq]; exact RC.refl _ _
    · rw [FreeGroup.mul_mk]
      apply ih
      rw [h]; simp

theorem good_zpowers (hH : FreeGroup.mk K ∈ Jc) (h : FreeGroup (Fin d))
    (hh : h ∈ Subgroup.zpowers (FreeGroup.mk K)) : GoodFrom K Jc 1 h.toWord := by
  have key : h ∈ Jc ∧ ∃ L, FreeGroup.mk L = h ∧ GoodFrom K Jc 1 L := by
    rw [Subgroup.zpowers_eq_closure] at hh
    induction hh using Subgroup.closure_induction with
    | mem g hg =>
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact ⟨hH, K, rfl, goodFrom_K hH K [] rfl⟩
    | one => exact ⟨Jc.one_mem, [], rfl, trivial⟩
    | mul a b _ _ ha hb =>
      obtain ⟨ha1, L1, rfl, h1⟩ := ha
      obtain ⟨hb1, L2, rfl, h2⟩ := hb
      refine ⟨Jc.mul_mem ha1 hb1, L1 ++ L2, FreeGroup.mul_mk.symm, ?_⟩
      rw [goodFrom_append]
      refine ⟨h1, ?_⟩
      have := goodFrom_shift h2 ha1
      rw [mul_one] at this
      rw [one_mul]
      exact this
    | inv a _ ha =>
      obtain ⟨ha1, L, rfl, h1⟩ := ha
      refine ⟨Jc.inv_mem ha1, FreeGroup.invRev L, FreeGroup.inv_mk.symm, ?_⟩
      have := goodFrom_shift (goodFrom_invRev h1) (Jc.inv_mem ha1)
      rw [one_mul, inv_mul_cancel] at this
      exact this
  obtain ⟨_, L, rfl, hL⟩ := key
  rw [FreeGroup.toWord_mk]
  exact goodFrom_red FreeGroup.reduce.red hL

theorem split_of_goodFrom {L p s : List (Fin d × Bool)} {t : FreeGroup (Fin d)} {x : Fin d}
    {b : Bool} (h : GoodFrom K Jc t L) (hs : L = p ++ (x, b) :: s) :
    CE K Jc (tailOf (t * FreeGroup.mk p) x b) x := by
  rw [hs, goodFrom_append] at h
  exact h.2.1

theorem goodFrom_of_splits {L : List (Fin d × Bool)} {t : FreeGroup (Fin d)}
    (h : ∀ (p : List (Fin d × Bool)) (x : Fin d) (b : Bool) (s : List (Fin d × Bool)),
      L = p ++ (x, b) :: s → CE K Jc (tailOf (t * FreeGroup.mk p) x b) x) :
    GoodFrom K Jc t L := by
  induction L generalizing t with
  | nil => trivial
  | cons a c ih =>
    obtain ⟨x, b⟩ := a
    refine ⟨?_, ih fun p y e s hs => ?_⟩
    · have := h [] x b c rfl
      have e1 : t * FreeGroup.mk ([] : List (Fin d × Bool)) = t := mul_one t
      rw [e1] at this
      exact this
    · have := h ((x, b) :: p) y e s (by rw [hs]; rfl)
      rw [mk_cons, ← mul_assoc] at this
      exact this

/-- (α): a good walk starting at a cycle position ends at a cycle position, modulo `J K Q`. -/
theorem alpha (hH : FreeGroup.mk K ∈ Jc) :
    ∀ (L : List (Fin d × Bool)) (t : FreeGroup (Fin d)), GoodFrom K Jc t L →
      ∀ u : Fin K.length, RC (J K (kp K Jc)) t (pfx K u) →
        ∃ u' : Fin K.length, RC (J K (kp K Jc)) (t * FreeGroup.mk L) (pfx K u') := by
  have hle : J K (kp K Jc) ≤ Jc := (j_le_iff K _ Jc).2 ⟨hH, le_rfl⟩
  have hbridge : ∀ p q : Fin K.length, RC Jc (pfx K p) (pfx K q) →
      RC (J K (kp K Jc)) (pfx K p) (pfx K q) := fun p q h =>
    j_gen K _ p q ((kp_part K Jc p q).2 h)
  intro L
  induction L with
  | nil =>
    intro t _ u hu
    refine ⟨u, ?_⟩
    have e1 : t * FreeGroup.mk ([] : List (Fin d × Bool)) = t := mul_one t
    rw [e1]; exact hu
  | cons a c ih =>
    obtain ⟨x, b⟩ := a
    intro t hg u hu
    obtain ⟨⟨q, hq, hqr⟩, hc⟩ := hg
    have he := edge_rel K (J K (kp K Jc)) (j_mem_mk K _) q
    rw [hq] at he
    have hm : t * FreeGroup.mk ((x, b) :: c) = t * FreeGroup.mk [(x, b)] * FreeGroup.mk c := by
      rw [mk_cons, mul_assoc]
    rw [hm]
    cases b
    · apply ih _ hc (tl K q)
      rw [mk_false]
      have hqr' : RC Jc (pfx K (tl K q)) (t * (FreeGroup.of x)⁻¹) := hqr
      have h0 := hqr'.mul_right (FreeGroup.of x)
      have e1 : t * (FreeGroup.of x)⁻¹ * FreeGroup.of x = t := by group
      rw [e1] at h0
      have h1 : RC Jc (pfx K (hd K q)) (pfx K u) := ((he.mono hle).trans h0).trans (hu.mono hle)
      have h2 := hbridge _ _ h1
      have h3 := (hu.trans h2.symm).mul_right (FreeGroup.of x)⁻¹
      have h4 := he.mul_right (FreeGroup.of x)⁻¹
      have e2 : pfx K (tl K q) * FreeGroup.of x * (FreeGroup.of x)⁻¹ = pfx K (tl K q) := by group
      rw [e2] at h4
      exact h3.trans h4
    · apply ih _ hc (hd K q)
      rw [mk_true]
      have hqr' : RC Jc (pfx K (tl K q)) t := hqr
      have h1 : RC Jc (pfx K (tl K q)) (pfx K u) := hqr'.trans (hu.mono hle)
      have h2 := hbridge _ _ h1
      exact ((hu.trans h2.symm).mul_right (FreeGroup.of x)).trans he.symm

theorem gt_crit (K : List (Fin d × Bool)) (hK : K ≠ []) (Jc : Subgroup (FreeGroup (Fin d)))
    (h : Jc ∈ Crit (FreeGroup.mk K)) : ∃ Q : Part K, FF K Q ∧ J K Q = Jc := by
  have hH : FreeGroup.mk K ∈ Jc := h.1
  have halg := Puder.isAlgExt_zpowers_of_mem_crit h
  have hle : J K (kp K Jc) ≤ Jc := (j_le_iff K _ Jc).2 ⟨hH, le_rfl⟩
  refine ⟨kp K Jc, kp_ff K Jc hH, le_antisymm hle ?_⟩
  intro g hg
  have hgood : GoodFrom K Jc 1 g.toWord := by
    apply goodFrom_of_splits
    intro p x b s hs
    have htr : Traverses Jc g p.length (tailOf (1 * FreeGroup.mk p) x b) x := by
      refine ⟨p, s, b, hs, rfl, ?_⟩
      rw [one_mul]
      exact RC.refl Jc (tailOf (FreeGroup.mk p) x b)
    obtain ⟨h', hh', i, p', s', b', hs', -, hmem⟩ :=
      Puder.exists_mem_traverses_of_isAlgExt_of_isCoreEdge (Subgroup.zpowers (FreeGroup.mk K)) Jc
        halg _ x ⟨g, hg, _, htr⟩
    obtain ⟨q, hq, hqr⟩ := split_of_goodFrom (good_zpowers hH h' hh') hs'
    refine ⟨q, hq, hqr.trans ?_⟩
    rw [one_mul]
    exact hmem
  have hn : 0 < K.length := List.length_pos_iff.2 hK
  have h0 : pfx K ((⟨0, hn⟩ : Fin K.length) : ℕ) = 1 := rfl
  obtain ⟨u', hu'⟩ := alpha hH _ 1 hgood ⟨0, hn⟩ (by rw [h0]; exact RC.refl _ _)
  rw [one_mul, FreeGroup.mk_toWord] at hu'
  have h1 : RC Jc (pfx K u') (pfx K ((⟨0, hn⟩ : Fin K.length) : ℕ)) := by
    rw [h0]
    have := Jc.mul_mem (hu'.mono hle).symm hg
    simpa [RC] using this
  have h2 : RC (J K (kp K Jc)) (pfx K u') (pfx K ((⟨0, hn⟩ : Fin K.length) : ℕ)) :=
    j_gen K _ _ _ ((kp_part K Jc _ _).2 h1)
  rw [h0] at h2
  have := hu'.trans h2
  simpa [RC] using this

end Puder.PP.PartG
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias gt_crit := Puder.PP.PartG.gt_crit

alias crit_finite := Puder.PP.PartG.crit_finite

alias j_bot := Puder.PP.PartG.j_bot

end Puder.PP
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartP
variable {d N : ℕ}
/-!
# Part P: a primitive word has one expected lift (`gt_psi`)

`Psi K Q N` is the expected number of fixed points of the word `Kt K Q` over the edge alphabet,
and that word belongs to a basis (`exists_basis`).
-/
/-! ## Fixed points of a word = closed walks (after HP102) -/
/-- The permutation by which a letter moves a walk one step forward. -/
def rho (σ : Fin d → Perm (Fin N)) (x : Fin d × Bool) : Perm (Fin N) :=
  if x.2 then σ x.1 else (σ x.1)⁻¹

/-- The walk product of the first `p` letters (first letter applied first). -/
def pre (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (p : ℕ) : Perm (Fin N) :=
  ((K.take p).map (rho σ)).reverse.prod

theorem pre_zero (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) : pre σ K 0 = 1 := by
  simp [pre]

theorem pre_succ (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (p : ℕ)
    (hp : p < K.length) : pre σ K (p + 1) = rho σ K[p] * pre σ K p := by
  rw [pre, pre, List.take_add_one, List.getElem?_eq_getElem hp]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]

/-- The edge condition at position `p` of a cycle labelled by `K`. -/
def Step (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (h : Fin K.length → Fin N)
    (p : Fin K.length) : Prop :=
  σ (K[p]).1 (h (if (K[p]).2 then p else cnxt p)) = h (if (K[p]).2 then cnxt p else p)

theorem step_iff (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (h : Fin K.length → Fin N)
    (p : Fin K.length) : Step σ K h p ↔ h (cnxt p) = rho σ K[p] (h p) := by
  unfold Step rho
  by_cases hb : (K[p]).2 = true
  · rw [if_pos hb, if_pos hb, if_pos hb, eq_comm]
  · rw [if_neg hb, if_neg hb, if_neg hb, Perm.eq_inv_iff_eq]

theorem card_cycle (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (hn : 0 < K.length) :
    (univ.filter fun h : Fin K.length → Fin N => ∀ p, Step σ K h p).card =
      (univ.filter fun y : Fin N => pre σ K K.length y = y).card := by
  have hfw : ∀ h : Fin K.length → Fin N, (∀ p, Step σ K h p) →
      ∀ k (hk : k < K.length), h ⟨k, hk⟩ = pre σ K k (h ⟨0, hn⟩) := by
    intro h hs k
    induction k with
    | zero => intro hk; simp [pre_zero]
    | succ k ih =>
      intro hk
      have h1 := (step_iff σ K h ⟨k, by omega⟩).1 (hs _)
      have h2 : cnxt (⟨k, by omega⟩ : Fin K.length) = ⟨k + 1, hk⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hk)
      rw [h2] at h1
      rw [h1, ih (by omega), pre_succ σ K k (by omega), Perm.mul_apply]
      rfl
  obtain ⟨m, hm⟩ : ∃ m, K.length = m + 1 := ⟨K.length - 1, by omega⟩
  have hclose : ∀ h : Fin K.length → Fin N, (∀ p, Step σ K h p) →
      pre σ K K.length (h ⟨0, hn⟩) = h ⟨0, hn⟩ := by
    intro h hs
    have h1 := (step_iff σ K h ⟨m, by omega⟩).1 (hs _)
    have h2 : cnxt (⟨m, by omega⟩ : Fin K.length) = ⟨0, hn⟩ :=
      Fin.ext (by simp only [cnxt]; rw [← hm, Nat.mod_self])
    rw [h2] at h1
    have h3 := hfw h hs m (by omega)
    rw [congrArg (pre σ K) hm, pre_succ σ K m (by omega), Perm.mul_apply, ← h3, h1]
    rfl
  refine card_bij' (fun h _ => h ⟨0, hn⟩) (fun y _ => fun p => pre σ K p y) ?_ ?_ ?_ ?_
  · intro h hh
    exact mem_filter.2 ⟨mem_univ _, hclose h (mem_filter.1 hh).2⟩
  · intro y hy
    have hy := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, fun p => (step_iff σ K _ p).2 ?_⟩
    by_cases hp : (p : ℕ) + 1 < K.length
    · have h2 : cnxt p = ⟨(p : ℕ) + 1, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
      rw [h2]
      show pre σ K ((p : ℕ) + 1) y = _
      rw [pre_succ σ K p p.2, Perm.mul_apply]
      rfl
    · have hp' : (p : ℕ) + 1 = K.length := by omega
      have h2 : cnxt p = ⟨0, hn⟩ := Fin.ext (by simp only [cnxt]; rw [hp', Nat.mod_self])
      rw [h2]
      show pre σ K 0 y = _
      rw [pre_zero, Perm.one_apply]
      conv_lhs => rw [← hy, ← hp']
      rw [pre_succ σ K p p.2, Perm.mul_apply]
      rfl
  · intro h hh
    funext p
    exact (hfw h (mem_filter.1 hh).2 p p.2).symm
  · intro y _
    simp [pre_zero]

theorem lift_inv_mk (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) :
    FreeGroup.lift σ⁻¹ (FreeGroup.mk K) = (pre σ K K.length)⁻¹ := by
  rw [FreeGroup.lift_mk, pre, List.take_length, List.prod_inv_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rcases x with ⟨i, b⟩
  cases b <;> simp [rho]

theorem card_fix_inv (W : Perm (Fin N)) :
    (univ.filter fun y : Fin N => W⁻¹ y = y).card = (univ.filter fun y : Fin N => W y = y).card := by
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and]
  rw [Perm.inv_eq_iff_eq, eq_comm]

/-! ## The expectation of a basis element -/
theorem sum_card_fix_perm (hN : 1 ≤ N) :
    ∑ τ : Perm (Fin N), ((univ.filter fun x => τ x = x).card : ℝ) =
      (Fintype.card (Perm (Fin N)) : ℝ) := by
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Perm (Fin N)) (Fin N)
  have h1 : Fintype.card (MulAction.orbitRel.Quotient (Perm (Fin N)) (Fin N)) = 1 := by
    have hs := (MulAction.pretransitive_iff_subsingleton_quotient (Perm (Fin N)) (Fin N)).mp
      inferInstance
    rw [Fintype.card_eq_one_iff]
    exact ⟨Quotient.mk (MulAction.orbitRel (Perm (Fin N)) (Fin N)) ⟨0, hN⟩,
      fun y => Subsingleton.elim _ _⟩
  rw [h1, one_mul] at hB
  rw [← hB, Nat.cast_sum]
  refine sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Fintype.card_subtype]
  simp [MulAction.mem_fixedBy, Perm.smul_def]

theorem fix_eq_one {e : ℕ} (w : FreeGroup (Fin e))
    (B : FreeGroupBasis (Fin e) (FreeGroup (Fin e))) (i : Fin e) (hi : B i = w) (hN : 1 ≤ N) :
    Fix w N = 1 := by
  let Eq : (Fin e → Perm (Fin N)) ≃ (Fin e → Perm (Fin N)) := FreeGroup.lift.trans B.lift.symm
  have he : ∀ σ, Eq σ i = FreeGroup.lift σ w := fun σ => by
    rw [← hi]
    simp [Eq, FreeGroupBasis.lift_symm_apply]
    rfl
  have hc : (Fintype.card (Fin e → Perm (Fin N)) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin e → Perm (Fin N)) := Fintype.card_pos
    positivity
  unfold Fix StrongConv.uniformExp
  rw [div_eq_one_iff_eq hc]
  set f : Perm (Fin N) → ℝ := fun τ => ((univ.filter fun x => τ x = x).card : ℝ) with hf
  change ∑ σ, f (FreeGroup.lift σ w) = _
  simp_rw [← he]
  rw [Eq.sum_comp (fun τ => f (τ i)), ← (Equiv.funSplitAt i (Perm (Fin N))).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.funSplitAt_symm_apply, dif_pos, sum_const, card_univ, nsmul_eq_mul]
  rw [Fintype.card_congr (Equiv.funSplitAt i (Perm (Fin N))), Fintype.card_prod]
  have h2 := sum_card_fix_perm hN
  simp only [hf] at h2 ⊢
  rw [← mul_sum, h2]
  push_cast
  ring

end Puder.PP.PartP
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartF
variable {d : ℕ}
/-!
# Part F: PP15 Theorem 1.8 for a cyclically reduced word (assembly)
-/
/-! ### Partitions -/
lemma part_top (K : List (Fin d × Bool)) (p : Fin K.length) :
    (⊤ : Part K).part p = univ := by
  have h1 : (⊤ : Part K).part p ∈ (⊤ : Part K).parts := (Finpartition.part_mem _).2 (mem_univ p)
  exact mem_singleton.1 (Finpartition.parts_top_subset _ h1)

lemma ff_top (K : List (Fin d × Bool)) : FF K ⊤ := by
  intro e e' _
  simp [part_top]

lemma part_subset_of_le {K : List (Fin d × Bool)} {P Q : Part K} (h : P ≤ Q)
    (p : Fin K.length) : P.part p ⊆ Q.part p := by
  obtain ⟨c, hc, hsub⟩ := h ((Finpartition.part_mem _).2 (mem_univ p))
  have hp : p ∈ c := hsub ((Finpartition.mem_part_self _).2 (mem_univ p))
  rw [Finpartition.part_eq_of_mem _ hc hp]
  exact hsub

lemma part_eq_of_le {K : List (Fin d × Bool)} {P Q : Part K} (h : P ≤ Q)
    {p q : Fin K.length} (hpq : P.part p = P.part q) : Q.part p = Q.part q := by
  have hq : q ∈ Q.part p := by
    apply part_subset_of_le h p
    rw [hpq]
    exact (Finpartition.mem_part_self _).2 (mem_univ q)
  exact (Finpartition.part_eq_of_mem _ ((Finpartition.part_mem _).2 (mem_univ p)) hq).symm

lemma le_of_part_imp {K : List (Fin d × Bool)} {P Q : Part K}
    (h : ∀ p q : Fin K.length, P.part p = P.part q → Q.part p = Q.part q) : P ≤ Q := by
  intro b hb
  obtain ⟨p, hp⟩ := P.nonempty_of_mem_parts hb
  refine ⟨Q.part p, (Finpartition.part_mem _).2 (mem_univ p), ?_⟩
  intro q hq
  have h1 : P.part p = b := Finpartition.part_eq_of_mem _ hb hp
  have h2 : P.part q = b := Finpartition.part_eq_of_mem _ hb hq
  have h3 := h p q (h1.trans h2.symm)
  rw [h3]
  exact (Finpartition.mem_part_self _).2 (mem_univ q)

/-! ### The subgroups `J K Q` -/
lemma J_mono {K : List (Fin d × Bool)} {P Q : Part K} (h : P ≤ Q) : J K P ≤ J K Q := by
  unfold J
  apply Subgroup.closure_mono
  apply Set.union_subset_union_right
  rintro g ⟨p, q, hpq, rfl⟩
  exact ⟨p, q, part_eq_of_le h hpq, rfl⟩

lemma mk_mem_J (K : List (Fin d × Bool)) (P : Part K) : FreeGroup.mk K ∈ J K P :=
  Subgroup.subset_closure (Or.inl rfl)

lemma J_inj (K : List (Fin d × Bool)) (hK : K ≠ []) {P Q : Part K} (hP : FF K P)
    (hQ : FF K Q) (h : J K P = J K Q) : P = Q := by
  have key : ∀ P Q : Part K, FF K Q → J K P = J K Q → P ≤ Q := by
    intro P Q hQ h
    apply le_of_part_imp
    intro p q hpq
    apply gt_inj K hK Q hQ
    rw [← h]
    exact Subgroup.subset_closure (Or.inr ⟨p, q, hpq, rfl⟩)
  exact le_antisymm (key P Q hQ h) (key Q P hP h.symm)

lemma mk_ne_one (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) : FreeGroup.mk K ≠ 1 := by
  intro h
  have h2 := congrArg FreeGroup.toWord h
  rw [FreeGroup.toWord_mk, hred.isReduced.reduce_eq, FreeGroup.toWord_one] at h2
  exact hK h2

lemma prim_bot (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) :
    IsPrimitiveIn (J K (⊥ : Part K)) (FreeGroup.mk K) := by
  rw [j_bot K hK]
  exact (isPrimitiveIn_zpowers _ (mk_ne_one K hK hred)).1

/-! ### Ranks -/
/-- The rank of `J K Q`. -/
def rk (K : List (Fin d × Bool)) (Q : Part K) : ℕ := (E K Q).card + 1 - Q.parts.card

lemma hasRank_rk (K : List (Fin d × Bool)) (hK : K ≠ []) (Q : Part K) (hQ : FF K Q) :
    HasRank (J K Q) (rk K Q) := gt_rank K hK Q hQ

lemma rk_pos (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) (Q : Part K) (hQ : FF K Q) : 1 ≤ rk K Q := by
  have := ex_pos K hK hred Q hQ
  unfold rk
  omega

lemma ek_eq (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) (Q : Part K) (hQ : FF K Q) :
    ((E K Q).card : ℤ) - (Q.parts.card : ℤ) = ((rk K Q - 1 : ℕ) : ℤ) := by
  have := ex_pos K hK hred Q hQ
  unfold rk
  omega

lemma hasRank_unique {H : Subgroup (FreeGroup (Fin d))} {r s : ℕ} (h1 : HasRank H r)
    (h2 : HasRank H s) : r = s := by
  have hH : H = Subgroup.closure
      (↑H ∪ Set.range (Fin.elim0 : Fin 0 → FreeGroup (Fin d))) := by
    simp
  have a := (fg_a H H r s 0 h1 h2 _ hH).1
  have b := (fg_a H H s r 0 h2 h1 _ hH).1
  omega

lemma prank_le {w : FreeGroup (Fin d)} {H : Subgroup (FreeGroup (Fin d))} {s : ℕ}
    (hw : w ∈ H) (hs : HasRank H s) (hnp : ¬ IsPrimitiveIn H w) :
    primitivityRank w ≤ (s : ℕ∞) :=
  iInf₂_le s ⟨H, hw, hs, hnp⟩

lemma gen_rank (K : List (Fin d × Bool)) (hK : K ≠ []) {Q' Q : Part K} {m : ℕ}
    (hQ' : FF K Q') (h : Gen K Q' Q m) :
    rk K Q ≤ rk K Q' + m ∧ (rk K Q = rk K Q' + m →
      ∀ w, IsPrimitiveIn (J K Q') w → IsPrimitiveIn (J K Q) w) := by
  obtain ⟨g, hg⟩ := gt_gen K hK Q' Q m h
  have hQ : FF K Q := by
    obtain ⟨s, hQ, -⟩ := h
    exact hQ
  exact fg_a (J K Q') (J K Q) _ _ m (hasRank_rk K hK Q' hQ') (hasRank_rk K hK Q hQ) g hg

lemma gen_zero {K : List (Fin d × Bool)} {Q' Q : Part K} (hQ' : FF K Q')
    (h : Gen K Q' Q 0) : Q ≤ Q' := by
  obtain ⟨s, -, -, -, hmin⟩ := h
  exact hmin Q' hQ' le_rfl (fun i => i.elim0)

/-! ### The engine and `R` -/
/-- Clause (i) of `engine`. -/
def EngI (K : List (Fin d × Bool)) (C : Part K → Part K → ℝ → ℝ) : Prop :=
  ∀ Q' Q : Part K, FF K Q' → FF K Q → Q' ≤ Q → ∀ x : ℝ, 0 < x → x * K.length < 1 →
    Lx K Q' Q x = ∑ Q'' ∈ (univ : Finset (Part K)).filter
      (fun Q'' => FF K Q'' ∧ Q' ≤ Q'' ∧ Q'' ≤ Q), C Q' Q'' x

/-- Clause (ii) of `engine`. -/
def EngII (K : List (Fin d × Bool)) (C : Part K → Part K → ℝ → ℝ) : Prop :=
  ∀ Q' Q : Part K, FF K Q' → FF K Q → Q' ≤ Q → ∀ m : ℕ, (∀ m' < m, ¬ Gen K Q' Q m') →
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → 2 * x * K.length ≤ 1 →
      |C Q' Q x| ≤ B * x ^ (((E K Q').card : ℤ) - (Q'.parts.card : ℤ) + m)

/-- `R(Q) = Σ_{Q' ≤ Q} C Q' Q`. -/
noncomputable def R (K : List (Fin d × Bool)) (C : Part K → Part K → ℝ → ℝ) (Q : Part K)
    (x : ℝ) : ℝ :=
  ∑ Q' ∈ (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ Q), C Q' Q x

lemma sum_Lx {K : List (Fin d × Bool)} {C : Part K → Part K → ℝ → ℝ} (h1 : EngI K C)
    {Q : Part K} (hQ : FF K Q) {x : ℝ} (hx : 0 < x) (hxn : x * K.length < 1) :
    ∑ Q' ∈ (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ Q), Lx K Q' Q x =
      ∑ Q'' ∈ (univ : Finset (Part K)).filter (fun Q'' => FF K Q'' ∧ Q'' ≤ Q),
        R K C Q'' x := by
  have h : ∀ Q' ∈ (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ Q),
      Lx K Q' Q x = ∑ Q'' ∈ (univ : Finset (Part K)).filter
        (fun Q'' => FF K Q'' ∧ Q' ≤ Q'' ∧ Q'' ≤ Q), C Q' Q'' x := by
    intro Q' hQ'
    rw [mem_filter] at hQ'
    exact h1 Q' Q hQ'.2.1 hQ hQ'.2.2 x hx hxn
  rw [sum_congr rfl h]
  unfold R
  apply sum_comm'
  intro Q' Q''
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, _⟩, c, e, f⟩
    exact ⟨⟨a, e⟩, c, f⟩
  · rintro ⟨⟨a, e⟩, c, f⟩
    exact ⟨⟨a, e.trans f⟩, c, e, f⟩

lemma x_facts {n N : ℕ} (hN : n < N) : 0 < 1 / (N : ℝ) ∧ 1 / (N : ℝ) * n < 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨by positivity, ?_⟩
  rw [one_div_mul_eq_div, div_lt_one hN0]
  exact_mod_cast hN

lemma psi_eq (K : List (Fin d × Bool)) (hK : K ≠ []) {C : Part K → Part K → ℝ → ℝ}
    (h1 : EngI K C) (Q : Part K) (hQ : FF K Q) (N : ℕ) (hN : K.length < N) :
    Psi K Q N = ∑ Q'' ∈ (univ : Finset (Part K)).filter (fun Q'' => FF K Q'' ∧ Q'' ≤ Q),
      R K C Q'' (1 / N) := by
  rw [psi_eq_sum K hK Q hQ N hN.le]
  exact sum_Lx h1 hQ (x_facts hN).1 (x_facts hN).2

lemma fix_eq (K : List (Fin d × Bool)) (hK : K ≠ []) {C : Part K → Part K → ℝ → ℝ}
    (h1 : EngI K C) (N : ℕ) (hN : K.length < N) :
    Fix (FreeGroup.mk K) N =
      ∑ Q ∈ (univ : Finset (Part K)).filter (FF K), R K C Q (1 / N) := by
  have e : (univ : Finset (Part K)).filter (FF K) =
      (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ ⊤) := by
    ext Q
    simp
  rw [fix_eq_sum K hK N hN.le, e]
  exact sum_Lx h1 (ff_top K) (x_facts hN).1 (x_facts hN).2

/-! ### The diagonal -/
lemma vfib_self (K : List (Fin d × Bool)) (Q : Part K) {B : Finset (Fin K.length)}
    (hB : B ∈ Q.parts) : vfib K Q B = 1 := by
  unfold vfib
  have h : Q.parts.filter (· ⊆ B) = {B} := by
    ext A
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hA, hAB⟩
      obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hA
      exact Q.eq_of_mem_parts hA hB ha (hAB ha)
    · rintro rfl
      exact ⟨hB, subset_rfl⟩
  rw [h, card_singleton]

lemma efib_self (K : List (Fin d × Bool)) (Q : Part K)
    {ε : Fin d × Finset (Fin K.length) × Finset (Fin K.length)} (hε : ε ∈ E K Q) :
    efib K Q Q ε = 1 := by
  unfold efib
  obtain ⟨p, -, rfl⟩ := mem_image.1 hε
  have h : ((univ : Finset (Fin K.length)).filter
      fun q => qedge K Q q = qedge K Q p).image (qedge K Q) = {qedge K Q p} := by
    ext e
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · rintro rfl
      exact ⟨p, rfl, rfl⟩
  rw [h, card_singleton]

lemma Lx_self (K : List (Fin d × Bool)) (Q : Part K) (x : ℝ) :
    Lx K Q Q x = x ^ (((E K Q).card : ℤ) - (Q.parts.card : ℤ)) := by
  unfold Lx
  have h1 : ∏ B ∈ Q.parts, ∏ i ∈ Finset.range (vfib K Q B), (1 - (i : ℝ) * x) = 1 := by
    apply prod_eq_one
    intro B hB
    rw [vfib_self K Q hB]
    simp
  have h2 : ∏ ε ∈ E K Q, ∏ i ∈ Finset.range (efib K Q Q ε), (1 - (i : ℝ) * x) = 1 := by
    apply prod_eq_one
    intro ε hε
    rw [efib_self K Q hε]
    simp
  rw [h1, h2]
  simp

lemma C_self (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) {C : Part K → Part K → ℝ → ℝ} (h1 : EngI K C)
    {Q : Part K} (hQ : FF K Q) {x : ℝ} (hx : 0 < x) (hxn : x * K.length < 1) :
    C Q Q x = x ^ (rk K Q - 1) := by
  have h := h1 Q Q hQ hQ le_rfl x hx hxn
  have e : (univ : Finset (Part K)).filter (fun Q'' => FF K Q'' ∧ Q ≤ Q'' ∧ Q'' ≤ Q) =
      {Q} := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨-, a, b⟩
      exact le_antisymm b a
    · rintro rfl
      exact ⟨hQ, le_rfl, le_rfl⟩
  rw [e, sum_singleton, Lx_self, ek_eq K hK hred Q hQ, zpow_natCast] at h
  exact h.symm

lemma R_bot (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) {C : Part K → Part K → ℝ → ℝ} (h1 : EngI K C)
    {x : ℝ} (hx : 0 < x) (hxn : x * K.length < 1) : R K C ⊥ x = 1 := by
  have hb := ff_bot K hK hred
  have e : (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ ⊥) = {⊥} := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_singleton, le_bot_iff]
    constructor
    · rintro ⟨-, a⟩
      exact a
    · rintro rfl
      exact ⟨hb.1, rfl⟩
  unfold R
  rw [e, sum_singleton, C_self K hK hred h1 hb.1 hx hxn]
  have : rk K (⊥ : Part K) - 1 = 0 := by
    unfold rk
    rw [hb.2, Finpartition.card_bot]
    simp
  rw [this, pow_zero]

end Puder.PP.PartF
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartC
variable {d : ℕ}
/-!
# Part C: conjugation invariance, and leaf A from the cyclically reduced case
-/
/-! ## Transport along an automorphism -/
theorem map_map_symm (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    (J : Subgroup (FreeGroup (Fin d))) :
    (J.map (φ : FreeGroup (Fin d) →* FreeGroup (Fin d))).map
      (φ.symm : FreeGroup (Fin d) →* FreeGroup (Fin d)) = J := by
  ext x
  simp [Subgroup.mem_map]

theorem hasRank_map (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    {J : Subgroup (FreeGroup (Fin d))} {r : ℕ} (h : HasRank J r) :
    HasRank (J.map (φ : FreeGroup (Fin d) →* FreeGroup (Fin d))) r := by
  obtain ⟨b⟩ := h
  exact ⟨b.map (φ.subgroupMap J)⟩

theorem prim_map (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    {J : Subgroup (FreeGroup (Fin d))} {w : FreeGroup (Fin d)} (h : IsPrimitiveIn J w) :
    IsPrimitiveIn (J.map (φ : FreeGroup (Fin d) →* FreeGroup (Fin d))) (φ w) := by
  obtain ⟨ι, b, i, hi⟩ := h
  refine ⟨ι, b.map (φ.subgroupMap J), i, ?_⟩
  rw [FreeGroupBasis.map_apply, MulEquiv.coe_subgroupMap_apply, hi]

theorem not_prim_map (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    {J : Subgroup (FreeGroup (Fin d))} {w : FreeGroup (Fin d)} (h : ¬ IsPrimitiveIn J w) :
    ¬ IsPrimitiveIn (J.map (φ : FreeGroup (Fin d) →* FreeGroup (Fin d))) (φ w) := by
  intro h'
  have := prim_map φ.symm h'
  rw [map_map_symm, MulEquiv.symm_apply_apply] at this
  exact h this

theorem mem_map_of_mem (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    {J : Subgroup (FreeGroup (Fin d))} {w : FreeGroup (Fin d)} (h : w ∈ J) :
    φ w ∈ J.map (φ : FreeGroup (Fin d) →* FreeGroup (Fin d)) :=
  Subgroup.mem_map.2 ⟨w, h, rfl⟩

theorem primitivityRank_map_le (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    (w : FreeGroup (Fin d)) : primitivityRank (φ w) ≤ primitivityRank w := by
  unfold primitivityRank
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨J, hwJ, hJ, hnp⟩ := hr
  exact iInf₂_le (f := fun (r : ℕ) (_ : ∃ J : Subgroup (FreeGroup (Fin d)),
      φ w ∈ J ∧ HasRank J r ∧ ¬ IsPrimitiveIn J (φ w)) => (r : ℕ∞))
    r ⟨_, mem_map_of_mem φ hwJ, hasRank_map φ hJ, not_prim_map φ hnp⟩

theorem primitivityRank_map (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    (w : FreeGroup (Fin d)) : primitivityRank (φ w) = primitivityRank w := by
  refine le_antisymm (primitivityRank_map_le φ w) ?_
  have := primitivityRank_map_le φ.symm (φ w)
  rwa [MulEquiv.symm_apply_apply] at this

theorem map_mem_crit (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d))
    {J : Subgroup (FreeGroup (Fin d))} {w : FreeGroup (Fin d)} (h : J ∈ Crit w) :
    J.map (φ : FreeGroup (Fin d) →* FreeGroup (Fin d)) ∈ Crit (φ w) := by
  obtain ⟨hw, hnp, r, hr, hrk⟩ := h
  exact ⟨mem_map_of_mem φ hw, not_prim_map φ hnp, r, hasRank_map φ hr,
    by rw [primitivityRank_map]; exact hrk⟩

theorem crit_map (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d)) (w : FreeGroup (Fin d)) :
    Crit (φ w) = Subgroup.map (φ : FreeGroup (Fin d) →* FreeGroup (Fin d)) '' Crit w := by
  ext J
  constructor
  · intro h
    refine ⟨J.map (φ.symm : FreeGroup (Fin d) →* FreeGroup (Fin d)), ?_, ?_⟩
    · have := map_mem_crit φ.symm h
      rwa [MulEquiv.symm_apply_apply] at this
    · have := map_map_symm φ.symm J
      simpa using this
  · rintro ⟨J', hJ', rfl⟩
    exact map_mem_crit φ hJ'

theorem ncard_crit_map (φ : FreeGroup (Fin d) ≃* FreeGroup (Fin d)) (w : FreeGroup (Fin d)) :
    (Crit (φ w)).ncard = (Crit w).ncard := by
  rw [crit_map]
  exact Set.ncard_image_of_injective _ (Subgroup.map_injective φ.injective)

/-! ## Fixed points -/
theorem card_fix_conj {N : ℕ} (G W : Equiv.Perm (Fin N)) :
    (univ.filter fun y : Fin N => (G * W * G⁻¹) y = y).card =
      (univ.filter fun y : Fin N => W y = y).card := by
  refine card_bij' (fun y _ => G⁻¹ y) (fun y _ => G y) ?_ ?_ ?_ ?_
  · intro y hy
    have hy := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hy
    rw [Equiv.Perm.eq_inv_iff_eq, hy]
  · intro y hy
    have hy := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simp [Equiv.Perm.mul_apply, hy]
  · intro y _; simp
  · intro y _; simp

theorem fix_conj (g w : FreeGroup (Fin d)) (N : ℕ) : Fix (g * w * g⁻¹) N = Fix w N := by
  unfold Fix
  congr 1
  funext σ
  rw [map_mul, map_mul, map_inv, card_fix_conj]

theorem conj_inv (g w : FreeGroup (Fin d)) :
    primitivityRank (g * w * g⁻¹) = primitivityRank w ∧
      (Crit (g * w * g⁻¹)).ncard = (Crit w).ncard ∧
      ∀ N, Fix (g * w * g⁻¹) N = Fix w N := by
  have h1 := primitivityRank_map (MulAut.conj g) w
  have h2 := ncard_crit_map (MulAut.conj g) w
  rw [MulAut.conj_apply] at h1 h2
  exact ⟨h1, h2, fix_conj g w⟩

end Puder.PP.PartC
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part C: conjugation invariance and the target of leaf A -/

end Puder.PP
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartC
variable {d : ℕ}
/-! ## The trivial word -/
theorem freeGroup_fin_zero_eq_one (x : FreeGroup (Fin 0)) : x = 1 := by
  apply FreeGroup.toWord_injective
  rw [FreeGroup.toWord_one]
  rcases h : x.toWord with _ | ⟨a, _⟩
  · rfl
  · exact a.1.elim0

theorem eq_one_of_rank_zero {J : Subgroup (FreeGroup (Fin d))}
    (b : FreeGroupBasis (Fin 0) J) {x : FreeGroup (Fin d)} (hx : x ∈ J) : x = 1 := by
  have : b.repr ⟨x, hx⟩ = b.repr 1 := by
    rw [freeGroup_fin_zero_eq_one (b.repr ⟨x, hx⟩), freeGroup_fin_zero_eq_one (b.repr 1)]
  have := congrArg Subtype.val (b.repr.injective this)
  simpa using this

theorem hasRank_bot : HasRank (⊥ : Subgroup (FreeGroup (Fin d))) 0 := by
  refine ⟨FreeGroupBasis.ofRepr
    { toFun := fun _ => 1
      invFun := fun _ => 1
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun x => (freeGroup_fin_zero_eq_one x).symm
      map_mul' := fun _ _ => (mul_one _).symm }⟩

theorem not_prim_one (J : Subgroup (FreeGroup (Fin d))) : ¬ IsPrimitiveIn J 1 := by
  rintro ⟨ι, b, i, hi⟩
  have h1 : b i = 1 := Subtype.ext hi
  have h2 := b.repr_apply_coe i
  rw [h1, map_one] at h2
  exact FreeGroup.of_ne_one i h2.symm

theorem primitivityRank_one : primitivityRank (1 : FreeGroup (Fin d)) = 0 := by
  refine le_antisymm ?_ bot_le
  exact iInf₂_le (f := fun (r : ℕ) (_ : ∃ J : Subgroup (FreeGroup (Fin d)),
      (1 : FreeGroup (Fin d)) ∈ J ∧ HasRank J r ∧ ¬ IsPrimitiveIn J 1) => (r : ℕ∞))
    0 ⟨⊥, one_mem _, hasRank_bot, not_prim_one _⟩

theorem crit_one : Crit (1 : FreeGroup (Fin d)) = {⊥} := by
  ext J
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, -, r, ⟨b⟩, hr⟩
    rw [primitivityRank_one] at hr
    have : r = 0 := by exact_mod_cast hr
    subst this
    exact (Subgroup.eq_bot_iff_forall _).2 fun x hx => eq_one_of_rank_zero b hx
  · rintro rfl
    exact ⟨one_mem _, not_prim_one _, 0, hasRank_bot, by rw [primitivityRank_one]; rfl⟩

theorem fix_one (N : ℕ) : Fix (1 : FreeGroup (Fin d)) N = N := by
  unfold Fix StrongConv.uniformExp
  simp only [map_one, Equiv.Perm.coe_one, id_eq, filter_true_of_mem, implies_true, card_univ,
    Fintype.card_fin, sum_const, nsmul_eq_mul]
  have : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end Puder.PP.PartC
end

section
open scoped Classical
open Finset Asymptotics Filter Topology
namespace Puder.PP.PartB
variable {d : ℕ}
/-!
# Part B: Puder §5.5, the coefficient bound
-/
/-! ## Coefficients of `∏ (1 - c X)` -/

end Puder.PP.PartB
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part B: Puder §5.5, the coefficient bound -/

end Puder.PP
end

section
open scoped Classical
open Finset Asymptotics Filter Topology
namespace Puder.PP.PartB
variable {d : ℕ}
/-! ## `asympCoeff` of a function with a full expansion -/

/-! ## The bound for a cyclically reduced word -/

end Puder.PP.PartB
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}

end Puder.PP
end

section
open scoped Classical
open Finset Asymptotics Filter Topology
namespace Puder.PP.PartB
variable {d : ℕ}
/-! ## Reduction to a cyclically reduced word -/

end Puder.PP.PartB
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {L I I' : Type} [Fintype L] [PartialOrder L] [Fintype I] [Fintype I']
  (j : L → L → L) (aI : I → L) (sI : I → ℕ) (aE : I' → L) (sE : I' → ℕ)
/-!
# Part N, file 1: the abstract two-sided Möbius derivation on a finite join-semilattice

`L` is a finite partial order with a join `j`. Two finite families of "maps" `I`, `I'` carry an
element `aI φ`, `aE ψ` of `L` and a size. With `Nm x Q = ∑_{aI φ ≤ Q} (-x)^|φ|` and
`Dn x Q = ∑_{aE ψ ≤ Q} (-x)^|ψ|` we build `cc x : L → ℝ` with
`(∑_{Q'' ≤ Q} cc x Q'') * Dn x Q = Nm x Q` and bound `cc x Q` by `B * x ^ m`.
-/
/-- The denominator. -/
noncomputable def Dn (x : ℝ) (Q : L) : ℝ := ∑ ψ ∈ univ.filter (fun ψ => aE ψ ≤ Q), (-x) ^ sE ψ

/-- The numerator. -/
noncomputable def Nm (x : ℝ) (Q : L) : ℝ := ∑ φ ∈ univ.filter (fun φ => aI φ ≤ Q), (-x) ^ sI φ

/-- The derivation, by recursion on `Q`. -/
noncomputable def cc (x : ℝ) : L → ℝ :=
  (wellFounded_lt (α := L)).fix (fun Q rec =>
    (∑ φ ∈ univ.filter (fun φ => aI φ = Q), (-x) ^ sI φ -
      ∑ Q1 : L, if h : Q1 < Q then
        ∑ ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q), rec Q1 h * (-x) ^ sE ψ else 0) /
      Dn aE sE x Q)

theorem cc_eq (x : ℝ) (Q : L) :
    cc j aI sI aE sE x Q =
      (∑ φ ∈ univ.filter (fun φ => aI φ = Q), (-x) ^ sI φ -
        ∑ Q1 ∈ univ.filter (fun Q1 : L => Q1 < Q),
          ∑ ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q),
            cc j aI sI aE sE x Q1 * (-x) ^ sE ψ) / Dn aE sE x Q := by
  rw [cc, WellFounded.fix_eq]
  congr 2
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro Q1 _
  split_ifs <;> rfl

end Puder.PP.PartN
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {L I I' : Type} [Fintype L] [PartialOrder L] [Fintype I] [Fintype I']
  (j : L → L → L) (aI : I → L) (sI : I → ℕ) (aE : I' → L) (sE : I' → ℕ)
variable (hj : ∀ a b c : L, j a b ≤ c ↔ a ≤ c ∧ b ≤ c)
include hj
omit [Fintype L] in
theorem j_eq_iff (Q b : L) : j Q b = Q ↔ b ≤ Q := by
  constructor
  · intro h
    exact ((hj Q b Q).1 (le_of_eq h)).2
  · intro h
    exact le_antisymm ((hj Q b Q).2 ⟨le_rfl, h⟩) ((hj Q b (j Q b)).1 le_rfl).1

theorem conv_eq (x : ℝ) (Q : L) (hD : Dn aE sE x Q ≠ 0) :
    ∑ Q1 : L, ∑ ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q),
        cc j aI sI aE sE x Q1 * (-x) ^ sE ψ =
      ∑ φ ∈ univ.filter (fun φ => aI φ = Q), (-x) ^ sI φ := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ Q)]
  have h1 : ∑ ψ ∈ univ.filter (fun ψ => j Q (aE ψ) = Q), cc j aI sI aE sE x Q * (-x) ^ sE ψ =
      cc j aI sI aE sE x Q * Dn aE sE x Q := by
    rw [Dn, Finset.mul_sum]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j_eq_iff j hj Q (aE ψ)
  have h2 : ∑ Q1 ∈ (univ : Finset L).erase Q, ∑ ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q),
        cc j aI sI aE sE x Q1 * (-x) ^ sE ψ =
      ∑ Q1 ∈ univ.filter (fun Q1 : L => Q1 < Q), ∑ ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q),
        cc j aI sI aE sE x Q1 * (-x) ^ sE ψ := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro Q1 h
      rw [Finset.mem_filter] at h
      exact Finset.mem_erase.2 ⟨ne_of_lt h.2, Finset.mem_univ _⟩
    · intro Q1 h1 h2
      refine Finset.sum_eq_zero ?_
      intro ψ hψ
      exfalso
      rw [Finset.mem_filter] at hψ
      apply h2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, lt_of_le_of_ne ?_ (Finset.mem_erase.1 h1).1⟩
      exact ((hj Q1 (aE ψ) Q).1 (le_of_eq hψ.2)).1
  rw [h1, h2, cc_eq j aI sI aE sE x Q, div_mul_cancel₀ _ hD]
  ring

/-- The summation identity. -/
theorem sum_cc_mul (x : ℝ) (hD : ∀ Q : L, Dn aE sE x Q ≠ 0) (Q : L) :
    (∑ Q'' ∈ univ.filter (fun Q'' : L => Q'' ≤ Q), cc j aI sI aE sE x Q'') * Dn aE sE x Q =
      Nm aI sI x Q := by
  have hN : Nm aI sI x Q = ∑ Q'' ∈ univ.filter (fun Q'' : L => Q'' ≤ Q),
      ∑ φ ∈ univ.filter (fun φ => aI φ = Q''), (-x) ^ sI φ := by
    rw [Nm, ← Finset.sum_fiberwise_of_maps_to (g := aI)
      (t := univ.filter (fun Q'' : L => Q'' ≤ Q))]
    · refine Finset.sum_congr rfl ?_
      intro Q'' hQ''
      rw [Finset.mem_filter] at hQ''
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h ▸ hQ''.2, h⟩
    · intro φ hφ
      rw [Finset.mem_filter] at hφ ⊢
      exact ⟨Finset.mem_univ _, hφ.2⟩
  rw [hN]
  have h3 : ∀ Q'' : L, ∑ φ ∈ univ.filter (fun φ => aI φ = Q''), (-x) ^ sI φ =
      ∑ Q1 : L, ∑ ψ : I', if j Q1 (aE ψ) = Q'' then cc j aI sI aE sE x Q1 * (-x) ^ sE ψ
        else 0 := by
    intro Q''
    rw [← conv_eq j aI sI aE sE hj x Q'' (hD Q'')]
    refine Finset.sum_congr rfl ?_
    intro Q1 _
    rw [Finset.sum_filter]
  simp only [h3]
  rw [Finset.sum_comm]
  rw [Dn, Finset.sum_mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro Q1 _
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  by_cases hQ1 : Q1 ≤ Q
  · rw [if_pos hQ1]
    refine Finset.sum_congr rfl ?_
    intro ψ _
    by_cases hψ : aE ψ ≤ Q
    · rw [if_pos hψ, Finset.sum_ite_eq]
      rw [if_pos]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hj _ _ _).2 ⟨hQ1, hψ⟩⟩
    · rw [if_neg hψ]
      symm
      apply Finset.sum_eq_zero
      intro Q'' hQ''
      rw [Finset.mem_filter] at hQ''
      rw [if_neg]
      intro h
      exact hψ ((hj _ _ _).1 (h ▸ hQ''.2)).2
  · rw [if_neg hQ1]
    symm
    apply Finset.sum_eq_zero
    intro ψ _
    apply Finset.sum_eq_zero
    intro Q'' hQ''
    rw [Finset.mem_filter] at hQ''
    rw [if_neg]
    intro h
    exact hQ1 ((hj _ _ _).1 (h ▸ hQ''.2)).1

omit hj in
/-- The bound. -/
theorem cc_bound (G : L → ℕ → Prop) (hGI : ∀ φ, ∃ m, m ≤ sI φ ∧ G (aI φ) m)
    (hGE : ∀ ψ, ∃ m, m ≤ sE ψ ∧ G (aE ψ) m)
    (hGj : ∀ Q1 Q2 m1 m2, G Q1 m1 → G Q2 m2 → G (j Q1 Q2) (m1 + m2))
    (δ : L → ℝ) (hδ : ∀ Q, 0 < δ Q) (Q : L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → (∀ Q, δ Q ≤ Dn aE sE x Q) →
      ∀ m : ℕ, (∀ m' < m, ¬ G Q m') → |cc j aI sI aE sE x Q| ≤ B * x ^ m := by
  induction Q using WellFoundedLT.induction with
  | ind Q IH =>
  have IH' : ∀ Q1 : L, ∃ B : ℝ, Q1 < Q → (0 ≤ B ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (∀ Q, δ Q ≤ Dn aE sE x Q) →
      ∀ m : ℕ, (∀ m' < m, ¬ G Q1 m') → |cc j aI sI aE sE x Q1| ≤ B * x ^ m) := by
    intro Q1
    by_cases h : Q1 < Q
    · obtain ⟨B, hB⟩ := IH Q1 h
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Bf hBf using IH'
  have hS0 : 0 ≤ ∑ Q1 ∈ univ.filter (fun Q1 : L => Q1 < Q), Bf Q1 * (Fintype.card I' : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro Q1 hQ1
    rw [Finset.mem_filter] at hQ1
    exact mul_nonneg (hBf Q1 hQ1.2).1 (Nat.cast_nonneg _)
  refine ⟨((Fintype.card I : ℝ) +
    ∑ Q1 ∈ univ.filter (fun Q1 : L => Q1 < Q), Bf Q1 * (Fintype.card I' : ℝ)) / δ Q,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) hS0) (hδ Q).le, ?_⟩
  intro x hx0 hx1 hD m hm
  have hxm : 0 ≤ x ^ m := pow_nonneg hx0.le m
  rw [cc_eq, abs_div, abs_of_pos (lt_of_lt_of_le (hδ Q) (hD Q))]
  rw [div_mul_eq_mul_div]
  have hnum : |∑ φ ∈ univ.filter (fun φ => aI φ = Q), (-x) ^ sI φ -
        ∑ Q1 ∈ univ.filter (fun Q1 : L => Q1 < Q),
          ∑ ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q),
            cc j aI sI aE sE x Q1 * (-x) ^ sE ψ| ≤
      ((Fintype.card I : ℝ) +
        ∑ Q1 ∈ univ.filter (fun Q1 : L => Q1 < Q), Bf Q1 * (Fintype.card I' : ℝ)) * x ^ m := by
    refine (abs_sub _ _).trans ?_
    rw [add_mul]
    refine add_le_add ?_ ?_
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∑ φ ∈ univ.filter (fun φ => aI φ = Q), |(-x) ^ sI φ| ≤
          ∑ _φ ∈ univ.filter (fun φ => aI φ = Q), x ^ m := by
        refine Finset.sum_le_sum ?_
        intro φ hφ
        rw [Finset.mem_filter] at hφ
        obtain ⟨m0, hm0, hG⟩ := hGI φ
        rw [hφ.2] at hG
        have hmm : m ≤ sI φ := by
          by_contra hlt
          exact hm m0 (by omega) hG
        rw [abs_pow, abs_neg, abs_of_pos hx0]
        exact pow_le_pow_of_le_one hx0.le hx1 hmm
      refine this.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ hxm
      exact_mod_cast Finset.card_le_univ _
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum ?_
      intro Q1 hQ1
      rw [Finset.mem_filter] at hQ1
      have hB1 := hBf Q1 hQ1.2
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∑ ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q),
          |cc j aI sI aE sE x Q1 * (-x) ^ sE ψ| ≤
          ∑ _ψ ∈ univ.filter (fun ψ => j Q1 (aE ψ) = Q), Bf Q1 * x ^ m := by
        refine Finset.sum_le_sum ?_
        intro ψ hψ
        rw [Finset.mem_filter] at hψ
        obtain ⟨m2, hm2, hG⟩ := hGE ψ
        have hc := hB1.2 x hx0 hx1 hD (m - m2) (by
          intro m' hm' hG1
          have := hGj Q1 (aE ψ) m' m2 hG1 hG
          rw [hψ.2] at this
          exact hm (m' + m2) (by omega) this)
        rw [abs_mul, abs_pow, abs_neg, abs_of_pos hx0]
        calc |cc j aI sI aE sE x Q1| * x ^ sE ψ
            ≤ (Bf Q1 * x ^ (m - m2)) * x ^ sE ψ :=
              mul_le_mul_of_nonneg_right hc (pow_nonneg hx0.le _)
          _ = Bf Q1 * x ^ (m - m2 + sE ψ) := by rw [pow_add]; ring
          _ ≤ Bf Q1 * x ^ m :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_one hx0.le hx1 (by omega)) hB1.1
      refine this.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((univ.filter (fun ψ => j Q1 (aE ψ) = Q)).card : ℝ) ≤ Fintype.card I' := by
        exact_mod_cast Finset.card_le_univ _
      calc ((univ.filter (fun ψ => j Q1 (aE ψ) = Q)).card : ℝ) * (Bf Q1 * x ^ m)
          ≤ (Fintype.card I' : ℝ) * (Bf Q1 * x ^ m) :=
            mul_le_mul_of_nonneg_right hcard (mul_nonneg hB1.1 hxm)
        _ = Bf Q1 * (Fintype.card I' : ℝ) * x ^ m := by ring
  calc _ ≤ ((Fintype.card I : ℝ) +
        ∑ Q1 ∈ univ.filter (fun Q1 : L => Q1 < Q), Bf Q1 * (Fintype.card I' : ℝ)) * x ^ m /
          Dn aE sE x Q := by
        exact div_le_div_of_nonneg_right hnum (lt_of_lt_of_le (hδ Q) (hD Q)).le
    _ ≤ _ := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (add_nonneg (Nat.cast_nonneg _) hS0) hxm) (hδ Q) (hD Q)

end Puder.PP.PartN
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {d : ℕ}
variable (K : List (Fin d × Bool))
/-!
# Part N, file 2: fold-free closures, forest maps and the two product formulas
-/
/-! ## Partitions as equivalence relations -/
theorem part_eq_iff_mem (P : Part K) (u v : Fin K.length) :
    P.part u = P.part v ↔ v ∈ P.part u := by
  rw [eq_comm]
  exact (Finpartition.mem_part_iff_part_eq_part (P := P) (Finset.mem_univ v)
    (Finset.mem_univ u)).symm

theorem le_iff (P Q : Part K) :
    P ≤ Q ↔ ∀ u v, P.part u = P.part v → Q.part u = Q.part v := by
  constructor
  · intro h u v huv
    obtain ⟨c, hc, hbc⟩ := h (P.part_mem.2 (Finset.mem_univ u))
    have hu : u ∈ c := hbc (P.mem_part_self.2 (Finset.mem_univ u))
    have hv : v ∈ c := hbc ((part_eq_iff_mem K P u v).1 huv)
    rw [Q.part_eq_of_mem hc hu, Q.part_eq_of_mem hc hv]
  · intro h b hb
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts hb
    refine ⟨Q.part u, Q.part_mem.2 (Finset.mem_univ u), ?_⟩
    intro v hv
    have h1 : P.part u = P.part v := by
      rw [P.part_eq_of_mem hb hu, P.part_eq_of_mem hb hv]
    exact (part_eq_iff_mem K Q u v).1 (h u v h1)

end Puder.PP.PartN
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {d : ℕ}
variable (K : List (Fin d × Bool))
variable (Q' : Part K)
/-- The relation "identified in every fold-free partition above `Q'` identifying `R`". -/
def attRel (R : Set (Fin K.length × Fin K.length)) (u v : Fin K.length) : Prop :=
  ∀ Q : Part K, FF K Q → Q' ≤ Q → (∀ r ∈ R, Q.part r.1 = Q.part r.2) → Q.part u = Q.part v

/-- The least fold-free partition above `Q'` identifying the pairs of `R`. -/
noncomputable def att (R : Set (Fin K.length × Fin K.length)) : Part K :=
  Finpartition.ofSetoid ⟨attRel K Q' R, ⟨fun _ _ _ _ _ => rfl,
    fun h Q a b c => (h Q a b c).symm, fun h1 h2 Q a b c => (h1 Q a b c).trans (h2 Q a b c)⟩⟩

theorem att_part (R : Set (Fin K.length × Fin K.length)) (u v : Fin K.length) :
    (att K Q' R).part u = (att K Q' R).part v ↔ attRel K Q' R u v := by
  rw [part_eq_iff_mem]
  exact Finpartition.mem_part_ofSetoid_iff_rel

theorem att_ff (R : Set (Fin K.length × Fin K.length)) : FF K (att K Q' R) := by
  intro e e' hl
  rw [att_part, att_part]
  constructor
  · intro h Q hQ hle hR
    exact (hQ e e' hl).1 (h Q hQ hle hR)
  · intro h Q hQ hle hR
    exact (hQ e e' hl).2 (h Q hQ hle hR)

theorem le_att (R : Set (Fin K.length × Fin K.length)) : Q' ≤ att K Q' R :=
  (le_iff K _ _).2 fun u v huv =>
    (att_part K Q' R u v).2 fun Q _ hle _ => (le_iff K Q' Q).1 hle u v huv

theorem att_rel (R : Set (Fin K.length × Fin K.length)) (r : Fin K.length × Fin K.length)
    (hr : r ∈ R) : (att K Q' R).part r.1 = (att K Q' R).part r.2 :=
  (att_part K Q' R _ _).2 fun _ _ _ hR => hR r hr

theorem att_le (R : Set (Fin K.length × Fin K.length)) (Q : Part K) (hQ : FF K Q)
    (hle : Q' ≤ Q) (hR : ∀ r ∈ R, Q.part r.1 = Q.part r.2) : att K Q' R ≤ Q :=
  (le_iff K _ _).2 fun u v huv => (att_part K Q' R u v).1 huv Q hQ hle hR

theorem att_le_iff (R : Set (Fin K.length × Fin K.length)) (Q : Part K) (hQ : FF K Q)
    (hle : Q' ≤ Q) : att K Q' R ≤ Q ↔ ∀ r ∈ R, Q.part r.1 = Q.part r.2 :=
  ⟨fun h r hr => (le_iff K _ _).1 h _ _ (att_rel K Q' R r hr), att_le K Q' R Q hQ hle⟩

/-- The fold-free partitions above `Q'`. -/
abbrev LL : Type := {Q : Part K // FF K Q ∧ Q' ≤ Q}

/-- `att` as an element of `LL`. -/
noncomputable def attL (R : Set (Fin K.length × Fin K.length)) : LL K Q' :=
  ⟨att K Q' R, att_ff K Q' R, le_att K Q' R⟩

/-- The join of two fold-free partitions above `Q'`. -/
noncomputable def jn (Q1 Q2 : LL K Q') : LL K Q' :=
  attL K Q' {r | Q1.1.part r.1 = Q1.1.part r.2 ∨ Q2.1.part r.1 = Q2.1.part r.2}

theorem jn_le_iff (a b c : LL K Q') : jn K Q' a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  change att K Q' _ ≤ c.1 ↔ a.1 ≤ c.1 ∧ b.1 ≤ c.1
  rw [att_le_iff K Q' _ c.1 c.2.1 c.2.2, le_iff, le_iff]
  constructor
  · intro h
    exact ⟨fun u v huv => h (u, v) (Or.inl huv), fun u v huv => h (u, v) (Or.inr huv)⟩
  · rintro ⟨h1, h2⟩ r (hr | hr)
    · exact h1 _ _ hr
    · exact h2 _ _ hr

theorem gen_att {m : ℕ} (s : Fin m → Fin K.length × Fin K.length) :
    Gen K Q' (att K Q' (Set.range s)) m :=
  ⟨s, att_ff K Q' _, le_att K Q' _, fun i => att_rel K Q' _ (s i) ⟨i, rfl⟩,
    fun Q'' h1 h2 h3 => att_le K Q' _ Q'' h1 h2 (by
      rintro r ⟨i, rfl⟩
      exact h3 i)⟩

theorem gen_jn (Q1 Q2 : LL K Q') (m1 m2 : ℕ) (h1 : Gen K Q' Q1.1 m1) (h2 : Gen K Q' Q2.1 m2) :
    Gen K Q' (jn K Q' Q1 Q2).1 (m1 + m2) := by
  obtain ⟨s1, -, -, hs1, hl1⟩ := h1
  obtain ⟨s2, -, -, hs2, hl2⟩ := h2
  have hle := (jn_le_iff K Q' Q1 Q2 (jn K Q' Q1 Q2)).1 le_rfl
  have hle1 : Q1.1 ≤ (jn K Q' Q1 Q2).1 := hle.1
  have hle2 : Q2.1 ≤ (jn K Q' Q1 Q2).1 := hle.2
  refine ⟨Fin.append s1 s2, (jn K Q' Q1 Q2).2.1, (jn K Q' Q1 Q2).2.2, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      exact (le_iff K _ _).1 hle1 _ _ (hs1 i)
    · rw [Fin.append_right]
      exact (le_iff K _ _).1 hle2 _ _ (hs2 i)
  · intro Q'' hF hle' hs
    have a1 : Q1.1 ≤ Q'' := hl1 Q'' hF hle' (fun i => by
      have := hs (Fin.castAdd m2 i)
      rwa [Fin.append_left] at this)
    have a2 : Q2.1 ≤ Q'' := hl2 Q'' hF hle' (fun i => by
      have := hs (Fin.natAdd m1 i)
      rwa [Fin.append_right] at this)
    exact (jn_le_iff K Q' Q1 Q2 ⟨Q'', hF, hle'⟩).2 ⟨a1, a2⟩

end Puder.PP.PartN
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {d : ℕ}
variable {n : ℕ} {β : Type}
/-! ## Forest maps on a set of representatives -/
/-- The number of assigned elements of a map. -/
def sz (φ : Fin n → Option (Fin n)) : ℕ := (univ.filter (fun p => φ p ≠ none)).card

/-- The number of earlier representatives with the same key. -/
noncomputable def rk (S : Finset (Fin n)) (κ : Fin n → β) (p : Fin n) : ℕ :=
  (univ.filter (fun q => p ∈ S ∧ q ∈ S ∧ q < p ∧ κ q = κ p)).card

/-- The allowed values of a forest map at `p`. -/
noncomputable def tset (S : Finset (Fin n)) (κ : Fin n → β) (p : Fin n) :
    Finset (Option (Fin n)) :=
  univ.filter (fun o => ∀ q, o = some q → p ∈ S ∧ q ∈ S ∧ q < p ∧ κ q = κ p)

/-- Forest maps on `S` respecting the key `κ`. -/
noncomputable def maps (S : Finset (Fin n)) (κ : Fin n → β) :
    Finset (Fin n → Option (Fin n)) :=
  Fintype.piFinset (tset S κ)

theorem mem_maps (S : Finset (Fin n)) (κ : Fin n → β) (φ : Fin n → Option (Fin n)) :
    φ ∈ maps S κ ↔ ∀ p q, φ p = some q → p ∈ S ∧ q ∈ S ∧ q < p ∧ κ q = κ p := by
  simp [maps, tset, Fintype.mem_piFinset]

theorem prod_expand (S : Finset (Fin n)) (κ : Fin n → β) (x : ℝ) :
    ∏ p : Fin n, (1 - (rk S κ p : ℝ) * x) = ∑ φ ∈ maps S κ, (-x) ^ sz φ := by
  have h1 : ∀ p : Fin n, (1 - (rk S κ p : ℝ) * x) =
      ∑ o ∈ tset S κ p, (if o = none then (1 : ℝ) else -x) := by
    intro p
    rw [tset, Finset.sum_filter, Fintype.sum_option]
    simp only [reduceCtorEq, IsEmpty.forall_iff, implies_true, if_true, Option.some.injEq,
      forall_eq', if_false]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, rk]
    ring
  rw [Finset.prod_congr rfl (fun p _ => h1 p), Finset.prod_univ_sum]
  unfold maps
  refine Finset.sum_congr rfl ?_
  intro φ _
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, sz]

theorem prod_rank (s : Finset (Fin n)) (g : ℕ → ℝ) :
    ∏ p ∈ s, g (s.filter (· < p)).card = ∏ i ∈ range s.card, g i := by
  refine Finset.induction_on_max s ?_ ?_
  · simp
  · intro a s ha ih
    have hnot : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot, Finset.prod_range_succ,
      mul_comm]
    congr 1
    · rw [← ih]
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [Finset.filter_insert, if_neg (not_lt.2 (ha p hp).le)]
    · rw [Finset.filter_insert, if_neg (lt_irrefl a), Finset.filter_true_of_mem ha]

theorem prod_fiber (S : Finset (Fin n)) (κ : Fin n → β) (T : Finset β)
    (hT : ∀ p ∈ S, κ p ∈ T) (x : ℝ) :
    ∏ p : Fin n, (1 - (rk S κ p : ℝ) * x) =
      ∏ ε ∈ T, ∏ i ∈ range (S.filter (fun p => κ p = ε)).card, (1 - (i : ℝ) * x) := by
  have h0 : ∏ p : Fin n, (1 - (rk S κ p : ℝ) * x) = ∏ p ∈ S, (1 - (rk S κ p : ℝ) * x) := by
    symm
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro p _ hp
    have : rk S κ p = 0 := by
      rw [rk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ h
      exact hp h.1
    rw [this]
    simp
  rw [h0, ← Finset.prod_fiberwise_of_maps_to hT]
  refine Finset.prod_congr rfl ?_
  intro ε _
  rw [← prod_rank (S.filter (fun p => κ p = ε)) (fun i => 1 - (i : ℝ) * x)]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [Finset.mem_filter] at hp
  have : rk S κ p = ((S.filter (fun p => κ p = ε)).filter (· < p)).card := by
    rw [rk]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hq, hlt, hk⟩
      exact ⟨⟨hq, hk.trans hp.2⟩, hlt⟩
    · rintro ⟨⟨hq, hk⟩, hlt⟩
      exact ⟨hp.1, hq, hlt, hk.trans hp.2.symm⟩
  rw [this]

/-- The pairs `(φ p, p)` of a map, enumerated. -/
noncomputable def prs (φ : Fin n → Option (Fin n)) (i : Fin (sz φ)) : Fin n × Fin n :=
  ((φ ((univ.filter (fun p => φ p ≠ none)).equivFin.symm i).1).getD
    ((univ.filter (fun p => φ p ≠ none)).equivFin.symm i).1,
    ((univ.filter (fun p => φ p ≠ none)).equivFin.symm i).1)

theorem prs_iff (φ : Fin n → Option (Fin n)) (Pr : Fin n → Fin n → Prop) :
    (∀ i, Pr (prs φ i).1 (prs φ i).2) ↔ ∀ p q, φ p = some q → Pr q p := by
  constructor
  · intro h p q hpq
    have hp : p ∈ univ.filter (fun p => φ p ≠ none) := by simp [hpq]
    have := h ((univ.filter (fun p => φ p ≠ none)).equivFin ⟨p, hp⟩)
    simp only [prs, Equiv.symm_apply_apply, hpq, Option.getD_some] at this
    exact this
  · intro h i
    have hne : φ ((univ.filter (fun p => φ p ≠ none)).equivFin.symm i).1 ≠ none :=
      (Finset.mem_filter.1 ((univ.filter (fun p => φ p ≠ none)).equivFin.symm i).2).2
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hne
    simp only [prs]
    rw [hq]
    exact h _ _ hq

end Puder.PP.PartN
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {d : ℕ}
variable (K : List (Fin d × Bool)) (Q' : Part K)
/-! ## The two families of forest maps of a partition `Q'` -/
/-- The first position of each block of `Q'`. -/
noncomputable def SV : Finset (Fin K.length) :=
  univ.filter (fun p => ∀ q, Q'.part q = Q'.part p → p ≤ q)

/-- The first position over each edge of the quotient of `Q'`. -/
noncomputable def SE : Finset (Fin K.length) := univ.filter (fun p => New K Q' p)

/-- Vertex forest maps. -/
noncomputable def VM : Finset (Fin K.length → Option (Fin K.length)) :=
  maps (SV K Q') (fun _ : Fin K.length => ())

/-- Edge forest maps. -/
noncomputable def EM : Finset (Fin K.length → Option (Fin K.length)) :=
  maps (SE K Q') (lab K)

/-- The fold-free partition generated by a vertex forest map. -/
noncomputable def aV (φ : {φ // φ ∈ VM K Q'}) : LL K Q' := attL K Q' (Set.range (prs φ.1))

/-- The fold-free partition generated by an edge forest map. -/
noncomputable def aE (ψ : {ψ // ψ ∈ EM K Q'}) : LL K Q' :=
  attL K Q' (Set.range (fun i => (tl K (prs ψ.1 i).1, tl K (prs ψ.1 i).2)))

end Puder.PP.PartN
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartN
variable {d : ℕ}
/-!
# Part N: the two-sided Möbius derivation `C` (PP15 §7.1)
-/
/-- The derivation `C_{Q',Q}` at `x = 1/N`. -/
noncomputable def CC (K : List (Fin d × Bool)) (Q' Q : Part K) (x : ℝ) : ℝ :=
  if h : FF K Q ∧ Q' ≤ Q then
    x ^ (((E K Q').card : ℤ) - (Q'.parts.card : ℤ)) *
      cc (jn K Q') (aV K Q') (fun φ => sz φ.1) (aE K Q') (fun ψ => sz ψ.1) x ⟨Q, h⟩
  else 0

end Puder.PP.PartN
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {d : ℕ}
variable (K : List (Fin d × Bool)) (Q' : Part K)
theorem aV_le_iff (φ : {φ // φ ∈ VM K Q'}) (Q : LL K Q') :
    aV K Q' φ ≤ Q ↔ ∀ p q, φ.1 p = some q → Q.1.part q = Q.1.part p := by
  change att K Q' _ ≤ Q.1 ↔ _
  rw [att_le_iff K Q' _ Q.1 Q.2.1 Q.2.2, Set.forall_mem_range]
  exact prs_iff φ.1 (fun q p => Q.1.part q = Q.1.part p)

theorem aE_le_iff (ψ : {ψ // ψ ∈ EM K Q'}) (Q : LL K Q') :
    aE K Q' ψ ≤ Q ↔ ∀ p q, ψ.1 p = some q → Q.1.part (tl K q) = Q.1.part (tl K p) := by
  change att K Q' _ ≤ Q.1 ↔ _
  rw [att_le_iff K Q' _ Q.1 Q.2.1 Q.2.2, Set.forall_mem_range]
  exact prs_iff ψ.1 (fun q p => Q.1.part (tl K q) = Q.1.part (tl K p))

theorem vfib_eq (Q : Part K) (hle : Q' ≤ Q) (B : Finset (Fin K.length)) (hB : B ∈ Q.parts) :
    ((SV K Q').filter (fun p => Q.part p = B)).card = vfib K Q' B := by
  unfold vfib
  refine Finset.card_bij (fun p _ => Q'.part p) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Q'.part_mem.2 (Finset.mem_univ _), ?_⟩
    intro v hv
    have h1 : Q'.part p = Q'.part v := (part_eq_iff_mem K Q' p v).2 hv
    have h2 := (le_iff K Q' Q).1 hle p v h1
    rw [← hp.2, h2]
    exact Q.mem_part_self.2 (Finset.mem_univ v)
  · intro p1 hp1 p2 hp2 h
    rw [Finset.mem_filter, SV, Finset.mem_filter] at hp1 hp2
    exact le_antisymm (hp1.1.2 p2 h.symm) (hp2.1.2 p1 h)
  · intro A hA
    rw [Finset.mem_filter] at hA
    have hne := Q'.nonempty_of_mem_parts hA.1
    have hmin := A.min'_mem hne
    have hpart : Q'.part (A.min' hne) = A := Q'.part_eq_of_mem hA.1 hmin
    refine ⟨A.min' hne, ?_, hpart⟩
    rw [Finset.mem_filter, SV, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_⟩, Q.part_eq_of_mem hB (hA.2 hmin)⟩
    intro q hq
    refine A.min'_le q ?_
    rw [← hpart, ← hq]
    exact Q'.mem_part_self.2 (Finset.mem_univ q)

theorem qedge_eq_iff (Q : Part K) (hQ : FF K Q) (q p : Fin K.length) :
    qedge K Q q = qedge K Q p ↔ lab K q = lab K p ∧ Q.part (tl K q) = Q.part (tl K p) := by
  unfold qedge
  rw [Prod.mk.injEq, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, (hQ q p h.1).1 h.2⟩

theorem qedge_mono (Q : Part K) (hle : Q' ≤ Q) (q p : Fin K.length)
    (h : qedge K Q' q = qedge K Q' p) : qedge K Q q = qedge K Q p := by
  unfold qedge at h ⊢
  rw [Prod.mk.injEq, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, (le_iff K Q' Q).1 hle _ _ h.2.1, (le_iff K Q' Q).1 hle _ _ h.2.2⟩

theorem efib_eq (Q : Part K) (hle : Q' ≤ Q)
    (ε : Fin d × Finset (Fin K.length) × Finset (Fin K.length)) :
    ((SE K Q').filter (fun p => qedge K Q p = ε)).card = efib K Q' Q ε := by
  unfold efib
  have hinj : Set.InjOn (qedge K Q') (((SE K Q').filter (fun p => qedge K Q p = ε) :
      Finset (Fin K.length)) : Set (Fin K.length)) := by
    intro p1 hp1 p2 hp2 h
    rw [Finset.mem_coe, Finset.mem_filter, SE, Finset.mem_filter] at hp1 hp2
    rcases lt_trichotomy p1 p2 with hlt | heq | hgt
    · exact absurd h (hp2.1.2 p1 hlt)
    · exact heq
    · exact absurd h.symm (hp1.1.2 p2 hgt)
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext e
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, ⟨_, hp⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hne : (univ.filter (fun q => qedge K Q' q = qedge K Q' p)).Nonempty :=
      ⟨p, by simp⟩
    have hmem := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at hmem
    refine ⟨Finset.min' _ hne, ⟨?_, ?_⟩, hmem.2⟩
    · rw [SE, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro q' hq' heq
      have : q' ∈ univ.filter (fun q => qedge K Q' q = qedge K Q' p) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, heq.trans hmem.2⟩
      exact absurd (Finset.min'_le _ q' this) (not_le.2 hq')
    · rw [qedge_mono K Q' Q hle _ _ hmem.2]
      exact hp

/-- The numerator of `Lx` as a sum over vertex forest maps. -/
theorem nm_eq (Q : LL K Q') (x : ℝ) :
    Nm (aV K Q') (fun φ => sz φ.1) x Q =
      ∏ B ∈ Q.1.parts, ∏ i ∈ range (vfib K Q' B), (1 - (i : ℝ) * x) := by
  rw [Nm, Finset.sum_filter]
  have h1 : ∀ φ : {φ // φ ∈ VM K Q'}, (if aV K Q' φ ≤ Q then (-x) ^ sz φ.1 else 0) =
      (fun φ : Fin K.length → Option (Fin K.length) =>
        if (∀ p q, φ p = some q → Q.1.part q = Q.1.part p) then (-x) ^ sz φ else 0) φ.1 := by
    intro φ
    simp only [aV_le_iff]
  rw [Finset.sum_congr rfl (fun φ _ => h1 φ)]
  rw [Finset.sum_coe_sort (VM K Q') (fun φ : Fin K.length → Option (Fin K.length) =>
        if (∀ p q, φ p = some q → Q.1.part q = Q.1.part p) then (-x) ^ sz φ else 0)]
  rw [← Finset.sum_filter]
  have hm : (VM K Q').filter (fun φ => ∀ p q, φ p = some q → Q.1.part q = Q.1.part p) =
      maps (SV K Q') (fun p => Q.1.part p) := by
    ext φ
    simp only [Finset.mem_filter, VM, mem_maps]
    constructor
    · rintro ⟨h1, h2⟩ p q hpq
      obtain ⟨a, b, c, _⟩ := h1 p q hpq
      exact ⟨a, b, c, h2 p q hpq⟩
    · intro h
      refine ⟨fun p q hpq => ?_, fun p q hpq => (h p q hpq).2.2.2⟩
      obtain ⟨a, b, c, _⟩ := h p q hpq
      exact ⟨a, b, c, trivial⟩
  rw [hm, ← prod_expand, prod_fiber (SV K Q') _ Q.1.parts
    (fun p _ => Q.1.part_mem.2 (Finset.mem_univ p))]
  refine Finset.prod_congr rfl ?_
  intro B hB
  rw [← vfib_eq K Q' Q.1 Q.2.2 B hB]
  congr!

/-- The denominator of `Lx` as a sum over edge forest maps. -/
theorem dn_eq (Q : LL K Q') (x : ℝ) :
    Dn (aE K Q') (fun ψ => sz ψ.1) x Q =
      ∏ ε ∈ E K Q.1, ∏ i ∈ range (efib K Q' Q.1 ε), (1 - (i : ℝ) * x) := by
  rw [Dn, Finset.sum_filter]
  have h1 : ∀ ψ : {ψ // ψ ∈ EM K Q'}, (if aE K Q' ψ ≤ Q then (-x) ^ sz ψ.1 else 0) =
      (fun ψ : Fin K.length → Option (Fin K.length) =>
        if (∀ p q, ψ p = some q → Q.1.part (tl K q) = Q.1.part (tl K p)) then (-x) ^ sz ψ
        else 0) ψ.1 := by
    intro ψ
    simp only [aE_le_iff]
  rw [Finset.sum_congr rfl (fun ψ _ => h1 ψ)]
  rw [Finset.sum_coe_sort (EM K Q') (fun ψ : Fin K.length → Option (Fin K.length) =>
        if (∀ p q, ψ p = some q → Q.1.part (tl K q) = Q.1.part (tl K p)) then (-x) ^ sz ψ
        else 0)]
  rw [← Finset.sum_filter]
  have hm : (EM K Q').filter
      (fun ψ => ∀ p q, ψ p = some q → Q.1.part (tl K q) = Q.1.part (tl K p)) =
      maps (SE K Q') (qedge K Q.1) := by
    ext ψ
    simp only [Finset.mem_filter, EM, mem_maps]
    constructor
    · rintro ⟨h1, h2⟩ p q hpq
      obtain ⟨a, b, c, e⟩ := h1 p q hpq
      exact ⟨a, b, c, (qedge_eq_iff K Q.1 Q.2.1 q p).2 ⟨e, h2 p q hpq⟩⟩
    · intro h
      refine ⟨fun p q hpq => ?_, fun p q hpq =>
        ((qedge_eq_iff K Q.1 Q.2.1 q p).1 (h p q hpq).2.2.2).2⟩
      obtain ⟨a, b, c, e⟩ := h p q hpq
      exact ⟨a, b, c, ((qedge_eq_iff K Q.1 Q.2.1 q p).1 e).1⟩
  rw [hm, ← prod_expand, prod_fiber (SE K Q') _ (E K Q.1)
    (fun p _ => Finset.mem_image_of_mem _ (Finset.mem_univ p))]
  refine Finset.prod_congr rfl ?_
  intro ε _
  rw [← efib_eq K Q' Q.1 Q.2.2 ε]
  congr!

theorem efib_le (Q : Part K) (ε : Fin d × Finset (Fin K.length) × Finset (Fin K.length)) :
    efib K Q' Q ε ≤ K.length := by
  unfold efib
  refine Finset.card_image_le.trans ?_
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

theorem dn_pos (Q : LL K Q') (x : ℝ) (hx : 0 < x) (hxn : x * K.length < 1) :
    0 < Dn (aE K Q') (fun ψ => sz ψ.1) x Q := by
  rw [dn_eq]
  refine Finset.prod_pos ?_
  intro ε _
  refine Finset.prod_pos ?_
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : (i : ℝ) ≤ K.length := by
    exact_mod_cast (hi.le.trans (efib_le K Q' Q.1 ε))
  nlinarith

end Puder.PP.PartN
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartN
variable {d : ℕ}
theorem engine1 (K : List (Fin d × Bool)) (Q' Q : Part K) (hQ : FF K Q) (hle : Q' ≤ Q)
    (x : ℝ) (hx : 0 < x) (hxn : x * K.length < 1) :
    Lx K Q' Q x = ∑ Q'' ∈ (univ : Finset (Part K)).filter
        (fun Q'' => FF K Q'' ∧ Q' ≤ Q'' ∧ Q'' ≤ Q), CC K Q' Q'' x := by
  have hD : ∀ Q1 : LL K Q', Dn (aE K Q') (fun ψ => sz ψ.1) x Q1 ≠ 0 :=
    fun Q1 => (dn_pos K Q' Q1 x hx hxn).ne'
  have main := sum_cc_mul (jn K Q') (aV K Q') (fun φ => sz φ.1) (aE K Q') (fun ψ => sz ψ.1)
    (jn_le_iff K Q') x hD ⟨Q, hQ, hle⟩
  have hsum : ∑ Q'' ∈ (univ : Finset (Part K)).filter
        (fun Q'' => FF K Q'' ∧ Q' ≤ Q'' ∧ Q'' ≤ Q), CC K Q' Q'' x =
      ∑ Q'' ∈ (univ : Finset (LL K Q')).filter (fun Q'' => Q'' ≤ ⟨Q, hQ, hle⟩),
        x ^ (((E K Q').card : ℤ) - (Q'.parts.card : ℤ)) *
          cc (jn K Q') (aV K Q') (fun φ => sz φ.1) (aE K Q') (fun ψ => sz ψ.1) x Q'' := by
    symm
    refine Finset.sum_bij (fun Q'' _ => Q''.1) ?_ ?_ ?_ ?_
    · intro Q'' h
      rw [Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, Q''.2.1, Q''.2.2, h.2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro b hb
      rw [Finset.mem_filter] at hb
      refine ⟨⟨b, hb.2.1, hb.2.2.1⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hb.2.2.2⟩
    · intro Q'' _
      rw [CC, dif_pos Q''.2]
  have hD' := hD ⟨Q, hQ, hle⟩
  rw [dn_eq] at main hD'
  rw [nm_eq] at main
  rw [hsum, ← Finset.mul_sum, Lx, mul_div_assoc]
  congr 1
  rw [eq_comm, eq_div_iff hD']
  exact main

end Puder.PP.PartN
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartN
variable {d : ℕ}
variable (K : List (Fin d × Bool)) (Q' : Part K)
/-- A lower bound for the denominator, independent of `x`. -/
noncomputable def dlt (Q : LL K Q') : ℝ :=
  ∏ ε ∈ E K Q.1, ∏ _i ∈ range (efib K Q' Q.1 ε), (1 / 2 : ℝ)

theorem dlt_pos (Q : LL K Q') : 0 < dlt K Q' Q := by
  unfold dlt
  refine Finset.prod_pos ?_
  intro ε _
  refine Finset.prod_pos ?_
  intro i _
  norm_num

theorem dlt_le (Q : LL K Q') (x : ℝ) (hx : 0 < x) (hxn : 2 * x * K.length ≤ 1) :
    dlt K Q' Q ≤ Dn (aE K Q') (fun ψ => sz ψ.1) x Q := by
  rw [dn_eq]
  unfold dlt
  refine Finset.prod_le_prod ?_ ?_
  · intro ε _
    refine Finset.prod_nonneg ?_
    intro i _
    norm_num
  · intro ε _
    refine Finset.prod_le_prod ?_ ?_
    · intro i _
      norm_num
    · intro i hi
      rw [Finset.mem_range] at hi
      have h1 : (i : ℝ) ≤ K.length := by
        exact_mod_cast (hi.le.trans (efib_le K Q' Q.1 ε))
      nlinarith

end Puder.PP.PartN
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartN
variable {d : ℕ}
theorem engine2 (K : List (Fin d × Bool)) (Q' Q : Part K) (hQ : FF K Q)
    (hle : Q' ≤ Q) (m : ℕ) (hm : ∀ m' < m, ¬ Gen K Q' Q m') :
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → 2 * x * K.length ≤ 1 →
      |CC K Q' Q x| ≤ B * x ^ (((E K Q').card : ℤ) - (Q'.parts.card : ℤ) + m) := by
  by_cases h0 : K.length = 0
  · have hemp : IsEmpty (Fin K.length) := by
      rw [h0]
      infer_instance
    have hP : ∀ P : Part K, P.parts = ∅ := by
      intro P
      refine Finset.eq_empty_of_forall_notMem ?_
      intro b hb
      obtain ⟨u, _⟩ := P.nonempty_of_mem_parts hb
      exact isEmptyElim u
    have hsub : ∀ A B : Part K, A = B := by
      intro A B
      ext1
      rw [hP A, hP B]
    have hE : ∀ P : Part K, E K P = ∅ := by
      intro P
      unfold E
      rw [Finset.univ_eq_empty, Finset.image_empty]
    have hm0 : m = 0 := by
      by_contra hne
      exact hm 0 (Nat.pos_of_ne_zero hne)
        ⟨Fin.elim0, hQ, hle, fun i => i.elim0, fun Q'' _ _ _ => le_of_eq (hsub _ _)⟩
    refine ⟨1, ?_⟩
    intro x hx _
    have h1 := engine1 K Q' Q hQ hle x hx (by rw [h0]; simp)
    rw [Finset.sum_eq_single Q (fun b _ hb => absurd (hsub b Q) hb)
      (fun h => absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hQ, hle, le_rfl⟩) h)] at h1
    rw [← h1, hm0]
    simp [Lx, hE, hP]
  · obtain ⟨B, _, hB⟩ := cc_bound (jn K Q') (aV K Q') (fun φ => sz φ.1) (aE K Q')
      (fun ψ => sz ψ.1) (fun Q m => Gen K Q' Q.1 m)
      (fun φ => ⟨sz φ.1, le_rfl, gen_att K Q' (prs φ.1)⟩)
      (fun ψ => ⟨sz ψ.1, le_rfl, gen_att K Q' _⟩)
      (fun Q1 Q2 m1 m2 => gen_jn K Q' Q1 Q2 m1 m2) (dlt K Q') (dlt_pos K Q') ⟨Q, hQ, hle⟩
    refine ⟨B, ?_⟩
    intro x hx0 hx2
    have hn1 : (1 : ℝ) ≤ K.length := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hx1 : x ≤ 1 := by nlinarith
    have hc := hB x hx0 hx1 (fun Q1 => dlt_le K Q' Q1 x hx0 hx2) m hm
    rw [CC, dif_pos ⟨hQ, hle⟩, abs_mul, abs_of_pos (zpow_pos hx0 _), zpow_add₀ hx0.ne',
      zpow_natCast]
    calc _ ≤ x ^ (((E K Q').card : ℤ) - (Q'.parts.card : ℤ)) * (B * x ^ m) :=
          mul_le_mul_of_nonneg_left hc (zpow_pos hx0 _).le
      _ = _ := by ring

theorem engine (K : List (Fin d × Bool)) : ∃ C : Part K → Part K → ℝ → ℝ,
    (∀ Q' Q : Part K, FF K Q' → FF K Q → Q' ≤ Q → ∀ x : ℝ, 0 < x → x * K.length < 1 →
      Lx K Q' Q x = ∑ Q'' ∈ (univ : Finset (Part K)).filter
        (fun Q'' => FF K Q'' ∧ Q' ≤ Q'' ∧ Q'' ≤ Q), C Q' Q'' x) ∧
    (∀ Q' Q : Part K, FF K Q' → FF K Q → Q' ≤ Q → ∀ m : ℕ, (∀ m' < m, ¬ Gen K Q' Q m') →
      ∃ B : ℝ, ∀ x : ℝ, 0 < x → 2 * x * K.length ≤ 1 →
        |C Q' Q x| ≤ B * x ^ (((E K Q').card : ℤ) - (Q'.parts.card : ℤ) + m)) :=
  ⟨CC K, fun Q' Q _ hQ hle x hx hxn => engine1 K Q' Q hQ hle x hx hxn,
    fun Q' Q _ hQ hle m hm => engine2 K Q' Q hQ hle m hm⟩

end Puder.PP.PartN
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part N: the two-sided Möbius derivation `C` (PP15 §7.1) -/
alias engine := Puder.PP.PartN.engine

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartP
variable {d : ℕ}
/-!
# Part P, first half: the edge alphabet

`Kt K Q` is the word `K` with each letter replaced by the edge of the quotient of `Q` it traverses.
If `mk K` is primitive in `J K Q` then `mk (Kt K Q)` belongs to a basis of the free group on the
edges (`exists_basis`).
-/
/-! ## Generic facts -/
theorem basis_closure {ι G : Type} [Group G] (b : FreeGroupBasis ι G) :
    Subgroup.closure (Set.range b) = ⊤ := by
  have h : Set.range b =
      (b.repr.symm.toMonoidHom) '' Set.range (FreeGroup.of : ι → FreeGroup ι) := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [h, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top]
  exact b.repr.symm.surjective

theorem pfx_succ (K : List (Fin d × Bool)) (p : Fin K.length) :
    pfx K ((p : ℕ) + 1) = pfx K p * FreeGroup.mk [K[p]] := by
  simp only [pfx, FreeGroup.mul_mk]
  congr 1
  rw [List.take_add_one]
  simp

theorem mk_single_mem (S : Subgroup (FreeGroup (Fin d))) (x : Fin d × Bool) :
    FreeGroup.mk [x] ∈ S ↔ FreeGroup.of x.1 ∈ S := by
  rcases x with ⟨i, b⟩
  cases b
  · have : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
    rw [this, inv_mem_iff]
  · exact Iff.rfl

/-- A subgroup containing the closed walks of the record steps and the letters of the discovery
steps contains every letter of the word. -/
theorem letters_mem (K : List (Fin d × Bool)) (P : Part K) (S : Subgroup (FreeGroup (Fin d)))
    (hR : ∀ p, Rec K P p → gam K P p ∈ S)
    (hD : ∀ p, New K P p → Disc K P p → FreeGroup.of (lab K p) ∈ S) :
    ∀ p : Fin K.length, FreeGroup.of (lab K p) ∈ S := by
  have key : ∀ k : ℕ, ∀ p : Fin K.length, (p : ℕ) < k → FreeGroup.of (lab K p) ∈ S := by
    intro k
    induction k with
    | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      have hpf : ∀ j : ℕ, j ≤ k → j ≤ K.length → pfx K j ∈ S := by
        intro j
        induction j with
        | zero => intro _ _; rw [PartT.pfx_zero]; exact S.one_mem
        | succ j ihj =>
          intro hj hjn
          have h := pfx_succ K ⟨j, hjn⟩
          rw [show pfx K (j + 1) = pfx K j * FreeGroup.mk [K[(⟨j, hjn⟩ : Fin K.length)]] from h]
          exact S.mul_mem (ihj (by omega) (by omega))
            ((mk_single_mem S _).2 (ih ⟨j, hjn⟩ (by simpa using hj)))
      intro p hp
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with h | h
      · exact ih p h
      by_cases hnew : New K P p
      · by_cases hdisc : Disc K P p
        · exact hD p hnew hdisc
        · have hg := hR p ⟨hnew, hdisc⟩
          have h1 : pfx K p ∈ S := hpf p (by omega) (le_of_lt p.2)
          have h2 : pfx K (first K P (cnxt p)) ∈ S :=
            hpf _ (by have := PartT.first_le_rec K P p hdisc; omega) (le_of_lt (Fin.is_lt _))
          have h3 : FreeGroup.mk [K[p]] =
              (pfx K p)⁻¹ * gam K P p * pfx K (first K P (cnxt p)) := by
            unfold gam; rw [pfx_succ]; group
          have h4 : FreeGroup.mk [K[p]] ∈ S := by
            rw [h3]; exact S.mul_mem (S.mul_mem (S.inv_mem h1) hg) h2
          exact (mk_single_mem S _).1 h4
      · unfold New at hnew
        push Not at hnew
        obtain ⟨q, hq, hqe⟩ := hnew
        have hl0 : (qedge K P q).1 = (qedge K P p).1 := congrArg Prod.fst hqe
        have hl : lab K q = lab K p := hl0
        rw [← hl]
        exact ih q (by have : (q : ℕ) < p := hq; omega)
  intro p
  exact key _ p (Nat.lt_succ_self _)

theorem first_eq (K : List (Fin d × Bool)) (P : Part K) (p x : Fin K.length)
    (h1 : P.part x = P.part p) (h2 : ∀ q, P.part q = P.part p → x ≤ q) : first K P p = x := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (h1 ▸ P.mem_part (Finset.mem_univ x))
  · exact h2 _ (PartT.part_first K P p)

/-! ## The edge alphabet -/
theorem qmem (K : List (Fin d × Bool)) (Q : Part K) (p : Fin K.length) : qedge K Q p ∈ E K Q :=
  Finset.mem_image_of_mem _ (Finset.mem_univ p)

/-- Numbering of the edges of the quotient. -/
noncomputable def idx (K : List (Fin d × Bool)) (Q : Part K) :
    {ε // ε ∈ E K Q} ≃ Fin (E K Q).card := (E K Q).equivFin

/-- The word `K` written in the edges of the quotient of `Q`. -/
noncomputable def Kt (K : List (Fin d × Bool)) (Q : Part K) : List (Fin (E K Q).card × Bool) :=
  List.ofFn (fun p : Fin K.length => (idx K Q ⟨qedge K Q p, qmem K Q p⟩, (K[p]).2))

theorem Kt_length (K : List (Fin d × Bool)) (Q : Part K) : (Kt K Q).length = K.length :=
  List.length_ofFn

/-- Positions of `Kt K Q` as positions of `K`. -/
noncomputable def cc (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) : Fin K.length :=
  Fin.cast (Kt_length K Q) p

/-- Positions of `K` as positions of `Kt K Q`. -/
noncomputable def cs (K : List (Fin d × Bool)) (Q : Part K) (p : Fin K.length) : Fin (Kt K Q).length :=
  Fin.cast (Kt_length K Q).symm p

theorem Kt_get (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    (Kt K Q)[p] =
      (idx K Q ⟨qedge K Q (cc K Q p), qmem K Q (cc K Q p)⟩, (K[cc K Q p]).2) := by
  exact List.getElem_ofFn
    (f := fun p : Fin K.length => (idx K Q ⟨qedge K Q p, qmem K Q p⟩, (K[p]).2)) p.2

/-- `Q` as a partition of the positions of `Kt K Q`. -/
noncomputable def Qt (K : List (Fin d × Bool)) (Q : Part K) : Part (Kt K Q) :=
  Finpartition.ofSetoid
    { r := fun p q => Q.part (cc K Q p) = Q.part (cc K Q q)
      iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ }

theorem part_iff (K : List (Fin d × Bool)) (Q : Part K) (p q : Fin (Kt K Q).length) :
    (Qt K Q).part p = (Qt K Q).part q ↔ Q.part (cc K Q p) = Q.part (cc K Q q) := by
  have h := (Qt K Q).mem_part_iff_part_eq_part (a := p) (b := q) (Finset.mem_univ _)
    (Finset.mem_univ _)
  rw [← h]
  unfold Qt
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact eq_comm

theorem cc_cnxt (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    cc K Q (cnxt p) = cnxt (cc K Q p) := by
  apply Fin.ext
  simp [cc, cnxt, Kt_length]

theorem cc_tl (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    cc K Q (tl (Kt K Q) p) = tl K (cc K Q p) := by
  unfold tl
  rw [Kt_get]
  split_ifs
  · rfl
  · exact cc_cnxt K Q p

theorem cc_hd (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    cc K Q (hd (Kt K Q) p) = hd K (cc K Q p) := by
  unfold hd
  rw [Kt_get]
  split_ifs
  · exact cc_cnxt K Q p
  · rfl

theorem lab_Kt (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    lab (Kt K Q) p = idx K Q ⟨qedge K Q (cc K Q p), qmem K Q (cc K Q p)⟩ := by
  unfold lab
  rw [Kt_get]

end Puder.PP.PartP
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartP
variable {d N : ℕ}
/-! ## `Psi` as the expectation of a word -/
theorem psi_eq_fix (K : List (Fin d × Bool)) (hn : 0 < K.length) (Q : Part K) (N : ℕ) :
    Psi K Q N = Fix (FreeGroup.mk (Kt K Q)) N := by
  have hn' : 0 < (Kt K Q).length := by rw [Kt_length]; exact hn
  let A : ({ε // ε ∈ E K Q} → Perm (Fin N)) ≃ (Fin (E K Q).card → Perm (Fin N)) :=
    (idx K Q).arrowCongr (Equiv.refl _)
  have hcount : ∀ τ : Fin (E K Q).card → Perm (Fin N),
      (univ.filter fun f : Fin K.length → Fin N => ∀ p : Fin K.length,
        A.symm τ ⟨qedge K Q p, Finset.mem_image_of_mem _ (Finset.mem_univ p)⟩ (f (tl K p)) =
          f (hd K p)).card =
      (univ.filter fun x : Fin N => FreeGroup.lift τ⁻¹ (FreeGroup.mk (Kt K Q)) x = x).card := by
    intro τ
    rw [lift_inv_mk, card_fix_inv, ← card_cycle τ (Kt K Q) hn']
    let cE : Fin K.length ≃ Fin (Kt K Q).length := finCongr (Kt_length K Q).symm
    refine Finset.card_equiv (cE.arrowCongr (Equiv.refl _)) ?_
    intro f
    simp only [mem_filter, mem_univ, true_and]
    have hstep : ∀ p' : Fin (Kt K Q).length,
        Step τ (Kt K Q) (cE.arrowCongr (Equiv.refl (Fin N)) f) p' ↔
          τ (idx K Q ⟨qedge K Q (cc K Q p'), qmem K Q (cc K Q p')⟩) (f (tl K (cc K Q p'))) =
            f (hd K (cc K Q p')) := by
      intro p'
      have h1 : Step τ (Kt K Q) (cE.arrowCongr (Equiv.refl (Fin N)) f) p' ↔
          τ (lab (Kt K Q) p') (f (cc K Q (tl (Kt K Q) p'))) = f (cc K Q (hd (Kt K Q) p')) :=
        Iff.rfl
      rw [h1, lab_Kt, cc_tl, cc_hd]
    constructor
    · intro h p'
      rw [hstep]
      exact h (cc K Q p')
    · intro h p
      have := (hstep (cs K Q p)).1 (h _)
      exact this
  unfold Psi Fix StrongConv.uniformExp
  rw [Fintype.card_congr A]
  congr 1
  rw [← A.symm.sum_comp, ← Equiv.sum_comp (Equiv.inv (Fin (E K Q).card → Perm (Fin N)))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hcount]
  rfl

end Puder.PP.PartP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartP
variable {d : ℕ}
theorem lab_iff (K : List (Fin d × Bool)) (Q : Part K) (p q : Fin (Kt K Q).length) :
    lab (Kt K Q) p = lab (Kt K Q) q ↔ qedge K Q (cc K Q p) = qedge K Q (cc K Q q) := by
  rw [lab_Kt, lab_Kt, (idx K Q).apply_eq_iff_eq, Subtype.mk.injEq]

theorem qedge_iff (K : List (Fin d × Bool)) (Q : Part K) (p q : Fin (Kt K Q).length) :
    qedge (Kt K Q) (Qt K Q) p = qedge (Kt K Q) (Qt K Q) q ↔
      qedge K Q (cc K Q p) = qedge K Q (cc K Q q) := by
  constructor
  · intro h
    have h0 : (qedge (Kt K Q) (Qt K Q) p).1 = (qedge (Kt K Q) (Qt K Q) q).1 := congrArg Prod.fst h
    exact (lab_iff K Q p q).1 h0
  · intro h
    unfold qedge
    refine Prod.ext ((lab_iff K Q p q).2 h) (Prod.ext ?_ ?_)
    · rw [part_iff, cc_tl, cc_tl]
      exact congrArg (fun x => x.2.1) h
    · rw [part_iff, cc_hd, cc_hd]
      exact congrArg (fun x => x.2.2) h

theorem lab_surj (K : List (Fin d × Bool)) (Q : Part K) (i : Fin (E K Q).card) :
    ∃ p : Fin (Kt K Q).length, lab (Kt K Q) p = i := by
  obtain ⟨⟨ε, hε⟩, rfl⟩ := (idx K Q).surjective i
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hε
  exact ⟨cs K Q p, by rw [lab_Kt]; rfl⟩

theorem New_iff (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    New (Kt K Q) (Qt K Q) p ↔ New K Q (cc K Q p) := by
  constructor
  · intro h q hq heq
    exact h (cs K Q q) hq ((qedge_iff K Q _ _).2 heq)
  · intro h q hq heq
    exact h (cc K Q q) hq ((qedge_iff K Q _ _).1 heq)

theorem Disc_iff (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    Disc (Kt K Q) (Qt K Q) p ↔ Disc K Q (cc K Q p) := by
  unfold Disc
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by have := Kt_length K Q; have h1' : (p : ℕ) + 1 < (Kt K Q).length := h1; show (p : ℕ) + 1 < K.length; omega, fun q hq heq => h2 (cs K Q q) hq ?_⟩
    rw [part_iff, cc_cnxt]
    exact heq
  · rintro ⟨h1, h2⟩
    refine ⟨by have := Kt_length K Q; have h1' : (p : ℕ) + 1 < K.length := h1; show (p : ℕ) + 1 < (Kt K Q).length; omega, fun q hq heq => h2 (cc K Q q) hq ?_⟩
    rw [part_iff, cc_cnxt] at heq
    exact heq

theorem Rec_iff (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    Rec (Kt K Q) (Qt K Q) p ↔ Rec K Q (cc K Q p) := by
  unfold Rec
  rw [New_iff, Disc_iff]

theorem cc_first (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    cc K Q (first (Kt K Q) (Qt K Q) p) = first K Q (cc K Q p) := by
  symm
  apply first_eq
  · exact (part_iff K Q _ _).1 (PartT.part_first (Kt K Q) (Qt K Q) p)
  · intro q hq
    have hmem : cs K Q q ∈ (Qt K Q).part p :=
      ((Qt K Q).mem_part_iff_part_eq_part (a := cs K Q q) (b := p) (Finset.mem_univ _)
        (Finset.mem_univ _)).2 ((part_iff K Q _ _).2 hq)
    have h : first (Kt K Q) (Qt K Q) p ≤ cs K Q q := Finset.min'_le _ _ hmem
    exact h

/-- Each edge to its generator. -/
noncomputable def lam (K : List (Fin d × Bool)) (Q : Part K) :
    FreeGroup (Fin (E K Q).card) →* FreeGroup (Fin d) :=
  FreeGroup.map (fun i => ((idx K Q).symm i).1.1)

theorem Kt_map (K : List (Fin d × Bool)) (Q : Part K) :
    (Kt K Q).map (fun x => (((idx K Q).symm x.1).1.1, x.2)) = K := by
  apply List.ext_getElem
  · simp [Kt_length]
  · intro i h1 h2
    simp [Kt, qedge, lab]

theorem lam_pfx (K : List (Fin d × Bool)) (Q : Part K) (k : ℕ) :
    lam K Q (pfx (Kt K Q) k) = pfx K k := by
  unfold pfx lam
  rw [FreeGroup.map.mk, List.map_take, Kt_map]

theorem lam_mk (K : List (Fin d × Bool)) (Q : Part K) :
    lam K Q (FreeGroup.mk (Kt K Q)) = FreeGroup.mk K := by
  rw [← PartT.pfx_length, lam_pfx, Kt_length, PartT.pfx_length]

theorem lam_gam (K : List (Fin d × Bool)) (Q : Part K) (p : Fin (Kt K Q).length) :
    lam K Q (gam (Kt K Q) (Qt K Q) p) = gam K Q (cc K Q p) := by
  unfold gam
  rw [map_mul, map_inv, lam_pfx, lam_pfx]
  have h : ((first (Kt K Q) (Qt K Q) (cnxt p) : Fin (Kt K Q).length) : ℕ) =
      ((first K Q (cnxt (cc K Q p)) : Fin K.length) : ℕ) := by
    rw [← cc_cnxt, ← cc_first]; rfl
  rw [h]
  rfl

/-! ## The basis -/
theorem exists_basis (K : List (Fin d × Bool)) (hK : K ≠ []) (Q : Part K) (hQ : FF K Q)
    (hprim : IsPrimitiveIn (J K Q) (FreeGroup.mk K)) :
    ∃ (B : FreeGroupBasis (Fin (E K Q).card) (FreeGroup (Fin (E K Q).card)))
      (i : Fin (E K Q).card), B i = FreeGroup.mk (Kt K Q) := by
  have hKt : Kt K Q ≠ [] := by
    intro h
    apply hK
    apply List.eq_nil_of_length_eq_zero
    rw [← Kt_length K Q, h]
    rfl
  let S := {p : Fin K.length // Rec K Q p}
  let m := Fintype.card S
  let rc : Fin m ≃ S := (Fintype.equivFin S).symm
  have hgen := Puder.PP.ex_gen K hK Q
  have hmem : ∀ p, Rec K Q p → gam K Q p ∈ J K Q := by
    intro p hp
    rw [hgen]
    exact Subgroup.subset_closure ⟨p, hp, rfl⟩
  let g : Fin m → J K Q := fun i => ⟨gam K Q (rc i).1, hmem _ (rc i).2⟩
  have hg : Subgroup.closure (Set.range g) = ⊤ := by
    apply Subgroup.map_injective (J K Q).subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    conv_rhs => rw [hgen]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨(rc i).1, (rc i).2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨g (rc.symm ⟨p, hp⟩), ⟨_, rfl⟩, by simp [g]⟩
  have hm : (E K Q).card + 1 - Q.parts.card = m := by
    have h1 := Puder.PP.ex_card K hK Q
    have h2 : m = (univ.filter (Rec K Q)).card := Fintype.card_subtype _
    omega
  have hr : HasRank (J K Q) m := by
    rw [← hm]; exact Puder.PP.gt_rank K hK Q hQ
  obtain ⟨b1⟩ := hr
  obtain ⟨b', hb'⟩ := Puder.PP.h_basis_of_gen b1 g hg
  obtain ⟨ι, b, i0, hi0⟩ := hprim
  obtain ⟨r, hrm, ⟨eι⟩⟩ := Puder.PP.h_fin_of_gen b g hg
  have hg2 : Subgroup.closure (Set.range (fun j : Fin r => b (eι.symm j))) = ⊤ := by
    have : Set.range (fun j : Fin r => b (eι.symm j)) = Set.range b := by
      ext x; constructor
      · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨eι i, by simp⟩
    rw [this, basis_closure]
  obtain ⟨r', hr'r, ⟨e2⟩⟩ := Puder.PP.h_fin_of_gen b1 _ hg2
  have hmr' : m = r' := by simpa using Fintype.card_congr e2
  have hrm' : r = m := by omega
  let s : ι ≃ S := (eι.trans (finCongr hrm')).trans rc
  let Λ : J K Q →* FreeGroup (Fin (E K Q).card) :=
    b'.lift (fun j => gam (Kt K Q) (Qt K Q) (cs K Q (rc j).1))
  have hΛ : ∀ j, Λ (b' j) = gam (Kt K Q) (Qt K Q) (cs K Q (rc j).1) := fun j => by
    simp [Λ]
  have hlamΛ : (lam K Q).comp Λ = (J K Q).subtype := by
    apply b'.ext_hom
    intro j
    rw [MonoidHom.comp_apply, hΛ, lam_gam, hb']
    rfl
  have hrange : ∀ p', Rec (Kt K Q) (Qt K Q) p' → gam (Kt K Q) (Qt K Q) p' ∈ Λ.range := by
    intro p' hp'
    have hp := (Rec_iff K Q p').1 hp'
    refine ⟨b' (rc.symm ⟨cc K Q p', hp⟩), ?_⟩
    rw [hΛ, Equiv.apply_symm_apply]
    rfl
  have hu : FreeGroup.mk (Kt K Q) ∈ Λ.range := by
    have h1 : FreeGroup.mk (Kt K Q) ∈ J (Kt K Q) (Qt K Q) :=
      Subgroup.subset_closure (Or.inl rfl)
    rw [Puder.PP.ex_gen (Kt K Q) hKt (Qt K Q)] at h1
    refine (Subgroup.closure_le _).2 ?_ h1
    rintro _ ⟨p', hp', rfl⟩
    exact hrange p' hp'
  obtain ⟨x, hx⟩ := hu
  have hx' : x = b i0 := by
    apply Subtype.ext
    have h1 := congrArg (lam K Q) hx
    rw [lam_mk] at h1
    have h2 : lam K Q (Λ x) = x.1 := DFunLike.congr_fun hlamΛ x
    rw [hi0, ← h1, h2]
  let T := {p' : Fin (Kt K Q).length // New (Kt K Q) (Qt K Q) p'}
  have hrecT : ∀ t : T, ¬ Disc (Kt K Q) (Qt K Q) t.1 → Rec K Q (cc K Q t.1) :=
    fun t h => (Rec_iff K Q t.1).1 ⟨t.2, h⟩
  let f : T → FreeGroup (Fin (E K Q).card) := fun t =>
    if h : Disc (Kt K Q) (Qt K Q) t.1 then FreeGroup.of (lab (Kt K Q) t.1)
    else Λ (b (s.symm ⟨cc K Q t.1, hrecT t h⟩))
  have hnewi : ∀ i : ι, New (Kt K Q) (Qt K Q) (cs K Q (s i).1) :=
    fun i => (New_iff K Q (cs K Q (s i).1)).2 (s i).2.1
  have hfi : ∀ i : ι, f ⟨cs K Q (s i).1, hnewi i⟩ = Λ (b i) := by
    intro i
    have hnd : ¬ Disc (Kt K Q) (Qt K Q) (cs K Q (s i).1) :=
      fun h => (s i).2.2 ((Disc_iff K Q _).1 h)
    simp only [f]
    rw [dif_neg hnd]
    congr 2
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext rfl
  have hS : Subgroup.closure (Set.range f) = ⊤ := by
    have h1 : Λ.range ≤ Subgroup.closure (Set.range f) := by
      rw [MonoidHom.range_eq_map, ← basis_closure b, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [← hfi i]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    have h2 := letters_mem (Kt K Q) (Qt K Q) (Subgroup.closure (Set.range f))
      (fun p hp => h1 (hrange p hp))
      (fun p hn hd => by
        have : f ⟨p, hn⟩ = FreeGroup.of (lab (Kt K Q) p) := dif_pos hd
        rw [← this]
        exact Subgroup.subset_closure ⟨_, rfl⟩)
    rw [eq_top_iff, ← FreeGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨p', hp'⟩ := lab_surj K Q i
    rw [← hp']
    exact h2 p'
  have hbij : Function.Bijective (fun t : T => lab (Kt K Q) t.1) := by
    constructor
    · intro t t' h
      have hq : qedge (Kt K Q) (Qt K Q) t.1 = qedge (Kt K Q) (Qt K Q) t'.1 :=
        (qedge_iff K Q _ _).2 ((lab_iff K Q _ _).1 h)
      apply Subtype.ext
      rcases lt_trichotomy t.1 t'.1 with h1 | h1 | h1
      · exact absurd hq (t'.2 _ h1)
      · exact h1
      · exact absurd hq.symm (t.2 _ h1)
    · intro i
      obtain ⟨p0, hp0⟩ := lab_surj K Q i
      let F := univ.filter (fun p' : Fin (Kt K Q).length => lab (Kt K Q) p' = i)
      have hne : F.Nonempty := ⟨p0, by simp [F, hp0]⟩
      have hmin := Finset.min'_mem F hne
      refine ⟨⟨F.min' hne, ?_⟩, (Finset.mem_filter.1 hmin).2⟩
      intro q hq heq
      have hqF : q ∈ F := Finset.mem_filter.2
        ⟨mem_univ _, (show lab (Kt K Q) q = lab (Kt K Q) (F.min' hne) from
          (congrArg Prod.fst heq : (qedge (Kt K Q) (Qt K Q) q).1 = _)).trans
            (Finset.mem_filter.1 hmin).2⟩
      exact absurd (Finset.min'_le F q hqF) (not_le.2 hq)
  let tE : T ≃ Fin (E K Q).card := Equiv.ofBijective _ hbij
  obtain ⟨B, hB⟩ := Puder.PP.h_basis_of_gen (FreeGroupBasis.ofFreeGroup (Fin (E K Q).card))
    (fun j => f (tE.symm j)) (by
      have : Set.range (fun j => f (tE.symm j)) = Set.range f := by
        ext x; constructor
        · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
        · rintro ⟨t, rfl⟩; exact ⟨tE t, by simp⟩
      rw [this]; exact hS)
  refine ⟨B, tE ⟨cs K Q (s i0).1, hnewi i0⟩, ?_⟩
  rw [hB, Equiv.symm_apply_apply, hfi i0, ← hx', hx]

end Puder.PP.PartP
end

section
open scoped Classical
open Finset Equiv
namespace Puder.PP.PartP
variable {d N : ℕ}
theorem gt_psi (K : List (Fin d × Bool)) (hK : K ≠ []) (Q : Part K) (hQ : FF K Q)
    (hprim : IsPrimitiveIn (J K Q) (FreeGroup.mk K)) (N : ℕ) (hN : 0 < N) : Psi K Q N = 1 := by
  obtain ⟨B, i, hi⟩ := exists_basis K hK Q hQ hprim
  rw [psi_eq_fix K (List.length_pos_of_ne_nil hK) Q N]
  exact fix_eq_one _ B i hi hN

end Puder.PP.PartP
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part P: a primitive word has one expected lift (PP15 Lemma 6.2 with `Φ_{H,J} = Φ_{H,L}`
for `H ≤ L` a free factor of `J`) -/
alias gt_psi := Puder.PP.PartP.gt_psi

end Puder.PP
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartF
variable {d : ℕ}
/-! ### Vanishing for primitive quotients -/
lemma R_vanish (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) {C : Part K → Part K → ℝ → ℝ} (h1 : EngI K C)
    (N : ℕ) (hN : K.length < N) :
    ∀ Q : Part K, FF K Q → Q ≠ ⊥ → IsPrimitiveIn (J K Q) (FreeGroup.mk K) →
      R K C Q (1 / N) = 0 := by
  intro Q
  induction Q using WellFoundedLT.induction with
  | ind Q ih =>
    intro hQ hne hprim
    have hpsi := psi_eq K hK h1 Q hQ N hN
    rw [gt_psi K hK Q hQ hprim N (by omega)] at hpsi
    have hsum : ∑ Q'' ∈ (univ : Finset (Part K)).filter (fun Q'' => FF K Q'' ∧ Q'' ≤ Q),
        R K C Q'' (1 / N) = R K C ⊥ (1 / N) + R K C Q (1 / N) := by
      apply Finset.sum_eq_add ⊥ Q (Ne.symm hne)
      · rintro Q'' hQ'' ⟨hb, hq⟩
        rw [mem_filter] at hQ''
        have hlt : Q'' < Q := lt_of_le_of_ne hQ''.2.2 hq
        exact ih Q'' hlt hQ''.2.1 hb
          (fg_b (J K Q'') (J K Q) _ (hasRank_rk K hK Q hQ) (J_mono hQ''.2.2) _
            (mk_mem_J K Q'') hprim)
      · intro h
        exact absurd (mem_filter.2 ⟨mem_univ _, (ff_bot K hK hred).1, bot_le⟩) h
      · intro h
        exact absurd (mem_filter.2 ⟨mem_univ _, hQ, le_rfl⟩) h
    rw [hsum, R_bot K hK hred h1 (x_facts hN).1 (x_facts hN).2] at hpsi
    linarith

/-! ### Orders of the `C Q' Q` -/
lemma x_small {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) (hxn : 2 * x * n ≤ 1) :
    x ≤ 1 ∧ x * n < 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : x ≤ x * n := le_mul_of_one_le_right hx.le hn'
  constructor <;> linarith

lemma C_bound (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) {C : Part K → Part K → ℝ → ℝ} (h2 : EngII K C)
    {Q' Q : Part K} (hQ' : FF K Q') (hQ : FF K Q) (hle : Q' ≤ Q) (e : ℕ)
    (h : ∀ m', Gen K Q' Q m' → e + 1 ≤ rk K Q' + m') :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 < x → 2 * x * K.length ≤ 1 → |C Q' Q x| ≤ B * x ^ e := by
  obtain ⟨B, hB⟩ := h2 Q' Q hQ' hQ hle (e + 1 - rk K Q') (by
    intro m' hm' hg
    have := h m' hg
    omega)
  refine ⟨|B|, abs_nonneg _, fun x hx hxn => ?_⟩
  have hx1 : x ≤ 1 := (x_small (List.length_pos_iff.2 hK) hx hxn).1
  have hr := rk_pos K hK hred Q' hQ'
  have h3 := hB x hx hxn
  rw [ek_eq K hK hred Q' hQ', ← Nat.cast_add, zpow_natCast] at h3
  calc |C Q' Q x| ≤ B * x ^ (rk K Q' - 1 + (e + 1 - rk K Q')) := h3
    _ ≤ |B| * x ^ (rk K Q' - 1 + (e + 1 - rk K Q')) :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg hx.le _)
    _ ≤ |B| * x ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx.le hx1 (by omega)) (abs_nonneg _)

/-- The exponent hypothesis of `C_bound` with `e = r` for a non-primitive `Q`: either `Q` has
rank above `r`, or `Q` is critical and `Q' < Q`. -/
lemma gen_exponent (K : List (Fin d × Bool)) (hK : K ≠ []) (r : ℕ)
    (hr : primitivityRank (FreeGroup.mk K) = r) {Q' Q : Part K} (hQ' : FF K Q')
    (hle : Q' ≤ Q) (hnp : ¬ IsPrimitiveIn (J K Q) (FreeGroup.mk K)) (hrk : r ≤ rk K Q)
    (hcase : Q' ≠ Q ∨ rk K Q ≠ r) (m' : ℕ) (hg : Gen K Q' Q m') :
    r + 1 ≤ rk K Q' + m' := by
  obtain ⟨h1, h2⟩ := gen_rank K hK hQ' hg
  by_contra hcon
  have hrq : rk K Q = r := by omega
  have hne : Q' ≠ Q := by
    rcases hcase with h | h
    · exact h
    · exact absurd hrq h
  have hm : m' ≠ 0 := by
    rintro rfl
    exact hne (le_antisymm hle (gen_zero hQ' hg))
  have hprim : IsPrimitiveIn (J K Q') (FreeGroup.mk K) := by
    by_contra hnp'
    have h3 := prank_le (mk_mem_J K Q') (hasRank_rk K hK Q' hQ') hnp'
    rw [hr] at h3
    have h4 : r ≤ rk K Q' := by exact_mod_cast h3
    omega
  exact hnp (h2 (by omega) _ hprim)

lemma term_bound (K : List (Fin d × Bool)) (hK : K ≠ [])
    (hred : FreeGroup.IsCyclicallyReduced K) {C : Part K → Part K → ℝ → ℝ} (h1 : EngI K C)
    (h2 : EngII K C) (r : ℕ) (hr : primitivityRank (FreeGroup.mk K) = r) (Q : Part K)
    (hQ : FF K Q) (hnp : ¬ IsPrimitiveIn (J K Q) (FreeGroup.mk K)) :
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → 2 * x * K.length ≤ 1 →
      |R K C Q x - (if rk K Q = r then x ^ (rk K Q - 1) else 0)| ≤ B * x ^ r := by
  have hrk : r ≤ rk K Q := by
    have h3 := prank_le (mk_mem_J K Q) (hasRank_rk K hK Q hQ) hnp
    rw [hr] at h3
    exact_mod_cast h3
  have key : ∀ Q' : Part K, ∃ B : ℝ, 0 ≤ B ∧ (FF K Q' → Q' ≤ Q → (Q' ≠ Q ∨ rk K Q ≠ r) →
      ∀ x : ℝ, 0 < x → 2 * x * K.length ≤ 1 → |C Q' Q x| ≤ B * x ^ r) := by
    intro Q'
    by_cases hc : FF K Q' ∧ Q' ≤ Q ∧ (Q' ≠ Q ∨ rk K Q ≠ r)
    · obtain ⟨B, hB0, hB⟩ := C_bound K hK hred h2 hc.1 hQ hc.2.1 r
        (gen_exponent K hK r hr hc.1 hc.2.1 hnp hrk hc.2.2)
      exact ⟨B, hB0, fun _ _ _ => hB⟩
    · exact ⟨0, le_rfl, fun a b c => absurd ⟨a, b, c⟩ hc⟩
  choose Bf hB0 hB using key
  refine ⟨∑ Q' : Part K, Bf Q', fun x hx hxn => ?_⟩
  have hs : ∀ s : Finset (Part K),
      (∀ Q' ∈ s, FF K Q' ∧ Q' ≤ Q ∧ (Q' ≠ Q ∨ rk K Q ≠ r)) →
      |∑ Q' ∈ s, C Q' Q x| ≤ (∑ Q' : Part K, Bf Q') * x ^ r := by
    intro s hs
    calc |∑ Q' ∈ s, C Q' Q x| ≤ ∑ Q' ∈ s, |C Q' Q x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ Q' ∈ s, Bf Q' * x ^ r := sum_le_sum (fun Q' h =>
          hB Q' (hs Q' h).1 (hs Q' h).2.1 (hs Q' h).2.2 x hx hxn)
      _ ≤ ∑ Q' : Part K, Bf Q' * x ^ r :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            (fun Q' _ _ => mul_nonneg (hB0 Q') (pow_nonneg hx.le _))
      _ = (∑ Q' : Part K, Bf Q') * x ^ r := (sum_mul _ _ _).symm
  by_cases hrq : rk K Q = r
  · rw [if_pos hrq]
    have hmem : Q ∈ (univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ Q) :=
      mem_filter.2 ⟨mem_univ _, hQ, le_rfl⟩
    have hsplit : R K C Q x - x ^ (rk K Q - 1) =
        ∑ Q' ∈ ((univ : Finset (Part K)).filter (fun Q' => FF K Q' ∧ Q' ≤ Q)).erase Q,
          C Q' Q x := by
      unfold R
      rw [← add_sum_erase _ _ hmem,
        C_self K hK hred h1 hQ hx (x_small (List.length_pos_iff.2 hK) hx hxn).2]
      ring
    rw [hsplit]
    apply hs
    intro Q' hQ'
    rw [mem_erase, mem_filter] at hQ'
    exact ⟨hQ'.2.2.1, hQ'.2.2.2, Or.inl hQ'.1⟩
  · rw [if_neg hrq, sub_zero]
    unfold R
    apply hs
    intro Q' hQ'
    rw [mem_filter] at hQ'
    exact ⟨hQ'.2.1, hQ'.2.2, Or.inr hrq⟩

/-! ### Counting the critical subgroups -/
lemma crit_count (K : List (Fin d × Bool)) (hK : K ≠ []) (r : ℕ)
    (hr : primitivityRank (FreeGroup.mk K) = r) :
    (Crit (FreeGroup.mk K)).ncard =
      ((((univ : Finset (Part K)).filter (FF K)).filter
        (fun Q => ¬ IsPrimitiveIn (J K Q) (FreeGroup.mk K))).filter
          (fun Q => rk K Q = r)).card := by
  set T := (((univ : Finset (Part K)).filter (FF K)).filter
        (fun Q => ¬ IsPrimitiveIn (J K Q) (FreeGroup.mk K))).filter
          (fun Q => rk K Q = r) with hT
  have memT : ∀ Q : Part K, Q ∈ T ↔
      FF K Q ∧ ¬ IsPrimitiveIn (J K Q) (FreeGroup.mk K) ∧ rk K Q = r := by
    intro Q
    simp only [hT, mem_filter, mem_univ, true_and, and_assoc]
  have himg : Crit (FreeGroup.mk K) = J K '' (T : Set (Part K)) := by
    ext Jc
    constructor
    · intro h
      obtain ⟨Q, hQ, rfl⟩ := gt_crit K hK Jc h
      obtain ⟨-, hnp, s, hs, hsr⟩ := h
      rw [hr] at hsr
      have hsr' : s = r := by exact_mod_cast hsr
      have := hasRank_unique hs (hasRank_rk K hK Q hQ)
      exact ⟨Q, mem_coe.2 ((memT Q).2 ⟨hQ, hnp, by omega⟩), rfl⟩
    · rintro ⟨Q, hQ, rfl⟩
      have hQ' := (memT Q).1 (mem_coe.1 hQ)
      refine ⟨mk_mem_J K Q, hQ'.2.1, rk K Q, hasRank_rk K hK Q hQ'.1, ?_⟩
      rw [hr, hQ'.2.2]
  rw [himg, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  intro P hP Q hQ h
  exact J_inj K hK ((memT P).1 (mem_coe.1 hP)).1 ((memT Q).1 (mem_coe.1 hQ)).1 h

/-! ### The theorem -/
theorem thm18_cyc (K : List (Fin d × Bool)) (hK : K ≠ []) (hred : FreeGroup.IsCyclicallyReduced K)
    (r : ℕ) (hr : primitivityRank (FreeGroup.mk K) = r) :
    (fun N : ℕ => Fix (FreeGroup.mk K) N - 1 -
        ((Crit (FreeGroup.mk K)).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1)) =O[atTop]
      (fun N : ℕ => 1 / (N : ℝ) ^ r) := by
  obtain ⟨C, h1, h2⟩ := engine K
  have h1 : EngI K C := h1
  have h2 : EngII K C := h2
  have hn : 1 ≤ K.length := List.length_pos_iff.2 hK
  set S := (univ : Finset (Part K)).filter (FF K) with hS
  set NP := S.filter (fun Q => ¬ IsPrimitiveIn (J K Q) (FreeGroup.mk K)) with hNP
  have key : ∀ Q : Part K, ∃ B : ℝ, Q ∈ NP → ∀ x : ℝ, 0 < x → 2 * x * K.length ≤ 1 →
      |R K C Q x - (if rk K Q = r then x ^ (rk K Q - 1) else 0)| ≤ B * x ^ r := by
    intro Q
    by_cases hQ : Q ∈ NP
    · have hQ' := hQ
      rw [hNP, mem_filter, hS, mem_filter] at hQ'
      obtain ⟨B, hB⟩ := term_bound K hK hred h1 h2 r hr Q hQ'.1.2 hQ'.2
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hQ⟩
  choose Bf hBf using key
  apply IsBigO.of_bound (∑ Q ∈ NP, Bf Q)
  filter_upwards [eventually_ge_atTop (2 * K.length)] with N hN
  have hnN : K.length < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hx, hxn⟩ := x_facts hnN
  have hxn2 : 2 * (1 / (N : ℝ)) * K.length ≤ 1 := by
    rw [show 2 * (1 / (N : ℝ)) * K.length = (2 * K.length : ℝ) / N by ring, div_le_one hN0]
    exact_mod_cast hN
  -- the primitive quotients contribute `1`
  have hprim : ∑ Q ∈ S.filter (fun Q => IsPrimitiveIn (J K Q) (FreeGroup.mk K)),
      R K C Q (1 / N) = 1 := by
    rw [sum_eq_single (⊥ : Part K), R_bot K hK hred h1 hx hxn]
    · intro Q hQ hne
      rw [mem_filter, hS, mem_filter] at hQ
      exact R_vanish K hK hred h1 N hnN Q hQ.1.2 hne hQ.2
    · intro h
      exact absurd (mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, (ff_bot K hK hred).1⟩,
        prim_bot K hK hred⟩) h
  -- the main terms of the critical quotients
  have hmain : ∑ Q ∈ NP, (if rk K Q = r then (1 / (N : ℝ)) ^ (rk K Q - 1) else 0) =
      ((Crit (FreeGroup.mk K)).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1) := by
    rw [← sum_filter, crit_count K hK r hr]
    have hc : ∀ Q ∈ NP.filter (fun Q => rk K Q = r),
        (1 / (N : ℝ)) ^ (rk K Q - 1) = 1 / (N : ℝ) ^ ((r : ℤ) - 1) := by
      intro Q hQ
      rw [mem_filter, hNP, mem_filter, hS, mem_filter] at hQ
      have hpos := rk_pos K hK hred Q hQ.1.1.2
      rw [hQ.2] at hpos ⊢
      rw [show (r : ℤ) - 1 = ((r - 1 : ℕ) : ℤ) by omega, zpow_natCast, one_div_pow]
    rw [sum_congr rfl hc, sum_const, nsmul_eq_mul, mul_one_div]
  have hid : Fix (FreeGroup.mk K) N - 1 -
      ((Crit (FreeGroup.mk K)).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1) =
      ∑ Q ∈ NP, (R K C Q (1 / N) -
        (if rk K Q = r then (1 / (N : ℝ)) ^ (rk K Q - 1) else 0)) := by
    rw [sum_sub_distrib, hmain, fix_eq K hK h1 N hnN, ← hS,
      ← sum_filter_add_sum_filter_not S (fun Q => IsPrimitiveIn (J K Q) (FreeGroup.mk K)),
      hprim]
    ring
  have hnorm : ‖1 / (N : ℝ) ^ r‖ = (1 / (N : ℝ)) ^ r := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ r),
      one_div_pow]
  have hfin : ‖Fix (FreeGroup.mk K) N - 1 -
      ((Crit (FreeGroup.mk K)).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1)‖ ≤
      (∑ Q ∈ NP, Bf Q) * ‖1 / (N : ℝ) ^ r‖ := by
    rw [hnorm, hid, Real.norm_eq_abs, sum_mul]
    calc |∑ Q ∈ NP, (R K C Q (1 / N) -
          (if rk K Q = r then (1 / (N : ℝ)) ^ (rk K Q - 1) else 0))|
        ≤ ∑ Q ∈ NP, |R K C Q (1 / N) -
          (if rk K Q = r then (1 / (N : ℝ)) ^ (rk K Q - 1) else 0)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ Q ∈ NP, Bf Q * (1 / (N : ℝ)) ^ r :=
          sum_le_sum (fun Q hQ => hBf Q hQ _ hx hxn2)
  exact hfin

end Puder.PP.PartF
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
/-! ## Part F: PP15 Theorem 1.8 for a cyclically reduced word -/
alias thm18_cyc := Puder.PP.PartF.thm18_cyc

end Puder.PP
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP.PartC
variable {d : ℕ}
theorem leafA (d : ℕ) (w : FreeGroup (Fin d)) (r : ℕ) (hr : primitivityRank w = r) :
    (Crit w).Finite ∧
      (fun N : ℕ => StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ)) - 1 -
          ((Crit w).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1)) =O[atTop]
        (fun N : ℕ => 1 / (N : ℝ) ^ r) := by
  refine ⟨Puder.PP.crit_finite w, ?_⟩
  change (fun N : ℕ => Fix w N - 1 - ((Crit w).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1)) =O[atTop]
    (fun N : ℕ => 1 / (N : ℝ) ^ r)
  by_cases hw : w = 1
  · subst hw
    rw [primitivityRank_one] at hr
    have : r = 0 := by exact_mod_cast hr.symm
    subst this
    rw [crit_one, Set.ncard_singleton]
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    rw [fix_one]
    simp only [Nat.cast_zero, zero_sub, zpow_neg, zpow_one, Nat.cast_one, one_div, inv_inv,
      pow_zero, inv_one, norm_one, mul_one]
    rw [show (N : ℝ) - 1 - N = -1 by ring]
    simp
  · have hG : ∃ G : FreeGroup (Fin d),
        w = G * FreeGroup.mk (FreeGroup.reduceCyclically w.toWord) * G⁻¹ := by
      refine ⟨FreeGroup.mk (FreeGroup.reduceCyclically.conjugator w.toWord), ?_⟩
      rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk,
        FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically, FreeGroup.mk_toWord]
    obtain ⟨G, hG⟩ := hG
    set K := FreeGroup.reduceCyclically w.toWord with hKdef
    have hK : K ≠ [] := by
      intro h
      apply hw
      rw [hG, h]
      show G * 1 * G⁻¹ = 1
      group
    have hred : FreeGroup.IsCyclicallyReduced K :=
      FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
    obtain ⟨h1, h2, h3⟩ := conj_inv G (FreeGroup.mk K)
    rw [← hG] at h1 h2 h3
    have key := Puder.PP.thm18_cyc K hK hred r (h1.symm.trans hr)
    rw [← h2] at key
    simpa only [h3] using key

end Puder.PP.PartC
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias leafA := Puder.PP.PartC.leafA

end Puder.PP
end


theorem solution (d : ℕ) (w : FreeGroup (Fin d)) (r : ℕ)
    (hr : Puder.primitivityRank w = r) :
    (Puder.Crit w).Finite ∧
      (fun N : ℕ => StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ)) - 1 -
          ((Puder.Crit w).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1)) =O[Filter.atTop]
        (fun N : ℕ => 1 / (N : ℝ) ^ r) :=
  Puder.PP.leafA d w r hr
