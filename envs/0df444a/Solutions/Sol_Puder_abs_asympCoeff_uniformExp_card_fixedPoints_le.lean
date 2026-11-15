-- Prove2me | solution 1 for Puder.abs_asympCoeff_uniformExp_card_fixedPoints_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T11:08:31.848928+00:00
-- url     : https://prove2.me/submissions/b5e87ec8-2ad1-4549-8489-bea2fa2b7ba8

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
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

/-- The element of `F_d` read along the first `p` edges of the cycle. -/
def pfx (K : List (Fin d × Bool)) (p : ℕ) : FreeGroup (Fin d) := FreeGroup.mk (K.take p)

/-- `π₁` of the quotient graph of `P` at the block of vertex `0`, as a subgroup of `F_d`. -/
def J (K : List (Fin d × Bool)) (P : Part K) : Subgroup (FreeGroup (Fin d)) :=
  Subgroup.closure ({FreeGroup.mk K} ∪
    {g | ∃ p q : Fin K.length, P.part p = P.part q ∧ g = pfx K p * (pfx K q)⁻¹})

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

/-! ## Part N: the two-sided Möbius derivation `C` (PP15 §7.1) -/

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

end Puder.PP
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
/-! ## Cyclically reduced words -/

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
/-- The early records of `P`: the pairs (first position of the block reached, position reached)
over the record steps that do not wrap around. -/
noncomputable def SS (K : List (Fin d × Bool)) (P : Part K) :
    Finset (Fin K.length × Fin K.length) :=
  (univ.filter fun p : Fin K.length => Rec K P p ∧ (p : ℕ) + 1 < K.length).image
    fun p => (first K P (cnxt p), cnxt p)

/-- The pairs of positions `a < b`. -/
noncomputable def UU (K : List (Fin d × Bool)) : Finset (Fin K.length × Fin K.length) :=
  univ.filter fun x => x.1 < x.2

end Puder.PP.PartX
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
variable {K : List (Fin d × Bool)}
theorem SS_subset (P : Part K) : SS K P ⊆ UU K := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
  simp only [mem_filter, mem_univ, true_and] at hp
  simp only [UU, mem_filter, mem_univ, true_and]
  refine lt_of_le_of_ne (first_le P rfl) fun h => ?_
  exact hp.1.2 ((disc_iff P p).2 ⟨hp.2, h⟩)

theorem card_SS_le (P : Part K) : (SS K P).card ≤ (univ.filter (Rec K P)).card :=
  Finset.card_image_le.trans (Finset.card_le_card fun p hp => by
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact hp.1)

theorem tl_hd_le {p q : Fin K.length} (hqp : q < p) : tl K q ≤ p ∧ hd K q ≤ p := by
  have hqp' : (q : ℕ) < p := hqp
  have hpl := p.2
  have hc : ((cnxt q : Fin K.length) : ℕ) = q + 1 := cnxt_val_of_lt (by omega)
  have hc' : cnxt q ≤ p := by
    show ((cnxt q : Fin K.length) : ℕ) ≤ p
    omega
  rcases tl_hd_cases K q with ⟨-, ht, hh⟩ | ⟨-, ht, hh⟩ <;> rw [ht, hh]
  · exact ⟨hqp.le, hc'⟩
  · exact ⟨hc', hqp.le⟩

theorem step (P P' : Part K) (hP' : FF K P') (hS : SS K P = SS K P') (p : Fin K.length)
    (hp : (p : ℕ) + 1 < K.length)
    (hC : ∀ a b : Fin K.length, a ≤ p → b ≤ p →
      (P.part a = P.part b ↔ P'.part a = P'.part b))
    (a : Fin K.length) (ha : a ≤ p) (hab : P.part a = P.part (cnxt p)) :
    P'.part a = P'.part (cnxt p) := by
  by_cases hN : New K P p
  · have hD : ¬ Disc K P p := fun hD => hD.2 a ha hab
    have hmem : (first K P (cnxt p), cnxt p) ∈ SS K P :=
      mem_image.2 ⟨p, by simp only [mem_filter, mem_univ, true_and]; exact ⟨⟨hN, hD⟩, hp⟩, rfl⟩
    rw [hS] at hmem
    obtain ⟨p', -, he⟩ := mem_image.1 hmem
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    rw [h2] at h1
    have hf' : P'.part (first K P (cnxt p)) = P'.part (cnxt p) := by
      rw [← h1]
      exact part_first P' _
    have hfa : first K P (cnxt p) ≤ a := first_le P hab
    have hf : P.part (first K P (cnxt p)) = P.part a := (part_first P _).trans hab.symm
    have := (hC _ _ (hfa.trans ha) ha).1 hf
    exact this.symm.trans hf'
  · unfold New at hN
    push Not at hN
    obtain ⟨q, hqp, he⟩ := hN
    simp only [qedge, Prod.mk.injEq] at he
    obtain ⟨hl, h2, h3⟩ := he
    obtain ⟨htl, hhd⟩ := tl_hd_le hqp
    have hff := hP' q p hl
    rcases tl_hd_cases K p with ⟨-, ht, hh⟩ | ⟨-, ht, hh⟩ <;> rw [ht] at h2 hff <;>
      rw [hh] at h3 hff
    · have e1 := hff.1 ((hC _ _ htl le_rfl).1 h2)
      have e2 := (hC _ a hhd ha).1 (h3.trans hab.symm)
      exact e2.symm.trans e1
    · have e1 := hff.2 ((hC _ _ hhd le_rfl).1 h3)
      have e2 := (hC _ a htl ha).1 (h2.trans hab.symm)
      exact e2.symm.trans e1

theorem agree (P P' : Part K) (hP : FF K P) (hP' : FF K P') (hS : SS K P = SS K P') (m : ℕ) :
    ∀ a b : Fin K.length, (a : ℕ) ≤ m → (b : ℕ) ≤ m →
      (P.part a = P.part b ↔ P'.part a = P'.part b) := by
  induction m with
  | zero =>
    intro a b ha hb
    have : a = b := Fin.ext (by omega)
    subst this
    simp
  | succ m ih =>
    intro a b ha hb
    by_cases hm : m + 1 < K.length
    · have hc : ((cnxt (⟨m, by omega⟩ : Fin K.length) : Fin K.length) : ℕ) = m + 1 :=
        cnxt_val_of_lt hm
      have hC' : ∀ a b : Fin K.length, a ≤ (⟨m, by omega⟩ : Fin K.length) →
          b ≤ (⟨m, by omega⟩ : Fin K.length) →
          (P.part a = P.part b ↔ P'.part a = P'.part b) := fun a b ha hb => ih a b ha hb
      have key1 : ∀ a : Fin K.length, (a : ℕ) ≤ m →
          (P.part a = P.part (cnxt (⟨m, by omega⟩ : Fin K.length)) ↔
            P'.part a = P'.part (cnxt (⟨m, by omega⟩ : Fin K.length))) := fun a ha =>
        ⟨step P P' hP' hS _ hm hC' a ha,
          step P' P hP hS.symm _ hm (fun a b ha hb => (hC' a b ha hb).symm) a ha⟩
      rcases Nat.lt_or_ge (a : ℕ) (m + 1) with ha' | ha' <;>
        rcases Nat.lt_or_ge (b : ℕ) (m + 1) with hb' | hb'
      · exact ih a b (by omega) (by omega)
      · have : b = cnxt (⟨m, by omega⟩ : Fin K.length) := Fin.ext (by omega)
        rw [this]
        exact key1 a (by omega)
      · have : a = cnxt (⟨m, by omega⟩ : Fin K.length) := Fin.ext (by omega)
        rw [this]
        exact eq_comm.trans ((key1 b (by omega)).trans eq_comm)
      · have : a = b := Fin.ext (by omega)
        subst this
        simp
    · have := a.2
      have := b.2
      exact ih a b (by omega) (by omega)

theorem parts_sub (P P' : Part K)
    (h : ∀ a b : Fin K.length, P.part a = P.part b ↔ P'.part a = P'.part b) :
    P.parts ⊆ P'.parts := by
  intro t ht
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts ht
  have h1 : P.part a = t := P.part_eq_of_mem ht ha
  have h2 : P'.part a = P.part a := by
    ext b
    rw [mem_part, mem_part]
    exact (h b a).symm
  rw [← h1, ← h2]
  exact P'.part_mem.2 (mem_univ _)

theorem SS_inj (P P' : Part K) (hP : FF K P) (hP' : FF K P') (hS : SS K P = SS K P') :
    P = P' := by
  have h : ∀ a b : Fin K.length, P.part a = P.part b ↔ P'.part a = P'.part b := fun a b =>
    agree P P' hP hP' hS K.length a b a.2.le b.2.le
  exact Finpartition.ext
    (Finset.Subset.antisymm (parts_sub P P' h) (parts_sub P' P fun a b => (h a b).symm))

theorem card_UU (K : List (Fin d × Bool)) : 2 * (UU K).card ≤ K.length * K.length := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin K.length × Fin K.length))) (p := fun x => x.1 < x.2)
  have h2 : (UU K).card ≤
      ((univ : Finset (Fin K.length × Fin K.length)).filter fun x => ¬ x.1 < x.2).card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro x hx
      simp only [UU, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap,
        not_lt]
      exact hx.le
    · exact Prod.swap_injective.injOn
  have h3 : (univ : Finset (Fin K.length × Fin K.length)).card = K.length * K.length := by
    simp [Finset.card_univ]
  unfold UU
  unfold UU at h2
  omega

theorem exp_half_le : Real.exp (1 / 2) ≤ 1.7 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  by_contra h
  push Not at h
  nlinarith

end Puder.PP.PartX
end

section
open scoped Classical
open Finset
namespace Puder.PP.PartX
variable {d : ℕ}
/-- Puder §5.5: counting the quotients by rank. -/
theorem ex_count (K : List (Fin d × Bool)) (hK : K ≠ []) (hred : FreeGroup.IsCyclicallyReduced K) :
    ∑ P ∈ (univ : Finset (Part K)).filter (FF K),
      (1 / (K.length : ℝ) ^ 2) ^ ((E K P).card + 1 - P.parts.card) ≤ 1 := by
  have hn : 1 ≤ K.length := List.length_pos_iff.2 hK
  have hnR : (1 : ℝ) ≤ (K.length : ℝ) := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (K.length : ℝ) ^ 2 := by nlinarith
  set y : ℝ := 1 / (K.length : ℝ) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one (by linarith)]
    exact hn2
  let g : Finset (Fin K.length × Fin K.length) → ℝ := fun s => if s = ∅ then y else y ^ s.card
  have hg0 : ∀ s, 0 ≤ g s := by
    intro s
    show 0 ≤ if s = ∅ then y else y ^ s.card
    split_ifs
    · exact hy0
    · positivity
  -- termwise bound
  have hterm : ∀ P ∈ (univ : Finset (Part K)).filter (FF K),
      y ^ ((E K P).card + 1 - P.parts.card) ≤ g (SS K P) := by
    intro P _
    have h1 := ex_card K hK P
    have h2 := rec_pos K hK hred P
    have h3 := card_SS_le P
    show _ ≤ if SS K P = ∅ then y else y ^ (SS K P).card
    split_ifs with h0
    · calc y ^ ((E K P).card + 1 - P.parts.card) ≤ y ^ 1 :=
            pow_le_pow_of_le_one hy0 hy1 (by omega)
        _ = y := pow_one y
    · exact pow_le_pow_of_le_one hy0 hy1 (by omega)
  have hinj : Set.InjOn (SS K) ((univ : Finset (Part K)).filter (FF K) : Set (Part K)) := by
    intro P hP P' hP' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hP hP'
    exact SS_inj P P' hP hP' h
  have hsub : ((univ : Finset (Part K)).filter (FF K)).image (SS K) ⊆ (UU K).powerset := by
    intro s hs
    obtain ⟨P, -, rfl⟩ := mem_image.1 hs
    exact mem_powerset.2 (SS_subset P)
  have hpow : ∑ t ∈ (UU K).powerset, y ^ t.card = (y + 1) ^ (UU K).card := by
    have := Finset.sum_pow_mul_eq_add_pow y 1 (UU K)
    simpa using this
  have hgsum : ∑ s ∈ (UU K).powerset, g s = (y + 1) ^ (UU K).card + (y - 1) := by
    have hg : ∀ s ∈ (UU K).powerset, g s = y ^ s.card + if s = ∅ then y - 1 else 0 := by
      intro s _
      show (if s = ∅ then y else y ^ s.card) = _
      split_ifs with h0
      · rw [h0]
        simp
      · simp
    rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib, hpow, Finset.sum_ite_eq']
    simp
  have hmain : ∑ P ∈ (univ : Finset (Part K)).filter (FF K),
      y ^ ((E K P).card + 1 - P.parts.card) ≤ (y + 1) ^ (UU K).card + (y - 1) := by
    calc ∑ P ∈ (univ : Finset (Part K)).filter (FF K), y ^ ((E K P).card + 1 - P.parts.card)
        ≤ ∑ P ∈ (univ : Finset (Part K)).filter (FF K), g (SS K P) := Finset.sum_le_sum hterm
      _ = ∑ s ∈ ((univ : Finset (Part K)).filter (FF K)).image (SS K), g s :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ s ∈ (UU K).powerset, g s :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => hg0 s
      _ = _ := hgsum
  refine hmain.trans ?_
  have hU := card_UU K
  rcases Nat.lt_or_ge K.length 2 with h2 | h2
  · have h1 : K.length = 1 := by omega
    have hU0 : (UU K).card = 0 := by
      have : K.length * K.length = 1 := by rw [h1]
      omega
    rw [hU0]
    linarith
  · have h2R : (2 : ℝ) ≤ (K.length : ℝ) := by exact_mod_cast h2
    have h4 : (4 : ℝ) ≤ (K.length : ℝ) ^ 2 := by nlinarith
    have hy4 : y ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
    have hUR : (2 : ℝ) * ((UU K).card : ℝ) ≤ (K.length : ℝ) ^ 2 := by
      have : ((2 * (UU K).card : ℕ) : ℝ) ≤ ((K.length * K.length : ℕ) : ℝ) := by exact_mod_cast hU
      push_cast at this
      nlinarith
    have hTy : ((UU K).card : ℝ) * y ≤ 1 / 2 := by
      rw [hy, mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    have h5 : (y + 1) ^ (UU K).card ≤ Real.exp (1 / 2) := by
      calc (y + 1) ^ (UU K).card ≤ Real.exp y ^ (UU K).card :=
            pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp y) _
        _ = Real.exp (((UU K).card : ℝ) * y) := (Real.exp_nat_mul y _).symm
        _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 hTy
    have h6 := exp_half_le
    norm_num at h6
    linarith

end Puder.PP.PartX
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias ex_count := Puder.PP.PartX.ex_count

/-! ## Part H: finitely generated free groups -/

/-! ## Part T: `π₁` of a fold-free quotient -/

/-! ## Part G: generation, critical subgroups -/

/-! ## Part P: a primitive word has one expected lift (PP15 Lemma 6.2 with `Φ_{H,J} = Φ_{H,L}`
for `H ≤ L` a free factor of `J`) -/

/-! ## Part F: PP15 Theorem 1.8 for a cyclically reduced word -/

/-! ## Part C: conjugation invariance and the target of leaf A -/

end Puder.PP
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
theorem coeff_prod_le {ι : Type} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (j : ℕ) :
    |(∏ i ∈ s, (1 - Polynomial.C (c i) * Polynomial.X)).coeff j| ≤ (∑ i ∈ s, c i) ^ j := by
  induction s using Finset.induction_on generalizing j with
  | empty =>
    cases j with
    | zero => simp
    | succ j => simp [Polynomial.coeff_one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have hca := hc a (mem_insert_self _ _)
    have ih' := fun j => ih (fun i hi => hc i (mem_insert_of_mem hi)) j
    have hS : 0 ≤ ∑ i ∈ s, c i := sum_nonneg fun i hi => hc i (mem_insert_of_mem hi)
    rw [sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul]
    cases j with
    | zero =>
      rw [Polynomial.coeff_X_mul_zero]
      simpa using ih' 0
    | succ j =>
      rw [Polynomial.coeff_X_mul]
      have h1 := pow_le_pow_left₀ hS (le_add_of_nonneg_left hca) j
      have h2 := ih' (j + 1)
      have h3 := ih' j
      have h4 : |c a * (∏ i ∈ s, (1 - Polynomial.C (c i) * Polynomial.X)).coeff j| ≤
          c a * (∑ i ∈ s, c i) ^ j := by
        rw [abs_mul, abs_of_nonneg hca]
        exact mul_le_mul_of_nonneg_left h3 hca
      have h5 := abs_sub ((∏ i ∈ s, (1 - Polynomial.C (c i) * Polynomial.X)).coeff (j + 1))
        (c a * (∏ i ∈ s, (1 - Polynomial.C (c i) * Polynomial.X)).coeff j)
      have h6 := mul_le_mul_of_nonneg_right h1 (add_nonneg hca hS)
      rw [pow_succ] at h2 ⊢
      nlinarith

theorem geom_two (q : ℕ) : ∑ k ∈ range q, (2 : ℝ) ^ k = 2 ^ q - 1 := by
  induction q with
  | zero => simp
  | succ q ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- The quotient of two polynomials with coefficients bounded by `S ^ j`. -/
theorem series_bound (A D : Polynomial ℝ) (S : ℝ) (hS : 0 ≤ S) (hA : ∀ j, |A.coeff j| ≤ S ^ j)
    (hD : ∀ j, |D.coeff j| ≤ S ^ j) (hD0 : D.coeff 0 = 1) :
    ∃ a : ℕ → ℝ, (∀ j, |a j| ≤ (2 * S) ^ j) ∧
      ∀ M : ℕ, (fun N : ℕ => A.eval (1 / (N : ℝ)) / D.eval (1 / (N : ℝ)) -
          ∑ j ∈ range (M + 1), a j * (1 / (N : ℝ)) ^ j) =O[atTop]
        (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1)) := by
  set f : PowerSeries ℝ := (A : PowerSeries ℝ) * (D : PowerSeries ℝ)⁻¹ with hf
  have hc0 : PowerSeries.constantCoeff (D : PowerSeries ℝ) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hD0]
    exact one_ne_zero
  have hfd : f * (D : PowerSeries ℝ) = (A : PowerSeries ℝ) := by
    rw [hf, mul_assoc, PowerSeries.inv_mul_cancel _ hc0, mul_one]
  have hrec : ∀ q, PowerSeries.coeff q f =
      A.coeff q - ∑ k ∈ range q, PowerSeries.coeff k f * D.coeff (q - k) := by
    intro q
    have h := congrArg (PowerSeries.coeff q) hfd
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ] at h
    simp only [Polynomial.coeff_coe, Nat.sub_self, hD0, mul_one] at h
    linarith
  have hbound : ∀ q, |PowerSeries.coeff q f| ≤ (2 * S) ^ q := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      rw [hrec q]
      have h1 : |∑ k ∈ range q, PowerSeries.coeff k f * D.coeff (q - k)| ≤
          ∑ k ∈ range q, (2 * S) ^ k * S ^ (q - k) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => by
          rw [abs_mul]
          exact mul_le_mul (ih k (mem_range.1 hk)) (hD _) (abs_nonneg _) (by positivity))
      have h2 : ∑ k ∈ range q, (2 * S) ^ k * S ^ (q - k) = S ^ q * (2 ^ q - 1) := by
        rw [← geom_two, mul_sum]
        refine sum_congr rfl fun k hk => ?_
        have hk' : k ≤ q := (mem_range.1 hk).le
        have : S ^ q = S ^ k * S ^ (q - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
        rw [this, mul_pow]; ring
      have h3 := abs_sub (A.coeff q) (∑ k ∈ range q, PowerSeries.coeff k f * D.coeff (q - k))
      have h4 := hA q
      have h5 : (2 * S) ^ q = S ^ q + S ^ q * (2 ^ q - 1) := by rw [mul_pow]; ring
      linarith
  refine ⟨fun j => PowerSeries.coeff j f, hbound, fun M => ?_⟩
  set T : Polynomial ℝ := PowerSeries.trunc (M + 1) f with hT
  have hdvd : (Polynomial.X : Polynomial ℝ) ^ (M + 1) ∣ A - T * D := by
    rw [Polynomial.X_pow_dvd_iff]
    intro q hq
    rw [Polynomial.coeff_sub, Polynomial.coeff_mul, sub_eq_zero]
    have h := congrArg (PowerSeries.coeff q) hfd
    rw [PowerSeries.coeff_mul] at h
    simp only [Polynomial.coeff_coe] at h
    rw [← h]
    refine sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = q := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [hT, PowerSeries.coeff_trunc, if_pos (by omega)]
  obtain ⟨R, hR⟩ := hdvd
  have heval : ∀ x : ℝ, A.eval x = T.eval x * D.eval x + x ^ (M + 1) * R.eval x := by
    intro x
    have h := congrArg (Polynomial.eval x) hR
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X] at h
    linarith
  have hTeval : ∀ x : ℝ, T.eval x = ∑ j ∈ range (M + 1), PowerSeries.coeff j f * x ^ j := by
    intro x
    rw [Polynomial.eval_eq_sum_range' (hT ▸ PowerSeries.natDegree_trunc_lt f M)]
    refine sum_congr rfl fun j hj => ?_
    rw [hT, PowerSeries.coeff_trunc, if_pos (mem_range.1 hj)]
  have hx : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hD0' : D.eval 0 = 1 := by rw [← Polynomial.coeff_zero_eq_eval_zero, hD0]
  have hDt : Tendsto (fun N : ℕ => D.eval (1 / (N : ℝ))) atTop (𝓝 1) := by
    have := (D.continuous.tendsto 0).comp hx
    rwa [hD0'] at this
  have hRt : Tendsto (fun N : ℕ => R.eval (1 / (N : ℝ))) atTop (𝓝 (R.eval 0)) :=
    (R.continuous.tendsto 0).comp hx
  have hne : ∀ᶠ N : ℕ in atTop, D.eval (1 / (N : ℝ)) ≠ 0 := hDt.eventually_ne one_ne_zero
  have hg : (fun N : ℕ => R.eval (1 / (N : ℝ)) / D.eval (1 / (N : ℝ))) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := (hRt.div hDt one_ne_zero).isBigO_one ℝ
  have hmul := (isBigO_refl (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1)) atTop).mul hg
  refine hmul.congr' ?_ (Eventually.of_forall fun N => by simp)
  filter_upwards [hne] with N hN
  show (1 / (N : ℝ)) ^ (M + 1) * (R.eval (1 / (N : ℝ)) / D.eval (1 / (N : ℝ))) =
    A.eval (1 / (N : ℝ)) / D.eval (1 / (N : ℝ)) -
      ∑ j ∈ range (M + 1), PowerSeries.coeff j f * (1 / (N : ℝ)) ^ j
  rw [← hTeval, heval, add_div, mul_div_assoc, mul_div_assoc, div_self hN, mul_one]
  ring

theorem sum_range_cast (v : ℕ) : ∑ i ∈ range v, (i : ℝ) = (v : ℝ) * ((v : ℝ) - 1) / 2 := by
  induction v with
  | zero => simp
  | succ v ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_efib_le (K : List (Fin d × Bool)) (Q' : Part K) :
    ∑ ε ∈ E K (⊤ : Part K), efib K Q' ⊤ ε ≤ K.length := by
  have h1 : ∑ ε ∈ E K (⊤ : Part K), efib K Q' ⊤ ε ≤
      ∑ ε ∈ E K (⊤ : Part K),
        ((univ : Finset (Fin K.length)).filter fun p => qedge K ⊤ p = ε).card :=
    sum_le_sum fun ε _ => card_image_le
  have h2 := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin K.length)))
    (t := E K (⊤ : Part K)) (f := qedge K ⊤) (fun p _ => mem_image_of_mem _ (mem_univ p))
  rw [card_univ, Fintype.card_fin] at h2
  omega

theorem series_general {ι : Type} (s : Finset ι) (e : ι → ℕ) (v n : ℕ) (hv : v ≤ n)
    (hsum : ∑ ε ∈ s, e ε ≤ n) :
    ∃ a : ℕ → ℝ, (∀ j, |a j| ≤ (n : ℝ) ^ (2 * j)) ∧
      ∀ M : ℕ, (fun N : ℕ =>
          (∏ i ∈ Finset.range v, (1 - (i : ℝ) * (1 / N))) /
            (∏ ε ∈ s, ∏ i ∈ Finset.range (e ε), (1 - (i : ℝ) * (1 / N))) -
          ∑ j ∈ Finset.range (M + 1), a j * (1 / (N : ℝ)) ^ j) =O[atTop]
        (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1)) := by
  set A : Polynomial ℝ :=
    ∏ i ∈ range v, (1 - Polynomial.C (i : ℝ) * Polynomial.X) with hA
  set D : Polynomial ℝ := ∏ p ∈ s.sigma (fun ε => range (e ε)),
    (1 - Polynomial.C (p.2 : ℝ) * Polynomial.X) with hD
  have hAe : ∀ x : ℝ, A.eval x = ∏ i ∈ range v, (1 - (i : ℝ) * x) := by
    intro x; simp [hA, Polynomial.eval_prod]
  have hDe : ∀ x : ℝ, D.eval x = ∏ ε ∈ s, ∏ i ∈ range (e ε), (1 - (i : ℝ) * x) := by
    intro x
    rw [hD, Polynomial.eval_prod, Finset.prod_sigma]
    simp
  have hvR : (v : ℝ) ≤ n := by exact_mod_cast hv
  have hsA : ∑ i ∈ range v, (i : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [sum_range_cast]
    have h0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
    nlinarith
  have hsumR : ∑ ε ∈ s, (e ε : ℝ) ≤ n := by exact_mod_cast hsum
  have hsD : ∑ p ∈ s.sigma (fun ε => range (e ε)), (p.2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [Finset.sum_sigma]
    have h1 : ∀ ε ∈ s, ∑ i ∈ range (e ε), (i : ℝ) ≤ (e ε : ℝ) * (n / 2) := by
      intro ε hε
      rw [sum_range_cast]
      have h0 : (0 : ℝ) ≤ e ε := Nat.cast_nonneg _
      have hle : e ε ≤ n :=
        (single_le_sum (f := fun ε => e ε) (fun _ _ => Nat.zero_le _) hε).trans hsum
      have hleR : (e ε : ℝ) ≤ n := by exact_mod_cast hle
      nlinarith
    refine (sum_le_sum h1).trans ?_
    rw [← sum_mul]
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hS : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by positivity
  have hAc : ∀ j, |A.coeff j| ≤ ((n : ℝ) ^ 2 / 2) ^ j := by
    intro j
    have h1 := coeff_prod_le (range v) (fun i => (i : ℝ)) (fun i _ => Nat.cast_nonneg i) j
    have h2 : (∑ i ∈ range v, (i : ℝ)) ^ j ≤ ((n : ℝ) ^ 2 / 2) ^ j :=
      pow_le_pow_left₀ (sum_nonneg fun i _ => Nat.cast_nonneg i) hsA j
    exact h1.trans h2
  have hDc : ∀ j, |D.coeff j| ≤ ((n : ℝ) ^ 2 / 2) ^ j := by
    intro j
    have h1 := coeff_prod_le (s.sigma (fun ε => range (e ε))) (fun p => ((p.2 : ℕ) : ℝ))
      (fun p _ => Nat.cast_nonneg p.2) j
    have h2 : (∑ p ∈ s.sigma (fun ε => range (e ε)), (p.2 : ℝ)) ^ j ≤ ((n : ℝ) ^ 2 / 2) ^ j :=
      pow_le_pow_left₀ (sum_nonneg fun p _ => Nat.cast_nonneg p.2) hsD j
    exact h1.trans h2
  have hD0 : D.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hDe]
    simp
  obtain ⟨a, ha1, ha2⟩ := series_bound A D _ hS hAc hDc hD0
  refine ⟨a, fun j => ?_, fun M => ?_⟩
  · have := ha1 j
    rwa [show 2 * ((n : ℝ) ^ 2 / 2) = (n : ℝ) ^ 2 by ring, ← pow_mul] at this
  · refine (ha2 M).congr_left fun N => ?_
    rw [hAe, hDe]

theorem lb_series (K : List (Fin d × Bool)) (hK : K ≠ []) (Q' : Part K) :
    ∃ a : ℕ → ℝ, (∀ j, |a j| ≤ (K.length : ℝ) ^ (2 * j)) ∧
      ∀ M : ℕ, (fun N : ℕ =>
          (∏ i ∈ Finset.range Q'.parts.card, (1 - (i : ℝ) * (1 / N))) /
            (∏ ε ∈ E K (⊤ : Part K), ∏ i ∈ Finset.range (efib K Q' ⊤ ε), (1 - (i : ℝ) * (1 / N))) -
          ∑ j ∈ Finset.range (M + 1), a j * (1 / (N : ℝ)) ^ j) =O[atTop]
        (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1)) := by
  have hv : Q'.parts.card ≤ K.length := by
    have := Q'.card_parts_le_card
    rwa [card_univ, Fintype.card_fin] at this
  exact series_general _ _ _ _ hv (sum_efib_le K Q')

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
theorem asympCoeff_of_expansion (F : ℕ → ℝ) (A : ℕ → ℝ)
    (h : ∀ M : ℕ, (fun N : ℕ => F N - ∑ j ∈ range (M + 1), A j * (1 / (N : ℝ)) ^ j) =O[atTop]
      (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1))) (j : ℕ) :
    StrongConv.asympCoeff F j = A j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [StrongConv.asympCoeff.eq_1 F j]
    have hsum : ∀ N : ℕ, ∑ i : Fin j, StrongConv.asympCoeff F i / (N : ℝ) ^ (i : ℕ) =
        ∑ i ∈ range j, A i * (1 / (N : ℝ)) ^ i := by
      intro N
      rw [← Fin.sum_univ_eq_sum_range (fun i => A i * (1 / (N : ℝ)) ^ i) j]
      refine Fintype.sum_congr _ _ fun i => ?_
      rw [ih i i.2, one_div, inv_pow, div_eq_mul_inv]
    simp only [hsum]
    apply Tendsto.limUnder_eq
    have he : ∀ N : ℕ, N ≠ 0 → (N : ℝ) ^ j * (1 / (N : ℝ)) ^ j = 1 := by
      intro N hN
      have : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      rw [← mul_pow, mul_one_div_cancel this, one_pow]
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ j *
        (F N - ∑ i ∈ range (j + 1), A i * (1 / (N : ℝ)) ^ i)) atTop (𝓝 0) := by
      have hO := (isBigO_refl (fun N : ℕ => (N : ℝ) ^ j) atTop).mul (h j)
      refine hO.trans_tendsto ?_
      refine Tendsto.congr' ?_ tendsto_one_div_atTop_nhds_zero_nat
      filter_upwards [eventually_ne_atTop 0] with N hN
      rw [pow_succ, ← mul_assoc, he N hN, one_mul]
    have h3 := h2.const_add (A j)
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    rw [sum_range_succ]
    linear_combination (-(A j)) * he N hN

theorem expansion_shift (g : ℕ → ℝ) (a : ℕ → ℝ) (k : ℕ)
    (h : ∀ M : ℕ, (fun N : ℕ => g N - ∑ j ∈ range (M + 1), a j * (1 / (N : ℝ)) ^ j) =O[atTop]
      (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1))) (M : ℕ) :
    (fun N : ℕ => (1 / (N : ℝ)) ^ k * g N -
        ∑ j ∈ range (M + 1), (if k ≤ j then a (j - k) else 0) * (1 / (N : ℝ)) ^ j) =O[atTop]
      (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1)) := by
  by_cases hk : k ≤ M
  · have h1 := (isBigO_refl (fun N : ℕ => (1 / (N : ℝ)) ^ k) atTop).mul (h (M - k))
    refine h1.congr ?_ ?_
    · intro N
      rw [mul_sub]
      congr 1
      rw [mul_sum]
      have : M + 1 = k + (M - k + 1) := by omega
      rw [this, sum_range_add _ k (M - k + 1), sum_eq_zero (s := range k), zero_add]
      · refine sum_congr rfl fun i _ => ?_
        rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left, pow_add]
        ring
      · intro i hi
        rw [if_neg (by have := mem_range.1 hi; omega), zero_mul]
    · intro N
      rw [← pow_add]
      congr 1
      omega
  · rw [not_le] at hk
    have hz : ∀ N : ℕ, ∑ j ∈ range (M + 1), (if k ≤ j then a (j - k) else 0) * (1 / (N : ℝ)) ^ j
        = 0 := by
      intro N
      refine sum_eq_zero fun j hj => ?_
      rw [if_neg (by have := mem_range.1 hj; omega), zero_mul]
    simp only [hz, sub_zero]
    have hx : Tendsto (fun N : ℕ => (1 / (N : ℝ)) ^ 1) atTop (𝓝 0) := by
      simp only [pow_one]; exact tendsto_one_div_atTop_nhds_zero_nat
    have hg : g =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
      have h0 := (h 0).trans (hx.isBigO_one ℝ)
      have hc : (fun _ : ℕ => a 0) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := isBigO_const_const _ one_ne_zero _
      refine (h0.add hc).congr_left fun N => ?_
      simp
    have hxk : (fun N : ℕ => (1 / (N : ℝ)) ^ k) =O[atTop] (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have h0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      have h1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN'
      rw [one_mul, Real.norm_of_nonneg (pow_nonneg h0 _), Real.norm_of_nonneg (pow_nonneg h0 _)]
      exact pow_le_pow_of_le_one h0 h1 hk
    refine (hxk.mul hg).congr_right fun N => ?_
    rw [mul_one]

/-! ## The bound for a cyclically reduced word -/
theorem parts_top (K : List (Fin d × Bool)) (hK : K ≠ []) :
    (⊤ : Part K).parts = {univ} := by
  have hne : (univ : Finset (Fin K.length)) ≠ ⊥ := by
    have : Nonempty (Fin K.length) := ⟨⟨0, List.length_pos_iff.2 hK⟩⟩
    exact Finset.univ_nonempty.ne_empty
  rcases Finset.subset_singleton_iff.1 (Finpartition.parts_top_subset
    (univ : Finset (Fin K.length))) with h | h
  · exact absurd (Finpartition.parts_eq_empty_iff.1 h) hne
  · exact h

theorem lb_cyc (K : List (Fin d × Bool)) (hK : K ≠ []) (hred : FreeGroup.IsCyclicallyReduced K)
    (s : ℕ) :
    |StrongConv.asympCoeff (Fix (FreeGroup.mk K)) s| ≤ (K.length : ℝ) ^ (2 * (s + 1)) := by
  have hn : 0 < K.length := List.length_pos_iff.2 hK
  have hnR : (1 : ℝ) ≤ K.length := by exact_mod_cast hn
  have hn0 : (K.length : ℝ) ≠ 0 := by linarith
  set FFs : Finset (Part K) := (univ : Finset (Part K)).filter (FF K) with hFFs
  set kn : Part K → ℕ := fun Q' => (E K Q').card - Q'.parts.card with hkn
  have hLx : ∀ Q' ∈ FFs, ∀ x : ℝ, Lx K Q' ⊤ x = x ^ (kn Q') *
      ((∏ i ∈ Finset.range Q'.parts.card, (1 - (i : ℝ) * x)) /
        (∏ ε ∈ E K (⊤ : Part K), ∏ i ∈ Finset.range (efib K Q' ⊤ ε), (1 - (i : ℝ) * x))) := by
    intro Q' hQ' x
    have hpos := Puder.PP.ex_pos K hK hred Q' (mem_filter.1 hQ').2
    have hv : vfib K Q' univ = Q'.parts.card := by
      unfold vfib
      rw [filter_true_of_mem fun B _ => subset_univ B]
    have hexp : ((E K Q').card : ℤ) - (Q'.parts.card : ℤ) = ((kn Q' : ℕ) : ℤ) := by
      rw [hkn]; push_cast [Nat.cast_sub hpos]; ring
    unfold Lx
    rw [parts_top K hK, prod_singleton, hv, hexp, zpow_natCast, mul_div_assoc]
  choose a ha1 ha2 using fun Q' : Part K => lb_series K hK Q'
  set b : Part K → ℕ → ℝ := fun Q' j => if kn Q' ≤ j then a Q' (j - kn Q') else 0 with hb
  have hexpand : ∀ M : ℕ, (fun N : ℕ => Fix (FreeGroup.mk K) N -
        ∑ j ∈ range (M + 1), (∑ Q' ∈ FFs, b Q' j) * (1 / (N : ℝ)) ^ j) =O[atTop]
      (fun N : ℕ => (1 / (N : ℝ)) ^ (M + 1)) := by
    intro M
    have h1 := IsBigO.sum (s := FFs)
      (fun Q' _ => expansion_shift _ (a Q') (kn Q') (ha2 Q') M)
    refine h1.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop K.length] with N hN
    simp only [Finset.sum_apply]
    rw [Puder.PP.fix_eq_sum K hK N hN, ← hFFs, sum_sub_distrib]
    congr 1
    · refine sum_congr rfl fun Q' hQ' => ?_
      rw [hLx Q' hQ']
    · rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_mul]
  rw [asympCoeff_of_expansion _ _ hexpand s]
  have hterm : ∀ Q' ∈ FFs, |b Q' s| ≤ (K.length : ℝ) ^ (2 * (s + 1)) *
      (1 / (K.length : ℝ) ^ 2) ^ ((E K Q').card + 1 - Q'.parts.card) := by
    intro Q' hQ'
    have hpos := Puder.PP.ex_pos K hK hred Q' (mem_filter.1 hQ').2
    have hk1 : (E K Q').card + 1 - Q'.parts.card = kn Q' + 1 := by
      show _ = (E K Q').card - Q'.parts.card + 1
      omega
    rw [hk1, hb]
    by_cases hks : kn Q' ≤ s
    · simp only [if_pos hks]
      refine (ha1 Q' (s - kn Q')).trans (le_of_eq ?_)
      have h2 : 2 * (s + 1) = 2 * (s - kn Q') + 2 * (kn Q' + 1) := by omega
      rw [h2, pow_add, pow_mul (K.length : ℝ) 2 (kn Q' + 1), mul_assoc, ← mul_pow,
        mul_one_div_cancel (pow_ne_zero 2 hn0), one_pow, mul_one]
    · simp only [if_neg hks, abs_zero]
      positivity
  calc |∑ Q' ∈ FFs, b Q' s| ≤ ∑ Q' ∈ FFs, |b Q' s| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q' ∈ FFs, (K.length : ℝ) ^ (2 * (s + 1)) *
          (1 / (K.length : ℝ) ^ 2) ^ ((E K Q').card + 1 - Q'.parts.card) := sum_le_sum hterm
    _ = (K.length : ℝ) ^ (2 * (s + 1)) * ∑ Q' ∈ FFs,
          (1 / (K.length : ℝ) ^ 2) ^ ((E K Q').card + 1 - Q'.parts.card) := by rw [mul_sum]
    _ ≤ (K.length : ℝ) ^ (2 * (s + 1)) * 1 :=
        mul_le_mul_of_nonneg_left (Puder.PP.ex_count K hK hred) (by positivity)
    _ = (K.length : ℝ) ^ (2 * (s + 1)) := mul_one _

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

theorem fix_conj (G u : FreeGroup (Fin d)) : Fix (G * u * G⁻¹) = Fix u := by
  funext N
  unfold Fix
  congr 1
  funext σ
  rw [map_mul, map_mul, map_inv, card_fix_conj]

theorem leafB (d : ℕ) (w : FreeGroup (Fin d)) (hw : w ≠ 1) (s : ℕ)
    (hs : primitivityRank w ≤ s) :
    |StrongConv.asympCoeff (fun N : ℕ => StrongConv.uniformExp
        (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ))) s| ≤
      (w.toWord.length : ℝ) ^ (2 * (s + 1)) := by
  have hconj : w = FreeGroup.mk (FreeGroup.reduceCyclically.conjugator w.toWord) *
      FreeGroup.mk (FreeGroup.reduceCyclically w.toWord) *
      (FreeGroup.mk (FreeGroup.reduceCyclically.conjugator w.toWord))⁻¹ := by
    rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk,
      FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically, FreeGroup.mk_toWord]
  have hK : FreeGroup.reduceCyclically w.toWord ≠ [] := by
    intro h
    apply hw
    rw [hconj, h]
    show _ * 1 * _ = 1
    group
  have hred : FreeGroup.IsCyclicallyReduced (FreeGroup.reduceCyclically w.toWord) :=
    FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
  have hlen : (FreeGroup.reduceCyclically w.toWord).length ≤ w.toWord.length := by
    have := congrArg List.length
      (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically w.toWord)
    simp only [List.length_append] at this
    omega
  have hfix : Fix w = Fix (FreeGroup.mk (FreeGroup.reduceCyclically w.toWord)) := by
    conv_lhs => rw [hconj]
    exact fix_conj _ _
  show |StrongConv.asympCoeff (Fix w) s| ≤ _
  rw [hfix]
  refine (lb_cyc _ hK hred s).trans ?_
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hlen) _

end Puder.PP.PartB
end

section
open scoped Classical
open Finset Asymptotics Filter
namespace Puder.PP
variable {d : ℕ}
alias leafB := Puder.PP.PartB.leafB

end Puder.PP
end


theorem solution (d : ℕ) (w : FreeGroup (Fin d)) (hw : w ≠ 1)
    (s : ℕ) (hs : Puder.primitivityRank w ≤ s) :
    |StrongConv.asympCoeff (fun N : ℕ => StrongConv.uniformExp
        (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ))) s| ≤
      (w.toWord.length : ℝ) ^ (2 * (s + 1)) :=
  Puder.PP.leafB d w hw s hs
