-- Prove2me | solution 1 for TenChallenges.challenge_04_r2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:23:34.769627+00:00
-- url     : https://prove2.me/submissions/4600b7f0-61da-4931-87d3-76a54fb1042f

import Definitions.Def_TenChallenges_Challenge_04
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sidorenko's Inequality for Bipartite Graphs with Sides at most `2` (`r = 2`)

Every finite bipartite graph `H` admitting a bipartition `V(H) = X ∪ Y` with
`|X| ≤ 2` and `|Y| ≤ 2` satisfies `SidorenkoFor H G` for every finite nonempty
graph `G`.

## Proof strategy
1. **Isolate padding & isomorphism invariance**: Adding `(2 - |X|) + (2 - |Y|)`
   isolated vertices preserves `SidorenkoFor` and yields a bipartite graph on
   `Fin 2 ⊕ Fin 2` of the form `bip22 M` for `M : Fin 2 → Fin 2 → Bool`.
2. **Symmetry reduction**: Swapping vertices within either part or swapping the
   two parts (`Equiv.sumComm`) reduces all `16` matrices `M` to `6` canonical
   patterns: `0` edges, `1` edge (`K₂ ⊕ K̄₂`), the `2`-matching (`2 K₂`), the
   `2`-star (`K₁,₂ ⊕ K̄₁`), the `4`-vertex path (`P₄`), and the `4`-cycle (`C₄`).
3. **Analytic bounds**:
   - `0`, `1`, and `2`-matching hold with equality;
   - `K₁,₂` and `C₄` follow from one and two applications of Cauchy–Schwarz;
   - `P₄` (`S³ ≤ n² ∑_{(u,v) ∈ E_dir} d(u) d(v)`) follows from bounding
     `∑_{(u,v) ∈ E_dir} 1 / √(d(u) d(v)) ≤ ∑_{(u,v) ∈ E_dir} (d(u)⁻¹ + d(v)⁻¹)/2 ≤ n`
     and applying Cauchy–Schwarz twice on directed edges.
-/

set_option linter.all false

open SimpleGraph

namespace TenChallenges.Challenge04R2

section General

/-- Graph isomorphisms preserve `homDensity`. -/
lemma homDensity_iso {W₁ W₂ V : Type*} [Fintype W₁] [Fintype W₂] [Fintype V]
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂} (e : H₁ ≃g H₂) (G : SimpleGraph V) :
    homDensity H₁ G = homDensity H₂ G := by
  unfold homDensity
  have hW : Fintype.card W₁ = Fintype.card W₂ := Fintype.card_congr e.toEquiv
  have hhom :
      Nat.card {f : W₁ → V // ∀ ⦃a b : W₁⦄, H₁.Adj a b → G.Adj (f a) (f b)} =
      Nat.card {f : W₂ → V // ∀ ⦃a b : W₂⦄, H₂.Adj a b → G.Adj (f a) (f b)} := by
    apply Nat.card_congr
    exact
      { toFun := fun f =>
          ⟨fun w₂ => f.1 (e.symm w₂), fun {_ _} h => f.2 ((e.symm.map_rel_iff).mpr h)⟩
        invFun := fun f =>
          ⟨fun w₁ => f.1 (e w₁), fun {_ _} h => f.2 ((e.map_rel_iff).mpr h)⟩
        left_inv := fun f => Subtype.ext (funext fun w₁ => by simp)
        right_inv := fun f => Subtype.ext (funext fun w₂ => by simp) }
  rw [hhom, hW]

/-- Graph isomorphisms preserve edge counts. -/
lemma edgeCount_iso {W₁ W₂ : Type*} [Fintype W₁] [Fintype W₂]
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂} (e : H₁ ≃g H₂) :
    Nat.card H₁.edgeSet = Nat.card H₂.edgeSet := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨Sym2.map e.toEquiv x.1, ?_⟩
      invFun := fun y => ⟨Sym2.map e.toEquiv.symm y.1, ?_⟩
      left_inv := fun ⟨z, _⟩ => Subtype.ext (by
        induction z using Sym2.ind
        simp only [Sym2.map_pair_eq, Sym2.eq_iff]
        exact Or.inl ⟨e.toEquiv.symm_apply_apply _, e.toEquiv.symm_apply_apply _⟩)
      right_inv := fun ⟨z, _⟩ => Subtype.ext (by
        induction z using Sym2.ind
        simp only [Sym2.map_pair_eq, Sym2.eq_iff]
        exact Or.inl ⟨e.toEquiv.apply_symm_apply _, e.toEquiv.apply_symm_apply _⟩) }
  · rcases x with ⟨z, hz⟩
    induction z using Sym2.ind with
    | h a b =>
      simp only [Sym2.map_pair_eq, mem_edgeSet] at hz ⊢
      exact (e.map_rel_iff).mpr hz
  · rcases y with ⟨z, hz⟩
    induction z using Sym2.ind with
    | h a b =>
      simp only [Sym2.map_pair_eq, mem_edgeSet] at hz ⊢
      exact (e.symm.map_rel_iff).mpr hz

/-- Graph isomorphisms preserve `SidorenkoFor`. -/
lemma sidorenko_iso {W₁ W₂ V : Type*} [Fintype W₁] [Fintype W₂] [Fintype V]
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂} (e : H₁ ≃g H₂) (G : SimpleGraph V) :
    SidorenkoFor H₁ G ↔ SidorenkoFor H₂ G := by
  simp only [SidorenkoFor, homDensity_iso e G, edgeCount_iso e]

/-- Homomorphism counts multiply over disjoint unions of source graphs. -/
lemma homCount_sum {W₁ W₂ V : Type*} (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (G : SimpleGraph V) :
    Nat.card {f : W₁ ⊕ W₂ → V // ∀ ⦃a b⦄, (H₁ ⊕g H₂).Adj a b → G.Adj (f a) (f b)} =
      Nat.card {f : W₁ → V // ∀ ⦃a b⦄, H₁.Adj a b → G.Adj (f a) (f b)} *
      Nat.card {f : W₂ → V // ∀ ⦃a b⦄, H₂.Adj a b → G.Adj (f a) (f b)} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun f =>
        (⟨fun a => f.1 (.inl a), fun {_ _} h => f.2 h⟩,
         ⟨fun a => f.1 (.inr a), fun {_ _} h => f.2 h⟩)
      invFun := fun f =>
        ⟨Sum.elim f.1.1 f.2.1,
         fun {a b} h => match a, b, h with
         | .inl _, .inl _, h => f.1.2 h
         | .inr _, .inr _, h => f.2.2 h
         | .inl a, .inr b, h => (not_adj_sum_inl_inr a b h).elim
         | .inr b, .inl a, h => (not_adj_sum_inl_inr a b h.symm).elim⟩
      left_inv := fun f => Subtype.ext (funext fun a => match a with
        | .inl _ => rfl
        | .inr _ => rfl)
      right_inv := fun f => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl) }

/-- Adding finite isolated vertices leaves `SidorenkoFor` unchanged for nonempty targets. -/
lemma sidorenko_add_isolates_iff {W₁ W₂ V : Type*} [Fintype W₁] [Fintype W₂] [Fintype V]
    [Nonempty V] (H : SimpleGraph W₁) (G : SimpleGraph V) :
    SidorenkoFor (H ⊕g (⊥ : SimpleGraph W₂)) G ↔ SidorenkoFor H G := by
  classical
  have hbot_hom : homDensity (⊥ : SimpleGraph W₂) G = 1 := by
    unfold homDensity
    simp only [bot_adj, false_implies, implies_true, Nat.card_subtype_true]
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
    exact div_self (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  have hsum_hom : homDensity (H ⊕g (⊥ : SimpleGraph W₂)) G = homDensity H G := by
    have hmul : homDensity (H ⊕g (⊥ : SimpleGraph W₂)) G =
        homDensity H G * homDensity (⊥ : SimpleGraph W₂) G := by
      unfold homDensity
      rw [homCount_sum, Fintype.card_sum, Nat.cast_mul, pow_add, mul_div_mul_comm]
    rw [hmul, hbot_hom, mul_one]
  have hedge : Nat.card (H ⊕g (⊥ : SimpleGraph W₂)).edgeSet = Nat.card H.edgeSet := by
    rw [Nat.card_congr (edgeSetSumEquiv (G := H) (H := (⊥ : SimpleGraph W₂))), Nat.card_sum]
    simp [edgeSet_bot]
  simp only [SidorenkoFor, hsum_hom, hedge]

/-- Finite Cauchy–Schwarz inequality proved directly via Lagrange's identity. -/
private lemma sum_mul_sq_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  have h0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      2 * ((∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) - (∑ i ∈ s, f i * g i) ^ 2) := by
    have h1 : ∀ i j, (f i * g j - f j * g i) ^ 2 =
        f i ^ 2 * g j ^ 2 + f j ^ 2 * g i ^ 2 - 2 * ((f i * g i) * (f j * g j)) := by
      intro i j; ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    rw [← Finset.mul_sum]
    ring
  linarith

end General

section Bip22

/-- Bipartite graph on `Fin 2 ⊕ Fin 2` specified by a `2 × 2` Boolean biadjacency matrix. -/
def bip22 (M : Fin 2 → Fin 2 → Bool) : SimpleGraph (Fin 2 ⊕ Fin 2) where
  Adj u v := match u, v with
    | .inl i, .inr j => M i j = true
    | .inr j, .inl i => M i j = true
    | _, _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

def edgePairs (M : Fin 2 → Fin 2 → Bool) : Finset (Fin 2 × Fin 2) :=
  Finset.univ.filter fun p => M p.1 p.2 = true

lemma edgeCount_bip22 (M : Fin 2 → Fin 2 → Bool) :
    Nat.card (bip22 M).edgeSet = (edgePairs M).card := by
  rw [← Fintype.card_coe (edgePairs M), ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine Equiv.symm (Equiv.ofBijective
    (fun (p : edgePairs M) =>
      (⟨s(Sum.inl p.1.1, Sum.inr p.1.2), (Finset.mem_filter.mp p.2).2⟩ : (bip22 M).edgeSet))
    ⟨?_, ?_⟩)
  · rintro ⟨⟨i₁, j₁⟩, _⟩ ⟨⟨i₂, j₂⟩, _⟩ h
    have h' := Subtype.mk.inj h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨hL, hR⟩ | ⟨hL, _⟩
    · injection hL with hi
      injection hR with hj
      subst hi hj
      rfl
    · nomatch hL
  · rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | h u v =>
      cases u with
      | inl i =>
        cases v with
        | inl _ => exact False.elim hz
        | inr j => exact ⟨⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩, rfl⟩
      | inr j =>
        cases v with
        | inl i =>
          exact ⟨⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩,
            Subtype.ext Sym2.eq_swap⟩
        | inr _ => exact False.elim hz

/-- Swapping the two left vertices of `bip22`. -/
def bip22SwapLeft (M : Fin 2 → Fin 2 → Bool) :
    bip22 (fun i j => M (1 - i) j) ≃g bip22 M where
  toEquiv := Equiv.sumCongr
    { toFun := fun i => 1 - i
      invFun := fun i => 1 - i
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
    (Equiv.refl (Fin 2))
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> rfl

/-- Swapping the two right vertices of `bip22`. -/
def bip22SwapRight (M : Fin 2 → Fin 2 → Bool) :
    bip22 (fun i j => M i (1 - j)) ≃g bip22 M where
  toEquiv := Equiv.sumCongr (Equiv.refl (Fin 2))
    { toFun := fun j => 1 - j
      invFun := fun j => 1 - j
      left_inv := fun j => by fin_cases j <;> rfl
      right_inv := fun j => by fin_cases j <;> rfl }
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> rfl

/-- Transposing the two sides of `bip22`. -/
def bip22Transpose (M : Fin 2 → Fin 2 → Bool) :
    bip22 (fun j i => M i j) ≃g bip22 M where
  toEquiv := Equiv.sumComm (Fin 2) (Fin 2)
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

def adjR (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℝ :=
  if G.Adj u v then 1 else 0

def degR (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : ℝ :=
  ∑ v : V, adjR G u v

lemma adjR_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    0 ≤ adjR G u v := by
  unfold adjR; split_ifs <;> norm_num

lemma adjR_symm (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    adjR G u v = adjR G v u := by
  unfold adjR; simp [G.adj_comm]

lemma degR_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    0 ≤ degR G u :=
  Finset.sum_nonneg fun v _ => adjR_nonneg G u v

def dirEdges (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p => G.Adj p.1 p.2

lemma card_dirEdges_eq_sum_degR (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((dirEdges G).card : ℝ) = ∑ u : V, degR G u := by
  unfold dirEdges degR adjR
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> norm_num

lemma sum_dirEdges_eq (G : SimpleGraph V) [DecidableRel G.Adj] (f : V × V → ℝ) :
    ∑ p ∈ dirEdges G, f p = ∑ u : V, ∑ v : V, adjR G u v * f (u, v) := by
  unfold dirEdges adjR
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

lemma homDensity_K2_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G =
      (∑ u : V, degR G u) / (Fintype.card V : ℝ) ^ 2 := by
  unfold homDensity
  rw [Fintype.card_fin, ← card_dirEdges_eq_sum_degR]
  congr 2
  rw [← Fintype.card_coe (dirEdges G), ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine
    { toFun := fun f => ⟨(f.1 0, f.1 1), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
         f.2 (by decide : (completeGraph (Fin 2)).Adj 0 1)⟩⟩
      invFun := fun p => ⟨fun i => if i = 0 then p.1.1 else p.1.2, ?_⟩
      left_inv := fun f => Subtype.ext (funext fun i => by fin_cases i <;> rfl)
      right_inv := fun p => Subtype.ext rfl }
  intro a b hab
  have hp : G.Adj p.1.1 p.1.2 := (Finset.mem_filter.mp p.2).2
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact hp
  · exact hp.symm
  · exact absurd rfl hab

def quads (G : SimpleGraph V) [DecidableRel G.Adj] (M : Fin 2 → Fin 2 → Bool) :
    Finset ((V × V) × (V × V)) :=
  Finset.univ.filter fun q =>
    (M 0 0 = true → G.Adj q.1.1 q.2.1) ∧
    (M 0 1 = true → G.Adj q.1.1 q.2.2) ∧
    (M 1 0 = true → G.Adj q.1.2 q.2.1) ∧
    (M 1 1 = true → G.Adj q.1.2 q.2.2)

lemma homDensity_bip22_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Fin 2 → Fin 2 → Bool) :
    homDensity (bip22 M) G = ((quads G M).card : ℝ) / (Fintype.card V : ℝ) ^ 4 := by
  unfold homDensity
  have hcard4 : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by decide
  rw [hcard4]
  congr 2
  rw [← Fintype.card_coe (quads G M), ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine
    { toFun := fun f => ⟨((f.1 (.inl 0), f.1 (.inl 1)), (f.1 (.inr 0), f.1 (.inr 1))),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨fun h => f.2 (a := .inl 0) (b := .inr 0) h,
           fun h => f.2 (a := .inl 0) (b := .inr 1) h,
           fun h => f.2 (a := .inl 1) (b := .inr 0) h,
           fun h => f.2 (a := .inl 1) (b := .inr 1) h⟩⟩⟩
      invFun := fun q => ⟨fun w => match w with
        | .inl i => if i = 0 then q.1.1.1 else q.1.1.2
        | .inr j => if j = 0 then q.1.2.1 else q.1.2.2, ?_⟩
      left_inv := fun f => Subtype.ext (funext fun w => by
        cases w with
        | inl i => fin_cases i <;> rfl
        | inr j => fin_cases j <;> rfl)
      right_inv := fun q => Subtype.ext rfl }
  intro a b hab
  obtain ⟨h00, h01, h10, h11⟩ := (Finset.mem_filter.mp q.2).2
  cases a with
  | inl i =>
    cases b with
    | inl i' => exact False.elim hab
    | inr j =>
      fin_cases i <;> fin_cases j
      · exact h00 hab
      · exact h01 hab
      · exact h10 hab
      · exact h11 hab
  | inr j =>
    cases b with
    | inl i =>
      fin_cases i <;> fin_cases j
      · exact (h00 hab).symm
      · exact (h01 hab).symm
      · exact (h10 hab).symm
      · exact (h11 hab).symm
    | inr j' => exact False.elim hab

lemma card_quads_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Fin 2 → Fin 2 → Bool) :
    ((quads G M).card : ℝ) =
      ∑ u₀ : V, ∑ u₁ : V, ∑ v₀ : V, ∑ v₁ : V,
        if (M 0 0 = true → G.Adj u₀ v₀) ∧
           (M 0 1 = true → G.Adj u₀ v₁) ∧
           (M 1 0 = true → G.Adj u₁ v₀) ∧
           (M 1 1 = true → G.Adj u₁ v₁) then (1 : ℝ) else 0 := by
  unfold quads
  rw [Finset.card_filter, Nat.cast_sum]
  have huniv : (Finset.univ : Finset ((V × V) × (V × V))) =
      (Finset.univ ×ˢ Finset.univ) ×ˢ (Finset.univ ×ˢ Finset.univ) := by ext; simp
  rw [huniv, Finset.sum_product, Finset.sum_product]
  refine Finset.sum_congr rfl fun u₀ _ => Finset.sum_congr rfl fun u₁ _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun v₀ _ => Finset.sum_congr rfl fun v₁ _ => ?_
  split_ifs <;> norm_num

/-! ### The 6 canonical `2 × 2` matrices -/

def M0 : Fin 2 → Fin 2 → Bool := fun _ _ => false
def M1 : Fin 2 → Fin 2 → Bool := fun i j => (i == 0) && (j == 0)
def Mmatch : Fin 2 → Fin 2 → Bool := fun i j => i == j
def Mstar : Fin 2 → Fin 2 → Bool := fun i _ => i == 0
def Mp4 : Fin 2 → Fin 2 → Bool := fun i j => !((i == 1) && (j == 1))
def Mc4 : Fin 2 → Fin 2 → Bool := fun _ _ => true

lemma sidorenko_M0 [Nonempty V] (G : SimpleGraph V) : SidorenkoFor (bip22 M0) G := by
  classical
  unfold SidorenkoFor
  rw [homDensity_bip22_eq, homDensity_K2_eq, edgeCount_bip22,
    show (edgePairs M0).card = 0 by decide, pow_zero, card_quads_sum]
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [M0, Bool.false_eq_true, false_implies, and_self, ↓reduceIte,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have h4 : (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) *
      ((Fintype.card V : ℝ) * (Fintype.card V : ℝ))) = (Fintype.card V : ℝ) ^ 4 := by ring
  rw [h4, div_self (pow_ne_zero 4 hn)]

lemma sidorenko_M1 [Nonempty V] (G : SimpleGraph V) : SidorenkoFor (bip22 M1) G := by
  classical
  unfold SidorenkoFor
  rw [homDensity_bip22_eq, homDensity_K2_eq, edgeCount_bip22,
    show (edgePairs M1).card = 1 by decide, pow_one, card_quads_sum]
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (∑ u₀ : V, ∑ u₁ : V, ∑ v₀ : V, ∑ v₁ : V,
      if (M1 0 0 = true → G.Adj u₀ v₀) ∧ (M1 0 1 = true → G.Adj u₀ v₁) ∧
         (M1 1 0 = true → G.Adj u₁ v₀) ∧ (M1 1 1 = true → G.Adj u₁ v₁) then (1 : ℝ) else 0) =
      (∑ u₀ : V, degR G u₀) * (Fintype.card V : ℝ) ^ 2 := by
    have hcond : ∀ u₀ u₁ v₀ v₁ : V,
        (if (M1 0 0 = true → G.Adj u₀ v₀) ∧ (M1 0 1 = true → G.Adj u₀ v₁) ∧
            (M1 1 0 = true → G.Adj u₁ v₀) ∧ (M1 1 1 = true → G.Adj u₁ v₁) then (1 : ℝ) else 0) =
        adjR G u₀ v₀ := by
      intro u₀ u₁ v₀ v₁
      have h00 : M1 0 0 = true := by decide
      have h01 : M1 0 1 = false := by decide
      have h10 : M1 1 0 = false := by decide
      have h11 : M1 1 1 = false := by decide
      rw [h00, h01, h10, h11]
      simp [adjR]
    simp_rw [hcond]
    calc ∑ u₀ : V, ∑ _u₁ : V, ∑ v₀ : V, ∑ _v₁ : V, adjR G u₀ v₀
        = ∑ u₀ : V, ∑ _u₁ : V, ∑ v₀ : V, (Fintype.card V : ℝ) * adjR G u₀ v₀ := by
            refine Finset.sum_congr rfl fun u₀ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun v₀ _ => by simp
      _ = ∑ u₀ : V, ∑ _u₁ : V, (Fintype.card V : ℝ) * degR G u₀ := by
            refine Finset.sum_congr rfl fun u₀ _ => Finset.sum_congr rfl fun _ _ => ?_
            rw [← Finset.mul_sum]; rfl
      _ = ∑ u₀ : V, (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * degR G u₀) := by
            refine Finset.sum_congr rfl fun u₀ _ => by simp
      _ = (∑ u₀ : V, degR G u₀) * (Fintype.card V : ℝ) ^ 2 := by
            have : ∀ u₀ : V, (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * degR G u₀) =
                degR G u₀ * (Fintype.card V : ℝ) ^ 2 := fun _ => by ring
            simp_rw [this, ← Finset.sum_mul]
  rw [hsum, ge_iff_le]
  have hdiv : ((∑ u₀ : V, degR G u₀) * (Fintype.card V : ℝ) ^ 2) / (Fintype.card V : ℝ) ^ 4 =
      (∑ u₀ : V, degR G u₀) / (Fintype.card V : ℝ) ^ 2 := by
    field_simp [hn]
  rw [hdiv]

lemma sidorenko_Mmatch [Nonempty V] (G : SimpleGraph V) : SidorenkoFor (bip22 Mmatch) G := by
  classical
  unfold SidorenkoFor
  rw [homDensity_bip22_eq, homDensity_K2_eq, edgeCount_bip22,
    show (edgePairs Mmatch).card = 2 by decide, card_quads_sum]
  have hsum : (∑ u₀ : V, ∑ u₁ : V, ∑ v₀ : V, ∑ v₁ : V,
      if (Mmatch 0 0 = true → G.Adj u₀ v₀) ∧ (Mmatch 0 1 = true → G.Adj u₀ v₁) ∧
         (Mmatch 1 0 = true → G.Adj u₁ v₀) ∧ (Mmatch 1 1 = true → G.Adj u₁ v₁) then (1 : ℝ) else 0) =
      (∑ u : V, degR G u) ^ 2 := by
    have hcond : ∀ u₀ u₁ v₀ v₁ : V,
        (if (Mmatch 0 0 = true → G.Adj u₀ v₀) ∧ (Mmatch 0 1 = true → G.Adj u₀ v₁) ∧
            (Mmatch 1 0 = true → G.Adj u₁ v₀) ∧ (Mmatch 1 1 = true → G.Adj u₁ v₁)
         then (1 : ℝ) else 0) = adjR G u₀ v₀ * adjR G u₁ v₁ := by
      intro u₀ u₁ v₀ v₁
      have h00 : Mmatch 0 0 = true := by decide
      have h01 : Mmatch 0 1 = false := by decide
      have h10 : Mmatch 1 0 = false := by decide
      have h11 : Mmatch 1 1 = true := by decide
      rw [h00, h01, h10, h11]
      unfold adjR
      by_cases ha : G.Adj u₀ v₀ <;> by_cases hb : G.Adj u₁ v₁ <;> simp [ha, hb]
    simp_rw [hcond]
    calc ∑ u₀ : V, ∑ u₁ : V, ∑ v₀ : V, ∑ v₁ : V, adjR G u₀ v₀ * adjR G u₁ v₁
        = ∑ u₀ : V, ∑ u₁ : V, degR G u₀ * degR G u₁ := by
            refine Finset.sum_congr rfl fun u₀ _ => Finset.sum_congr rfl fun u₁ _ => ?_
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; rfl
      _ = (∑ u : V, degR G u) ^ 2 := by
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
  rw [hsum, div_pow, ← pow_mul, ge_iff_le]

lemma sidorenko_Mstar [Nonempty V] (G : SimpleGraph V) : SidorenkoFor (bip22 Mstar) G := by
  classical
  unfold SidorenkoFor
  rw [homDensity_bip22_eq, homDensity_K2_eq, edgeCount_bip22,
    show (edgePairs Mstar).card = 2 by decide, card_quads_sum]
  have hsum : (∑ u₀ : V, ∑ u₁ : V, ∑ v₀ : V, ∑ v₁ : V,
      if (Mstar 0 0 = true → G.Adj u₀ v₀) ∧ (Mstar 0 1 = true → G.Adj u₀ v₁) ∧
         (Mstar 1 0 = true → G.Adj u₁ v₀) ∧ (Mstar 1 1 = true → G.Adj u₁ v₁) then (1 : ℝ) else 0) =
      (Fintype.card V : ℝ) * ∑ u₀ : V, degR G u₀ ^ 2 := by
    have hcond : ∀ u₀ u₁ v₀ v₁ : V,
        (if (Mstar 0 0 = true → G.Adj u₀ v₀) ∧ (Mstar 0 1 = true → G.Adj u₀ v₁) ∧
            (Mstar 1 0 = true → G.Adj u₁ v₀) ∧ (Mstar 1 1 = true → G.Adj u₁ v₁)
         then (1 : ℝ) else 0) = adjR G u₀ v₀ * adjR G u₀ v₁ := by
      intro u₀ u₁ v₀ v₁
      have h00 : Mstar 0 0 = true := by decide
      have h01 : Mstar 0 1 = true := by decide
      have h10 : Mstar 1 0 = false := by decide
      have h11 : Mstar 1 1 = false := by decide
      rw [h00, h01, h10, h11]
      unfold adjR
      by_cases ha : G.Adj u₀ v₀ <;> by_cases hb : G.Adj u₀ v₁ <;> simp [ha, hb]
    simp_rw [hcond]
    calc ∑ u₀ : V, ∑ _u₁ : V, ∑ v₀ : V, ∑ v₁ : V, adjR G u₀ v₀ * adjR G u₀ v₁
        = ∑ u₀ : V, ∑ _u₁ : V, degR G u₀ ^ 2 := by
            refine Finset.sum_congr rfl fun u₀ _ => Finset.sum_congr rfl fun _ _ => ?_
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; unfold degR; ring
      _ = ∑ u₀ : V, (Fintype.card V : ℝ) * degR G u₀ ^ 2 := by
            refine Finset.sum_congr rfl fun u₀ _ => by simp
      _ = (Fintype.card V : ℝ) * ∑ u₀ : V, degR G u₀ ^ 2 := by
            rw [← Finset.mul_sum]
  rw [hsum, div_pow, ← pow_mul, ge_iff_le]
  have hn4 : (0 : ℝ) < (Fintype.card V : ℝ) ^ 4 :=
    pow_pos (Nat.cast_pos.mpr Fintype.card_pos) 4
  rw [div_le_div_iff_of_pos_right hn4]
  have hcs := sum_mul_sq_le (Finset.univ : Finset V) (fun _ => (1 : ℝ)) (fun u => degR G u)
  simpa using hcs

lemma sidorenko_Mc4 [Nonempty V] (G : SimpleGraph V) : SidorenkoFor (bip22 Mc4) G := by
  classical
  unfold SidorenkoFor
  rw [homDensity_bip22_eq, homDensity_K2_eq, edgeCount_bip22,
    show (edgePairs Mc4).card = 4 by decide, card_quads_sum]
  let c : V × V → ℝ := fun p => ∑ v : V, adjR G p.1 v * adjR G p.2 v
  have hsum : (∑ u₀ : V, ∑ u₁ : V, ∑ v₀ : V, ∑ v₁ : V,
      if (Mc4 0 0 = true → G.Adj u₀ v₀) ∧ (Mc4 0 1 = true → G.Adj u₀ v₁) ∧
         (Mc4 1 0 = true → G.Adj u₁ v₀) ∧ (Mc4 1 1 = true → G.Adj u₁ v₁) then (1 : ℝ) else 0) =
      ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p ^ 2 := by
    have hcond : ∀ u₀ u₁ v₀ v₁ : V,
        (if (Mc4 0 0 = true → G.Adj u₀ v₀) ∧ (Mc4 0 1 = true → G.Adj u₀ v₁) ∧
            (Mc4 1 0 = true → G.Adj u₁ v₀) ∧ (Mc4 1 1 = true → G.Adj u₁ v₁)
         then (1 : ℝ) else 0) =
        (adjR G u₀ v₀ * adjR G u₁ v₀) * (adjR G u₀ v₁ * adjR G u₁ v₁) := by
      intro u₀ u₁ v₀ v₁
      simp only [Mc4, forall_const]
      unfold adjR
      by_cases h1 : G.Adj u₀ v₀ <;> by_cases h2 : G.Adj u₀ v₁ <;>
      by_cases h3 : G.Adj u₁ v₀ <;> by_cases h4 : G.Adj u₁ v₁ <;> simp [h1, h2, h3, h4]
    simp_rw [hcond, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun u₀ _ => Finset.sum_congr rfl fun u₁ _ => ?_
    dsimp [c]; ring
  have hcsum : ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p = ∑ v : V, degR G v ^ 2 := by
    rw [Finset.sum_product]
    dsimp [c]
    calc ∑ u₀ : V, ∑ u₁ : V, ∑ v : V, adjR G u₀ v * adjR G u₁ v
        = ∑ u₀ : V, ∑ v : V, ∑ u₁ : V, adjR G u₀ v * adjR G u₁ v :=
            Finset.sum_congr rfl fun u₀ _ => Finset.sum_comm
      _ = ∑ v : V, ∑ u₀ : V, ∑ u₁ : V, adjR G u₀ v * adjR G u₁ v := Finset.sum_comm
      _ = ∑ v : V, degR G v ^ 2 := by
            refine Finset.sum_congr rfl fun v _ => ?_
            unfold degR
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul, adjR_symm G _ v]
            ring
  have hcs1 : (∑ u : V, degR G u) ^ 2 ≤ (Fintype.card V : ℝ) * ∑ v : V, degR G v ^ 2 := by
    simpa using sum_mul_sq_le (Finset.univ : Finset V) (fun _ => (1 : ℝ)) (fun v => degR G v)
  have hcs2 : (∑ p ∈ Finset.univ ×ˢ Finset.univ, c p) ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p ^ 2 := by
    have h := sum_mul_sq_le (Finset.univ ×ˢ Finset.univ : Finset (V × V)) (fun _ => (1 : ℝ)) c
    simpa [sq] using h
  have hS_nonneg : 0 ≤ (∑ u : V, degR G u) ^ 2 := sq_nonneg _
  have hmain : (∑ u : V, degR G u) ^ 4 ≤
      (Fintype.card V : ℝ) ^ 4 * ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p ^ 2 := by
    have hsq1 : ((∑ u : V, degR G u) ^ 2) ^ 2 ≤
        ((Fintype.card V : ℝ) * ∑ v : V, degR G v ^ 2) ^ 2 :=
      pow_le_pow_left₀ hS_nonneg hcs1 2
    calc (∑ u : V, degR G u) ^ 4
        = ((∑ u : V, degR G u) ^ 2) ^ 2 := by ring
      _ ≤ ((Fintype.card V : ℝ) * ∑ v : V, degR G v ^ 2) ^ 2 := hsq1
      _ = (Fintype.card V : ℝ) ^ 2 * (∑ p ∈ Finset.univ ×ˢ Finset.univ, c p) ^ 2 := by
          rw [hcsum]; ring
      _ ≤ (Fintype.card V : ℝ) ^ 2 *
          ((Fintype.card V : ℝ) ^ 2 * ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p ^ 2) :=
          mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
      _ = (Fintype.card V : ℝ) ^ 4 * ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p ^ 2 := by ring
  rw [hsum, div_pow, ← pow_mul, ge_iff_le]
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_div_iff₀ (pow_pos hn 8) (pow_pos hn 4)]
  calc (∑ u : V, degR G u) ^ 4 * (Fintype.card V : ℝ) ^ 4
      ≤ ((Fintype.card V : ℝ) ^ 4 * ∑ p ∈ Finset.univ ×ˢ Finset.univ, c p ^ 2) *
        (Fintype.card V : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hmain (pow_nonneg hn.le 4)
    _ = (∑ p ∈ Finset.univ ×ˢ Finset.univ, c p ^ 2) * (Fintype.card V : ℝ) ^ 8 := by ring

lemma sidorenko_Mp4 [Nonempty V] (G : SimpleGraph V) : SidorenkoFor (bip22 Mp4) G := by
  classical
  unfold SidorenkoFor
  rw [homDensity_bip22_eq, homDensity_K2_eq, edgeCount_bip22,
    show (edgePairs Mp4).card = 3 by decide, card_quads_sum]
  let E := dirEdges G
  let S : ℝ := ∑ u : V, degR G u
  let T : ℝ := ∑ p ∈ E, degR G p.1 * degR G p.2
  let n : ℝ := Fintype.card V
  have hS_card : (E.card : ℝ) = S := card_dirEdges_eq_sum_degR G
  have hsum : (∑ u₀ : V, ∑ u₁ : V, ∑ v₀ : V, ∑ v₁ : V,
      if (Mp4 0 0 = true → G.Adj u₀ v₀) ∧ (Mp4 0 1 = true → G.Adj u₀ v₁) ∧
         (Mp4 1 0 = true → G.Adj u₁ v₀) ∧ (Mp4 1 1 = true → G.Adj u₁ v₁) then (1 : ℝ) else 0) = T := by
    have hcond : ∀ u₀ u₁ v₀ v₁ : V,
        (if (Mp4 0 0 = true → G.Adj u₀ v₀) ∧ (Mp4 0 1 = true → G.Adj u₀ v₁) ∧
            (Mp4 1 0 = true → G.Adj u₁ v₀) ∧ (Mp4 1 1 = true → G.Adj u₁ v₁)
         then (1 : ℝ) else 0) = adjR G u₀ v₀ * adjR G u₁ v₀ * adjR G u₀ v₁ := by
      intro u₀ u₁ v₀ v₁
      have h00 : Mp4 0 0 = true := by decide
      have h01 : Mp4 0 1 = true := by decide
      have h10 : Mp4 1 0 = true := by decide
      have h11 : Mp4 1 1 = false := by decide
      rw [h00, h01, h10, h11]
      unfold adjR
      by_cases h1 : G.Adj u₀ v₀ <;> by_cases h2 : G.Adj u₀ v₁ <;>
      by_cases h3 : G.Adj u₁ v₀ <;> simp [h1, h2, h3]
    simp_rw [hcond, ← Finset.mul_sum]
    simp only [show ∀ u, (∑ v : V, adjR G u v) = degR G u from fun _ => rfl]
    have hstep : ∀ u₀ : V, (∑ u₁ : V, ∑ v₀ : V, adjR G u₀ v₀ * adjR G u₁ v₀ * degR G u₀) =
        ∑ v₀ : V, adjR G u₀ v₀ * (degR G u₀ * degR G v₀) := by
      intro u₀
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v₀ _ => ?_
      have : ∀ u₁ : V, adjR G u₀ v₀ * adjR G u₁ v₀ * degR G u₀ =
          (adjR G u₀ v₀ * degR G u₀) * adjR G v₀ u₁ := by
        intro u₁; rw [adjR_symm G u₁ v₀]; ring
      simp_rw [this, ← Finset.mul_sum]
      unfold degR; ring
    simp_rw [hstep]
    exact (sum_dirEdges_eq G (fun p => degR G p.1 * degR G p.2)).symm
  -- Positivity of degrees on directed edges
  have hdeg_pos : ∀ p ∈ E, 0 < degR G p.1 ∧ 0 < degR G p.2 := by
    intro p hp
    have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    have h1 : (1 : ℝ) ≤ degR G p.1 := by
      unfold degR
      have := Finset.single_le_sum (fun y _ => adjR_nonneg G p.1 y) (Finset.mem_univ p.2)
      simpa [adjR, hadj] using this
    have h2 : (1 : ℝ) ≤ degR G p.2 := by
      unfold degR
      have := Finset.single_le_sum (fun y _ => adjR_nonneg G p.2 y) (Finset.mem_univ p.1)
      simpa [adjR, hadj.symm] using this
    exact ⟨by linarith, by linarith⟩
  -- Bound Q := ∑_{p ∈ E} (√(d_u d_v))⁻¹ ≤ n
  let Q : ℝ := ∑ p ∈ E, (Real.sqrt (degR G p.1 * degR G p.2))⁻¹
  let R : ℝ := ∑ p ∈ E, Real.sqrt (degR G p.1 * degR G p.2)
  have hinv_sum1 : ∑ p ∈ E, (degR G p.1)⁻¹ ≤ n := by
    rw [sum_dirEdges_eq]
    calc ∑ u : V, ∑ v : V, adjR G u v * (degR G u)⁻¹
        = ∑ u : V, degR G u * (degR G u)⁻¹ := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.sum_mul]; rfl
      _ ≤ ∑ _u : V, (1 : ℝ) := by
            refine Finset.sum_le_sum fun u _ => ?_
            by_cases hd : degR G u = 0
            · simp [hd]
            · rw [mul_inv_cancel₀ hd]
      _ = n := by simp [n]
  have hinv_sum2 : ∑ p ∈ E, (degR G p.2)⁻¹ ≤ n := by
    rw [sum_dirEdges_eq, Finset.sum_comm]
    calc ∑ v : V, ∑ u : V, adjR G u v * (degR G v)⁻¹
        = ∑ v : V, degR G v * (degR G v)⁻¹ := by
            refine Finset.sum_congr rfl fun v _ => ?_
            simp_rw [adjR_symm G _ v, ← Finset.sum_mul]; rfl
      _ ≤ ∑ _v : V, (1 : ℝ) := by
            refine Finset.sum_le_sum fun v _ => ?_
            by_cases hd : degR G v = 0
            · simp [hd]
            · rw [mul_inv_cancel₀ hd]
      _ = n := by simp [n]
  have hQ_le : Q ≤ n := by
    have hpt : ∀ p ∈ E, (Real.sqrt (degR G p.1 * degR G p.2))⁻¹ ≤
        ((degR G p.1)⁻¹ + (degR G p.2)⁻¹) / 2 := by
      intro p hp
      obtain ⟨h1, h2⟩ := hdeg_pos p hp
      rw [Real.sqrt_mul h1.le, mul_inv]
      have hsq : 0 ≤ ((Real.sqrt (degR G p.1))⁻¹ - (Real.sqrt (degR G p.2))⁻¹) ^ 2 := sq_nonneg _
      have ha2 : ((Real.sqrt (degR G p.1))⁻¹) ^ 2 = (degR G p.1)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt h1.le]
      have hb2 : ((Real.sqrt (degR G p.2))⁻¹) ^ 2 = (degR G p.2)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt h2.le]
      have hexp : ((Real.sqrt (degR G p.1))⁻¹ - (Real.sqrt (degR G p.2))⁻¹) ^ 2 =
          ((Real.sqrt (degR G p.1))⁻¹) ^ 2 + ((Real.sqrt (degR G p.2))⁻¹) ^ 2 -
          2 * ((Real.sqrt (degR G p.1))⁻¹ * (Real.sqrt (degR G p.2))⁻¹) := by ring
      linarith
    calc Q ≤ ∑ p ∈ E, ((degR G p.1)⁻¹ + (degR G p.2)⁻¹) / 2 := Finset.sum_le_sum hpt
      _ = ((∑ p ∈ E, (degR G p.1)⁻¹) + (∑ p ∈ E, (degR G p.2)⁻¹)) / 2 := by
            simp_rw [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]
      _ ≤ (n + n) / 2 := by linarith
      _ = n := by ring
  -- First Cauchy–Schwarz on E: S² ≤ R * Q
  have hcs1 : S ^ 2 ≤ R * Q := by
    let f : V × V → ℝ := fun p => Real.sqrt (Real.sqrt (degR G p.1 * degR G p.2))
    let g : V × V → ℝ := fun p => (Real.sqrt (Real.sqrt (degR G p.1 * degR G p.2)))⁻¹
    have hraw := sum_mul_sq_le E f g
    have hlhs : ∑ p ∈ E, f p * g p = S := by
      rw [← hS_card]
      calc ∑ p ∈ E, f p * g p = ∑ _p ∈ E, (1 : ℝ) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            obtain ⟨h1, h2⟩ := hdeg_pos p hp
            have hs : 0 < Real.sqrt (degR G p.1 * degR G p.2) :=
              Real.sqrt_pos.mpr (mul_pos h1 h2)
            have hss : Real.sqrt (Real.sqrt (degR G p.1 * degR G p.2)) ≠ 0 :=
              (Real.sqrt_pos.mpr hs).ne'
            exact mul_inv_cancel₀ hss
        _ = (E.card : ℝ) := by simp
    have hrhs1 : ∑ p ∈ E, f p ^ 2 = R :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (Real.sqrt_nonneg _)
    have hrhs2 : ∑ p ∈ E, g p ^ 2 = Q := by
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp [g]
      rw [inv_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    rwa [hlhs, hrhs1, hrhs2] at hraw
  -- Second Cauchy–Schwarz on E: R² ≤ S * T
  have hcs2 : R ^ 2 ≤ S * T := by
    have hraw := sum_mul_sq_le E (fun _ => (1 : ℝ)) (fun p => Real.sqrt (degR G p.1 * degR G p.2))
    have hlhs : ∑ p ∈ E, (1 : ℝ) * Real.sqrt (degR G p.1 * degR G p.2) = R := by simp [R]
    have hrhs1 : ∑ _p ∈ E, (1 : ℝ) ^ 2 = S := by simp [hS_card]
    have hrhs2 : ∑ p ∈ E, (Real.sqrt (degR G p.1 * degR G p.2)) ^ 2 = T :=
      Finset.sum_congr rfl fun p _ =>
        Real.sq_sqrt (mul_nonneg (degR_nonneg G p.1) (degR_nonneg G p.2))
    rwa [hlhs, hrhs1, hrhs2] at hraw
  have hR_nonneg : 0 ≤ R := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hT_nonneg : 0 ≤ T := Finset.sum_nonneg fun p _ =>
    mul_nonneg (degR_nonneg G p.1) (degR_nonneg G p.2)
  have hS_nonneg : 0 ≤ S := by rw [← hS_card]; exact Nat.cast_nonneg _
  have hS2_le : S ^ 2 ≤ R * n := hcs1.trans (mul_le_mul_of_nonneg_left hQ_le hR_nonneg)
  have hS4_le : S * S ^ 3 ≤ S * (n ^ 2 * T) := by
    have hsq : (S ^ 2) ^ 2 ≤ (R * n) ^ 2 := pow_le_pow_left₀ (sq_nonneg S) hS2_le 2
    calc S * S ^ 3 = (S ^ 2) ^ 2 := by ring
      _ ≤ (R * n) ^ 2 := hsq
      _ = n ^ 2 * R ^ 2 := by ring
      _ ≤ n ^ 2 * (S * T) := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg n)
      _ = S * (n ^ 2 * T) := by ring
  have hS3_le : S ^ 3 ≤ n ^ 2 * T := by
    rcases eq_or_lt_of_le hS_nonneg with hS0 | hSpos
    · rw [← hS0]
      simpa using mul_nonneg (sq_nonneg n) hT_nonneg
    · exact le_of_mul_le_mul_left hS4_le hSpos
  rw [hsum, div_pow, ← pow_mul, ge_iff_le]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_div_iff₀ (pow_pos hn_pos 6) (pow_pos hn_pos 4)]
  calc S ^ 3 * n ^ 4
      ≤ (n ^ 2 * T) * n ^ 4 := mul_le_mul_of_nonneg_right hS3_le (pow_nonneg hn_pos.le 4)
    _ = T * n ^ 6 := by ring

/-- Every `2 × 2` bipartite graph `bip22 M` satisfies Sidorenko's inequality. -/
theorem sidorenko_bip22 [Nonempty V] (M : Fin 2 → Fin 2 → Bool) (G : SimpleGraph V) :
    SidorenkoFor (bip22 M) G := by
  have hext : ∀ {A B : Fin 2 → Fin 2 → Bool},
      A 0 0 = B 0 0 → A 0 1 = B 0 1 → A 1 0 = B 1 0 → A 1 1 = B 1 1 → A = B := by
    intro A B h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> assumption
  rcases h00 : M 0 0 <;> rcases h01 : M 0 1 <;> rcases h10 : M 1 0 <;> rcases h11 : M 1 1
  · -- (0, 0, 0, 0) = M0
    rw [hext h00 h01 h10 h11 (B := M0)]; exact sidorenko_M0 G
  · -- (0, 0, 0, 1) -> swapLeft & swapRight of M1
    have hM : M = fun i j => M1 (1 - i) (1 - j) :=
      hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapLeft (fun i j => M1 i (1 - j))) G).mpr
      ((sidorenko_iso (bip22SwapRight M1) G).mpr (sidorenko_M1 G))
  · -- (0, 0, 1, 0) -> swapLeft of M1
    have hM : M = fun i j => M1 (1 - i) j := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapLeft M1) G).mpr (sidorenko_M1 G)
  · -- (0, 0, 1, 1) -> swapLeft of Mstar
    have hM : M = fun i j => Mstar (1 - i) j := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapLeft Mstar) G).mpr (sidorenko_Mstar G)
  · -- (0, 1, 0, 0) -> swapRight of M1
    have hM : M = fun i j => M1 i (1 - j) := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapRight M1) G).mpr (sidorenko_M1 G)
  · -- (0, 1, 0, 1) -> transpose + swapLeft of Mstar
    have hM : M = fun j i => Mstar (1 - i) j := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22Transpose (fun i j => Mstar (1 - i) j)) G).mpr
      ((sidorenko_iso (bip22SwapLeft Mstar) G).mpr (sidorenko_Mstar G))
  · -- (0, 1, 1, 0) -> swapRight of Mmatch
    have hM : M = fun i j => Mmatch i (1 - j) := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapRight Mmatch) G).mpr (sidorenko_Mmatch G)
  · -- (0, 1, 1, 1) -> swapLeft + swapRight of Mp4
    have hM : M = fun i j => Mp4 (1 - i) (1 - j) := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapLeft (fun i j => Mp4 i (1 - j))) G).mpr
      ((sidorenko_iso (bip22SwapRight Mp4) G).mpr (sidorenko_Mp4 G))
  · -- (1, 0, 0, 0) = M1
    rw [hext h00 h01 h10 h11 (B := M1)]; exact sidorenko_M1 G
  · -- (1, 0, 0, 1) = Mmatch
    rw [hext h00 h01 h10 h11 (B := Mmatch)]; exact sidorenko_Mmatch G
  · -- (1, 0, 1, 0) -> transpose of Mstar
    have hM : M = fun j i => Mstar i j := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22Transpose Mstar) G).mpr (sidorenko_Mstar G)
  · -- (1, 0, 1, 1) -> swapLeft of Mp4
    have hM : M = fun i j => Mp4 (1 - i) j := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapLeft Mp4) G).mpr (sidorenko_Mp4 G)
  · -- (1, 1, 0, 0) = Mstar
    rw [hext h00 h01 h10 h11 (B := Mstar)]; exact sidorenko_Mstar G
  · -- (1, 1, 0, 1) -> swapRight of Mp4
    have hM : M = fun i j => Mp4 i (1 - j) := hext h00 h01 h10 h11
    rw [hM]
    exact (sidorenko_iso (bip22SwapRight Mp4) G).mpr (sidorenko_Mp4 G)
  · -- (1, 1, 1, 0) = Mp4
    rw [hext h00 h01 h10 h11 (B := Mp4)]; exact sidorenko_Mp4 G
  · -- (1, 1, 1, 1) = Mc4
    rw [hext h00 h01 h10 h11 (B := Mc4)]; exact sidorenko_Mc4 G

end Bip22

/-- Sidorenko's inequality holds for every bipartite graph with sides at most `2`. -/
theorem challenge_4_r2_proof :
    ∀ {W V : Type*} [Fintype W] [Fintype V] [Nonempty V]
      (H : SimpleGraph W) (G : SimpleGraph V),
      BipartiteBoundedBy H 2 → SidorenkoFor H G := by
  intro W V _ _ _ H G hB
  classical
  obtain ⟨X, Y, hbip, hcov, hX, hY⟩ := hB
  have hX_card : Fintype.card X ≤ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact hX
  have hY_card : Fintype.card Y ≤ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact hY
  let a : ℕ := 2 - Fintype.card X
  let b : ℕ := 2 - Fintype.card Y
  have ha : Fintype.card (X ⊕ Fin a) = 2 := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  have hb : Fintype.card (Y ⊕ Fin b) = 2 := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  let eX : X ⊕ Fin a ≃ Fin 2 := Fintype.equivFinOfCardEq ha
  let eY : Y ⊕ Fin b ≃ Fin 2 := Fintype.equivFinOfCardEq hb
  have hmemY : ∀ w : W, w ∉ X → w ∈ Y := by
    intro w hnx
    have hw : w ∈ X ∪ Y := hcov ▸ Set.mem_univ w
    rcases hw with hwX | hwY
    · exact absurd hwX hnx
    · exact hwY
  let eW : W ≃ X ⊕ Y :=
    { toFun := fun w => if hw : w ∈ X then .inl ⟨w, hw⟩ else .inr ⟨w, hmemY w hw⟩
      invFun := fun s => match s with | .inl x => x.1 | .inr y => y.1
      left_inv := fun w => by dsimp; split_ifs <;> rfl
      right_inv := fun s => match s with
        | .inl ⟨w, hw⟩ => by simp [hw]
        | .inr ⟨w, hw⟩ => by
            have hnx : w ∉ X := Set.disjoint_right.mp hbip.disjoint hw
            simp [hnx] }
  let eMid : (X ⊕ Y) ⊕ (Fin a ⊕ Fin b) ≃ (X ⊕ Fin a) ⊕ (Y ⊕ Fin b) :=
    { toFun := fun s => match s with
        | .inl (.inl x) => .inl (.inl x)
        | .inl (.inr y) => .inr (.inl y)
        | .inr (.inl i) => .inl (.inr i)
        | .inr (.inr j) => .inr (.inr j)
      invFun := fun s => match s with
        | .inl (.inl x) => .inl (.inl x)
        | .inr (.inl y) => .inl (.inr y)
        | .inl (.inr i) => .inr (.inl i)
        | .inr (.inr j) => .inr (.inr j)
      left_inv := fun s => by rcases s with (x | y) | (i | j) <;> rfl
      right_inv := fun s => by rcases s with (x | i) | (y | j) <;> rfl }
  let eTot : W ⊕ (Fin a ⊕ Fin b) ≃ Fin 2 ⊕ Fin 2 :=
    ((Equiv.sumCongr eW (Equiv.refl _)).trans eMid).trans (Equiv.sumCongr eX eY)
  let H' : SimpleGraph (W ⊕ (Fin a ⊕ Fin b)) := H ⊕g (⊥ : SimpleGraph (Fin a ⊕ Fin b))
  have hno_left : ∀ i₁ i₂ : Fin 2, ¬ H'.Adj (eTot.symm (.inl i₁)) (eTot.symm (.inl i₂)) := by
    intro i₁ i₂ hadj
    change H'.Adj ((Equiv.sumCongr eW.symm (Equiv.refl _)) (eMid.symm (.inl (eX.symm i₁))))
      ((Equiv.sumCongr eW.symm (Equiv.refl _)) (eMid.symm (.inl (eX.symm i₂)))) at hadj
    rcases h1 : eX.symm i₁ with ⟨w₁, hw₁⟩ | k₁ <;> rcases h2 : eX.symm i₂ with ⟨w₂, hw₂⟩ | k₂
    · rw [h1, h2] at hadj
      have hadjW : H.Adj w₁ w₂ := hadj
      rcases hbip.mem_of_adj hadjW with ⟨_, hw₂Y⟩ | ⟨hw₁Y, _⟩
      · exact Set.disjoint_left.mp hbip.disjoint hw₂ hw₂Y
      · exact Set.disjoint_left.mp hbip.disjoint hw₁ hw₁Y
    · rw [h1, h2] at hadj
      exact not_adj_sum_inl_inr _ _ hadj
    · rw [h1, h2] at hadj
      exact not_adj_sum_inl_inr _ _ hadj.symm
    · rw [h1, h2] at hadj
      exact hadj
  have hno_right : ∀ j₁ j₂ : Fin 2, ¬ H'.Adj (eTot.symm (.inr j₁)) (eTot.symm (.inr j₂)) := by
    intro j₁ j₂ hadj
    change H'.Adj ((Equiv.sumCongr eW.symm (Equiv.refl _)) (eMid.symm (.inr (eY.symm j₁))))
      ((Equiv.sumCongr eW.symm (Equiv.refl _)) (eMid.symm (.inr (eY.symm j₂)))) at hadj
    rcases h1 : eY.symm j₁ with ⟨w₁, hw₁⟩ | k₁ <;> rcases h2 : eY.symm j₂ with ⟨w₂, hw₂⟩ | k₂
    · rw [h1, h2] at hadj
      have hadjW : H.Adj w₁ w₂ := hadj
      rcases hbip.mem_of_adj hadjW with ⟨hw₁X, _⟩ | ⟨_, hw₂X⟩
      · exact Set.disjoint_left.mp hbip.disjoint hw₁X hw₁
      · exact Set.disjoint_left.mp hbip.disjoint hw₂X hw₂
    · rw [h1, h2] at hadj
      exact not_adj_sum_inl_inr _ _ hadj
    · rw [h1, h2] at hadj
      exact not_adj_sum_inl_inr _ _ hadj.symm
    · rw [h1, h2] at hadj
      exact hadj
  let M : Fin 2 → Fin 2 → Bool := fun i j =>
    decide (H'.Adj (eTot.symm (.inl i)) (eTot.symm (.inr j)))
  let iso : bip22 M ≃g H' :=
    { toEquiv := eTot.symm
      map_rel_iff' := by
        intro u v
        cases u with
        | inl i =>
          cases v with
          | inl i' =>
            simp [bip22, hno_left i i']
          | inr j =>
            simp [bip22, M]
        | inr j =>
          cases v with
          | inl i =>
            simp only [bip22, M, decide_eq_true_eq]
            exact H'.adj_comm _ _
          | inr j' =>
            simp [bip22, hno_right j j'] }
  exact (sidorenko_add_isolates_iff H G).mp
    ((sidorenko_iso iso G).mp (sidorenko_bip22 M G))

end TenChallenges.Challenge04R2

theorem solution : TenChallenges.statement_04 2 :=
  fun H G hB => TenChallenges.Challenge04R2.challenge_4_r2_proof H G hB

#print axioms solution
