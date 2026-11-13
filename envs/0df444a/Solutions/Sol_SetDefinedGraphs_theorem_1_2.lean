-- Prove2me | solution 1 for SetDefinedGraphs.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:49.826+00:00
-- url     : https://prove2.me/submissions/8ce401d0-8dac-4112-875b-a77343a52a4a

import Mathlib
import Theorems.Thm_SetDefinedGraphs_theorem_4_4
import Theorems.Thm_SetDefinedGraphs_theorem_4_14
import Definitions.Def_FASTournament_induce
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.Thm12
open SetDefinedGraphs

lemma union_comap (c : ℕ) {A B : Type} (GA : Digraph A) (GB : Digraph B) (φ : A → B)
    (hinj : Function.Injective φ) (hadj : ∀ a b, GA.Adj a b ↔ GB.Adj (φ a) (φ b))
    (h : IsUnionOfShiftColorable c GB) : IsUnionOfShiftColorable c GA := by
  obtain ⟨k, hk, H, hH, hGB⟩ := h
  refine ⟨k, hk, fun j => ⟨fun a b => (H j).Adj (φ a) (φ b)⟩, ?_, ?_⟩
  · intro j
    obtain ⟨n, ψ, hψ⟩ := hH j
    exact ⟨n, ψ ∘ φ, fun a b hab => hψ _ _ hab⟩
  · intro a b hab
    rw [hadj, hGB _ _ (fun e => hab (hinj e))]

lemma union_mono {c c' : ℕ} {A : Type} {G : Digraph A} (hc : c ≤ c')
    (h : IsUnionOfShiftColorable c G) : IsUnionOfShiftColorable c' G := by
  obtain ⟨k, hk, H⟩ := h
  exact ⟨k, hk.trans hc, H⟩

lemma union_of_subsingleton (c : ℕ) {A : Type} [Subsingleton A] (G : Digraph A) :
    IsUnionOfShiftColorable c G :=
  ⟨0, Nat.zero_le _, fun j => j.elim0, fun j => j.elim0, fun a b hab => (hab (Subsingleton.elim a b)).elim⟩

lemma omega_pos {W : Type} [Finite W] [Nonempty W] (G : Digraph W) : 1 ≤ omega G := by
  classical
  haveI := Fintype.ofFinite W
  obtain ⟨w⟩ := ‹Nonempty W›
  have := @SimpleGraph.IsClique.card_le_cliqueNum W (SimpleGraph.fromRel G.Adj) _ {w}
    (by simp)
  simpa [omega] using this

lemma omega_induce_le {W : Type} [Finite W] (G : Digraph W) (S : Set W) :
    omega (FASTournament.induce G S) ≤ omega G := by
  classical
  haveI := Fintype.ofFinite W
  obtain ⟨s, hs⟩ := SimpleGraph.exists_isNClique_cliqueNum
    (G := SimpleGraph.fromRel (FASTournament.induce G S).Adj)
  have hcl : (SimpleGraph.fromRel G.Adj).IsClique
      ((s.map (Function.Embedding.subtype _) : Finset W) : Set W) := by
    intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coe_subtype] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun e => hxy (by rw [e])
    have := hs.isClique hx' hy' hne
    simp only [SimpleGraph.fromRel_adj] at this ⊢
    refine ⟨hxy, ?_⟩
    rcases this.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h2 := @SimpleGraph.IsClique.card_le_cliqueNum W (SimpleGraph.fromRel G.Adj) _
    (s.map (Function.Embedding.subtype _)) hcl
  rw [Finset.card_map, hs.card_eq] at h2
  exact h2

lemma part_lemma (d n : ℕ) (hn : n ≤ d) (F : Finset (FullClause (Fin n))) (hF : IsInjectiveDNF F)
    {U : Type} [Finite U] (G' : Digraph U) (hG : InY (dnfFun F) G') :
    ∃ q : U → ℕ, (∀ u, q u < ((d + 1) ^ 2 * omega G') ^ (2 ^ (d ^ 2))) ∧
      ∀ j : ℕ, IsUnionOfShiftColorable (2 ^ (d ^ 2)) (FASTournament.induce G' {u | q u = j}) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    obtain ⟨V, hV, -, -, ⟨e, -⟩⟩ := hG
    haveI : Subsingleton U := e.subsingleton
    refine ⟨fun _ => 0, fun u => ?_, fun j => union_of_subsingleton _ _⟩
    haveI : Nonempty U := ⟨u⟩
    have := omega_pos G'
    apply pow_pos
    exact Nat.mul_pos (by positivity) this
  · obtain ⟨part, hp⟩ := theorem_4_14 hpos F hF G' hG
    refine ⟨fun u => (part u : ℕ), fun u => ?_, fun j => ?_⟩
    · haveI : Nonempty U := ⟨u⟩
      have hω := omega_pos G'
      have hb : 0 < n ^ 2 * omega G' := Nat.mul_pos (by positivity) hω
      calc (part u : ℕ) < (n ^ 2 * omega G') ^ (2 ^ (n ^ 2)) := (part u).2
        _ ≤ ((d + 1) ^ 2 * omega G') ^ (2 ^ (n ^ 2)) := by
          apply Nat.pow_le_pow_left
          apply Nat.mul_le_mul_right
          exact Nat.pow_le_pow_left (by omega) 2
        _ ≤ ((d + 1) ^ 2 * omega G') ^ (2 ^ (d ^ 2)) := by
          apply Nat.pow_le_pow_right (Nat.mul_pos (by positivity) hω)
          exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left hn 2)
    · by_cases hj : j < (n ^ 2 * omega G') ^ (2 ^ (n ^ 2))
      · refine union_mono (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left hn 2)) ?_
        refine union_comap _ _ _ (fun a => ⟨a.1, Fin.ext a.2⟩) ?_ (fun a b => Iff.rfl) (hp ⟨j, hj⟩)
        intro a b hab
        exact Subtype.ext (congrArg (fun x : ↥{v : U | part v = ⟨j, hj⟩} => (x : U)) hab)
      · haveI : IsEmpty ↥{u : U | (part u : ℕ) = j} :=
          ⟨fun a => hj (a.2 ▸ (part a.1).2)⟩
        haveI : Subsingleton ↥{u : U | (part u : ℕ) = j} := inferInstance
        exact union_of_subsingleton _ _

lemma finite_of_inX {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) {W : Type} (G : Digraph W)
    (h : InX f G) : Finite W := by
  obtain ⟨V, hV, ⟨e, -⟩⟩ := h
  haveI : Finite ↥V := hV.to_subtype
  exact Finite.of_equiv _ e.symm

end SetDefinedGraphs.Dev.Thm12

namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.Thm12 in
theorem chk_theorem_1_2 (d : ℕ) (f : (Fin d → Fin d → Bool) → Bool) :
    ∃ c : ℕ, ∃ τ : Polynomial ℕ, ∀ {W : Type} (G : Digraph W), InX f G →
      ∃ part : W → Fin (τ.eval (omega G)),
        ∀ i, IsUnionOfShiftColorable c (FASTournament.induce G {v | part v = i}) := by
  obtain ⟨r, hr, d', hd', H, hH, hpart, -⟩ := theorem_4_4 f
  set E : ℕ := 2 ^ (d ^ 2) with hE
  set m : ℕ := (d + 1) ^ 2 with hm
  refine ⟨2 ^ (d ^ 2), Polynomial.C (r * m ^ E) * Polynomial.X ^ E, ?_⟩
  intro W G hG
  haveI := finite_of_inX f G hG
  obtain ⟨p, hp⟩ := hpart G hG
  have hq : ∀ i : Fin r, ∃ q : ↥{v | p v = i} → ℕ,
      (∀ u, q u < (m * omega (FASTournament.induce G {v | p v = i})) ^ E) ∧
      ∀ j : ℕ, IsUnionOfShiftColorable (2 ^ (d ^ 2))
        (FASTournament.induce (FASTournament.induce G {v | p v = i}) {u | q u = j}) :=
    fun i => part_lemma d (d' i) (hd' i) (H i) (hH i) _ (hp i)
  choose q hq1 hq2 using hq
  let Qw : W → ℕ := fun w => q (p w) ⟨w, rfl⟩
  have hQw : ∀ (i : Fin r) (v : W) (h : p v = i), Qw v = q i ⟨v, h⟩ := by
    intro i v h; subst h; rfl
  have hQb : ∀ w, Qw w < (m * omega G) ^ E := fun w =>
    (hq1 (p w) ⟨w, rfl⟩).trans_le (Nat.pow_le_pow_left
      (Nat.mul_le_mul_left _ (omega_induce_le G _)) _)
  have hle : r * (m * omega G) ^ E ≤ (Polynomial.C (r * m ^ E) * Polynomial.X ^ E).eval (omega G) := by
    simp [mul_pow, mul_assoc]
  let enc : W → Fin (r * (m * omega G) ^ E) := fun w =>
    finProdFinEquiv (p w, ⟨Qw w, hQb w⟩)
  have henc : ∀ v w, enc v = enc w → p v = p w ∧ Qw v = Qw w := by
    intro v w h
    have := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at this
    exact this
  refine ⟨fun w => Fin.castLE hle (enc w), fun t => ?_⟩
  by_cases hne : ∃ w0, Fin.castLE hle (enc w0) = t
  · obtain ⟨w0, hw0⟩ := hne
    subst hw0
    have key : ∀ v : W, Fin.castLE hle (enc v) = Fin.castLE hle (enc w0) →
        ∃ h : p v = p w0, q (p w0) ⟨v, h⟩ = Qw w0 := by
      intro v hv
      have := henc v w0 (Fin.castLE_injective hle hv)
      refine ⟨this.1, ?_⟩
      rw [← hQw _ v this.1]
      exact this.2
    have hU := hq2 (p w0) (Qw w0)
    refine union_comap _ _ _ (fun a => ⟨⟨a.1, (key a.1 a.2).1⟩, (key a.1 a.2).2⟩) ?_ ?_ hU
    · intro a b hab
      apply Subtype.ext
      have := congrArg (fun x => x.1.1) hab
      exact this
    · intro a b; exact Iff.rfl
  · push_neg at hne
    haveI : IsEmpty ↥{v : W | Fin.castLE hle (enc v) = t} := ⟨fun a => hne a.1 a.2⟩
    exact union_of_subsingleton _ _
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_theorem_1_2 := @SetDefinedGraphs.chk_theorem_1_2
