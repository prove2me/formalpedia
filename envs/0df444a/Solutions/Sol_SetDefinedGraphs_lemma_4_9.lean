-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.771191+00:00
-- url     : https://prove2.me/submissions/a6c8dfe0-84b3-49f5-84bd-009a9eb8599a

import Mathlib
import Theorems.Thm_SetDefinedGraphs_lemma_4_8
import Definitions.Def_SetDefinedGraphs_Functional

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.L49
open SetDefinedGraphs

theorem omega_le_of_inj {W W' : Type} (G : Digraph W) (G' : Digraph W') [Finite W'] (φ : W → W')
    (hφ : Function.Injective φ) (h : ∀ a b, G.Adj a b → G'.Adj (φ a) (φ b)) :
    omega G ≤ omega G' := by
  classical
  haveI : Finite W := Finite.of_injective φ hφ
  obtain ⟨K, hK⟩ := (SimpleGraph.fromRel G.Adj).exists_isNClique_cliqueNum
  have hcl : (SimpleGraph.fromRel G'.Adj).IsClique ((K.map ⟨φ, hφ⟩ : Finset W') : Set W') := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun e => hxy (by rw [e])
    have := hK.isClique ha hb hab
    rw [SimpleGraph.fromRel_adj] at this ⊢
    refine ⟨hxy, ?_⟩
    rcases this.2 with h1 | h1
    · exact Or.inl (h _ _ h1)
    · exact Or.inr (h _ _ h1)
  have := hcl.card_le_cliqueNum
  rw [Finset.card_map] at this
  show (SimpleGraph.fromRel G.Adj).cliqueNum ≤ _
  rw [← hK.card_eq]
  exact this

theorem main {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) :
    ∃ U : Fin (d ^ 2 * omega (realisation (dnfFun {D}) V)) → Set (Fin d → ℕ),
      (∀ k, U k ⊆ V) ∧ (⋃ k, U k) = V ∧ ∀ k, IsLFunctional L (U k) := by
  classical
  haveI : Finite V := hVfin.to_subtype
  set N := d ^ 2 * omega (realisation (dnfFun {D}) V) with hN
  set m := Lᶜ.card with hm
  have hmpos : 0 < m := by
    apply Finset.card_pos.2
    by_contra hne
    apply hL
    ext i
    simp only [Finset.not_nonempty_iff_eq_empty] at hne
    simpa using Finset.eq_empty_iff_forall_notMem.1 hne i
  have hmd : m ≤ d := by simpa using Finset.card_le_univ (Lᶜ)
  obtain ⟨lamOf, hlam1, hlam2⟩ : ∃ lamOf : ℕ → Fin d, (∀ t < m, lamOf t ∉ L) ∧
      ∀ i ∉ L, ∃ t < m, lamOf t = i := by
    let e : Fin m ≃ (Lᶜ : Finset (Fin d)) := (Lᶜ).equivFin.symm
    refine ⟨fun t => if h : t < m then (e ⟨t, h⟩).1 else ⟨0, by omega⟩, ?_, ?_⟩
    · intro t ht
      dsimp only
      rw [dif_pos ht]
      exact Finset.mem_compl.1 (e ⟨t, ht⟩).2
    · intro i hi
      refine ⟨(e.symm ⟨i, by simpa using hi⟩).1, (e.symm ⟨i, by simpa using hi⟩).2, ?_⟩
      dsimp only
      rw [dif_pos (e.symm ⟨i, by simpa using hi⟩).2]
      simp
  have hRex : ∀ a : L → ℕ, ∃ R : Finset ℕ, m * R.card ≤ N ∧
      ∀ v ∈ sliceSet V L a, ∃ i ∉ L, v i ∈ R := by
    intro a
    by_cases ha : Function.Injective a
    · obtain ⟨R, -, hR2, hR3⟩ := lemma_4_8 D hD L hLD hL V hVfin hV a ha
      refine ⟨R, ?_, ?_⟩
      · refine hR2.trans (Nat.mul_le_mul_left _ ?_)
        have hS : sliceSet V L a ⊆ V := fun v hv => hv.1
        haveI : Finite (sliceSet V L a) := (hVfin.subset hS).to_subtype
        exact omega_le_of_inj _ _ (Set.inclusion hS) (Set.inclusion_injective hS)
          (fun x y h => ⟨fun e => h.1 (Set.inclusion_injective hS e), h.2⟩)
      · intro v hv
        have hv' : v ∈ ⋃ i ∈ Lᶜ, ⋃ r ∈ R, {v | v ∈ sliceSet V L a ∧ v i = r} := hR3 ▸ hv
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hv'
        obtain ⟨i, hi, r, hr, -, e⟩ := hv'
        exact ⟨i, by simpa using hi, e ▸ hr⟩
    · refine ⟨∅, by simp, ?_⟩
      intro v hv
      exfalso
      apply ha
      intro i j hij
      have h1 := hv.2 i
      have h2 := hv.2 j
      have : v i.1 = v j.1 := h1.trans (hij.trans h2.symm)
      exact Subtype.ext (hV v hv.1 this)
  choose R hRN hRcov using hRex
  have hrf : ∀ R : Finset ℕ, ∃ rf : ℕ → ℕ, ∀ r ∈ R, ∃ j < R.card, rf j = r := by
    intro R
    refine ⟨fun j => if h : j < R.card then (R.orderEmbOfFin rfl ⟨j, h⟩) else 0, ?_⟩
    intro r hr
    have : r ∈ Set.range (R.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hr
    obtain ⟨⟨j, hj⟩, hjr⟩ := this
    exact ⟨j, hj, by simp [hj, hjr]⟩
  choose rf hrf using hrf
  let restr : (Fin d → ℕ) → (L → ℕ) := fun v i => v i.1
  refine ⟨fun k => {v | v ∈ V ∧ v (lamOf (k.val % m)) = rf (R (restr v)) (k.val / m)}, ?_, ?_, ?_⟩
  · intro k v hv; exact hv.1
  · apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hv
      exact hk.1
    · intro v hv
      have hvs : v ∈ sliceSet V L (restr v) := ⟨hv, fun i => rfl⟩
      obtain ⟨i, hi, hiR⟩ := hRcov (restr v) v hvs
      obtain ⟨t, ht, hti⟩ := hlam2 i hi
      obtain ⟨j, hj, hjr⟩ := hrf (R (restr v)) _ hiR
      have hk : t + m * j < N := by
        have : m * (j + 1) ≤ m * (R (restr v)).card := Nat.mul_le_mul_left _ hj
        have := hRN (restr v)
        nlinarith
      refine Set.mem_iUnion.2 ⟨⟨t + m * j, hk⟩, hv, ?_⟩
      have e1 : (t + m * j) % m = t := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
      have e2 : (t + m * j) / m = j := by
        rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt ht, zero_add]
      show v (lamOf ((t + m * j) % m)) = rf (R (restr v)) ((t + m * j) / m)
      rw [e1, e2, hti, hjr]
  · intro k
    have hlt : k.val % m < m := Nat.mod_lt _ hmpos
    refine ⟨hL, lamOf (k.val % m), hlam1 _ hlt, fun a => rf (R a) (k.val / m), ?_⟩
    intro v hv
    exact hv.2
end SetDefinedGraphs.Dev.L49
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.L49 in
theorem chk_lemma_4_9 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) :
    ∃ U : Fin (d ^ 2 * omega (realisation (dnfFun {D}) V)) → Set (Fin d → ℕ),
      (∀ k, U k ⊆ V) ∧ (⋃ k, U k) = V ∧ ∀ k, IsLFunctional L (U k) :=
  main D hD L hLD hL V hVfin hV
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_9 := @SetDefinedGraphs.chk_lemma_4_9
