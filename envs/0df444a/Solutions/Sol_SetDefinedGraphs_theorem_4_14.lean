-- Prove2me | solution 1 for SetDefinedGraphs.theorem_4_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:51.229765+00:00
-- url     : https://prove2.me/submissions/677ebfd3-eaac-4064-8df9-0b4fbdb13cdc

import Mathlib
import Definitions.Def_FASTournament_induce
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_ShiftDigraph
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Theorems.Thm_SetDefinedGraphs_theorem_4_12
import Theorems.Thm_SetDefinedGraphs_lemma_4_13
import Theorems.Thm_SetDefinedGraphs_lemma_4_5

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.T414
open SetDefinedGraphs

theorem omega_mono {W1 W2 : Type} [Finite W2] (G1 : Digraph W1) (G2 : Digraph W2) (f : W1 → W2)
    (hf : Function.Injective f) (h : ∀ a b, G1.Adj a b → G2.Adj (f a) (f b)) :
    omega G1 ≤ omega G2 := by
  classical
  obtain ⟨s, hs⟩ := (SimpleGraph.fromRel G1.Adj).exists_isNClique_cliqueNum
  have hc : (SimpleGraph.fromRel G2.Adj).IsClique ((s.map ⟨f, hf⟩ : Finset W2) : Set W2) := by
    intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (h ▸ rfl)
    have := hs.isClique ha hb hab
    rw [SimpleGraph.fromRel_adj] at this ⊢
    refine ⟨hxy, ?_⟩
    rcases this.2 with h1 | h1
    · exact Or.inl (h _ _ h1)
    · exact Or.inr (h _ _ h1)
  have h2 := SimpleGraph.IsClique.card_le_cliqueNum (G := SimpleGraph.fromRel G2.Adj)
    (t := s.map ⟨f, hf⟩) (tc := hc)
  rw [Finset.card_map, hs.card_eq] at h2
  exact h2

theorem omega_pos {W : Type} [Finite W] [Nonempty W] (G : Digraph W) : 1 ≤ omega G := by
  classical
  obtain ⟨w⟩ := ‹Nonempty W›
  have hc : (SimpleGraph.fromRel G.Adj).IsClique (({w} : Finset W) : Set W) := by
    simp
  have h2 := SimpleGraph.IsClique.card_le_cliqueNum (G := SimpleGraph.fromRel G.Adj)
    (t := {w}) (tc := hc)
  unfold omega
  simpa using h2

theorem union_transfer {c : ℕ} {U U' : Type} (G : Digraph U) (G' : Digraph U') (e : U' ≃ U)
    (he : ∀ a b, G'.Adj a b ↔ G.Adj (e a) (e b)) (h : IsUnionOfShiftColorable c G) :
    IsUnionOfShiftColorable c G' := by
  obtain ⟨k, hk, H, hH, hG⟩ := h
  refine ⟨k, hk, fun j => ⟨fun a b => (H j).Adj (e a) (e b)⟩, ?_, ?_⟩
  · intro j
    obtain ⟨n, φ, hφ⟩ := hH j
    exact ⟨n, φ ∘ e, fun a b hab => hφ _ _ hab⟩
  · intro a b hab
    rw [he]
    exact hG (e a) (e b) (e.injective.ne hab)

theorem induce_InY {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) (V : Set (Fin d → ℕ))
    (hfin : V.Finite) (hinj : IsInjectiveSet V) (hou : IsOrderUniform V) (S : Set V) :
    InY f (FASTournament.induce (realisation f V) S) := by
  refine ⟨Subtype.val '' S, hfin.subset (by rintro _ ⟨x, _, rfl⟩; exact x.2),
    fun v hv => hinj v (by obtain ⟨x, _, rfl⟩ := hv; exact x.2),
    fun u hu w hw => hou u (by obtain ⟨x, _, rfl⟩ := hu; exact x.2) w
      (by obtain ⟨x, _, rfl⟩ := hw; exact x.2),
    Equiv.Set.image Subtype.val S Subtype.val_injective, ?_⟩
  intro a b
  simp [realisation, FASTournament.induce, Subtype.ext_iff]

theorem dnf_true {d : ℕ} (F : Finset (FullClause (Fin d))) (Q : FullClause (Fin d)) :
    dnfFun F Q = true ↔ Q ∈ F := by
  classical
  simp [dnfFun]

theorem no_cyclic {d : ℕ} (C : FullClause (Fin d)) (hC : IsCyclicClause C)
    (V : Set (Fin d → ℕ)) (hfin : V.Finite) (hinj : IsInjectiveSet V) (hou : IsOrderUniform V)
    (u w : V) (hne : u ≠ w) (h : eqPattern u.1 w.1 = C) : False := by
  let V' : Set (Fin d → ℕ) := {u.1, w.1}
  have hsub : V' ⊆ V := by
    intro x hx
    rcases hx with rfl | rfl
    · exact u.2
    · exact w.2
  have hG : InY (dnfFun {C}) (realisation (dnfFun {C}) V') :=
    ⟨V', Set.toFinite _, fun v hv => hinj v (hsub hv), fun a ha b hb => hou a (hsub ha) b (hsub hb),
      Equiv.refl _, fun a b => Iff.rfl⟩
  refine lemma_4_5 C hC _ hG ⟨u.1, Or.inl rfl⟩ ⟨w.1, Or.inr rfl⟩ ⟨?_, ?_⟩
  · intro h'
    have h3 : u.1 = w.1 := by simpa using congrArg Subtype.val h'
    exact hne (Subtype.ext h3)
  · rw [dnf_true, h]; simp

theorem card_le {d : ℕ} (F : Finset (FullClause (Fin d))) : F.card ≤ 2 ^ (d ^ 2) := by
  have h := Finset.card_le_univ F
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  rw [pow_two]
  have : (2 ^ d) ^ d = 2 ^ (d * d) := (pow_mul 2 d d).symm
  omega

open Classical in
theorem main_union {d : ℕ} (F : Finset (FullClause (Fin d))) (hF : IsInjectiveDNF F)
    (V : Set (Fin d → ℕ)) (hfin : V.Finite) (hinj : IsInjectiveSet V) (hou : IsOrderUniform V)
    (S : Set V)
    (hS : ∀ a ∈ S, ∀ b ∈ S, ¬ (realisation (dnfFun (F.filter fun D =>
      IsDiscreteClause D ∧ loopCoords D ≠ Finset.univ)) V).Adj a b) :
    IsUnionOfShiftColorable (2 ^ (d ^ 2)) (FASTournament.induce (realisation (dnfFun F) V) S) := by
  classical
  set Fp := F.filter IsPathClause with hFp
  set Fd := F.filter (fun D => IsDiscreteClause D ∧ loopCoords D ≠ Finset.univ) with hFd
  have arc : ∀ u w : V, (realisation (dnfFun F) V).Adj u w →
      (∃ P ∈ Fp, (realisation (dnfFun {P}) V).Adj u w) ∨ (realisation (dnfFun Fd) V).Adj u w := by
    intro u w huw
    obtain ⟨hne, hmem⟩ := huw
    rw [dnf_true] at hmem
    have hinjC := hF _ hmem
    by_cases cyc : IsCyclicClause (eqPattern u.1 w.1)
    · exact (no_cyclic _ cyc V hfin hinj hou u w hne rfl).elim
    · by_cases hex : ∃ i j, i ≠ j ∧ eqPattern u.1 w.1 i j = true
      · left
        refine ⟨_, Finset.mem_filter.2 ⟨hmem, hinjC, cyc, hex⟩, hne, ?_⟩
        rw [dnf_true]; simp
      · right
        have hdisc : IsDiscreteClause (eqPattern u.1 w.1) := by
          refine ⟨hinjC, fun i j hij => ?_⟩
          by_contra hij'
          exact hex ⟨i, j, hij', hij⟩
        refine ⟨hne, ?_⟩
        rw [dnf_true]
        refine Finset.mem_filter.2 ⟨hmem, hdisc, fun hl => hne ?_⟩
        apply Subtype.ext
        funext i
        have hi : i ∈ loopCoords (eqPattern u.1 w.1) := by rw [hl]; exact Finset.mem_univ i
        have := (by simpa [loopCoords] using hi : eqPattern u.1 w.1 i i = true)
        simpa [eqPattern] using this
  have back : ∀ P ∈ Fp, ∀ u w : V, (realisation (dnfFun {P}) V).Adj u w →
      (realisation (dnfFun F) V).Adj u w := by
    intro P hP u w h
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [dnf_true, Finset.mem_singleton] at h2
    rw [dnf_true, h2]
    exact (Finset.mem_filter.1 hP).1
  let e0 := Fp.equivFin
  refine ⟨Fp.card, (Finset.card_filter_le _ _).trans (card_le F),
    fun j => FASTournament.induce (realisation (dnfFun {(e0.symm j).1}) V) S, ?_, ?_⟩
  · intro j
    have hP := (Finset.mem_filter.1 (e0.symm j).2).2
    exact (lemma_4_13 _ hP _ (induce_InY _ V hfin hinj hou S)).1
  · intro a b hab
    constructor
    · intro h
      rcases arc a.1 b.1 h with ⟨P, hP, hadj⟩ | hd
      · refine ⟨e0 ⟨P, hP⟩, ?_⟩
        simpa [FASTournament.induce] using hadj
      · exact (hS a.1 a.2 b.1 b.2 hd).elim
    · rintro ⟨j, hj⟩
      exact back _ (e0.symm j).2 _ _ hj

open Classical in
theorem main {d : ℕ} (hd : 1 ≤ d) (F : Finset (FullClause (Fin d))) (hF : IsInjectiveDNF F)
    {W : Type} (G : Digraph W) (hG : InY (dnfFun F) G) :
    ∃ part : W → Fin ((d ^ 2 * omega G) ^ (2 ^ (d ^ 2))),
      ∀ i, IsUnionOfShiftColorable (2 ^ (d ^ 2)) (FASTournament.induce G {v | part v = i}) := by
  classical
  obtain ⟨V, hVfin, hVinj, hVou, e, he⟩ := hG
  rcases isEmpty_or_nonempty W with hW | hW
  · refine ⟨fun w => (IsEmpty.false w).elim, fun i => ?_⟩
    exact ⟨0, Nat.zero_le _, fun j => j.elim0, fun j => j.elim0,
      fun a _ _ => (IsEmpty.false a.1).elim⟩
  set Fd := F.filter (fun D => IsDiscreteClause D ∧ loopCoords D ≠ Finset.univ) with hFd
  obtain ⟨part0, hpart0⟩ := theorem_4_12 Fd
    (fun D hD => (Finset.mem_filter.1 hD).2.1) (fun D hD => (Finset.mem_filter.1 hD).2.2)
    V hVfin hVinj
  haveI : Finite V := hVfin.to_subtype
  haveI : Finite W := Finite.of_equiv V e.symm
  have hpos : 1 ≤ omega G := omega_pos G
  have hle : omega (realisation (dnfFun F) V) ≤ omega G :=
    omega_mono _ G e.symm e.symm.injective (fun a b h => by
      have := (he (e.symm a) (e.symm b)).2 (by simpa using h)
      exact this)
  have hd2 : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
  have hB : 0 < d ^ 2 * omega G := Nat.mul_pos hd2 hpos
  have hMN : (d ^ 2 * omega (realisation (dnfFun Fd) V)) ^ Fd.card ≤
      (d ^ 2 * omega G) ^ (2 ^ (d ^ 2)) := by
    have h1 : omega (realisation (dnfFun Fd) V) ≤ omega G := by
      refine le_trans (omega_mono _ (realisation (dnfFun F) V) id Function.injective_id ?_) hle
      intro a b h
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [dnf_true] at h2 ⊢
      exact (Finset.mem_filter.1 h2).1
    calc _ ≤ (d ^ 2 * omega G) ^ Fd.card :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h1) _
      _ ≤ _ := Nat.pow_le_pow_right hB ((Finset.card_filter_le _ _).trans (card_le F))
  refine ⟨fun w => Fin.castLE hMN (part0 (e w)), fun i => ?_⟩
  refine union_transfer (FASTournament.induce (realisation (dnfFun F) V)
    {u : V | Fin.castLE hMN (part0 u) = i}) _
    (Equiv.subtypeEquiv e (fun v => Iff.rfl)) (fun a b => he a.1 b.1) ?_
  refine main_union F hF V hVfin hVinj hVou _ ?_
  intro a ha b hb
  have hab : part0 a = part0 b := by
    apply Fin.ext
    have := congrArg Fin.val (ha.trans hb.symm)
    simpa using this
  exact (hpart0 (part0 a)).1 a rfl b hab.symm

end SetDefinedGraphs.Dev.T414
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.T414 in
theorem chk_theorem_4_14 {d : ℕ} (hd : 1 ≤ d) (F : Finset (FullClause (Fin d))) (hF : IsInjectiveDNF F)
    {W : Type} (G : Digraph W) (hG : InY (dnfFun F) G) :
    ∃ part : W → Fin ((d ^ 2 * omega G) ^ (2 ^ (d ^ 2))),
      ∀ i, IsUnionOfShiftColorable (2 ^ (d ^ 2)) (FASTournament.induce G {v | part v = i}) :=
  main hd F hF G hG
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_theorem_4_14 := @SetDefinedGraphs.chk_theorem_4_14
