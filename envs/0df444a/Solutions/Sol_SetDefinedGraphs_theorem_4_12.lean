-- Prove2me | solution 1 for SetDefinedGraphs.theorem_4_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:51.68627+00:00
-- url     : https://prove2.me/submissions/d6b8006c-7aa0-471f-bdcd-c6551fd05eae

import Mathlib
import Theorems.Thm_SetDefinedGraphs_lemma_4_9
import Theorems.Thm_SetDefinedGraphs_lemma_4_10
import Definitions.Def_SetDefinedGraphs_Functional

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.T412
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

theorem dnf_true {ι : Type} (H : Finset (FullClause ι)) (Q : FullClause ι) :
    dnfFun H Q = true ↔ Q ∈ H := by
  simp [dnfFun]

theorem lfun_mono {d : ℕ} {L : Finset (Fin d)} {U U' : Set (Fin d → ℕ)} (h : IsLFunctional L U)
    (hs : U' ⊆ U) : IsLFunctional L U' := by
  obtain ⟨hL, lam, hlam, φ, hφ⟩ := h
  exact ⟨hL, lam, hlam, φ, fun v hv => hφ v (hs hv)⟩

theorem main {d : ℕ} (F : Finset (FullClause (Fin d))) (hF : IsDiscreteDNF F)
    (hL : ∀ D ∈ F, loopCoords D ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) :
    ∃ part : V → Fin ((d ^ 2 * omega (realisation (dnfFun F) V)) ^ F.card),
      ∀ s, IsIndependent (realisation (dnfFun F) V) {x | part x = s} ∧
        ∀ D ∈ F, IsLFunctional (loopCoords D) {v | ∃ h : v ∈ V, part ⟨v, h⟩ = s} := by
  classical
  haveI : Finite V := hVfin.to_subtype
  set N := d ^ 2 * omega (realisation (dnfFun F) V) with hN
  have hW : ∀ D : ↥F, ∃ W : ℕ → Set (Fin d → ℕ), (∀ n, W n ⊆ V) ∧
      (∀ n, IsLFunctional (loopCoords D.1) (W n)) ∧ ∀ v ∈ V, ∃ n < N, v ∈ W n := by
    intro D
    obtain ⟨U, hU1, hU2, hU3⟩ := lemma_4_9 D.1 (hF D.1 D.2) (loopCoords D.1) rfl (hL D.1 D.2) V
      hVfin hV
    have hle : omega (realisation (dnfFun {D.1}) V) ≤ omega (realisation (dnfFun F) V) :=
      omega_le_of_inj _ _ id Function.injective_id (fun a b h => by
        refine ⟨h.1, ?_⟩
        have h2 := h.2
        rw [dnf_true] at h2 ⊢
        rw [Finset.mem_singleton] at h2
        show eqPattern a.1 b.1 ∈ F
        rw [h2]; exact D.2)
    refine ⟨fun n => if h : n < d ^ 2 * omega (realisation (dnfFun {D.1}) V) then U ⟨n, h⟩ else ∅,
      ?_, ?_, ?_⟩
    · intro n
      by_cases h : n < d ^ 2 * omega (realisation (dnfFun {D.1}) V)
      · simp only [dif_pos h]; exact hU1 _
      · simp only [dif_neg h]; exact Set.empty_subset _
    · intro n
      by_cases h : n < d ^ 2 * omega (realisation (dnfFun {D.1}) V)
      · simp only [dif_pos h]; exact hU3 _
      · simp only [dif_neg h]
        obtain ⟨lam, hlam⟩ : ∃ lam, lam ∉ loopCoords D.1 := by
          by_contra hne
          push_neg at hne
          exact hL D.1 D.2 (Finset.eq_univ_iff_forall.2 hne)
        exact ⟨hL D.1 D.2, lam, hlam, fun _ => 0, fun v hv => hv.elim⟩
    · intro v hv
      have : v ∈ ⋃ k, U k := by rw [hU2]; exact hv
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
      refine ⟨k.val, lt_of_lt_of_le k.2 (Nat.mul_le_mul_left _ hle), ?_⟩
      simp only [dif_pos k.2]
      exact hk
  choose W hW1 hW2 hW3 using hW
  have hc : ∀ (x : V) (D : ↥F), ∃ n : Fin N, x.1 ∈ W D n.val := by
    intro x D
    obtain ⟨n, hn, hx⟩ := hW3 D x.1 x.2
    exact ⟨⟨n, hn⟩, hx⟩
  choose c hc using hc
  let e : (↥F → Fin N) ≃ Fin (N ^ F.card) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun x => e (c x), fun s => ⟨?_, ?_⟩⟩
  · intro a ha b hb hadj
    have hca : c a = e.symm s := by rw [← ha]; simp
    have hcb : c b = e.symm s := by rw [← hb]; simp
    have h2 := hadj.2
    rw [dnf_true] at h2
    have hD := hF _ h2
    have hadj' : (realisation (dnfFun {eqPattern a.1 b.1}) V).Adj a b := by
      refine ⟨hadj.1, ?_⟩
      rw [dnf_true]; simp
    let Dn : ↥F := ⟨eqPattern a.1 b.1, h2⟩
    have hind := lemma_4_10 (eqPattern a.1 b.1) hD (loopCoords (eqPattern a.1 b.1)) rfl V
      (W Dn ((e.symm s) Dn).val) (hW1 _ _) (hW2 Dn _)
    have ha' : a ∈ {x : V | x.1 ∈ W Dn ((e.symm s) Dn).val} := by
      show a.1 ∈ W Dn ((e.symm s) Dn).val
      rw [← hca]; exact hc a Dn
    have hb' : b ∈ {x : V | x.1 ∈ W Dn ((e.symm s) Dn).val} := by
      show b.1 ∈ W Dn ((e.symm s) Dn).val
      rw [← hcb]; exact hc b Dn
    exact hind a ha' b hb' hadj'
  · intro D hD
    refine lfun_mono (hW2 ⟨D, hD⟩ ((e.symm s) ⟨D, hD⟩).val) ?_
    rintro v ⟨hv, hs⟩
    have : c ⟨v, hv⟩ = e.symm s := by rw [← hs]; simp
    have := hc ⟨v, hv⟩ ⟨D, hD⟩
    rw [‹c ⟨v, hv⟩ = e.symm s›] at this
    exact this
end SetDefinedGraphs.Dev.T412
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.T412 in
theorem chk_theorem_4_12 {d : ℕ} (F : Finset (FullClause (Fin d))) (hF : IsDiscreteDNF F)
    (hL : ∀ D ∈ F, loopCoords D ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) :
    ∃ part : V → Fin ((d ^ 2 * omega (realisation (dnfFun F) V)) ^ F.card),
      ∀ s, IsIndependent (realisation (dnfFun F) V) {x | part x = s} ∧
        ∀ D ∈ F, IsLFunctional (loopCoords D) {v | ∃ h : v ∈ V, part ⟨v, h⟩ = s} :=
  main F hF hL V hVfin hV
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_theorem_4_12 := @SetDefinedGraphs.chk_theorem_4_12
