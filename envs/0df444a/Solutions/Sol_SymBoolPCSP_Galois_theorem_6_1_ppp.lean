-- Prove2me | solution 1 for SymBoolPCSP.Galois.theorem_6_1_ppp
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T12:12:29.696329+00:00
-- url     : https://prove2.me/submissions/f251fa3a-0f3b-4baf-8bc3-0bde943cfc8c

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Definitions.Def_SymBoolPCSP_Galois_Basic

open PCSPBLPAff.Symmetric
open SymBoolPCSP.Galois

/-
The canonical gadget has one auxiliary variable for every column in D^m,
where the m rows enumerate the strong target relation. Its relational clauses
express that an assignment to those variables is a polymorphism. Equality
clauses identify the k free variables with their corresponding columns.
The construction includes m = 0 and requires no nonempty-domain assumption.
-/
theorem solution {τ τ' : Type} [Fintype τ] {ar : τ → ℕ} {ar' : τ' → ℕ}
    {D : Type} [Fintype D] [DecidableEq D]
    (𝔸 𝔹 : RelStruct τ ar D) (𝔸' 𝔹' : RelStruct τ' ar' D)
    (_hΓ : IsPromiseFamily 𝔸 𝔹) (_hΓ' : IsPromiseFamily 𝔸' 𝔹')
    (hPol : PolSubset 𝔸 𝔹 𝔸' 𝔹') :
    ∀ R' : τ', PPPDefinable 𝔸 𝔹 (𝔸'.rel R') (𝔹'.rel R') := by
  classical
  intro R'
  let k := ar' R'
  let : Fintype (𝔸'.rel R') := Fintype.ofFinite _
  let m := Fintype.card (𝔸'.rel R')
  let rows : Fin m ≃ 𝔸'.rel R' := (Fintype.equivFin (𝔸'.rel R')).symm
  let x : Fin m → Fin k → D := fun j => (rows j).val
  let V := Fin m → D
  let N := Fintype.card V
  let columns : Fin N ≃ V := (Fintype.equivFin V).symm
  let : ∀ R : τ, Fintype (𝔸.rel R) := fun R => Fintype.ofFinite _
  let C := (Σ R : τ, Fin m → 𝔸.rel R) ⊕ Fin k
  let clauses : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  let sym : C → τ ⊕ Unit := fun c =>
    match c with
    | .inl p => .inl p.1
    | .inr _ => .inr ()
  let scope : (c : C) → Fin (arEq ar (sym c)) → Fin (k + N) := fun c =>
    match c with
    | .inl ⟨R, M⟩ => fun i => Fin.natAdd k (columns.symm (fun j => (M j).val i))
    | .inr i => fun (b : Fin 2) => if b = 0 then Fin.castAdd N i
        else Fin.natAdd k (columns.symm (fun j => x j i))
  let Ψ : Instance (τ ⊕ Unit) (arEq ar) :=
    { n := k + N
      m := Fintype.card C
      sym := fun j => sym (clauses j)
      scope := fun j => scope (clauses j) }
  refine ⟨N, Ψ, rfl, ?_, ?_⟩
  · intro t ht
    let r : Fin m := rows.symm ⟨t, ht⟩
    have hr : x r = t := by
      change (rows (rows.symm ⟨t, ht⟩)).val = t
      simp
    refine ⟨fun a => columns a r, ?_⟩
    intro j
    change (Fin.append t (fun a => columns a r)) ∘ scope (clauses j) ∈
      (withEqual 𝔸).rel (sym (clauses j))
    generalize hc : clauses j = c
    cases c with
    | inl p =>
      rcases p with ⟨R, M⟩
      change (fun i : Fin (ar R) => Fin.append t (fun a => columns a r)
        (Fin.natAdd k (columns.symm (fun j => (M j).val i)))) ∈ 𝔸.rel R
      simpa only [k, Fin.append_right, columns.apply_symm_apply] using (M r).property
    | inr i =>
      change Fin.append t (fun a => columns a r)
        (if (0 : Fin 2) = 0 then Fin.castAdd N i else
          Fin.natAdd k (columns.symm (fun j => x j i))) =
        Fin.append t (fun a => columns a r)
        (if (1 : Fin 2) = 0 then Fin.castAdd N i else
          Fin.natAdd k (columns.symm (fun j => x j i)))
      simp only [ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0),
        k, Fin.append_left, Fin.append_right, columns.apply_symm_apply, hr]
  · intro z hz
    let f : (Fin m → D) → D := fun a => z (Fin.natAdd k (columns.symm a))
    have hf : IsPolymorphism 𝔸 𝔹 f := by
      intro R M hM
      let c : C := .inl ⟨R, fun j => ⟨M j, hM j⟩⟩
      have hc := hz (clauses.symm c)
      change z ∘ scope (clauses (clauses.symm c)) ∈
        (withEqual 𝔹).rel (sym (clauses (clauses.symm c))) at hc
      rw [clauses.apply_symm_apply] at hc
      change (fun i => z (Fin.natAdd k (columns.symm (fun j => M j i)))) ∈ 𝔹.rel R at hc
      exact hc
    have hout := hPol m f hf R' x (fun j => (rows j).property)
    have heq : (fun i : Fin k => z (Fin.castAdd N i)) = fun i => f (fun j => x j i) := by
      funext i
      have hc := hz (clauses.symm (.inr i))
      change z ∘ scope (clauses (clauses.symm (.inr i))) ∈
        (withEqual 𝔹).rel (sym (clauses (clauses.symm (.inr i)))) at hc
      rw [clauses.apply_symm_apply] at hc
      change z (if (0 : Fin 2) = 0 then Fin.castAdd N i else
        Fin.natAdd k (columns.symm (fun j => x j i))) =
        z (if (1 : Fin 2) = 0 then Fin.castAdd N i else
        Fin.natAdd k (columns.symm (fun j => x j i))) at hc
      simpa only [ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0), f] using hc
    change (fun i : Fin k => z (Fin.castAdd N i)) ∈ 𝔹'.rel R'
    rw [heq]
    exact hout

#print axioms solution
