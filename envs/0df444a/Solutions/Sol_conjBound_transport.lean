-- Prove2me | solution 1 for conjBound_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:17:27.506174+00:00
-- url     : https://prove2.me/submissions/59987073-804d-4e4c-bf7a-1451069e5dc0

import Mathlib

section
-- module Solutions.OAIQ093_PR.Unipotent_FG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite generation of subgroups

That subgroups of finitely generated abelian and nilpotent groups are finitely generated, plus
the supporting transfer lemmas along homomorphisms.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)


/-- Compare cardinalities of two images of the same underlying products, pushed through a
homomorphism `ψ` and through an injective homomorphism `j`.  Used to move a bound proved in
`↥N'` across to the quotient `↥(Subgroup.center ↥N') ⧸ torsion`. -/
theorem card_image_listProd_hom_le {C Q N ι : Type*}
    [Group C] [Group Q] [Group N] [DecidableEq Q] [DecidableEq N]
    (ψ : C →* Q) (j : C →* N) (hj : Function.Injective j)
    (P : Finset (Finset ι)) (f : ι → C) :
    (P.image (fun x => (List.map (fun i => ψ (f i)) x.toList).prod)).card
      ≤ (P.image (fun x => (List.map (fun i => j (f i)) x.toList).prod)).card := by
  classical
  have h1 : ∀ x : Finset ι,
      (List.map (fun i => ψ (f i)) x.toList).prod = ψ ((List.map f x.toList).prod) := by
    intro x
    rw [show (fun i => ψ (f i)) = (ψ : C → Q) ∘ f from rfl, ← List.map_map, List.prod_hom]
  have h2 : ∀ x : Finset ι,
      (List.map (fun i => j (f i)) x.toList).prod = j ((List.map f x.toList).prod) := by
    intro x
    rw [show (fun i => j (f i)) = (j : C → N) ∘ f from rfl, ← List.map_map, List.prod_hom]
  simp_rw [h1, h2]
  rw [show (fun x : Finset ι => ψ ((List.map f x.toList).prod))
        = ψ ∘ (fun x : Finset ι => (List.map f x.toList).prod) from rfl,
     show (fun x : Finset ι => j ((List.map f x.toList).prod))
        = j ∘ (fun x : Finset ι => (List.map f x.toList).prod) from rfl,
     ← Finset.image_image, ← Finset.image_image, Finset.card_image_of_injective _ hj]
  exact Finset.card_image_le
end

section
-- module Solutions.OAIQ093_PR.Unipotent_GammaN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Existence of a unipotent `γ_n`

`exists_gamma_n_unipotent_center_N'` and `exists_gamma_n_unipotent_N'`.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

/-- Transport a `gamma_conj_bound`-style bound along a common "source" group `C`: out of `C`
there is an injective `j` into the group `N` where the bound is known, and a surjective `ψ`
onto the group `Q` where it is wanted, each intertwining the respective self-maps. -/
theorem conjBound_transport_oai {C Q N : Type*} [Group C] [Group Q] [Group N]
    [DecidableEq Q] [DecidableEq N]
    {fC : C → C} {fQ : Q → Q} {fN : N → N}
    (ψ : C →* Q) (hψ : Function.Surjective ψ) (j : C →* N) (hj : Function.Injective j)
    (hψcomm : ∀ x, ψ (fC x) = fQ (ψ x)) (hjcomm : ∀ x, j (fC x) = fN (j x))
    (hbound : ∀ k : ℕ, 0 < k → ∀ g : N, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fN^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q) :
    ∀ k : ℕ, 0 < k → ∀ g : Q, ∃ p q : ℕ, 0 < p ∧ ∀ b : ℕ, 0 < b → ∀ a : ℕ, 0 < a →
      a < b → (Finset.image
        (fun x ↦ (List.map (fun (i : ↥(Finset.Ico a b)) ↦ fQ^[k * ↑i] g) x.toList).prod)
        (Finset.Ico a b).attach.powerset).card ≤ p * b ^ q * (b - a) ^ q := by
  have hiterψ : ∀ (n : ℕ) (x : C), ψ (fC^[n] x) = fQ^[n] (ψ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hψcomm]
  have hiterj : ∀ (n : ℕ) (x : C), j (fC^[n] x) = fN^[n] (j x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hjcomm]
  intro k hk gQ
  obtain ⟨gC, rfl⟩ := hψ gQ
  obtain ⟨p, q, ppos, hb⟩ := hbound k hk (j gC)
  refine ⟨p, q, ppos, ?_⟩
  intro b hb' a ha hab
  refine le_trans ?_ (hb b hb' a ha hab)
  simp_rw [← hiterψ, ← hiterj]
  exact card_image_listProd_hom_le ψ j hj ((Finset.Ico a b).attach.powerset)
    (fun (i : ↥(Finset.Ico a b)) => fC^[k * ↑i] gC)


--   -- simp at ord_fin
--   --rw [Nat.card_prod] at ord_fin
end

theorem solution.{u_2, u_3, u_4} : type_of% @conjBound_transport_oai.{u_2, u_3, u_4} := @conjBound_transport_oai.{u_2, u_3, u_4}
