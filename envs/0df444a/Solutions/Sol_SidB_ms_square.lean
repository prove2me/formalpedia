-- Prove2me | solution 1 for SidB.ms_square
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:47:45.368001+00:00
-- url     : https://prove2.me/submissions/7ee05911-7908-4675-90e0-9c91cf6ad0b9

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper
open SidB

lemma g73s_exp_nonneg (g : Graphon) (S : Type) [Fintype S] (f : (S → g.dom) → ℝ)
    (h : ∀ x, 0 ≤ f x) : 0 ≤ g.EX S f := by
  have h0 := g.exp_linear S inferInstance 0 0 (fun _ => 1) (fun _ => 1)
  simp only [zero_mul, add_zero] at h0
  have h1 := g.exp_mono S inferInstance (fun _ => 0) f h
  unfold Graphon.EX
  linarith

lemma g73s_rho_nonneg (g : Graphon) {A : Type} (F : Finset A) (x : A → g.dom) : 0 ≤ g.rho F x := by
  unfold Graphon.rho
  exact g73s_exp_nonneg g Unit _ (fun u => Finset.prod_nonneg (fun i _ => g.w_nonneg _ _))

/-- multiplication by 2 on Z/5 -/
def g73s_sigma : Fin 5 ≃ Fin 5 where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide
  right_inv := by decide

lemma g73s_rho_map (g : Graphon) (F : Finset (Fin 5)) (x : Fin 5 → g.dom) :
    g.rho (F.map g73s_sigma.toEmbedding) x = g.rho F (fun a => x (g73s_sigma a)) := by
  unfold Graphon.rho
  simp only [Finset.prod_map]
  rfl

lemma g73s_split :
    (Finset.univ.filter (fun s : Finset (Fin 5) => s.card = 3)) =
      (Finset.univ.image (fun i => mobiusLadder.nbr i)) ∪
      (Finset.univ.image (fun i => (mobiusLadder.nbr i).map g73s_sigma.toEmbedding)) := by
  decide

lemma g73s_disj : Disjoint (Finset.univ.image (fun i => mobiusLadder.nbr i))
      (Finset.univ.image (fun i => (mobiusLadder.nbr i).map g73s_sigma.toEmbedding)) := by
  decide

lemma g73s_inj1 : Set.InjOn (fun i => mobiusLadder.nbr i) (Finset.univ : Finset (Fin 5)) := by
  intro a _ b _ h; revert a b; decide

lemma g73s_inj2 : Set.InjOn (fun i => (mobiusLadder.nbr i).map g73s_sigma.toEmbedding)
    (Finset.univ : Finset (Fin 5)) := by
  intro a _ b _ h; revert a b; decide

theorem solution (g : Graphon) :
    g.dens incGraph53 ≤ g.dens mobiusSquare := by
  set f1 : (Fin 5 → g.dom) → ℝ := fun x => ∏ i : Fin 5, g.rho (mobiusLadder.nbr i) x with hf1
  have f1nn : ∀ x, 0 ≤ f1 x := fun x => Finset.prod_nonneg (fun i _ => g73s_rho_nonneg g _ x)
  -- the incidence density
  have hinc : g.dens incGraph53 = g.EX (Fin 5) (fun x => f1 x * f1 (fun a => x (g73s_sigma a))) := by
    unfold Graphon.dens
    congr 1; funext x
    have e1 : ∏ b : {s : Finset (Fin 5) // s.card = 3}, g.rho (incGraph53.nbr b) x =
        ∏ s ∈ Finset.univ.filter (fun s : Finset (Fin 5) => s.card = 3), g.rho s x := by
      rw [Finset.prod_subtype (Finset.univ.filter (fun s : Finset (Fin 5) => s.card = 3))
        (p := fun s => s.card = 3) (by simp)]
      apply Finset.prod_congr rfl
      intro b _
      congr 1
      ext a; simp [Bigraph.nbr, incGraph53]
    rw [e1, g73s_split, Finset.prod_union g73s_disj, Finset.prod_image g73s_inj1,
      Finset.prod_image g73s_inj2]
    simp only [hf1, g73s_rho_map]
  have hsq : g.dens mobiusSquare = g.EX (Fin 5) (fun x => f1 x ^ 2) := by
    unfold Graphon.dens
    congr 1; funext x
    rw [Fintype.prod_prod_type]
    simp only [hf1, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fin.prod_univ_two, pow_two]
    rfl
  rw [hinc, hsq]
  have hH := g.exp_holder (Fin 5) inferInstance Bool inferInstance
    (fun j x => cond j (f1 x) (f1 (fun a => x (g73s_sigma a))))
    (by intro j x; cases j <;> exact f1nn _) (by simp)
  simp only [Fintype.prod_bool, cond_true, cond_false, Fintype.card_bool] at hH
  have htr : g.exp (Fin 5) inferInstance (fun x => f1 (fun a => x (g73s_sigma a)) ^ ((2:ℕ) : ℝ)) =
      g.exp (Fin 5) inferInstance (fun x => f1 x ^ ((2:ℕ) : ℝ)) :=
    g.exp_transport (Fin 5) (Fin 5) inferInstance inferInstance g73s_sigma.symm
      (fun x => f1 x ^ ((2:ℕ) : ℝ))
  have hE : 0 ≤ g.EX (Fin 5) (fun x => f1 x ^ 2) := g73s_exp_nonneg g _ _ (fun x => by positivity)
  simp only [Nat.cast_ofNat] at htr hH
  rw [htr] at hH
  simp only [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow] at hH
  unfold Graphon.EX at hE ⊢
  rw [Real.mul_self_sqrt hE] at hH
  exact hH
