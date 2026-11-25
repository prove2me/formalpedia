-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.v_det_vandermonde_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:49.415915+00:00
-- url     : https://prove2.me/submissions/ce213a7b-ded8-4352-9ba5-aa701529172f

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n : ℕ} (a : Fin n → C) :
    v (Matrix.vandermonde a).det ^ 2 = v (discr a) := by
  have hsplit : ∀ τ : Fin n, Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
    intro τ
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
  have hdisj : ∀ τ : Fin n, Disjoint (Finset.Ioi τ) (Finset.Iio τ) := by
    intro τ
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Finset.mem_Ioi.1 h1) (Finset.mem_Iio.1 h2)
  rw [Matrix.det_vandermonde, discr]
  simp only [map_prod]
  have h1 : ∏ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
      (∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ')) *
        ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => by rw [hsplit τ, Finset.prod_union (hdisj τ)]
  have h2 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') =
      ∏ τ' : Fin n, ∏ τ ∈ Finset.Ioi τ', v (a τ - a τ') :=
    Finset.prod_comm' (by intro x y; simp [Finset.mem_Iio, Finset.mem_Ioi])
  have h3 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ') =
      ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ) :=
    Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => Valuation.map_sub_swap v _ _
  rw [h1, h2, h3, sq]
end ReciprocityTheory.PGsh.Up
