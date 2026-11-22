-- Prove2me | solution 1 for ShiShallow.product_family_parseval_three
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T03:42:33.898734+00:00
-- url     : https://prove2.me/submissions/34fe316e-4828-4685-bb05-2cd053c862d4

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow ShiTensor

/-! ### Private infrastructure

Parseval for a finite orthonormal family whose cardinality equals the dimension.  Such a family
is a basis (`basisOfOrthonormalOfCardEqFinrank`), hence an `OrthonormalBasis`, and Parseval for an
`OrthonormalBasis` is `OrthonormalBasis.sum_sq_norm_inner_left`.  The only arithmetic needed is
`Fintype.card ((Bits m × Bits p) × Bits q) = 2 ^ (m + p + q) = finrank ℂ (EuclideanSpace ...)`. -/

private theorem shiThree_parseval_of_card_eq_finrank
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {V : ι → E} (hV : Orthonormal ℂ V)
    (hcard : Fintype.card ι = Module.finrank ℂ E) (x : E) :
    ∑ i, ‖inner ℂ x (V i)‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  have hBv :
      ((basisOfOrthonormalOfCardEqFinrank hV hcard : Module.Basis ι ℂ E) : ι → E) = V :=
    coe_basisOfOrthonormalOfCardEqFinrank hV hcard
  have hon :
      Orthonormal ℂ
        ((basisOfOrthonormalOfCardEqFinrank hV hcard : Module.Basis ι ℂ E) : ι → E) := by
    rw [hBv]
    exact hV
  have hcoe :
      (((basisOfOrthonormalOfCardEqFinrank hV hcard :
            Module.Basis ι ℂ E).toOrthonormalBasis hon) : ι → E) = V := by
    rw [Module.Basis.coe_toOrthonormalBasis, hBv]
  have key :=
    ((basisOfOrthonormalOfCardEqFinrank hV hcard :
        Module.Basis ι ℂ E).toOrthonormalBasis hon).sum_sq_norm_inner_left x
  rw [← key]
  refine Finset.sum_congr rfl ?_
  intro i _
  first
  | (rw [hcoe]; done)
  | (rw [← hcoe]; done)
  | (simp only [hcoe]; done)

private theorem shiThree_card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by
  first
  | (simp [Fintype.card_fun]; done)
  | (rw [Fintype.card_fun]; simp; done)
  | (simp [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; done)

private theorem shiThree_card_triple_eq_finrank (m p q : ℕ) :
    Fintype.card ((Bits m × Bits p) × Bits q)
      = Module.finrank ℂ (EuclideanSpace ℂ (Bits (m + p + q))) := by
  have hR : Module.finrank ℂ (EuclideanSpace ℂ (Bits (m + p + q))) = 2 ^ (m + p + q) := by
    rw [finrank_euclideanSpace, shiThree_card_bits]
  rw [hR, Fintype.card_prod, Fintype.card_prod, shiThree_card_bits, shiThree_card_bits,
    shiThree_card_bits]
  first
  | (rw [pow_add, pow_add]; done)
  | (rw [pow_add m p, pow_add (m + p) q]; done)
  | (simp [pow_add]; done)
  | (simp [pow_add, mul_assoc]; done)

theorem solution {m p q : ℕ}
    (V : (Bits m × Bits p) × Bits q → EuclideanSpace ℂ (Bits (m + p + q)))
    (hV : Orthonormal ℂ V) (x : EuclideanSpace ℂ (Bits (m + p + q))) :
    ∑ i : (Bits m × Bits p) × Bits q, ‖inner ℂ x (V i)‖ ^ 2 = ‖x‖ ^ 2 := by
  haveI : Nonempty ((Bits m × Bits p) × Bits q) :=
    ⟨⟨⟨fun _ => false, fun _ => false⟩, fun _ => false⟩⟩
  exact shiThree_parseval_of_card_eq_finrank hV (shiThree_card_triple_eq_finrank m p q) x
