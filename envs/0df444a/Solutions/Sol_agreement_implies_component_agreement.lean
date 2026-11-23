-- Prove2me | solution 1 for agreement_implies_component_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:43:01.518276+00:00
-- url     : https://prove2.me/submissions/53440640-d9d6-413a-af33-e660d0034787

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
  (D : Finset F) (m : ℕ) (f g : F → F) (S : Finset F) (_hS : S ⊆ D)
  (h_blocks : ∀ z ∈ pow_domain S m, Block D m z ⊆ S) :
  (∀ x ∈ S, f x = g x) →
  ∀ i : Fin m, ∀ z ∈ pow_domain S m,
    folding_component D m f i z = folding_component D m g i z := by
  intro h i z hz
  simp only [folding_component, Lagrange.interpolate, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
  exact Finset.sum_congr rfl fun x hx ↦ h x (h_blocks z hz hx) ▸ rfl
