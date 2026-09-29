-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.pair_comp_eq_pair_comp_cartierTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/24853afe-ad3f-57a4-816f-e067a5f8bf1e

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_pair_comp_eq_pair_comp_cartierTranspose

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (v : ℕ) (u : G.level v →ₐc[R] G.level v)
    (L : Type) [CommRing L] [Algebra R L]
    (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (u : G.level v →ₐ[R] G.level v))) ψ =
      D.pair L v f (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom ψ).comp
        (((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map u).comp (D.equiv v : G'.level v →ₐc[R] CartierDual R (G.level v))) :
            G'.level v →ₐ[R] G'.level v))) := by
  classical
  rw [PDivisibleGroup.CartierDuality.pair_def, PDivisibleGroup.CartierDuality.pair_def]
  simp only [PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply]
  set b := Module.Free.chooseBasis R (G.level v) with hb

  have hT : ∀ μ : Module.Dual R (G.level v),
      ((((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map u).comp (D.equiv v : G'.level v →ₐc[R] CartierDual R (G.level v))) :
            G'.level v →ₐ[R] G'.level v)) ((D.toDualEquiv v).symm μ) =
        (D.toDualEquiv v).symm (μ ∘ₗ (u : G.level v →ₗ[R] G.level v)) := by
    intro μ
    rw [PDivisibleGroup.CartierDuality.toDualEquiv_symm_apply,
      PDivisibleGroup.CartierDuality.toDualEquiv_symm_apply]
    show (D.equiv v).symm (CartierDual.map u ((D.equiv v) ((D.equiv v).symm
      (CartierDual.ofDual R (G.level v) μ)))) = _
    rw [BialgEquiv.apply_symm_apply]
    congr 1

  have hdual : ∀ i, (b.coord i) ∘ₗ (u : G.level v →ₗ[R] G.level v) =
      ∑ j, (b.coord i (u (b j))) • b.coord j := by
    intro i
    conv_lhs => rw [← Module.Basis.sum_dual_apply_smul_coord b ((b.coord i) ∘ₗ (u : G.level v →ₗ[R] G.level v))]
    rfl
  have hvec : ∀ j, u (b j) = ∑ i, (b.coord i (u (b j))) • b i := by
    intro j
    conv_lhs => rw [← b.sum_repr (u (b j))]
    simp only [Module.Basis.coord_apply]
  have hR : ∀ i, PDivisibleGroup.Point.toAlgHom ψ
        (((((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map u).comp (D.equiv v : G'.level v →ₐc[R] CartierDual R (G.level v))) :
            G'.level v →ₐ[R] G'.level v)) ((D.toDualEquiv v).symm (b.coord i))) =
      ∑ j, (b.coord i (u (b j))) • PDivisibleGroup.Point.toAlgHom ψ ((D.toDualEquiv v).symm (b.coord j)) := by
    intro i
    rw [hT, hdual, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, map_smul]
  have hL : ∀ j, PDivisibleGroup.Point.toAlgHom f ((u : G.level v →ₐ[R] G.level v) (b j)) =
      ∑ i, (b.coord i (u (b j))) • PDivisibleGroup.Point.toAlgHom f (b i) := by
    intro j
    have h1 : (u : G.level v →ₐ[R] G.level v) (b j) = u (b j) := rfl
    have h2 := congrArg (PDivisibleGroup.Point.toAlgHom f) (hvec j)
    rw [map_sum] at h2
    rw [h1, h2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  simp_rw [hR, hL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [Finset.sum_comm]

end S_PDivisibleGroup_CartierDuality_pair_comp_eq_pair_comp_cartierTranspose
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_pair_comp_eq_pair_comp_cartierTranspose (solution)
