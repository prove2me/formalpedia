-- Prove2me | solution 1 for ReciprocityTheory.PGsh.cayOp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:59:13.528352+00:00
-- url     : https://prove2.me/submissions/964ac650-361b-4678-b5b8-0f8acd8390fb

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (p : MvPolynomial (Fin n × Fin n) ℤ) :
    cayOp n R (map (Int.castRingHom R) p) = map (Int.castRingHom R) (cayOp n ℤ p) := by
  have hl : ∀ (l : List (Fin n)) (σ : Equiv.Perm (Fin n)) (q : MvPolynomial (Fin n × Fin n) ℤ),
      (l.map fun j => ((pderiv (σ j, j) : Derivation R _ _) :
        MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod
          (map (Int.castRingHom R) q) =
      map (Int.castRingHom R) ((l.map fun j => ((pderiv (σ j, j) : Derivation ℤ _ _) :
        MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ)).prod q) := by
    intro l σ q
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, Derivation.coeFn_coe,
        pderiv_map]
  simp only [cayOp, cayMono, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, hl]
end ReciprocityTheory.PGsh
