-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_primeOfOne_739683a29f58
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:02.5118+00:00
-- url     : https://prove2.me/submissions/fea04bf6-930d-4842-b924-f5c1b60018e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_homogeneousComponent_066005156b15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_eq_619a623144ca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
variable {N : ℕ} (x : Fin (N + 1) → Ω)
open NumbersDVR
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hx : x ≠ 0) : IsMultiProjPrime (primeOfOne (S := S) x) where
  isPrime := Ideal.comap_isPrime _ _
  multiHomog := by
    classical
    intro f hf b
    have hw : ∀ d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ,
        Finsupp.weight (blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.degree := by
      intro d
      funext u
      rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [blockWeight]
    have heq : weightedHomogeneousComponent (blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, hw d]
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]
      · intro h; funext u; exact h
    rw [heq]
    change oneBlock _ ∈ primeOf x
    change oneBlock f ∈ primeOf x at hf
    rw [primeOf_eq, RingHom.mem_ker] at hf ⊢
    rw [oneBlock, cone_eq, coneGen, aeval_rename] at hf ⊢
    exact coneGen_homogeneousComponent (fun v : Σ _ : Unit, Fin (N + 1) => x v.2) hf _
  relevant := by
    intro k
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    refine ⟨i, ?_⟩
    change oneBlock (X _) ∉ primeOf x
    rw [oneBlock, rename_X, primeOf_eq, RingHom.mem_ker, cone_eq, coneGen, aeval_X]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hi) Polynomial.X_ne_zero
end GroundTheory.Heights₂.Heights.Kleiman
