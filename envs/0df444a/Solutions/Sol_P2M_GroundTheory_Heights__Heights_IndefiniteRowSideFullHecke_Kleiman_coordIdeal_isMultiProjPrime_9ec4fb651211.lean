-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coordIdeal_isMultiProjPrime_9ec4fb651211
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:27.116817+00:00
-- url     : https://prove2.me/submissions/27e4c335-4fa8-4857-8d30-50cfa6736f59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_coeff_88bc714e5f8c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo
variable {S : Type} [CommRing S] {σ : Type} {Ω : Type} [Field Ω] [Algebra S Ω]
open GroundTheory.Heights₂.Heights.NumbersDVR
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
theorem _root_.solution {N : ℕ} (x : Fin (N + 1) → Ω) (hx : ∃ i, x i ≠ 0) :
    IsMultiProjPrime (coordIdeal S (fun v : (Σ _ : Unit, Fin (N + 1)) => x v.2)) where
  isPrime := RingHom.ker_isPrime (coneMap S (fun v : (Σ _ : Unit, Fin (N + 1)) => x v.2)).toRingHom
  multiHomog := by
    intro f hf b
    have hw : ∀ d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ,
        Finsupp.weight (blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.sum fun _ e => e := by
      intro d
      funext u
      simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight,
        smul_eq_mul, Pi.single_apply, if_true, mul_one]
    have hcomp : weightedHomogeneousComponent (blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, hw]
      have : ((fun _ : Unit => d.sum fun _ e => e) = b) ↔ d.degree = b () := by
        constructor
        · intro h; rw [← h]; rfl
        · intro h; funext u; rw [Subsingleton.elim u ()]; exact h
      simp only [this]
    rw [hcomp]
    rw [coordIdeal, RingHom.mem_ker] at hf ⊢
    ext k
    rw [coneMap_coeff, homogeneousComponent_of_mem (homogeneousComponent_mem _ _), Polynomial.coeff_zero]
    split_ifs with hk
    · rw [← coneMap_coeff, hf, Polynomial.coeff_zero]
    · rw [map_zero]
  relevant := by
    intro k
    obtain ⟨i, hi⟩ := hx
    refine ⟨i, fun h => ?_⟩
    have h' : coneMap S (fun v : (Σ _ : Unit, Fin (N + 1)) => x v.2) (X ⟨k, i⟩) = 0 := h
    simp only [coneMap, aeval_X] at h'
    exact hi (by simpa using congrArg (Polynomial.coeff · 1) h')
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
