-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_mCoordIdeal_latticeCoord_f0c94eca4f56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:43.314391+00:00
-- url     : https://prove2.me/submissions/8afa8f02-982a-4e20-ad6e-82d7d6ab244e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_algebraMap_C_06ff1ad36227
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (φ : Fin (N + 1) → Fin (r + 1) → K) :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) = latticeIdeal φ := by
  ext f
  rw [Geo.mCoordIdeal, RingHom.mem_ker, latticeIdeal, RingHom.mem_ker]
  constructor
  · intro hf
    have hw : ∀ w : Fin (r + 1) → K, w 0 ≠ 0 → eval w (latticeMap φ f) = 0 := by
      intro w hw0
      let χ : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* MvPolynomial (Fin r) K :=
        eval₂Hom (Int.castRingHom _) fun v ↦ C (w 0) * (C (φ v.2 0) + ∑ j : Fin r, C (φ v.2 j.succ) * X j)
      have h1 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
          eval (fun _ : Unit ↦ algebraMap K (LatticeField K r) (w 0))
            (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) g) =
          algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (χ g) := by
        intro g
        induction g using MvPolynomial.induction_on with
        | C a => simp [Geo.mConeMap, χ]
        | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
        | mul_X p v hp =>
          rw [map_mul, map_mul, hp, map_mul, map_mul]
          congr 1
          simp only [Geo.mConeMap, aeval_X, map_mul, eval_C, eval_X, χ, coe_eval₂Hom, eval₂_X, algebraMap_C,
            latticeCoord]
          ring
      have h2 : χ f = 0 := by
        apply IsFractionRing.injective (MvPolynomial (Fin r) K) (LatticeField K r)
        rw [map_zero, ← h1, hf, map_zero]
      have h3 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
          eval (fun j : Fin r ↦ w j.succ / w 0) (χ g) = eval w (latticeMap φ g) := by
        intro g
        induction g using MvPolynomial.induction_on with
        | C a => simp [χ, latticeMap]
        | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
        | mul_X p v hp =>
          rw [map_mul, map_mul, hp, map_mul, map_mul]
          congr 1
          simp only [χ, latticeMap, coe_eval₂Hom, eval₂_X, latticeForm, map_mul, map_add, map_sum, eval_C, eval_X,
            Fin.sum_univ_succ]
          rw [mul_add, Finset.mul_sum]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro j _
            field_simp
      rw [← h3, h2, map_zero]
    have hX : (X 0 : MvPolynomial (Fin (r + 1)) K) * latticeMap φ f = 0 := by
      apply MvPolynomial.funext
      intro w
      by_cases h0 : w 0 = 0
      · simp [h0]
      · simp [hw w h0]
    exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)
  · intro hf
    let ψ : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial Unit (LatticeField K r) :=
      eval₂Hom (C.comp (algebraMap K (LatticeField K r))) fun j ↦ C (genericVal K r j) * X ()
    have h1 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
        Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) g = ψ (latticeMap φ g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [Geo.mConeMap, ψ, latticeMap]
      | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
      | mul_X p v hp =>
        rw [map_mul, map_mul, hp, map_mul]
        congr 1
        obtain ⟨⟨⟩, b⟩ := v
        simp only [Geo.mConeMap, aeval_X, latticeCoord_eq, dehom, latticeMap, ψ, coe_eval₂Hom, eval₂_X,
          latticeForm, map_sum, map_mul, eval₂_C, RingHom.comp_apply, Finset.sum_mul, mul_assoc]
    rw [h1, hf, map_zero]
end GroundTheory.Heights₂.Heights.LatticeModel
