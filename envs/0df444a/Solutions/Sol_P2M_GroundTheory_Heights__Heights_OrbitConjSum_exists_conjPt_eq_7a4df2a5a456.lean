-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_conjPt_eq_7a4df2a5a456
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:11.824538+00:00
-- url     : https://prove2.me/submissions/37dea737-08d9-4015-bf9d-747ff447143c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_mem_orbitIdeal_of_homog_7800250f67a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_chart_ne_zero_10cb68d2f03b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_exists_int_mul_3eff43bbc16e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_isWeightedHomogeneous_chartHomog_c0b2ddf82b13
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_aeval_chartHomog_4ac03b3e97ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitConjSum_conj_chart_ne_zero_edf026820d33
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_card_embeddings_restrict_a19e8def3342


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0)
    (q : projPts (ι := blockIdx n) (orbitIdeal x)) : ∃ σ, conjPt x hx σ = q := by
  classical
  induction q using Quot.ind with
  | mk z =>
  obtain ⟨z, hz⟩ := z
  have hz0 := chart_ne_zero x c hc hz
  have hne := conj_chart_ne_zero x c hc
  let L := ratioField x c
  let gen : Coord n → L := fun p ↦ ⟨ratio x c p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  let φ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] L := aeval gen
  have hφ : ∀ F, ((φ F : L) : coordField x) = aeval (ratio x c) F := fun F ↦
    DFunLike.congr_fun (comp_aeval (R := ℚ) (f := gen) L.val) F
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ Algebra.adjoin ℚ (Set.range (ratio x c)) := by
      rw [← IntermediateField.adjoin_toSubalgebra]
      exact ha
    rw [← aeval_range] at ha'
    obtain ⟨F, hF⟩ := ha'
    exact ⟨F, Subtype.ext ((hφ F).trans hF)⟩
  let r : Coord n → ℂ := fun p ↦ z p / z ⟨p.1, c p.1⟩
  have hint : ∀ P : MvPolynomial (Coord n) ℤ, aeval (ratio x c) P = 0 → aeval r P = 0 := by
    intro P hP
    have hx0 : aeval (flatCone x) (chartHomog c P) = 0 := by
      rw [show aeval (flatCone x) (chartHomog c P) = _ from aeval_chartHomog c P (flatCone x) hc]
      have h1 : aeval (fun p ↦ (coordField x).val.toRingHom (ratio x c p)) P = 0 :=
        (map_aeval_int (coordField x).val.toRingHom (ratio x c) P).symm.trans
          (by exact (congrArg _ hP).trans (map_zero _))
      have h2 : (fun p : Coord n ↦ flatCone x p / flatCone x ⟨p.1, c p.1⟩) =
          fun p ↦ (coordField x).val.toRingHom (ratio x c p) := by
        funext p
        simp [ratio, flatCone, coordVec]
      have h5 : aeval (fun p : Coord n ↦ flatCone x p / flatCone x ⟨p.1, c p.1⟩) P = 0 := by
        rw [h2]
        exact h1
      exact mul_eq_zero_of_right _ h5
    have h3 := hz.2 _ (mem_orbitIdeal_of_homog x (isWeightedHomogeneous_chartHomog c P) hx0)
    rw [eval_map_int, aeval_chartHomog c P z hz0] at h3
    exact (mul_eq_zero.mp h3).resolve_left
      (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hz0 k))
  let ψ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ := aeval r
  let φR : MvPolynomial (Coord n) ℚ →+* L := φ.toRingHom
  have hsurjR : Function.Surjective φR := hsurj
  have hker : RingHom.ker φR ≤ RingHom.ker ψ.toRingHom := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    obtain ⟨N, P, hN, hP⟩ := exists_int_mul F
    have hF' : aeval (ratio x c) F = 0 := by
      rw [← hφ]
      exact congrArg Subtype.val hF
    have hyP : aeval (ratio x c) P = 0 := by
      have := congrArg (aeval (ratio x c)) hP
      rw [← algebraMap_int_eq, aeval_map_algebraMap, map_mul, aeval_C, hF', mul_zero] at this
      exact this
    have := congrArg (aeval r) hP
    rw [← algebraMap_int_eq, aeval_map_algebraMap, map_mul, aeval_C, hint P hyP] at this
    have hN' : algebraMap ℚ ℂ (N : ℚ) ≠ 0 := by simpa using hN
    exact (mul_eq_zero.mp this.symm).resolve_left hN'
  let τ : L →+* ℂ := φR.liftOfSurjective hsurjR ⟨ψ.toRingHom, hker⟩
  have hτ : ∀ p, τ (gen p) = r p := fun p ↦ by
    have := φR.liftOfSurjective_comp_apply hsurjR ⟨ψ.toRingHom, hker⟩ (X p)
    have e1 : φR (X p) = gen p := aeval_X gen p
    have e2 : ψ.toRingHom (X p) = r p := aeval_X r p
    rw [e1, e2] at this
    exact this
  obtain ⟨σ, hσ⟩ : ∃ σ : coordField x →+* ℂ, σ.comp (algebraMap L (coordField x)) = τ := by
    have h := card_embeddings_restrict (K := L) (L := coordField x) τ
    have hpos : 0 < (Finset.univ.filter fun σ : coordField x →+* ℂ ↦
        σ.comp (algebraMap L (coordField x)) = τ).card := by
      rw [h]
      exact Module.finrank_pos
    obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
    exact ⟨σ, (Finset.mem_filter.mp hσ).2⟩
  have hσr : ∀ p, σ (ratio x c p) = r p := fun p ↦ by
    rw [← hτ p, ← hσ]
    rfl
  refine ⟨σ, (Quot.sound ⟨fun k ↦ σ (coordVec x k (c k)) / z ⟨k, c k⟩,
    fun k ↦ div_ne_zero (hne σ k) (hz0 k), funext fun p ↦ ?_⟩).symm⟩
  have e := hσr p
  rw [ratio, map_div₀, div_eq_div_iff (hne σ p.1) (hz0 p.1)] at e
  show σ (coordVec x p.1 p.2) = σ (coordVec x p.1 (c p.1)) / z ⟨p.1, c p.1⟩ * z p
  rw [div_mul_eq_mul_div, eq_div_iff (hz0 p.1)]
  linear_combination e
end GroundTheory.Heights₂.Heights.OrbitConjSum
