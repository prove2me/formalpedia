-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_full_e5b7437fc745
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:26.82983+00:00
-- url     : https://prove2.me/submissions/93274d12-b189-44be-998b-cc4b4f4617ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint
theorem _root_.solution : CurveComplexPoint.Statement := by
  intro K _ ι _ W hW
  classical
  obtain ⟨_, ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩, hhor, _⟩ := hW
  choose c hc using hrel
  let R := MRing ι ⧸ W
  let F := FractionRing R
  let x : (Σ k, ι k) → F := fun p => algebraMap R F (Ideal.Quotient.mk W (X p))
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k h => hc k
    (Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective R F (h.trans (map_zero _).symm)))
  have hxeval : ∀ f : MRing ι,
      eval₂ (Int.castRingHom F) x f = algebraMap R F (Ideal.Quotient.mk W f) := by
    intro f
    have h : eval₂Hom (Int.castRingHom F) x = (algebraMap R F).comp (Ideal.Quotient.mk W) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [x])
    exact RingHom.congr_fun h f
  have : CharZero F := charZero_of_inj_zero fun n hn => by
    have h1 : Ideal.Quotient.mk W (C (n : ℤ)) = 0 :=
      IsFractionRing.injective R F (by simpa using hn)
    have h2 : (n : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    rw [hhor, Ideal.mem_bot] at h2
    exact_mod_cast h2
  let y : (Σ k, ι k) → F := fun p => (x ⟨p.1, c p.1⟩)⁻¹ * x p
  let ψ : MvPolynomial (Σ k, ι k) ℚ →+* F := eval₂Hom (Rat.castHom F) y
  have hψmap : ∀ f : MRing ι,
      ψ (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom F) y f := by
    intro f
    simp only [ψ, coe_eval₂Hom, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have hWker : ∀ f ∈ W, map (Int.castRingHom ℚ) f ∈ RingHom.ker ψ := by
    intro f hf
    rw [hWS] at hf
    have hle : Ideal.span S ≤ (RingHom.ker ψ).comap (map (Int.castRingHom ℚ)) := by
      refine Ideal.span_le.mpr fun s hs => ?_
      obtain ⟨a, ha⟩ := hS s hs
      have hsW : s ∈ W := hWS ▸ Ideal.subset_span hs
      show ψ (map (Int.castRingHom ℚ) s) = 0
      rw [hψmap]
      refine (eval₂_smul_homog s a ha (fun k => (x ⟨k, c k⟩)⁻¹) x).trans ?_
      rw [hxeval, Ideal.Quotient.eq_zero_iff_mem.mpr hsW, map_zero, mul_zero]
    exact hle hf
  have hXker : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker ψ := by
    intro k
    rw [RingHom.mem_ker, map_sub, map_one]
    simp only [ψ, coe_eval₂Hom, eval₂_X, y]
    rw [inv_mul_cancel₀ (hx k), sub_self]
  obtain ⟨m, hm, hkm⟩ := Ideal.exists_le_maximal (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
  let L := MvPolynomial (Σ k, ι k) ℚ ⧸ m
  let : Field L := Ideal.Quotient.field m
  have : Module.Finite ℚ L := finite_of_finite_type_of_isJacobsonRing ℚ L
  have : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  let φ : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let z : (Σ k, ι k) → ℂ := fun p => φ (Ideal.Quotient.mk m (X p))
  have hz : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
      φ (Ideal.Quotient.mk m (map (Int.castRingHom ℚ) f)) := by
    intro f
    have h : eval₂Hom (Int.castRingHom ℂ) z =
        (φ : L →+* ℂ).comp ((Ideal.Quotient.mk m).comp (map (Int.castRingHom ℚ))) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [z])
    rw [eval_map]
    exact RingHom.congr_fun h f
  refine ⟨z, fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : Ideal.Quotient.mk m (X ⟨k, c k⟩) = Ideal.Quotient.mk m 1 :=
      Ideal.Quotient.eq.mpr (hkm (hXker k))
    simp only [z, h1, map_one]
    exact one_ne_zero
  · rw [hz, Ideal.Quotient.eq_zero_iff_mem.mpr (hkm (hWker f hf)), map_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint
