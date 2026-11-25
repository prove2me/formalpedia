-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_exists_betaB_mul_eq_45dd53d7220e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:44.26581+00:00
-- url     : https://prove2.me/submissions/2fbc6781-6d14-47e9-9963-437cad19b39c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_X_292343fa3182
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {O : Type*} [CommRing O] [IsDomain O]
variable {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
include hγ
omit [IsDomain O]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution [hVp : V.IsPrime] (hε : Function.Surjective ε)
    (c : (k : ι) → Fin (n k + 1)) (hXc : ∀ k, ε (X ⟨k, c k⟩) = 1)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hmax : ∀ F, betaB γ (V.map ε) F ∈ maximalIdeal (locB ι (V.map ε)) ↔ F ∈ V)
    (b : locB ι (V.map ε)) :
    ∃ F t, t ∉ V ∧ betaB γ (V.map ε) t * b = betaB γ (V.map ε) F := by
  have h1 : (1 : MvPolynomial (Coord n) ℤ) ∉ V := (Ideal.ne_top_iff_one V).mp hVp.ne_top
  let S : Subring (locB ι (V.map ε)) :=
    { carrier := {b | ∃ F t, t ∉ V ∧ betaB γ (V.map ε) t * b = betaB γ (V.map ε) F}
      mul_mem' := by
        rintro _ _ ⟨F₁, t₁, h₁, e₁⟩ ⟨F₂, t₂, h₂, e₂⟩
        refine ⟨F₁ * F₂, t₁ * t₂, fun h ↦ (hVp.mem_or_mem h).elim h₁ h₂, ?_⟩
        rw [map_mul, map_mul, ← e₁, ← e₂]
        ring
      one_mem' := ⟨1, 1, h1, by simp⟩
      add_mem' := by
        rintro _ _ ⟨F₁, t₁, h₁, e₁⟩ ⟨F₂, t₂, h₂, e₂⟩
        refine ⟨F₁ * t₂ + F₂ * t₁, t₁ * t₂, fun h ↦ (hVp.mem_or_mem h).elim h₁ h₂, ?_⟩
        rw [map_add, map_mul, map_mul, map_mul, ← e₁, ← e₂]
        ring
      zero_mem' := ⟨0, 1, h1, by simp⟩
      neg_mem' := by
        rintro _ ⟨F, t, h, e⟩
        exact ⟨-F, t, h, by rw [map_neg, ← e]; ring⟩ }
  have hβ : ∀ F, betaB γ (V.map ε) F ∈ S := fun F ↦ ⟨F, 1, h1, by simp⟩
  have hinv : ∀ (b : locB ι (V.map ε)) (hb : IsUnit b), b ∈ S →
      (↑hb.unit⁻¹ : locB ι (V.map ε)) ∈ S := by
    rintro b hb ⟨F, t, ht, e⟩
    have htu : IsUnit (betaB γ (V.map ε) t) := by
      by_contra h
      exact ht ((hmax t).mp ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)))
    have hF : F ∉ V := fun hF ↦ mem_nonunits_iff.mp ((mem_maximalIdeal _).mp ((hmax F).mpr hF))
      (e ▸ htu.mul hb)
    refine ⟨t, F, hF, ?_⟩
    rw [← e, mul_assoc, IsUnit.mul_val_inv, mul_one]
  let ρ : O →+* locB ι (V.map ε) := (algebraMap (MvPolynomial ι O) (locB ι (V.map ε))).comp C
  have hρX : ∀ p : Coord n, betaB γ (V.map ε) (X ⟨p.1, c p.1⟩) * ρ (ε (X p)) =
      betaB γ (V.map ε) (X p) := fun p ↦ by
    rw [betaB_X ε γ hγ V, betaB_X ε γ hγ V, hXc]
    simp only [ρ, RingHom.comp_apply, map_one, one_mul]
    rw [← map_mul, mul_comm (X p.1)]
  have hρ : ∀ F, ρ (ε F) ∈ S := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C z =>
      rw [eq_intCast C z, map_intCast, map_intCast]
      exact intCast_mem S z
    | add p q hp hq =>
      rw [map_add, map_add]
      exact S.add_mem hp hq
    | mul_X p q hp =>
      rw [map_mul, map_mul]
      exact S.mul_mem hp ⟨X q, X ⟨q.1, c q.1⟩, hXV q.1, hρX q⟩
  have hP : ∀ p : MvPolynomial ι O, algebraMap _ (locB ι (V.map ε)) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C o =>
      obtain ⟨F, rfl⟩ := hε o
      exact hρ F
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | mul_X p k hp =>
      rw [map_mul]
      refine S.mul_mem hp ?_
      have e : algebraMap (MvPolynomial ι O) (locB ι (V.map ε)) (X k) =
          betaB γ (V.map ε) (X ⟨k, c k⟩) := by
        rw [betaB_X ε γ hγ V, hXc]
        simp
      rw [e]
      exact hβ _
  obtain ⟨p, q, rfl⟩ := IsLocalization.exists_mk'_eq (fibO ι (V.map ε)).primeCompl b
  have hq : IsUnit (algebraMap _ (locB ι (V.map ε)) (q : MvPolynomial ι O)) :=
    IsLocalization.map_units _ q
  have e : IsLocalization.mk' (locB ι (V.map ε)) p q = algebraMap _ _ p * ↑hq.unit⁻¹ := by
    rw [← IsLocalization.mk'_spec (locB ι (V.map ε)) p q, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hmem : IsLocalization.mk' (locB ι (V.map ε)) p q ∈ S := by
    rw [e]
    exact S.mul_mem (hP p) (hinv _ hq (hP q))
  exact hmem
end GroundTheory.Heights₂.Heights.OrbitChartMult
