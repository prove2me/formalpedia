-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegLe_proof_f7c6889d19f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:06:24.036806+00:00
-- url     : https://prove2.me/submissions/af6cf935-3550-4733-96e4-3fdf9d33f48e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpanBundleTrdegLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IntermediateField.algebraAdjoinAdjoin
noncomputable section
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpanBundleTrdegLe
theorem _root_.solution : SpanBundleTrdegLe.Statement := by
  intro F _ Ω _ _ K _ ι y M i G c a H _hc hH hGH Φ _ _ s

  let κΦ : Φ →+* FractionRing (MvPolynomial (Option K) Φ) :=
    (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp C
  let κ : Ω →+* FractionRing (MvPolynomial (Option K) Φ) := κΦ.comp (algebraMap Ω Φ)
  let _ : Algebra F (FractionRing (MvPolynomial (Option K) Φ)) := (κ.comp (algebraMap F Ω)).toAlgebra
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))) :=
    IsFractionRing.injective _ _
  let Xo : Option K → FractionRing (MvPolynomial (Option K) Φ) := fun o =>
    algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ)) (X o)

  let gy : (Σ k, ι k) → FractionRing (MvPolynomial (Option K) Φ) := fun p => κ (y p) * Xo (some p.1)

  have hAy : Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) ≤
      Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) := by
    have hθ : ∀ f, (aeval gy : MRing ι F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) f =
        algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
          (rename some (map (algebraMap Ω Φ) (pointConeMap F y f))) := by
      intro f
      have e := MvPolynomial.ringHom_ext
        (f := ((aeval gy : MRing ι F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
          MRing ι F →+* FractionRing (MvPolynomial (Option K) Φ)))
        (g := ((algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp
          (((rename some : MvPolynomial K Φ →ₐ[Φ] MvPolynomial (Option K) Φ) :
            MvPolynomial K Φ →+* MvPolynomial (Option K) Φ).comp
            ((map (algebraMap Ω Φ)).comp (pointConeMap F y : MRing ι F →+* MvPolynomial K Ω)))))
        (fun r => by
          simp [pointConeMap, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra, κ, κΦ])
        (fun p => by simp [pointConeMap, gy, κ, κΦ, Xo])
      exact congrArg (fun φ => φ f) e
    rw [Algebra.adjoin_range_eq_range_aeval]
    refine trdeg_le_of_surjective (Ideal.Quotient.liftₐ (pointIdeal F y) (aeval gy).rangeRestrict ?_) ?_
    · intro f hf
      apply Subtype.ext
      change (aeval gy) f = 0
      rw [hθ, show pointConeMap F y f = 0 from hf]
      simp
    · intro x
      obtain ⟨f, rfl⟩ := AlgHom.rangeRestrict_surjective _ x
      exact ⟨Ideal.Quotient.mk _ f, rfl⟩

  have hSyL : Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) =
      Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) := by
    have : FaithfulSMul F (Algebra.adjoin F (Set.range gy)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have : FaithfulSMul F (IntermediateField.adjoin F (Set.range gy)) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have e := trdeg_add_eq F (Algebra.adjoin F (Set.range gy))
      (A := IntermediateField.adjoin F (Set.range gy))
    rwa [trdeg_eq_zero (R := Algebra.adjoin F (Set.range gy)), add_zero] at e

  have hchart : ∀ u ∈ chartRing F (segreVec y) c, κ u ∈ IntermediateField.adjoin F (Set.range gy) := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem u hu =>
      obtain ⟨c', rfl⟩ := hu
      have hQ : ∏ k, Xo (some k) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => (map_ne_zero_iff _ hinj).2 (X_ne_zero _)
      have e : κ (segreVec y c' / segreVec y c) = (∏ k, gy ⟨k, c' k⟩) / ∏ k, gy ⟨k, c k⟩ := by
        simp only [gy, Finset.prod_mul_distrib, segreVec, map_div₀, map_prod]
        rw [mul_div_mul_right _ _ hQ]
      rw [e]
      exact div_mem (prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)
        (prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)
    | algebraMap r => exact IntermediateField.algebraMap_mem _ r
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | mul u v _ _ hu hv => rw [map_mul]; exact mul_mem hu hv

  choose g hg hGm using hGH
  set p0 : Ω := ∏ k, y ⟨k, c k⟩ ^ a k with hp0
  have hgL : ∀ l m, κ (g l m) ∈ IntermediateField.adjoin F (Set.range gy) := fun l m => hchart _ (hg l m)

  let w : Fin i → FractionRing (MvPolynomial (Option K) Φ) := fun m =>
    κ p0 * κΦ (∑ m', algebraMap Ω Φ (H⁻¹ m m') * s m') * Xo none
  let T := (aeval w : MvPolynomial (Fin i) (IntermediateField.adjoin F (Set.range gy)) →ₐ[_]
    FractionRing (MvPolynomial (Option K) Φ)).range
  have hTi : Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T ≤ i := by
    have := trdeg_le_of_surjective _ (AlgHom.rangeRestrict_surjective
      (aeval w : MvPolynomial (Fin i) (IntermediateField.adjoin F (Set.range gy)) →ₐ[_]
        FractionRing (MvPolynomial (Option K) Φ)))
    simpa using this
  have : FaithfulSMul F (IntermediateField.adjoin F (Set.range gy)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul (IntermediateField.adjoin F (Set.range gy)) T :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have hT : Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) +
      Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T = Algebra.trdeg F T :=
    trdeg_add_eq F (IntermediateField.adjoin F (Set.range gy)) (A := T)

  let gz : (Σ o, bundleIdx ι M o) → FractionRing (MvPolynomial (Option K) Φ) := fun p =>
    algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
      (C (projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) *
        X p.1)
  have hφ : ∀ l m', ((LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) (Pi.basisFun Ω (Fin i) m') : Ω) =
      G l m' := by
    intro l m'
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hΦ : ∀ l, (∑ m', s m' * algebraMap Ω Φ (G l m')) =
      ∑ m, algebraMap Ω Φ (g l m) * algebraMap Ω Φ p0 * ∑ m', algebraMap Ω Φ (H⁻¹ m m') * s m' := by
    intro l
    have hG : ∀ m', G l m' = ∑ m, (g l m * p0) * H⁻¹ m m' := by
      intro m'
      have h := congrFun (congrFun (Matrix.mul_nonsing_inv_cancel_right H (Matrix.of G) hH) l) m'
      rw [Matrix.mul_apply] at h
      calc G l m' = Matrix.of G l m' := rfl
        _ = _ := h.symm
        _ = _ := Finset.sum_congr rfl fun m _ => by rw [hGm]
    simp_rw [hG, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
  have hnone : ∀ l : Fin M, gz ⟨none, l⟩ = ∑ m, κ (g l m) * w m := by
    intro l
    have e1 : projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s
        (⟨none, l⟩ : Σ o, bundleIdx ι M o) = ∑ m', s m' * algebraMap Ω Φ (G l m') := by
      simp only [projCoord, hφ]
    have e2 : gz ⟨none, l⟩ = κΦ (∑ m', s m' * algebraMap Ω Φ (G l m')) * Xo none := by
      simp only [gz, e1, map_mul]
      rfl
    rw [e2, hΦ l, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [w, κ, RingHom.comp_apply, map_mul]
    ring
  have hsome : ∀ k (j : ι k), gz ⟨some k, j⟩ = gy ⟨k, j⟩ := by
    intro k j
    simp only [gz, gy, projCoord, map_mul]
    rfl
  have hgzT : ∀ p, gz p ∈ T := by
    rintro ⟨_ | k, j⟩
    · rw [hnone j]
      refine ⟨∑ m, C ⟨κ (g j m), hgL j m⟩ * X m, ?_⟩
      simp
    · rw [hsome k j]
      exact ⟨C ⟨gy ⟨k, j⟩, IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩⟩, by simp⟩

  have hz : ∀ f, (aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) f =
      algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))
        (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
          (fun p => C (projCoord y (Pi.basisFun Ω (Fin i))
            (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) * X p.1) f) := by
    intro f
    have e := MvPolynomial.ringHom_ext
      (f := ((aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
        MRing (bundleIdx ι M) F →+* FractionRing (MvPolynomial (Option K) Φ)))
      (g := (algebraMap (MvPolynomial (Option K) Φ) (FractionRing (MvPolynomial (Option K) Φ))).comp
        (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
          (fun p => C (projCoord y (Pi.basisFun Ω (Fin i))
            (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s p) * X p.1)))
      (fun r => by simp [RingHom.algebraMap_toAlgebra, κ, κΦ])
      (fun p => by simp [gz])
    exact congrArg (fun φ => φ f) e
  let φT : MRing (bundleIdx ι M) F →ₐ[F] T := aeval fun p => ⟨gz p, hgzT p⟩
  have hφT : ∀ f, (φT f : FractionRing (MvPolynomial (Option K) Φ)) = aeval gz f := by
    intro f
    have e := MvPolynomial.ringHom_ext
      (f := (T.val : T →+* FractionRing (MvPolynomial (Option K) Φ)).comp
        (φT : MRing (bundleIdx ι M) F →+* T))
      (g := ((aeval gz : MRing (bundleIdx ι M) F →ₐ[F] FractionRing (MvPolynomial (Option K) Φ)) :
        MRing (bundleIdx ι M) F →+* FractionRing (MvPolynomial (Option K) Φ)))
      (fun r => by simp [φT])
      (fun p => by simp [φT])
    exact congrArg (fun φ => φ f) e
  have hmem : ∀ f, φT f = 0 ↔ f ∈ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s := by
    intro f
    rw [projIdeal, RingHom.mem_ker, ← Subtype.val_inj, hφT, hz, ZeroMemClass.coe_zero,
      map_eq_zero_iff _ hinj]
  have hAz : Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ≤ Algebra.trdeg F T := by
    refine trdeg_le_of_injective (Ideal.Quotient.liftₐ _ φT fun f hf => (hmem f).2 hf) ?_
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hmem f).1 hx)
  calc _ ≤ Algebra.trdeg F T := hAz
    _ = Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) +
        Algebra.trdeg (IntermediateField.adjoin F (Set.range gy)) T := hT.symm
    _ ≤ Algebra.trdeg F (IntermediateField.adjoin F (Set.range gy)) + i := by gcongr
    _ = Algebra.trdeg F (Algebra.adjoin F (Set.range gy)) + i := by rw [hSyL]
    _ ≤ _ := by gcongr
end SpanBundleTrdegLe
end GroundTheory.Heights₂.Heights.NumbersDVR
