-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraicIndependent_forgotten_dc1a9fb6b9cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:03.450719+00:00
-- url     : https://prove2.me/submissions/9d1fa2ad-cffc-49d1-862e-d561ba61b9cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncompTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_aeval_scale_40eda7b64db9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_coeff_eval__scale_c1644af1f8da

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
variable {S : Type} [CommRing S]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (V' : Ideal (MRingOver S ι')) [V'.IsPrime] (hV' : IsMultiHomogIdeal V') (i : ∀ k : FibreBlock κ, ι' k.1)
    (hi : ∀ k : FibreBlock κ, (X ⟨k.1, i k⟩ : MRingOver S ι') ∉ V') :
    letI := (Ideal.quotientMap V' (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom le_rfl).toAlgebra
    AlgebraicIndependent (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom)
      (fun k : FibreBlock κ => Ideal.Quotient.mk V' (X ⟨k.1, i k⟩ : MRingOver S ι')) := by
  classical
  set φ := (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom with hφ
  set j := Ideal.quotientMap V' φ le_rfl with hj
  let _ := j.toAlgebra
  set y : FibreBlock κ → MRingOver S ι' ⧸ V' := fun k => Ideal.Quotient.mk V' (X ⟨k.1, i k⟩) with hy
  let z : (Σ k, ι' k) → MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V') :=
    fun q => C (Ideal.Quotient.mk V' (X q))
  let Θ : MRingOver S ι' →ₐ[S] MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V') :=
    aeval fun q => scaleWt κ _ q.1 * z q
  have hz : ∀ f : MRingOver S ι', aeval z f = C (Ideal.Quotient.mk V' f) := by
    intro f
    have e : (aeval z : MRingOver S ι' →ₐ[S] MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')) =
        (IsScalarTower.toAlgHom S (MRingOver S ι' ⧸ V') (MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V'))).comp
          (Ideal.Quotient.mkₐ S V') :=
      algHom_ext fun q => by simp [z]
    rw [e]
    simp
  have hkill : ∀ f ∈ V', Θ f = 0 := by
    obtain ⟨T, hT, hVT⟩ := hV'
    have hle : Ideal.span T ≤ RingHom.ker (Θ : MRingOver S ι' →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')) := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hT f hf
      have hfV : f ∈ V' := by rw [hVT]; exact Ideal.subset_span hf
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show aeval (fun q => scaleWt κ _ q.1 * z q) f = 0
      refine (aeval_scale ha (scaleWt κ (MRingOver S ι' ⧸ V')) z).trans ?_
      rw [hz, Ideal.Quotient.eq_zero_iff_mem.mpr hfV, map_zero, mul_zero]
    intro f hf
    rw [hVT] at hf
    exact RingHom.mem_ker.mp (hle hf)
  let θ : MRingOver S ι' ⧸ V' →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V') :=
    Ideal.Quotient.lift V' (Θ : MRingOver S ι' →+* _) hkill
  have hθj : ∀ r, θ (j r) = C (j r) := by
    intro r
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [hj, Ideal.quotientMap_mk]
    show Θ (rename v g) = C (Ideal.Quotient.mk V' (rename v g))
    have e : (fun p => scaleWt κ (MRingOver S ι' ⧸ V') (v p).1 * z (v p)) = z ∘ v := by
      funext p
      have : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      simp [scaleWt, this]
    show aeval (fun q => scaleWt κ _ q.1 * z q) (rename v g) = _
    rw [aeval_rename, Function.comp_def, e, ← aeval_rename, hz]
  have hθy : ∀ k, θ (y k) = X k * C (y k) := by
    intro k
    show aeval (fun q => scaleWt κ _ q.1 * z q) (X ⟨k.1, i k⟩ : MRingOver S ι') = _
    rw [aeval_X]
    simp [scaleWt, k.2, z, y]
  have hcomp : θ.comp (aeval y : MvPolynomial (FibreBlock κ) (MRingOver S ι ⧸ V'.comap φ) →ₐ[_] _).toRingHom =
      eval₂Hom ((C : _ →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')).comp j) (fun k => X k * C (y k)) := by
    refine ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, coe_eval₂Hom, eval₂_C]
      exact hθj r
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, coe_eval₂Hom, eval₂_X]
      exact hθy k
  have hjinj : Function.Injective j := Ideal.quotientMap_injective
  have hyprod : ∀ m : FibreBlock κ →₀ ℕ, ∏ k, y k ^ m k ≠ 0 := by
    intro m
    rw [Finset.prod_ne_zero_iff]
    intro k _
    refine pow_ne_zero _ fun h => hi k ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [algebraicIndependent_iff]
  intro P hP
  have h0 : eval₂ ((C : _ →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')).comp j)
      (fun k => X k * C (y k)) P = 0 := by
    have := congrArg (fun f => f P) hcomp
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_eval₂Hom] at this
    rw [← this, hP, map_zero]
  ext m
  have hc := coeff_eval₂_scale j y P m
  rw [h0, coeff_zero] at hc
  rw [coeff_zero]
  exact hjinj ((mul_eq_zero.mp hc.symm).resolve_right (hyprod m) |>.trans (map_zero j).symm)
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
