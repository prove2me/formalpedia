-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_proof_63329d51f704
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:58.73617+00:00
-- url     : https://prove2.me/submissions/e987e6b0-f84f-4ff0-b17a-57f430c4aaae

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_kaehler_D_aeval_da53b3b7fe57
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_finrank_kaehler_eq_card_119c331f97c9
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg_fractionRing


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
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace JacobianRankGeneric
theorem _root_.solution : JacobianRankGeneric.Statement := by
  classical
  intro n d J _ hd
  set A := MvPolynomial (Fin n) ℂ ⧸ J
  set K := FractionRing A

  let ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ A K).comp (Ideal.Quotient.mkₐ ℂ J)
  let x : Fin n → K := fun l => ψ (X l)
  have hψ : ∀ f, ψ f = aeval x f := fun f => congrArg (fun φ => φ f) (MvPolynomial.aeval_unique ψ)
  have hgrad : ∀ f l, genericGradient J f l = aeval x (pderiv l f) := fun f l => hψ (pderiv l f)
  let Φ : (Fin n → K) →ₗ[K] Ω[K⁄ℂ] :=
    ∑ l, (LinearMap.proj l : (Fin n → K) →ₗ[K] K).smulRight (KaehlerDifferential.D ℂ K (x l))
  have hΦ : ∀ w, Φ w = ∑ l, w l • KaehlerDifferential.D ℂ K (x l) := fun w => by
    simp [Φ, LinearMap.sum_apply]

  have hker : Submodule.span K (genericGradient J '' (J : Set _)) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h0 : aeval x f = 0 := by
      rw [← hψ]
      simp only [ψ, AlgHom.comp_apply]
      rw [show Ideal.Quotient.mkₐ ℂ J f = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hΦ, hgrad]
    rw [← JacobianRankGeneric.kaehler_D_aeval, h0, map_zero]

  have hsurj : LinearMap.range Φ = ⊤ := by
    have hA : ∀ f, KaehlerDifferential.D ℂ K (ψ f) ∈ LinearMap.range Φ := fun f =>
      ⟨fun l => aeval x (pderiv l f), by rw [hΦ, hψ, JacobianRankGeneric.kaehler_D_aeval]⟩
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective (A := A) a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hf := hA f
    have hg := hA g
    change KaehlerDifferential.D ℂ K (ψ f / ψ g) ∈ _
    rw [Derivation.leibniz_div]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg))

  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField ℂ K
  have hcard : s.card = d := by
    have h1 := hs.cardinalMk_eq_trdeg
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing ℂ (A := A) K
    rw [hd, ← h1, Cardinal.mk_coe_finset] at h2
    simp at h2
    exact_mod_cast h2.symm
  have hrank : Module.finrank K Ω[K⁄ℂ] = d := by
    rw [JacobianRankGeneric.finrank_kaehler_eq_card s hs H, hcard]

  have h1 := Submodule.finrank_mono hker
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, finrank_top, hrank, Module.finrank_fin_fun] at h2
  change Module.finrank K (Submodule.span K (genericGradient J '' (J : Set _))) ≤ n - d
  calc _ ≤ _ := h1
    _ = n - d := by
      generalize Module.finrank K (LinearMap.ker Φ) = m at h2 ⊢
      omega
end JacobianRankGeneric
end GroundTheory.Heights₂.Heights
