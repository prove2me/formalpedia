-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_indep_grads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:59.74484+00:00
-- url     : https://prove2.me/submissions/9f319a98-8b8d-4183-b8dd-6a8184e6823b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_grad_rename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MvPolynomial Module ReciprocityTheory.AnForm.R
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) (z₀ : J → ℂ) (T : Submodule ℂ (J → ℂ))
    (hT : ∀ w, w ∈ T ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsConeTangent (Int.castRingHom ℂ) P z₀ w)
    (hTd : finrank ℂ T = D + 1) :
    ∃ f : Fin c → MvPolynomial J ℤ, (∀ i, f i ∈ P) ∧
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j))
        (map (Int.castRingHom ℂ) (rename e (f i)))) := by
  classical
  let g : MvPolynomial J ℤ → (J → ℂ) := fun f i => eval z₀ (pderiv i (map (Int.castRingHom ℂ) f))
  obtain ⟨s, hsS, hspan, hsli⟩ := exists_linearIndependent ℂ (g '' (P : Set (MvPolynomial J ℤ)))
  have hfin : Finite s := hsli.finite
  haveI : Fintype s := Fintype.ofFinite s
  let ℓ : (J → ℂ) → (J → ℂ) →ₗ[ℂ] ℂ := fun w =>
    { toFun := fun v => ∑ i, v i * w i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.mul_sum, mul_assoc] }
  let A : Matrix s J ℂ := Matrix.of fun v i => (v : J → ℂ) i
  have hAli : LinearIndependent ℂ A.row := hsli
  have hker : ∀ w, w ∈ LinearMap.ker A.mulVecLin ↔ w ∈ T := by
    intro w
    rw [LinearMap.mem_ker, hT]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsConeTangent]
    constructor
    · intro hw f hf
      have hle : Submodule.span ℂ (s : Set (J → ℂ)) ≤ LinearMap.ker (ℓ w) := by
        rw [Submodule.span_le]
        intro v hv
        have := congrFun hw ⟨v, hv⟩
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, ℓ] using this
      have hg : g f ∈ Submodule.span ℂ (s : Set (J → ℂ)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
      have := hle hg
      simpa [ℓ, g] using this
    · intro hw
      funext v
      obtain ⟨f, hf, hfv⟩ := hsS v.2
      have := hw f hf
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, Matrix.of_apply, Pi.zero_apply]
      rw [← hfv]
      simpa [g] using this
  have hkerT : LinearMap.ker A.mulVecLin = T := by
    ext w
    exact hker w
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrange : Module.finrank ℂ (LinearMap.range A.mulVecLin) = Fintype.card s := by
    have : A.rank = Fintype.card s := by
      rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hAli]
    exact this
  rw [hrange, hkerT, hTd, Module.finrank_fintype_fun_eq_card, Fintype.card_congr e,
    Fintype.card_fin] at hrn
  have hcard : Fintype.card s = c := by omega
  let σ : Fin c ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, ∃ f ∈ P, g f = (σ i : J → ℂ) := fun i => by
    obtain ⟨f, hf, hfv⟩ := hsS (σ i).2
    exact ⟨f, hf, hfv⟩
  choose f hfP hfg using hmem
  refine ⟨f, hfP, ?_⟩
  have hfam : (fun i => grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e (f i)))) =
      (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toLinearMap ∘ (fun i => (σ i : J → ℂ)) := by
    funext i j
    rw [gbap_grad_rename]
    show g (f i) (e.symm j) = (σ i : J → ℂ) (e.symm j)
    rw [hfg i]
  rw [hfam]
  exact (hsli.comp σ σ.injective).map' _ (LinearEquiv.ker _)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
