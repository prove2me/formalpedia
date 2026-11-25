-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity.nonvanishing_coefficient_positivity_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:13:43.265272+00:00
-- url     : https://prove2.me/submissions/59b501c7-c02d-429d-b44d-abad46ebe128

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bNormHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_psd_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_flow_eq_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_fz_zero_of_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Zb_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_chiAt_embH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_herm_rank1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_pairR_rank1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_posDef_of_posSemidef_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma herm_add_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private lemma herm_add_right_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  simp only [herm, cc, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
private lemma herm_smul_left_fundamental_domains' (G : Matrix (Fin r) (Fin r) E) (t : E) (x y : Fin r → E) :
    herm G (t • x) y = t * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private lemma herm_smul_right_eq_cc_mul' (G : Matrix (Fin r) (Fin r) E) (t : E) (x y : Fin r → E) :
    herm G x (t • y) = cc t * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end
end ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
theorem _root_.solution (h2 : UnipotentLatticeLift (E := E)) (h3 : FourierCoefficientProperties (E := E)) :
    NonvanishingCoefficientPositivity (E := E) := by
  intro r X u hu hΛ la P hP hχΓ χ hex τ
  obtain ⟨x1, hx1, hfz⟩ := hex
  obtain ⟨-, hinvP, hβ⟩ := h2 r X u hu hΛ
  have hcond : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
    by_contra hc
    exact hfz (by simp only [Data.fz, if_neg hc])
  have hωex : ∃ ω, X.IsLZBasis X.g ω := by
    by_contra hc
    exact hfz (by simp only [Data.fz, if_pos hcond, dif_neg hc])
  obtain ⟨⟨hPsec, C, hC⟩, hcusp⟩ := hP
  have hPinv := hinvP la P hPsec hχΓ
  obtain ⟨⟨hFd, -, hFZ⟩, hFn, -⟩ :=
    h3 r X.toData u X.g hu X.g_pos la P hPsec.1 hPsec.2.1 hPinv χ
  have hFC : ∀ y ∈ X.dom, X.pnorm la (X.fz u X.g χ P) y ≤ C := fun y hy =>
    hFn y hy C fun b hb => hC _ (X.toData.Zb_dom u hu.1 b hb hy)
  have hpsd := psd_of X.toData u hu la χ hcond.1 _ hFd hFZ C hFC hx1 hfz τ
  obtain ⟨β, -, rfl, -⟩ := hβ χ hcond.1 hcond.2
  refine posDef_of_posSemidef_det hpsd ?_
  have hdet : (Matrix.of (X.embH β τ)).det = τ.1 β.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  rw [hdet]
  intro h0
  have hβ0 : β.det = 0 := (RingHom.injective τ.1) (h0.trans (map_zero τ.1).symm)

  obtain ⟨c, hc0, hcβ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hβ0
  obtain ⟨d, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ c
  have hint' : ∀ i, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (d : 𝓞 E) • c i := fun i =>
    RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
  choose c' hc' using hint'
  set e : Fin 2 → E := fun i => algebraMap (𝓞 E) E (c' i) with he_def
  have hde : ∀ i, e i = algebraMap (𝓞 E) E d * c i := fun i => by
    simp only [he_def, hc', Algebra.smul_def]
  have hdne : algebraMap (𝓞 E) E d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (𝓞 E) E)]
    exact fun h => nonZeroDivisors.coe_ne_zero d (IsFractionRing.injective (𝓞 E) E h)
  have he0 : e ≠ 0 := by
    intro h
    apply hc0
    funext i
    have h1 := congrFun h i
    rw [hde, Pi.zero_apply] at h1
    simpa [hdne] using h1
  have hek : ∀ k, ∑ i, e i * β i k = 0 := by
    intro k
    have h1 := congrFun hcβ k
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h1
    simp only [hde, mul_assoc, ← Finset.mul_sum, h1, mul_zero]
  set ξ : Fin r → E := ∑ i, e i • u i with hξ_def
  have hξΛ : ξ ∈ X.Λ := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [he_def]
    dsimp only
    rw [algebraMap_smul E (c' i) (u i)]
    exact Submodule.smul_mem _ _ (hΛ i)
  have hξ0 : ξ ≠ 0 := fun h => he0 (funext (Fintype.linearIndependent_iff.1 hu.2 e h))
  have hξξ : herm X.Gm ξ ξ = 0 := by
    simp only [hξ_def, Fin.sum_univ_two, herm_add_left_fundamental_domains, herm_add_right_fundamental_domains, herm_smul_left_fundamental_domains',
      herm_smul_right_eq_cc_mul', hu.1, mul_zero, add_zero]
  have hemb : ∀ σ : X.Ψ, Data.emb σ.1 ξ = X.uvec u (fun σ i => σ.1 (e i)) σ := by
    intro σ
    funext j
    simp [Data.emb, Data.uvec, hξ_def, Finset.sum_apply, map_sum, map_mul]

  have hinv : ∀ s : X.Ψ → ℝ, X.fz u X.g (X.embH β) P (X.flow ξ (fun τ => (s τ : ℂ)) x1) =
      X.fz u X.g (X.embH β) P x1 := by
    intro s
    rw [flow_eq_Zb X.toData u ξ _ hemb s x1, hFZ _ (herm_rank1 X.toData s _) x1 hx1, pairR_rank1]
    have hz : ∀ σ, X.chiAt (X.embH β) (fun σ i => σ.1 (e i)) σ = 0 := by
      intro σ
      rw [chiAt_embH, Finset.sum_comm]
      have h1 : ∑ k, ∑ i, β i k * e i * cc (e k) = 0 := Finset.sum_eq_zero fun k _ => by
        rw [← Finset.sum_mul,
          show (∑ i, β i k * e i) = ∑ i, e i * β i k from Finset.sum_congr rfl fun i _ => mul_comm _ _,
          hek k, zero_mul]
      rw [h1, map_zero]
    simp [hz]
  exact hfz (fz_zero_of_inv X.toData u hu.1 X.g _ hcond hωex la P hPsec.1.continuousOn C hC ξ hξξ _
    hemb (hcusp ξ ⟨hξΛ, hξξ, hξ0⟩) hx1 hinv)
end ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
