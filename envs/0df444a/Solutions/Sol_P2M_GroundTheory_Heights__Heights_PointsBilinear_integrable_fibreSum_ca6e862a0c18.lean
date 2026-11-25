-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointsBilinear_integrable_fibreSum_ca6e862a0c18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:26.743803+00:00
-- url     : https://prove2.me/submissions/5200aa9d-1c2c-4d54-b79e-b3393713a63b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_isSmoothHerm_ofWeight_e0b623fc4e1e

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PointsBilinear
theorem _root_.solution (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {f g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (n + 2)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hf : IsDegZeroSmooth f) (hg : IsDegZeroSmooth g) :
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (Fin.cons f (pot L)) g y w) := by
  have hf' : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → -f (fun p => c p.1 * z p) = -f z :=
    fun c z hc => by simp only [hf.2 c z hc]
  have hF := isSmoothHerm_ofWeight (w := fun z => -f z) hf' hf.1.neg
  have hG := isSmoothHerm_ofWeight hg.2 hg.1
  have hLF : ∀ j, IsSmoothHerm ((Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → HermLine ι) j) := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.cons_zero] using hF
    · simpa only [Fin.cons_succ] using hL j
  have hpot : pot (Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → HermLine ι) = Fin.cons f (pot L) := by
    funext j z
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pot, HermLine.ofWeight, Real.log_exp]
    · simp [pot]
  have hlog : logNorm (HermLine.ofWeight g hg.2) 1 = g := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_exp]
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hm : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    simp only [Finset.mem_singleton] at hm
    subst hm
    simp
  have hsec : IsSectionOn P (HermLine.ofWeight g hg.2) 1 :=
    ⟨fun _ => 0, fun k => by simp [HermLine.ofWeight], hm, h1⟩
  have := hInt K ι P (n + 1) Ψ _ _ 1 hP hΨ hLF hG hsec
  rwa [hpot, hlog] at this
end GroundTheory.Heights₂.Heights.PointsBilinear
