-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kugaAbs_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:42.726651+00:00
-- url     : https://prove2.me/submissions/fc2dd3aa-119c-45df-ab11-4b7efbf97eac

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KugaAbsHolds
import Theorems.Thm_PositivityTheory_Rg_Cz_kIp_kD
import Theorems.Thm_PositivityTheory_Rg_Cz_kAlt_eq_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_kHom
import Theorems.Thm_PositivityTheory_Rg_Cz_kB_re_nonneg
import Theorems.Thm_PositivityTheory_Rg_Cz_kT_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_KAdjoint_kIp_kD
import Theorems.Thm_PositivityTheory_Rg_Cz_kD_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : KugaAbs := by
  intro P _ _ M _ _ _ _ β γ _ _ b B a r a' r' D c hb hB hpos ha hr har ha'r' hca hcr hc hD hcas q ω hω X
  have hadj : ∀ X x y, B ((a + r) X x) y = B x ((r - a) X y) := by
    intro X x y
    simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, ha, hr]
    ring
  have hzero : kD (a + r) ω = 0 := by
    apply kAlt_eq_zero b hb
    have hK : ∀ J : Fin q → β, kDel (r - a) b (kD (a + r) ω) (b ∘ J) =
        ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
          Module.End ℂ M) (ω (b ∘ J)) -
        ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i)))) :=
      fun J => eq_sub_of_add_eq (kHom b a r a' r' D c har ha'r' hca hcr hc hD ω hω J)
    have hA := kIp_kD B b (a + r) (r - a) hadj ω (kD (a + r) ω)
    have hT := kT_nonneg B b (a + r) (r - a) hB hpos hadj ω
    have h2 : ∀ J : Fin q → β, (B (ω (b ∘ J))
        (((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
          Module.End ℂ M) (ω (b ∘ J)))).re ≤ 0 := by
      intro J
      rw [hB]
      simpa using hcas (ω (b ∘ J))
    have h1 : (kIp B b ω (kDel (r - a) b (kD (a + r) ω))).re ≤ 0 := by
      unfold kIp
      simp only [hK, map_sub, Finset.sum_sub_distrib, Complex.sub_re]
      have h3 := Finset.sum_nonpos (fun J (_ : J ∈ Finset.univ) => h2 J)
      rw [Complex.re_sum] at hT
      rw [Complex.re_sum, Complex.re_sum]
      linarith
    have h4 : (kIp B b (kD (a + r) ω) (kD (a + r) ω)).re ≤ 0 := by
      rw [hA, Complex.mul_re]
      have : (((q : ℂ) + 1)).im = 0 := by simp
      rw [this, zero_mul, sub_zero]
      have : (((q : ℂ) + 1)).re = (q : ℝ) + 1 := by simp
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    unfold kIp at h4
    rw [Complex.re_sum] at h4
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun I (_ : I ∈ Finset.univ) =>
      kB_re_nonneg B hpos (kD (a + r) ω (b ∘ I)))).1
      (le_antisymm h4 (Finset.sum_nonneg (fun I _ => kB_re_nonneg B hpos _)))
    intro I
    by_contra hI
    exact (hpos _ hI).ne' (h5 I (Finset.mem_univ _))
  have := congrArg (fun f => f X) hzero
  simpa [kD_apply] using this
end PositivityTheory.Rg.Cz
