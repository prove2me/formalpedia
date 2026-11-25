-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.trace_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:29.05163+00:00
-- url     : https://prove2.me/submissions/c9adb61d-40de-4e74-8efb-76df26ff3daf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_nil_pow_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
namespace PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (hfin : {μ | T.maxGenEigenspace μ ≠ ⊥}.Finite) (k : ℕ) :
    LinearMap.trace ℂ V (T ^ k) =
      ∑ μ ∈ hfin.toFinset, (Module.finrank ℂ (T.maxGenEigenspace μ) : ℂ) * μ ^ k := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    T.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top T)
  have hk : ∀ μ, Set.MapsTo (T ^ k) (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) :=
    fun μ => T.mapsTo_maxGenEigenspace_of_comm (Commute.self_pow T k) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds hfin hk]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 := T.mapsTo_maxGenEigenspace_of_comm (Commute.refl T) μ
  have hnil := T.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  have hpow : (T ^ k).restrict (hk μ) = (T.restrict h1) ^ k :=
    (Module.End.pow_restrict (f' := T) k h1).symm
  have hA : Set.MapsTo (algebraMap ℂ (Module.End ℂ V) μ) (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) :=
    fun x hx => by simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ μ hx
  have hAe : (algebraMap ℂ (Module.End ℂ V) μ).restrict hA =
      algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace μ)) μ := by
    ext x
    show (algebraMap ℂ (Module.End ℂ V) μ) x.1 = _
    simp [Module.algebraMap_end_apply]
  have hnil' : IsNilpotent (T.restrict h1 - algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace μ)) μ) := by
    rw [← hAe, LinearMap.restrict_sub h1 hA]; exact hnil
  have hcomm : Commute (T.restrict h1) (algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace μ)) μ) :=
    Algebra.commute_algebraMap_right _ _
  have hn2 : IsNilpotent ((T.restrict h1) ^ k - algebraMap ℂ _ (μ ^ k)) := by
    rw [map_pow]
    exact nil_pow_sub hcomm hnil' k
  have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (μ ^ k)
    (Commute.one_left ((T.restrict h1) ^ k)) hn2
  rw [Module.End.one_eq_id, LinearMap.id_comp] at this
  rw [hpow, this, LinearMap.trace_id]
  ring
end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
