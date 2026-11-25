-- Prove2me | solution 1 for PI.VolStabW.archPos_of_lb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:49.6896+00:00
-- url     : https://prove2.me/submissions/ceeee17a-2a25-4601-aa49-66f18f7cc0b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FreeOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensPos
import Theorems.Thm_PI_VolStabW_LocPosW_pos_of_lb
import Theorems.Thm_PI_VolStabW_LocPosW_gramR_ratTup
import Theorems.Thm_PI_VolStabW_continuous_gramH
import Theorems.Thm_PI_VolStabW_isUnit_det_hermOf
import Theorems.Thm_PI_VolStabW_linIndep_of_isUnit_det
import Theorems.Thm_PI_VolStabW_sigma_invol
import Theorems.Thm_PI_VolStabW_tensAll_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal
open LocPosW
namespace PI.VolStabW
theorem _root_.solution (hL : LBInf) : ArchPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Ainf F) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  have hX1U : X1 ∈ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset t7 hX1U
  obtain ⟨φ, hφ1, hφ0, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := X1)) isOpen_interior.isClosed_compl
    (disjoint_singleton_left.2 fun h => h hxK)
  have hsupp : Function.support φ ⊆ interior K := fun X hX => by
    by_contra h
    exact hX (hφ0 h)
  have hts : tsupport φ ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    (closure_mono hsupp).trans ((closure_minimal interior_subset hK.isClosed).trans hKU)
  let W : Set (Fin a → Fin M → Ainf F ⊗[F] E) := {X | (1 / 2 : ℝ) < φ X}
  have hWo : IsOpen W := isOpen_lt continuous_const φ.continuous
  have hX1W : X1 ∈ W := by
    show (1 / 2 : ℝ) < φ X1
    rw [hφ1 (mem_singleton X1)]
    norm_num
  have hWU : W ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    fun X hX => hts (subset_tsupport _ (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hX).ne')
  obtain ⟨c, hc0, hctop, N, hN, hlb⟩ :=
    hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ.1 hν.1 W hWo hX1W
  have hpos := pos_of_lb (f' := gramH (Ainf F) σ hσ J hJ.1) Subtype.val_injective hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) φ.continuous hφc hts
    (fun X => (hφr X).1) hWU (by norm_num : (0 : ℝ) < 1 / 2) (fun X hX => hX.le) hc0 hctop hN hlb
    (fun O hO hne => (hO.measure_pos νinf hne).ne') (νinf.finiteAt_nhds _)
  refine ⟨fun X => ((φ X : ℝ) : ℂ), Complex.continuous_ofReal.comp φ.continuous,
    hφc.comp_left Complex.ofReal_zero, ?_⟩
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'
end PI.VolStabW
