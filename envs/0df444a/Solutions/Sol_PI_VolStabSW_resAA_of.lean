-- Prove2me | solution 1 for PI.VolStabSW.resAA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:18:18.537975+00:00
-- url     : https://prove2.me/submissions/555af6fa-fbaf-46e2-851c-a3bce8eedc28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensAAOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isCompact_latV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
namespace PI.VolStabSW
theorem _root_.solution (hV : VolAA) (hL : LatFacts) (hH : HensAA) (hI : IdxAA) (hC : CntAA) :
    ResAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  filter_upwards [hV F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b,
    hH F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hI F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hC F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b] with v hv hh hi hc
  intro μv hμ νv hν
  have := hμ.1
  have := hν.1
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hL F E σ d b a M v
  refine ⟨latSub b v a M, lamF b v a M, hF b v σ a, rfl,
    (PositiveNearLattice.isClopen_latV b v a M).isOpen, PositiveNearLattice.isCompact_latV b v a M, l4, l1, l2, l3,
    l5, l6, l7, hh, ?_⟩
  obtain ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, hcard, hcnt⟩ :=
    hc μv hμ.1
  refine ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, ?_, ?_⟩
  · rw [hcard]; rfl
  obtain ⟨e1, e2⟩ := hi μv νv hμ.1 hν.1
  rw [hv.1 μv hμ, ← hcard] at e1
  rw [hv.2 νv hν, ← hcard] at e2
  show (μv (latV b v ∩ _) / νv _).toReal = _
  rw [hcnt, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have f1 := congrArg ENNReal.toReal e1
  have f2 := congrArg ENNReal.toReal e2
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_one] at f1 f2
  have hq : (0 : ℝ) < Nat.card k := by exact_mod_cast Nat.card_pos
  have hle : a ^ 2 ≤ 2 * M * a := by nlinarith
  have hp : (Nat.card k : ℝ) ^ (2 * M * a) = (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
      (Nat.card k : ℝ) ^ (a ^ 2) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hA : (0 : ℝ) < (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) := pow_pos hq _
  have hB : (0 : ℝ) < (Nat.card k : ℝ) ^ (a ^ 2) := pow_pos hq _
  rw [hp] at f1
  have hn : (νv (hF b v σ a 0)).toReal = 1 / (Nat.card k : ℝ) ^ (a ^ 2) := by
    field_simp; linarith
  have hm : (μv (lamF b v a M 0)).toReal =
      1 / ((Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) * (Nat.card k : ℝ) ^ (a ^ 2)) := by
    field_simp; linarith
  rw [hm, hn]
  field_simp
end PI.VolStabSW
