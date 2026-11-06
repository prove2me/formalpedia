-- Prove2me | solution 1 for QEC.Semantics.Davies.spectralGibbsDensity_basis_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:53.268777+00:00
-- url     : https://prove2.me/submissions/cc889810-1b11-43a3-9a92-d9dbf5d26b69

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Theorems.Thm_QEC_Semantics_Davies_spectralGibbsDensity_normalized_exp
import Theorems.Thm_QEC_Semantics_Davies_gibbsPartitionFunction_eq_trace_exp

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace QEC.Semantics.Davies
theorem _root_.solution {ι' : Type} [Fintype ι'] [Nonempty ι']
    (H : Operator V) (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : OrthonormalBasis ι' ℂ V) (f : ι' → ℝ)
    (hb : ∀ i, H (b i) = (e i : ℂ) • b i)
    (hc : ∀ j, H (c j) = (f j : ℂ) • c j) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator = (spectralGibbsDensity c f β).toOperator := by
  rw [spectralGibbsDensity_normalized_exp H b e hb,
    spectralGibbsDensity_normalized_exp H c f hc,
    gibbsPartitionFunction_eq_trace_exp H b e hb,
    gibbsPartitionFunction_eq_trace_exp H c f hc]
end QEC.Semantics.Davies
