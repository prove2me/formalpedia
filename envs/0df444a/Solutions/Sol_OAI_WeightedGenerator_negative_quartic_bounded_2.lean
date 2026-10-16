-- Prove2me | solution 2 for OAI.WeightedGenerator.negative_quartic_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:43:07.227506+00:00
-- url     : https://prove2.me/submissions/30272d60-32be-4fd5-a427-a895e38a3566

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean:L907-L961
-- (upload_full_project.md Phase 4): solution for node OAI.WeightedGenerator.negative_quartic_bounded. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum

-- ---- from OAI.InformationTheory.PhotonNumber.Minimum ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology _root_.Complex _root_.OAI.Complex Metric
open MeasureTheory Set Filter Topology _root_.Complex _root_.OAI.Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology _root_.Complex _root_.OAI.Complex MeasureTheory

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp BeamLadder
open scoped ComplexConjugate
variable {n : ℕ}

end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace TensorLp
variable {A B I J : Type*}
end TensorLp

namespace EntropyPhotonNumber.WeightedColumns
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {ρ σ τ : State n}

end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

end

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

section
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ σ τ : State n}

end

open QuantumTrace
variable {n : ℕ}

end EntropyPhotonNumber.WeightedColumns

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace WeightedColumns
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber
open QuantumTrace WeightedColumns
variable {n : ℕ}

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators ComplexConjugate

section
open TensorLp KrausBounded BeamLadder
variable {n : ℕ}

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

section
open scoped BigOperators

namespace WeightedGenerator

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
end

theorem negative_quartic_bounded (a b c d : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → -4*t^4+a*t^3+b*t^2+c*t+d ≤ C := by
  let S : ℝ := 1+|a|+|b|+|c|+|d|
  have hS : 1 ≤ S := by dsimp [S]; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  have ha : a ≤ |a| := le_abs_self a
  have hb : b ≤ |b| := le_abs_self b
  have hc : c ≤ |c| := le_abs_self c
  have hd : d ≤ |d| := le_abs_self d
  have hsa : 0 ≤ |a| := abs_nonneg a
  have hsb : 0 ≤ |b| := abs_nonneg b
  have hsc : 0 ≤ |c| := abs_nonneg c
  have hsd : 0 ≤ |d| := abs_nonneg d
  refine ⟨S*(S^3+S^2+S+1), ?_⟩
  intro t ht
  have htop : -4*t^4+a*t^3+b*t^2+c*t+d ≤ |a| *t^3+|b| *t^2+|c| *t+|d| := by
    nlinarith [mul_le_mul_of_nonneg_right ha (pow_nonneg ht 3),
      mul_le_mul_of_nonneg_right hb (sq_nonneg t), mul_le_mul_of_nonneg_right hc ht,
      pow_nonneg ht 4]
  have hC : 0 ≤ S*(S^3+S^2+S+1) := by positivity
  by_cases h : t ≤ S
  · have h₁ : |a| *t^3 ≤ S*S^3 := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact pow_le_pow_left₀ ht h 3
      · positivity
      · linarith
    have h₂ : |b| *t^2 ≤ S*S^2 := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact pow_le_pow_left₀ ht h 2
      · positivity
      · linarith
    have h₃ : |c| *t ≤ S*S := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact h
      · exact ht
      · linarith
    have h₄ : |d| ≤ S := by dsimp [S]; linarith
    nlinarith
  · have htS : S ≤ t := (lt_of_not_ge h).le
    have ht1 : 1 ≤ t := hS.trans htS
    have ht2 : t ≤ t^2 := by nlinarith
    have ht3 : t^2 ≤ t^3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
    have h₁ := mul_le_mul_of_nonneg_left ht3 hsb
    have h₂ := mul_le_mul_of_nonneg_left (ht2.trans ht3) hsc
    have h₃ := mul_le_mul_of_nonneg_left (ht1.trans (ht2.trans ht3)) hsd
    have h₄ : (|a|+|b|+|c|+|d|)*t^3 ≤ t^4 := by
      have hs : |a|+|b|+|c|+|d| ≤ t := by dsimp [S] at htS; linarith
      simpa only [← pow_succ'] using mul_le_mul_of_nonneg_right hs (pow_nonneg ht 3)
    have ht4 : 0 ≤ t^4 := pow_nonneg ht 4
    have hlead : a*t^3+b*t^2+c*t+d ≤ (|a|+|b|+|c|+|d|)*t^3 := by
      nlinarith [mul_le_mul_of_nonneg_right ha (pow_nonneg ht 3),
        mul_le_mul_of_nonneg_right hb (sq_nonneg t), mul_le_mul_of_nonneg_right hc ht]
    nlinarith

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

namespace ThermalSetup
variable (P : ThermalSetup)
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
end WeightedColumns
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
end

open QuantumTrace ThermalMetric Annihilation
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup

namespace ThermalDual

end ThermalDual
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.WeightedGenerator
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.WeightedGenerator.negative_quartic_bounded := @_root_.OAI.WeightedGenerator.negative_quartic_bounded
