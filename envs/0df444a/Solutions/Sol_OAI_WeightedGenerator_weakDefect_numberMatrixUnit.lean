-- Prove2me | solution 1 for OAI.WeightedGenerator.weakDefect_numberMatrixUnit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:29:18.67927+00:00
-- url     : https://prove2.me/submissions/2275f27b-3424-4a28-97c2-75912a8d15d1

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean:L984-L1021
-- (upload_full_project.md Phase 4): solution for node OAI.WeightedGenerator.weakDefect_numberMatrixUnit. The node keeps its source
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

-- ---- from OAI.InformationTheory.PhotonNumber.ThermalMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric

section
open EntropyPhotonNumber DiagonalForms.System

end

section
open DiagonalForms.System

end

section
open EntropyPhotonNumber
variable {J : Type*}

end

section
variable {J : Type*}

end

open scoped ComplexConjugate
variable {J : Type*}

end ThermalMetric

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ} {J : Type*}

theorem centeredLadder_summable (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (μ : ℂ) (up : Bool) :
    Summable (fun r => ‖centeredLadder j μ up (x r)‖^2) :=
  CrossEnsemble.applied_summable hx _

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalMetric
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ}

theorem lowering_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    lowering j (inverseWeight 2 x) k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  rw [lowering_apply]
  change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
  rw [← inverseWeight_add]

theorem raising_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    raising j (inverseWeight 2 x) k=
      (Real.sqrt (k j:ℝ):ℂ)*inverseWeight 3 x (down j k) := by
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp only [raising_zero j _ k hk, hk, Nat.cast_zero, Real.sqrt_zero,
      Complex.ofReal_zero, zero_mul]
  · rw [raising_up]
    change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
    rw [← inverseWeight_add, up_same, down_up]
    norm_cast
end Annihilation

namespace EntropyPhotonNumber
open Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem inverseColumns_entry (x : J → Fock n) (hx : Summable (fun j => ‖x j‖^2))
    (ρ : State n)
    (he : CrossEnsemble.operator (fun j => inverseWeight 3 (x j)) (fun j => inverseWeight 3 (x j))=ρ.op)
    (a b : NumberIndex n) :
    HasSum (fun j => inverseWeight 3 (x j) a*conj (inverseWeight 3 (x j) b)) (entry ρ.op a b) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  simpa only [he, numberKet_inner, inner_numberKet, entry] using
    CrossEnsemble.entry_hasSum hi hi (numberKet a) (numberKet b)

theorem weakDefect_numberMatrixUnit (t : ℝ) (x : J → Fock n)
    (hx : Summable (fun j => ‖x j‖^2)) (ρ : State n)
    (he : CrossEnsemble.operator (fun j => inverseWeight 3 (x j)) (fun j => inverseWeight 3 (x j))=ρ.op)
    (j : Fin n) (μ : ℂ) (a b : NumberIndex n) :
    weakDefect t x j μ (numberMatrixUnit a b)=
      (t+1:ℂ)*(Real.sqrt ((a j:ℝ)+1):ℂ)*entry ρ.op b (up j a)-
      (t:ℂ)*(Real.sqrt (b j:ℝ):ℂ)*entry ρ.op (down j b) a-
      conj μ*entry ρ.op b a := by
  have hw := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have h₀ := inverseColumns_entry x hx ρ he b a
  have h₁ := inverseColumns_entry x hx ρ he b (up j a)
  have h₂ := inverseColumns_entry x hx ρ he (down j b) a
  have hi (y : Fock n) : inverseWeight 1 (inverseWeight 2 y)=inverseWeight 3 y := by
    change (inverseWeight 1 ∘L inverseWeight 2) y=_
    rw [← inverseWeight_add]
  have hl : CrossEnsemble.pairing (fun r => inverseWeight 3 (x r))
      (fun r => centeredLadder j μ false (x r)) (numberMatrixUnit a b)=
        (Real.sqrt ((a j:ℝ)+1):ℂ)*entry ρ.op b (up j a)-conj μ*entry ρ.op b a := by
    apply (CrossEnsemble.pairing_summable hw (centeredLadder_summable x hx j μ false) _).hasSum.unique
    convert! (h₁.mul_left (Real.sqrt ((a j:ℝ)+1):ℂ)).sub (h₀.mul_left (conj μ)) using 1
    ext r
    simp only [numberMatrixUnit_inner, centeredLadder, Bool.false_eq_true, ↓reduceIte,
      ContinuousLinearMap.comp_apply, sub_apply, smul_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hi, lowering_weighted_apply,
      map_sub, map_mul, Complex.conj_ofReal]
    ring
  have hu : CrossEnsemble.pairing (fun r => centeredLadder j μ true (x r))
      (fun r => inverseWeight 3 (x r)) (numberMatrixUnit a b)=
        (Real.sqrt (b j:ℝ):ℂ)*entry ρ.op (down j b) a-conj μ*entry ρ.op b a := by
    apply (CrossEnsemble.pairing_summable (centeredLadder_summable x hx j μ true) hw _).hasSum.unique
    convert! (h₂.mul_left (Real.sqrt (b j:ℝ):ℂ)).sub (h₀.mul_left (conj μ)) using 1
    ext r
    simp only [numberMatrixUnit_inner, centeredLadder, ↓reduceIte,
      ContinuousLinearMap.comp_apply, sub_apply, smul_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hi, raising_weighted_apply]
    ring
  rw [weakDefect, hl, hu]
  ring
end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open Annihilation WeightedGenerator
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

end

end OAI

-- ---- platform node ----
open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate


theorem solution : type_of% @_root_.OAI.WeightedGenerator.weakDefect_numberMatrixUnit := @_root_.OAI.WeightedGenerator.weakDefect_numberMatrixUnit
