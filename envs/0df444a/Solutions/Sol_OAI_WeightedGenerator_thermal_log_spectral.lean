-- Prove2me | solution 1 for OAI.WeightedGenerator.thermal_log_spectral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:33:09.268683+00:00
-- url     : https://prove2.me/submissions/ed0b6a89-67ab-4d19-a076-2818a0fc34ca

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Gibbs.lean:L844-L875
-- (upload_full_project.md Phase 4): solution for node OAI.WeightedGenerator.thermal_log_spectral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Theorems.Thm_OAI_WeightedGenerator_dissipator_log_sum

-- ---- from OAI.InformationTheory.PhotonNumber.Gibbs ----
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace TraceEnsemble

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber

end EntropyPhotonNumber

namespace WeightedShift
open scoped BigOperators ComplexConjugate
variable {I K : Type*} [DecidableEq K]

end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type*}

end EntropyPhotonNumber

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {I J K : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open Annihilation CrossEnsemble
variable {n : ℕ} {J : Type*}

end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

variable {n : ℕ} {k : ℝ} {ρ : State n}

namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {J : Type*}

theorem log_difference_summable (b : HilbertBasis J ℂ (Fock n))
    (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (j : Fin n) (u : Bool) :
    Summable (fun a : J × J => (c a.1-c a.2)*‖spectralGain b x j u a.1 a.2‖^2) := by
  simpa only [sub_mul] using (crossed_log_summable b x hx S c hc hf j u).sub
    (uncrossed_log_summable b x hx S hS c hc he j u)

theorem thermal_log_spectral (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (t : ℝ) :
    (pairing t x S).re = ∑ j, ∑' a : J × J,
      (c a.1-c a.2)*((t+1)*p a.2-t*p a.1)*‖loweringEntry b p x j a.1 a.2‖^2 := by
  unfold pairing
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [dissipator_log_sum b x hx S hS c hc hf he j false,
    dissipator_log_sum b x hx S hS c hc hf he j true]
  have hd := log_difference_summable b x hx S hS c hc hf he j false
  have hu := (log_difference_summable b x hx S hS c hc hf he j true).prod_symm
  simp only [Prod.swap] at hu
  rw [← (Equiv.prodComm J J).tsum_eq
      (fun a : J × J => (c a.1-c a.2)*‖spectralGain b x j true a.1 a.2‖^2)]
  change (t+1)*(∑' a : J × J, (c a.1-c a.2)*‖spectralGain b x j false a.1 a.2‖^2)+
    t*(∑' a : J × J, (c a.2-c a.1)*‖spectralGain b x j true a.2 a.1‖^2)=_
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hd.mul_left (t+1)).tsum_add (hu.mul_left t)]
  apply tsum_congr
  intro a
  rw [spectralGain_lowering_sq b p hp, spectralGain_raising_sq b p hp x hi]
  ring

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open EntropyPhotonNumber Annihilation


theorem solution : type_of% @_root_.OAI.WeightedGenerator.thermal_log_spectral := @_root_.OAI.WeightedGenerator.thermal_log_spectral
