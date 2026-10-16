-- Prove2me | solution 1 for OAI.WeightedGenerator.weakDefect_spectral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:27:43.425345+00:00
-- url     : https://prove2.me/submissions/e831273e-ef2e-4b3d-a815-c6e79afe3ca1

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean:L779-L815
-- (upload_full_project.md Phase 4): solution for node OAI.WeightedGenerator.weakDefect_spectral. The node keeps its source
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
import Theorems.Thm_OAI_WeightedGenerator_centered_raising_coordinate

-- ---- from OAI.MathematicalPhysics.Fock.Operators ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate

namespace WeightedShift
variable {I J : Type*}
variable [DecidableEq I] [DecidableEq J]

end WeightedShift

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace CrossEnsemble
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem trace_norm_summable (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((square_coordinates_summable b hu).add (square_coordinates_summable b hv))
  intro ij
  rw [norm_mul, norm_inner_symm (v ij.1)]
  nlinarith [sq_nonneg (‖inner ℂ (b ij.2) (u ij.1)‖-‖inner ℂ (b ij.2) (v ij.1)‖)]

end CrossEnsemble

namespace CrossEnsemble
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

end

end

end OAI

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

theorem centered_lowering_coordinate (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    inner ℂ (b l) (centeredLadder j μ false (x r))=
      (Real.sqrt (p r):ℂ)*centeredEntry b p x j μ l r := by
  classical
  have hw : inverseWeight 1 (inverseWeight 2 (x r))=(Real.sqrt (p r):ℂ) • b r := by
    change (inverseWeight 1 ∘L inverseWeight 2) (x r)=_
    rw [← inverseWeight_add]; exact hi r
  have hb : inner ℂ (b l) (b r)=if l=r then 1 else 0 := orthonormal_iff_ite.mp b.orthonormal l r
  have hd := spectralGain_lowering b p hp x j l r
  change inner ℂ (b l) (lowering j (inverseWeight 2 (x r)))=_ at hd
  simp only [centeredLadder, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, inner_sub_right, inner_smul_right, hw, hd, hb, centeredEntry]
  split_ifs <;> ring

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem pairing_rows (b : HilbertBasis J ℂ E) (u v : I → E)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) :
    HasSum (fun a : I × J => inner ℂ (v a.1) (b a.2)*inner ℂ (b a.2) (Z (u a.1)))
      (pairing u v Z) := by
  have hs : Summable (fun a : I × J => inner ℂ (v a.1) (b a.2)*inner ℂ (b a.2) (Z (u a.1))) := by
    simpa only [mul_comm] using (trace_norm_summable b (applied_summable hu Z) hv).of_norm
  have ht := hs.hasSum.prod_fiberwise (fun i => b.hasSum_inner_mul_inner (v i) (Z (u i)))
  have he := ht.unique (pairing_summable hu hv Z).hasSum
  change HasSum _ (∑' i, inner ℂ (v i) (Z (u i)))
  rw [← he]
  exact hs.hasSum

theorem pairing_columns (b : HilbertBasis J ℂ E) (u v : I → E)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) :
    HasSum (fun a : I × J => inner ℂ (v a.1) (Z (b a.2))*inner ℂ (b a.2) (u a.1))
      (pairing u v Z) := by
  have hh := pairing_rows b u (fun i => Z.adjoint (v i)) hu (applied_summable hv Z.adjoint)
    (ContinuousLinearMap.id ℂ E)
  simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_inner_left, pairing] using hh
end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem weakDefect_spectral (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ r, 0<p r) (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (t : ℝ) (j : Fin n) (μ : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun a : J × J => (defectCoefficient t (p a.1) (p a.2):ℂ)*
      conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2)))
      (weakDefect t x j μ Z) := by
  have hw := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hd := centeredLadder_summable x hx j μ false
  have hu := centeredLadder_summable x hx j μ true
  have hr := (Equiv.prodComm J J).hasSum_iff.mpr
    (CrossEnsemble.pairing_rows b (fun r => inverseWeight 3 (x r))
      (fun r => centeredLadder j μ false (x r)) hw hd Z)
  have hl := CrossEnsemble.pairing_columns b (fun r => centeredLadder j μ true (x r))
      (fun r => inverseWeight 3 (x r)) hu hw Z
  have he₁ (a : J × J) :
      inner ℂ (centeredLadder j μ false (x a.2)) (b a.1)*
        inner ℂ (b a.1) (Z (inverseWeight 3 (x a.2)))=
      (p a.2:ℂ)*conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2)) := by
    rw [← inner_conj_symm, centered_lowering_coordinate b p hp x hi, hi, map_smul, inner_smul_right,
      map_mul, Complex.conj_ofReal]
    have hs : (Real.sqrt (p a.2):ℂ)^2=(p a.2:ℂ) := by exact_mod_cast Real.sq_sqrt (hp a.2).le
    linear_combination conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2))*hs
  have he₂ (a : J × J) :
      inner ℂ (inverseWeight 3 (x a.1)) (Z (b a.2))*
        inner ℂ (b a.2) (centeredLadder j μ true (x a.1))=
      (p a.1:ℂ)*conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2)) := by
    rw [centered_raising_coordinate b p hp x hi, hi, inner_smul_left, Complex.conj_ofReal]
    have hs : (Real.sqrt (p a.1):ℂ)^2=(p a.1:ℂ) := by exact_mod_cast Real.sq_sqrt (hp a.1).le
    linear_combination conj (centeredEntry b p x j μ a.1 a.2)*inner ℂ (b a.1) (Z (b a.2))*hs
  simp only [Equiv.prodComm_apply, Function.comp_def, Prod.swap, he₁] at hr
  simp only [he₂] at hl
  convert! (hr.mul_left (t+1:ℂ)).sub (hl.mul_left (t:ℂ)) using 1
  ext a
  simp only [defectCoefficient, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_mul]
  ring

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
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate


theorem solution : type_of% @_root_.OAI.WeightedGenerator.weakDefect_spectral := @_root_.OAI.WeightedGenerator.weakDefect_spectral
