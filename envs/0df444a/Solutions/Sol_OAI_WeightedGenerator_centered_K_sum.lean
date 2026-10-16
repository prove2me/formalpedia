-- Prove2me | solution 1 for OAI.WeightedGenerator.centered_K_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:24:51.959498+00:00
-- url     : https://prove2.me/submissions/bbb35541-88a4-4ba2-b702-2708008cc979

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean:L615-L635
-- (upload_full_project.md Phase 4): solution for node OAI.WeightedGenerator.centered_K_sum. The node keeps its source
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

 theorem canonical_norm_identity (j : Fin n) (x : Fock n) :
    ‖raising j x‖^2 = ‖lowering j x‖^2+‖inverseWeight 1 x‖^2 := by
  have hh := (lowering_norm_sum j x).add (WeightedShift.hasSum_square (inverseWeight 1 x))
  have he : HasSum (fun k : NumberIndex n => ((k j:ℝ)+1)*‖inverseWeight 1 x k‖^2)
      (‖lowering j x‖^2+‖inverseWeight 1 x‖^2) := by
    convert! hh using 1
    ext k
    ring
  exact (raising_norm_sum j x).unique he

end Annihilation

namespace CrossEnsemble
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

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

theorem centered_canonical_norm (j : Fin n) (x : Fock n) (μ : ℂ) :
    ‖raising j x-conj μ • inverseWeight 1 x‖^2 =
      ‖lowering j x-μ • inverseWeight 1 x‖^2+‖inverseWeight 1 x‖^2 := by
  have ha := ladder_adjoint_pairing j x x
  have hc : (inner ℂ (raising j x) (conj μ • inverseWeight 1 x)).re =
      (inner ℂ (lowering j x) (μ • inverseWeight 1 x)).re := by
    rw [inner_smul_right, inner_smul_right, ha]
    have he := inner_conj_symm (𝕜 := ℂ) (inverseWeight 1 x) (raising j x)
    calc
      _ = (conj (μ*inner ℂ (inverseWeight 1 x) (raising j x))).re := by
        rw [map_mul, ← he]
        simp
      _ = _ := Complex.conj_re _
  change RCLike.re (inner ℂ (raising j x) (conj μ • inverseWeight 1 x)) =
    RCLike.re (inner ℂ (lowering j x) (μ • inverseWeight 1 x)) at hc
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), hc, norm_smul, norm_smul, Complex.norm_conj,
    canonical_norm_identity]
  ring

theorem centeredLadder_summable (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (μ : ℂ) (up : Bool) :
    Summable (fun r => ‖centeredLadder j μ up (x r)‖^2) :=
  CrossEnsemble.applied_summable hx _

theorem centeredLadder_ccr (x : Fock n) (j : Fin n) (μ : ℂ) :
    ‖centeredLadder j μ true x‖^2=‖centeredLadder j μ false x‖^2+‖inverseWeight 3 x‖^2 := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simpa only [centeredLadder, Bool.false_eq_true, ↓reduceIte,
    ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, hw] using centered_canonical_norm j (inverseWeight 2 x) μ

theorem centeredLadder_ensemble_gap (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hn : HasSum (fun r => ‖inverseWeight 3 (x r)‖^2) 1) (μ : Fin n → ℂ) :
    (∑ j, ∑' r, ‖centeredLadder j (μ j) true (x r)‖^2) =
      (∑ j, ∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)+(n:ℝ) := by
  have hj (j : Fin n) : (∑' r, ‖centeredLadder j (μ j) true (x r)‖^2) =
      (∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)+1 := by
    simp only [centeredLadder_ccr]
    exact ((centeredLadder_summable x hx j (μ j) false).hasSum.add hn).tsum_eq
  simp only [hj, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

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

theorem centered_down_sq (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    ‖inner ℂ (b l) (centeredLadder j μ false (x r))‖^2=
      p r*‖centeredEntry b p x j μ l r‖^2 := by
  rw [centered_lowering_coordinate b p hp x hi, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp r).le]

theorem centered_up_sq (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    ‖inner ℂ (b r) (centeredLadder j μ true (x l))‖^2=
      p l*‖centeredEntry b p x j μ l r‖^2 := by
  rw [centered_raising_coordinate b p hp x hi, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp l).le, Complex.norm_conj]

theorem centered_down_sum (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) :
    (∑' a : J × J, p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2)=
      ∑' r, ‖centeredLadder j μ false (x r)‖^2 := by
  have hs := (CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j μ false)).prod_symm
  simp only [Prod.swap] at hs
  simp only [← centered_down_sq b p hp x hi]
  rw [hs.tsum_prod]
  calc
    _ = ∑' (r : J) (l : J), ‖inner ℂ (b l) (centeredLadder j μ false (x r))‖^2 :=
      (Summable.tsum_comm (f := fun l r : J => ‖inner ℂ (b l) (centeredLadder j μ false (x r))‖^2) hs).symm
    _ = _ := by simp only [(TraceEnsemble.basis_hasSum_norm_sq b _).tsum_eq]

theorem centered_up_sum (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) :
    (∑' a : J × J, p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2)=
      ∑' l, ‖centeredLadder j μ true (x l)‖^2 := by
  have hs := CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j μ true)
  simp only [← centered_up_sq b p hp x hi]
  rw [hs.tsum_prod]
  simp only [(TraceEnsemble.basis_hasSum_norm_sq b _).tsum_eq]

theorem centered_K_sum (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (hn : HasSum (fun r => ‖inverseWeight 3 (x r)‖^2) 1) (μ : Fin n → ℂ) (t : ℝ) :
    (∑ j, ∑' a : J × J, ((t+1)*p a.2-t*p a.1)*‖centeredEntry b p x j (μ j) a.1 a.2‖^2)=
      (∑ j, ∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)-(n:ℝ)*t := by
  have hj (j : Fin n) :
      (∑' a : J × J, ((t+1)*p a.2-t*p a.1)*‖centeredEntry b p x j (μ j) a.1 a.2‖^2)=
      (t+1)*(∑' r, ‖centeredLadder j (μ j) false (x r)‖^2)-
      t*(∑' r, ‖centeredLadder j (μ j) true (x r)‖^2) := by
    have hd := (CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j (μ j) false)).prod_symm
    have hu := CrossEnsemble.square_coordinates_summable b (centeredLadder_summable x hx j (μ j) true)
    simp only [Prod.swap, centered_down_sq b p hp x hi] at hd
    simp only [centered_up_sq b p hp x hi] at hu
    simp only [sub_mul, mul_assoc]
    rw [(hd.mul_left (t+1)).tsum_sub (hu.mul_left t), tsum_mul_left, tsum_mul_left,
      centered_down_sum b p hp x hx hi, centered_up_sum b p hp x hx hi]
  simp only [hj, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [centeredLadder_ensemble_gap x hx hn μ]
  ring
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
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators


theorem solution : type_of% @_root_.OAI.WeightedGenerator.centered_K_sum := @_root_.OAI.WeightedGenerator.centered_K_sum
