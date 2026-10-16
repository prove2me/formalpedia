-- Prove2me | solution 1 for OAI.WeightedGenerator.dissipator_log_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:31:49.403273+00:00
-- url     : https://prove2.me/submissions/b828ce44-989c-4831-bb3a-4de88d7a3f3c

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Gibbs.lean:L580-L636
-- (upload_full_project.md Phase 4): solution for node OAI.WeightedGenerator.dissipator_log_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs

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

theorem log_mode_right (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric)
    (x : Fock n) (c : ℝ)
    (he : S (inverseWeight 1 x) = (c : ℂ) • inverseWeight 5 x)
    (j : Fin n) (u : Bool) :
    inner ℂ (modeBound j u x) (S (inverseWeight 1 x)) =
      ((c*‖unweightedGain j u (inverseWeight 2 x)‖^2 : ℝ) : ℂ) := by
  have hs := hS (modeBound j u x) (inverseWeight 1 x)
  change inner ℂ (S (modeBound j u x)) (inverseWeight 1 x) =
    inner ℂ (modeBound j u x) (S (inverseWeight 1 x)) at hs
  rw [← hs, ← inner_conj_symm, log_mode_left S hS x c he j u, Complex.conj_ofReal]
end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem tsum_prod_columns {I K : Type*} (f : I × K → ℝ) (hs : Summable f)
    (g : K → ℝ) (hc : ∀ k, HasSum (fun i => f (i,k)) (g k)) :
    (∑' a, f a) = ∑' k, g k := by
  rw [hs.tsum_prod, ← Summable.tsum_comm (f := fun i k => f (i,k)) hs]
  exact tsum_congr (fun k => (hc k).tsum_eq)

theorem dissipator_log_sum (b : HilbertBasis J ℂ (Fock n))
    (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (j : Fin n) (u : Bool) :
    (CrossEnsemble.pairing (fun r => gain j u (x r)) (fun r => gain j u (x r)) S-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S+
        CrossEnsemble.pairing (fun r => inverseWeight 1 (x r)) (fun r => modeBound j u (x r)) S)).re =
      ∑' a : J × J, (c a.1-c a.2)*‖spectralGain b x j u a.1 a.2‖^2 := by
  have hcross := crossed_log_summable b x hx S c hc hf j u
  have huncross := uncrossed_log_summable b x hx S hS c hc he j u
  have hg := CrossEnsemble.applied_summable hx (gain j u)
  have hm := CrossEnsemble.applied_summable hx (modeBound j u)
  have hv := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have hgcol (r : J) : HasSum (fun l => c l*‖spectralGain b x j u l r‖^2)
      (inner ℂ (gain j u (x r)) (S (gain j u (x r)))).re := by
    have hi := congrArg (fun T : Fock n →L[ℂ] Fock n => T (x r)) (gain_factor j u)
    change inverseWeight 2 (gain j u (x r)) = unweightedGain j u (inverseWeight 2 (x r)) at hi
    simpa only [hi, spectralGain] using hf (gain j u (x r))
  have hmcol (r : J) : HasSum (fun l => c r*‖spectralGain b x j u l r‖^2)
      (c r*‖unweightedGain j u (inverseWeight 2 (x r))‖^2) :=
    (TraceEnsemble.basis_hasSum_norm_sq b _).mul_left _
  have hxval : (∑' a : J × J, c a.1*‖spectralGain b x j u a.1 a.2‖^2) =
      (CrossEnsemble.pairing (fun r => gain j u (x r)) (fun r => gain j u (x r)) S).re := by
    have ht := tsum_prod_columns (fun a : J × J => c a.1*‖spectralGain b x j u a.1 a.2‖^2)
      hcross (fun r => (inner ℂ (gain j u (x r)) (S (gain j u (x r)))).re) hgcol
    exact ht.trans (Complex.re_tsum (CrossEnsemble.pairing_summable hg hg S)).symm
  have hmval : (∑' a : J × J, c a.2*‖spectralGain b x j u a.1 a.2‖^2) =
      (CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S).re := by
    rw [tsum_prod_columns (fun a : J × J => c a.2*‖spectralGain b x j u a.1 a.2‖^2)
      huncross (fun r => c r*‖unweightedGain j u (inverseWeight 2 (x r))‖^2) hmcol]
    change (∑' r, c r*‖unweightedGain j u (inverseWeight 2 (x r))‖^2) =
      (∑' r, inner ℂ (inverseWeight 1 (x r)) (S (modeBound j u (x r)))).re
    rw [Complex.re_tsum (CrossEnsemble.pairing_summable hm hv S)]
    apply tsum_congr
    intro r
    exact (congrArg Complex.re (log_mode_left S hS _ _ (he r) j u)).symm
  have hequal : CrossEnsemble.pairing (fun r => inverseWeight 1 (x r)) (fun r => modeBound j u (x r)) S =
      CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S := by
    unfold CrossEnsemble.pairing
    apply tsum_congr
    intro r
    rw [log_mode_right S hS _ _ (he _) j u, log_mode_left S hS _ _ (he _) j u]
  calc
    _ = (CrossEnsemble.pairing (fun r => gain j u (x r)) (fun r => gain j u (x r)) S).re-
        (CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S).re := by
      rw [hequal]
      rw [show (2:ℂ)⁻¹ * (CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S + CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S) = CrossEnsemble.pairing (fun r => modeBound j u (x r)) (fun r => inverseWeight 1 (x r)) S by ring]
      exact Complex.sub_re _ _
    _ = _ := by
      rw [← hxval, ← hmval, ← hcross.tsum_sub huncross]
      apply tsum_congr
      intro a
      ring
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
open scoped BigOperators ComplexConjugate


theorem solution : type_of% @_root_.OAI.WeightedGenerator.dissipator_log_sum := @_root_.OAI.WeightedGenerator.dissipator_log_sum
