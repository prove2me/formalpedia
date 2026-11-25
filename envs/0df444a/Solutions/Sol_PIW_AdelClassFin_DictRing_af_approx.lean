-- Prove2me | solution 1 for PIW.AdelClassFin.DictRing.af_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:08.745889+00:00
-- url     : https://prove2.me/submissions/4f447e81-7452-41f4-87e9-406e7144c4de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Theorems.Thm_PIW_AdelClassFin_DictRing_comp_algebraMap
import Theorems.Thm_PIW_AdelClassFin_DictRing_val_alg
import Theorems.Thm_PIW_AdelClassFin_DictRing_val_int
import Theorems.Thm_PIW_AdelClassFin_DictRing_cancel
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_StrongApproxE_DedekindLFunctions_sa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictRing
variable {F : Type} [Field F] [NumberField F]
namespace PIW.AdelClassFin.DictRing
theorem _root_.solution (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (N : ℕ) (hN : 0 < N) :
    ∃ β : 𝓞 F, ∃ y ∈ Formalism.UG.intAd F, a = algebraMap (𝓞 F) (Af F) β + (N : Af F) * y := by
  classical
  have ha' : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (a v) ≤ 1 := ha
  set n : 𝓞 F := (N : 𝓞 F) with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast hN.ne'
  have hnF : algebraMap (𝓞 F) F n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hn0
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | v.valuation F (algebraMap (𝓞 F) F n) < 1}.Finite := by
    simp_rw [HeightOneSpectrum.valuation_lt_one_iff_dvd]
    apply Ideal.finite_factors
    simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
  let T := hTfin.toFinset
  have hν0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≠ 0 := by
    intro v
    rw [val_int]
    exact (Valuation.ne_zero_iff _).2 hnF
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≤ 1 := by
    intro v
    rw [val_int]
    exact v.valuation_le_one n
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : F,
      Valued.v (algebraMap F (v.adicCompletion F) k - a v) <
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
    intro v
    have hx0 : algebraMap (𝓞 F) (v.adicCompletion F) n ≠ 0 := (Valuation.ne_zero_iff _).1 (hν0 v)
    have hs : {x : v.adicCompletion F | Valued.v (x - a v) <
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n)} ∈ nhds (a v) :=
      Valued.mem_nhds.mpr ⟨Units.mk0 (Valued.v.restrict (algebraMap (𝓞 F) (v.adicCompletion F) n))
        ((Valuation.ne_zero_iff _).2 hx0), fun y hy => by simpa [Valuation.restrict_lt_iff] using hy⟩
    obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
      mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (v := v) (a v)) _ hs
    exact ⟨k, hy⟩
  choose k hk using hloc
  obtain ⟨t, ht1, ht2⟩ := PI.StrongApproxE.DedekindLFunctions.sa (R := 𝓞 F) (K := F) T k
    (fun _ => algebraMap (𝓞 F) F n) (fun _ _ => hnF)

  have hclose : ∀ v ∈ T, Valued.v (a v - algebraMap F (v.adicCompletion F) t) ≤
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
    intro v hv
    have e : a v - algebraMap F (v.adicCompletion F) t =
        -(algebraMap F (v.adicCompletion F) (k v) - a v) + algebraMap F (v.adicCompletion F) (k v - t) := by
      rw [map_sub]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]; exact (hk v).le
    · rw [val_alg, Valuation.map_sub_swap, val_int]; exact ht1 v hv
  have htint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F t ≤ 1 := by
    intro v
    by_cases hv : v ∈ T
    · rw [← val_alg]
      have e : algebraMap F (v.adicCompletion F) t = a v - (a v - algebraMap F (v.adicCompletion F) t) := by ring
      rw [e]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha' v) ((hclose v hv).trans (hν1 v)))
    · exact ht2 v hv
  obtain ⟨β, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) t htint
  have hu : IsUnit (algebraMap (𝓞 F) (Af F) n) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    exact (Ne.isUnit hnF).map (algebraMap F (Af F))
  set y : Af F := ↑hu.unit⁻¹ * (a - algebraMap (𝓞 F) (Af F) β) with hy
  have hNy : algebraMap (𝓞 F) (Af F) n * y = a - algebraMap (𝓞 F) (Af F) β := by
    rw [hy, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hNcast : (N : Af F) = algebraMap (𝓞 F) (Af F) n := by rw [hn, map_natCast]
  refine ⟨β, y, ?_, by rw [hNcast, hNy]; ring⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F := by
    intro v
    have hv' : algebraMap (𝓞 F) (v.adicCompletion F) n * y v =
        a v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F β) := by
      have := congrArg (fun z : Af F => z v) hNy
      rw [← IsScalarTower.algebraMap_apply, ← comp_algebraMap, ← comp_algebraMap]
      exact this
    have hle : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) * Valued.v (y v) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
      rw [← Valuation.map_mul, hv']
      by_cases hv : v ∈ T
      · exact hclose v hv
      · have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) = 1 := by
          refine le_antisymm (hν1 v) (not_lt.mp ?_)
          rw [val_int]
          simpa [T] using hv
        rw [h1]
        refine (Valuation.map_sub _ _ _).trans (max_le (ha' v) ?_)
        rw [val_alg]; exact htint v
    exact cancel (hν0 v) hle
  exact key
end PIW.AdelClassFin.DictRing
