-- Prove2me | solution 1 for PIW.AdelClassFin.DictRing.af_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:11.792305+00:00
-- url     : https://prove2.me/submissions/aaa1265f-9513-4630-b084-01ea8ed9fe3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Theorems.Thm_PIW_AdelClassFin_DictRing_comp_algebraMap
import Theorems.Thm_PIW_AdelClassFin_DictRing_int_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
theorem _root_.solution (a : Af F) : ∃ m : ℕ, 0 < m ∧ (m : Af F) * a ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (a v ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb0 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  let T := hfin.toFinset
  let mv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => Ideal.absNorm (Ideal.span {b v})
  have hmv : ∀ v, 0 < mv v := fun v => by
    refine Nat.pos_of_ne_zero ?_
    simp only [mv, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero (hb0 v)
  refine ⟨∏ v ∈ T, mv v, Finset.prod_pos fun v _ => hmv v, ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((∏ w ∈ T, mv w : ℕ) : Af F) v * a v ∈ v.adicCompletionIntegers F := by
    intro v
    have hcast : ((∏ w ∈ T, mv w : ℕ) : Af F) = algebraMap (𝓞 F) (Af F) ((∏ w ∈ T, mv w : ℕ) : 𝓞 F) :=
      (map_natCast _ _).symm
    rw [hcast, comp_algebraMap]
    by_cases hv : v ∈ T
    · have hdvd : (b v : 𝓞 F) ∣ ((∏ w ∈ T, mv w : ℕ) : 𝓞 F) := by
        have h1 : ((mv v : ℕ) : 𝓞 F) ∈ Ideal.span {b v} := Ideal.absNorm_mem _
        rw [Ideal.mem_span_singleton] at h1
        exact h1.trans (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem mv hv))
      obtain ⟨d, hd⟩ := hdvd
      rw [hd, map_mul, mul_comm (algebraMap (𝓞 F) (v.adicCompletion F) (b v)), mul_assoc]
      exact mul_mem (int_mem d v) (by rw [mul_comm]; exact hb v)
    · have : a v ∈ v.adicCompletionIntegers F := by simpa [T] using hv
      exact mul_mem (int_mem _ v) this
  exact key
end PIW.AdelClassFin.DictRing
