-- Prove2me | solution 1 for PI.KerIso.FourSqW.orthogonal_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:31.948686+00:00
-- url     : https://prove2.me/submissions/07c8481b-fa13-407a-95bd-773823a25f7d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
import Theorems.Thm_PI_KerIso_FourSqW_trL_apply
import Theorems.Thm_PI_KerIso_FourSqW_tr_swap
import Theorems.Thm_PI_KerIso_FourSqW_tr_self_rat
import Theorems.Thm_PI_KerIso_FourSqW_exists_orth
import Theorems.Thm_PI_KerIso_FourSqW_orth_linInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KerIso.FourSqW
theorem _root_.solution : OrthDiag := by
  intro K E _ _ _ _ _ cj n _ h2 hn hc hpos
  classical
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  obtain ⟨e, he0, heo⟩ := exists_orth (K := K) cj hc hpos (finrank K E) le_rfl
  let σ : n ≃ Fin (finrank K E) := Fintype.equivFinOfCardEq hn
  let v : n → E := fun i => e (σ i)
  have hv0 : ∀ i, v i ≠ 0 := fun i => he0 _
  have hvo : ∀ i j, i ≠ j → Algebra.trace K E (v i * cj (v j)) = 0 :=
    fun i j hij => heo _ _ (fun h => hij (σ.injective h))
  have hli := orth_linInd (K := K) cj hpos v hv0 hvo
  let b : Basis n K E := basisOfLinearIndependentOfCardEqFinrank' v hli hn
  have hb : ∀ i, b i = v i := fun i => by simp [b]
  choose q hq0 hq using fun i => tr_self_rat (K := K) cj hc h2 hpos (v i) (hv0 i)
  refine ⟨b, q, hq0, ?_⟩

  have hcol : ∀ y i, Algebra.trace K E (y * cj (v i)) = b.repr y i * (q i : K) := by
    intro y i
    have h := congrArg (trL (K := K) cj (v i)) (b.sum_repr y)
    rw [map_sum, Finset.sum_eq_single i] at h
    · rw [← trL_apply, ← h, map_smul, trL_apply, hb, hq, smul_eq_mul]
    · intro j _ hji
      rw [map_smul, trL_apply, hb, hvo j i hji, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  intro x y
  have hx := congrArg (fun z => algebraMap K E (trL (K := K) cj y z)) (b.sum_repr x)
  simp only [map_sum, map_smul, trL_apply, smul_eq_mul, map_mul] at hx
  rw [← hx]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hb, tr_swap cj hc, hcol, map_mul, map_mul, map_ratCast, map_ratCast]
  ring
end PI.KerIso.FourSqW
