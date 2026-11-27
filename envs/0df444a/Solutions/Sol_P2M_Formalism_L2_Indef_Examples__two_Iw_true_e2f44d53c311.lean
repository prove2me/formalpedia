-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__two_Iw_true_e2f44d53c311
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:03.121558+00:00
-- url     : https://prove2.me/submissions/f7786d01-e650-461b-a9df-113ebeb82298

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Theorems.Thm_Formalism_DivisionValues_index_change_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
namespace Formalism.L2.Indef.Examples₂
namespace two
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : K) (kap l : InfinitePlace K → ℝ) (ha : a ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) : (two.dat K v0 S a kap l).Iw () true w = vw w a := by
  have hf : (fun i => ∑ k, (a • (1 : Matrix (Fin 1) (Fin 1) K)) k i • sb K 1 k) =
      fun i => a • sb K 1 i := by
    funext i
    fin_cases i
    simp [Matrix.smul_apply]
  have hmat : matLat (a • (1 : Matrix (Fin 1) (Fin 1) K)) (sl K 1) =
      Submodule.span (𝓞 K) (Set.range fun i => a • sb K 1 i) := by
    unfold matLat sl
    rw [Submodule.map_span, ← Set.range_comp]
    exact congrArg (fun s => Submodule.span (𝓞 K) s)
      (congrArg Set.range (funext fun i => by simp [smul_one_mulVec]))
  have hlin : LinearIndependent K (fun i => a • sb K 1 i) := by
    rw [linearIndependent_unique_iff]
    intro h0
    exact ha (by simpa [sb] using congrFun h0 0)
  have hlat : Submodule.IsLattice K (matLat (a • (1 : Matrix (Fin 1) (Fin 1) K)) (sl K 1)) := by
    rw [hmat]
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [Submodule.span_span_of_tower]
    exact hlin.span_eq_top_of_card_eq_finrank (by simp)
  have hidx := (index_change_formula K 1 _ hlat (sb K 1) (locB K 1 w).1 w (a • 1)
    ⟨hf ▸ hlin, by rw [hf, hmat]⟩).1
  have h2 : (two.dat K v0 S a kap l).Iw () true w =
      vw w (a • (1 : Matrix (Fin 1) (Fin 1) K)).det := hidx
  rw [h2, Matrix.det_smul, Matrix.det_one]
  simp
end two
end Formalism.L2.Indef.Examples₂
