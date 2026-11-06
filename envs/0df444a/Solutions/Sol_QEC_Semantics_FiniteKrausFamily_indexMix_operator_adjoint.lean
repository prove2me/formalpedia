-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexMix_operator_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:10:42.608225+00:00
-- url     : https://prove2.me/submissions/9650244e-bddf-4cf9-a4f6-a56d45afd610

-- ID: 3f252050-d990-42d2-98ac-bfaf5d67a260 | NAME: QEC.Semantics.FiniteKrausFamily.indexMix_operator_adjoint | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
variable [DecidableEq ι]
omit [DecidableEq ι]

theorem solution (E : FiniteKrausFamily ι H H)
    (U : Matrix ι ι Complex) (a : ι) :
    LinearMap.adjoint ((E.indexMix U).operator a) =
      ∑ i : ι, star (U i a) • LinearMap.adjoint (E.operator i) := by
  solve
    | simp [indexMix, map_sum, map_smulₛₗ]
    | simp [indexMix, map_sum, map_smulₛₗ, star_eq_adjoint, star_smul]
    | simp [indexMix]
