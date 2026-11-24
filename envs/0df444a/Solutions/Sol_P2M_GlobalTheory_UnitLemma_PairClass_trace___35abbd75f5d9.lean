-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_PairClass_trace___35abbd75f5d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:40:55.992585+00:00
-- url     : https://prove2.me/submissions/de720317-81bf-496b-ac95-9ec22d675f78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass
namespace GlobalTheory.UnitLemma.PairClass
theorem _root_.solution (K : UQ) (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  let b := Module.finBasis K.E B.A
  have hσsum : ∀ y : B.A, B.σ y = ∑ i, K.c (b.repr y i) • B.σ (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [σsm]
  have hli : LinearIndependent K.E (fun i => B.σ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro r hr i
    have h1 := congrArg B.σ hr
    rw [map_sum, map_zero] at h1
    simp only [σsm, B.σ_σ] at h1
    have h2 := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h1 i
    have := congrArg K.c h2
    rwa [K.c_c, map_zero] at this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range fun i => B.σ (b i)) := by
    intro y _
    rw [← B.σ_σ y, hσsum (B.σ y)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => Module.Basis.mk_apply hli hsp i
  have hrepr : ∀ (y : B.A) (i), b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      rw [hσsum y]; simp only [hb']
    rw [this, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', ← map_mul, hrepr]
end GlobalTheory.UnitLemma.PairClass
