-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_TwistUnit_trace___3993ddab228e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:11.635318+00:00
-- url     : https://prove2.me/submissions/8ff1d328-5b9b-4646-8429-36617d986693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemAdjoinOfMulEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TwistUnit
open GlobalTheory.UnitLemma Polynomial
variable {K : UQ}
namespace GlobalTheory.UnitLemma.TwistUnit
theorem _root_.solution (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  let b := Module.Free.chooseBasis K.E B.A
  have hsm : ∀ (e : K.E) (y : B.A), B.σ (e • y) = K.c e • B.σ y := by
    intro e y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hli : LinearIndependent K.E ((B.σ : B.A →+ B.A) ∘ b) := by
    refine b.linearIndependent.map_of_injective_injective (fun r => K.c.symm r) (B.σ : B.A →+ B.A) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro m hm
      have : B.σ m = 0 := hm
      simpa using this
    · intro r m
      show B.σ (K.c.symm r • m) = r • B.σ m
      rw [hsm, RingEquiv.apply_symm_apply]
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range ((B.σ : B.A →+ B.A) ∘ b)) := by
    intro y _
    have h1 : y = ∑ j, K.c (b.repr (B.σ.symm y) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ.apply_symm_apply y, ← b.sum_repr (B.σ.symm y)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hsm _ _
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K.E B.A) K.E B.A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => by
    simp only [b', Module.Basis.mk_apply]
    rfl
  have hrepr : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have h1 : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hsm, hb']
    rw [h1, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hb', ← map_mul, hrepr]
end GlobalTheory.UnitLemma.TwistUnit
