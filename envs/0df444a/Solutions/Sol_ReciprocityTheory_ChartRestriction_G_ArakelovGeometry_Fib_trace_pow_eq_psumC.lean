-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.trace_pow_eq_psumC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:52.389068+00:00
-- url     : https://prove2.me/submissions/b0fd417d-33d3-4029-b002-eacfae68047f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_map_psumC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_sum_roots_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_card_roots
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_mem_roots


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open Polynomial IntermediateField
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K]
    [FiniteDimensional K E] {θ : E} (hθ : K⟮θ⟯ = ⊤) (j : ℕ) :
    Algebra.trace K E (θ ^ j) = psumC (minpoly K θ) (minpoly K θ).natDegree j := by
  classical
  have hint : IsIntegral K θ := IsIntegral.of_finite K θ
  have hmon := minpoly.monic hint
  have hsep : (minpoly K θ).Separable := Algebra.IsSeparable.isSeparable K θ
  have hc : Multiset.card ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).natDegree := by
    first
    | exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
    | exact (IsAlgClosed.splits _).card_roots
    | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits _)).symm
  have hnd : ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.Nodup :=
    Polynomial.nodup_roots hsep.map
  have hadj : Algebra.adjoin K {θ} = ⊤ := by
    first
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hθ,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
          (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hint.isAlgebraic), hθ,
        IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) := by
    intro σ τ h
    exact AlgHom.ext_of_adjoin_eq_top hadj (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h)
  have hfin : Module.finrank K E = (minpoly K θ).natDegree := by
    rw [← IntermediateField.finrank_top', ← hθ, IntermediateField.adjoin.finrank hint]
  have himg : Finset.univ.image (fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) =
      ((minpoly K θ).map (algebraMap K (AlgebraicClosure K))).roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (hmon.map _).ne_zero]
      first
      | rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      | simp [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]
    · rw [Multiset.toFinset_card_of_nodup hnd, hc, hmon.natDegree_map,
        Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hfin]
      exact (AlgHom.card K E (AlgebraicClosure K)).ge
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_psumC, ← hmon.natDegree_map (algebraMap K (AlgebraicClosure K)),
    ← sum_roots_pow _ (hmon.map _) hc j]
  first
  | rw [trace_eq_sum_embeddings (AlgebraicClosure K)]
  | rw [trace_eq_sum_embeddings]
  | rw [Algebra.trace_eq_sum_embeddings (AlgebraicClosure K)]
  simp only [map_pow]
  have hsum := Finset.sum_image (s := Finset.univ)
    (g := fun σ : E →ₐ[K] AlgebraicClosure K => σ θ) (f := fun y => y ^ j)
    (fun σ _ τ _ h => hinj h)
  rw [himg] at hsum
  rw [← hsum, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
