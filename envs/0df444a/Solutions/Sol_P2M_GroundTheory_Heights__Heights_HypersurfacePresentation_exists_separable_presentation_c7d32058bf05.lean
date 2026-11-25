-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_separable_presentation_c7d32058bf05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:33.278809+00:00
-- url     : https://prove2.me/submissions/53ed5295-dd34-4a90-b159-8fdf1878a6fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_minpoly_separable_up_to_f836c61939fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_mul_eq_aeval_af68aaf6f222
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_integral_primitive_79d7c8a66779

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
namespace GroundTheory.Heights₂.Heights.HypersurfacePresentation
theorem _root_.solution {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Algebra.IsAlgebraic R A]
    {n : ℕ} (x : Fin n → A) (hx : Algebra.adjoin R (Set.range x) = ⊤) {ι : Type} [Fintype ι] (z : ι → A) :
    ∃ θ : A, (minpoly R θ).Monic ∧ (∀ H : Polynomial R, Polynomial.aeval θ H = 0 ↔ minpoly R θ ∣ H) ∧
      ∃ D : R, D ≠ 0 ∧ ∃ (q : ι → Polynomial R) (u v : Polynomial R),
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C D ∧
      ∀ i, Polynomial.aeval θ (q i) = algebraMap R A D * z i := by
  classical
  have : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq R A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp (FaithfulSMul.algebraMap_injective R A))
  let : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra _ _
  have : CharZero (FractionRing R) :=
    charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hgen : IntermediateField.adjoin (FractionRing R)
      (Set.range fun j => algebraMap A (FractionRing A) (x j)) = ⊤ := by
    set F := IntermediateField.adjoin (FractionRing R) (Set.range fun j => algebraMap A (FractionRing A) (x j))
    have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈ F := by
      intro a
      have ha : a ∈ Algebra.adjoin R (Set.range x) := hx ▸ Algebra.mem_top
      induction ha using Algebra.adjoin_induction with
      | mem a h =>
        obtain ⟨j, rfl⟩ := h
        exact IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
      | algebraMap r =>
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A)]
        exact F.algebraMap_mem _
      | add a b _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | mul a b _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective A w
    exact div_mem (hA a) (hA b)
  obtain ⟨θ, hθ, hθgen⟩ :=
    exists_integral_primitive (R := R) (E := FractionRing R) (L := FractionRing A) x hgen
  obtain ⟨δ, hδ, u, v, huv⟩ := minpoly_separable_up_to (E := FractionRing R) (L := FractionRing A) hθ
  choose b hb q hq using fun i =>
    exists_mul_eq_aeval (E := FractionRing R) (L := FractionRing A) hθ hθgen (z i)
  have : Module.IsTorsionFree R A :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective R A)
  refine ⟨θ, minpoly.monic hθ, minpoly.isIntegrallyClosed_dvd_iff hθ, δ * ∏ i, b i, mul_ne_zero hδ (Finset.prod_ne_zero_iff.2 fun i _ => hb i),
    fun i => Polynomial.C (δ * ∏ j ∈ Finset.univ.erase i, b j) * q i,
    Polynomial.C (∏ i, b i) * u, Polynomial.C (∏ i, b i) * v, ?_, fun i => ?_⟩
  · rw [Polynomial.C_mul]
    linear_combination Polynomial.C (∏ i, b i) * huv
  · rw [map_mul, Polynomial.aeval_C, hq i, ← mul_assoc, ← map_mul, mul_assoc δ,
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
end GroundTheory.Heights₂.Heights.HypersurfacePresentation
