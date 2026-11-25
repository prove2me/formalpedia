-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_finrank_eq_beef6e4ea699
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:21.62081+00:00
-- url     : https://prove2.me/submissions/deb74022-5a17-432c-9e8e-e7131f7220a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_component_mul_form_2d063eda04f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_exists_sub_component_mem_380caf9d8097

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
theorem _root_.solution (h1 : GradedFinite.Statement.{u}) [Fintype K] [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {c : K → ℕ} {s : MRing ι F}
    (hs : IsMultiHomog s c) (n : K → ℕ) :
    Module.finrank F (gradedPiece I n) =
      Module.finrank F (gradedPiece (I ⊔ Ideal.span {s}) n) +
        (if c ≤ n then Module.finrank F (gradedPiece (I.colon (Ideal.span {s})) (n - c))
          else 0) := by
  have hIL : I ≤ I ⊔ Ideal.span {s} := le_sup_left
  let π : (MRing ι F ⧸ I) →ₗ[F] (MRing ι F ⧸ (I ⊔ Ideal.span {s})) :=
    (Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ F (I ⊔ Ideal.span {s}))
      (fun a ha => by
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hIL ha)).toLinearMap
  have hπ : ∀ x, π (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (I ⊔ Ideal.span {s}) x :=
    fun x => rfl
  have : FiniteDimensional F (gradedPiece I n) := (h1 F K ι I n).1
  have hrn := (π.domRestrict (gradedPiece I n)).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (π.domRestrict (gradedPiece I n)) =
      gradedPiece (I ⊔ Ideal.span {s}) n := by
    rw [LinearMap.range_domRestrict, gradedPiece, gradedPiece, ← Submodule.map_comp]
    congr 1

  have hkerdesc : ∀ y ∈ LinearMap.ker (π.domRestrict (gradedPiece I n)),
      ∃ f : MRing ι F, IsMultiHomog f n ∧ f ∈ I ⊔ Ideal.span {s} ∧
        ((y : gradedPiece I n) : MRing ι F ⧸ I) = Ideal.Quotient.mk I f := by
    rintro ⟨y, hy⟩ hker
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    refine ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, ?_, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hker
    have : π (Ideal.Quotient.mk I f) = 0 := hker
    rwa [hπ, Ideal.Quotient.eq_zero_iff_mem] at this
  rw [← hrange, ← hrn]
  congr 1
  by_cases hc : c ≤ n
  · rw [if_pos hc]
    let W := weightedHomogeneousSubmodule F (blockWeight ι) (n - c)
    let α : W →ₗ[F] (MRing ι F ⧸ I.colon (Ideal.span {s})) :=
      (Ideal.Quotient.mkₐ F (I.colon (Ideal.span {s}))).toLinearMap ∘ₗ W.subtype
    let β : W →ₗ[F] (MRing ι F ⧸ I) :=
      (Ideal.Quotient.mkₐ F I).toLinearMap ∘ₗ (LinearMap.mulRight F s) ∘ₗ W.subtype
    have hker : LinearMap.ker α = LinearMap.ker β := by
      ext g
      simp [α, β, Ideal.Quotient.eq_zero_iff_mem]
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : LinearMap.range α = gradedPiece (I.colon (Ideal.span {s})) (n - c) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    have e2 : LinearMap.range β =
        (LinearMap.ker (π.domRestrict (gradedPiece I n))).map (gradedPiece I n).subtype := by
      ext x
      constructor
      · rintro ⟨⟨g, hg⟩, rfl⟩
        have hgs : g * s ∈ weightedHomogeneousSubmodule F (blockWeight ι) n := by
          have := IsWeightedHomogeneous.mul ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg) hs
          rw [tsub_add_cancel_of_le hc] at this
          exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr this
        refine ⟨⟨(Ideal.Quotient.mkₐ F I).toLinearMap (g * s), Submodule.mem_map_of_mem hgs⟩,
          ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.domRestrict_apply]
        change π ((Ideal.Quotient.mkₐ F I) (g * s)) = 0
        rw [Ideal.Quotient.mkₐ_eq_mk, hπ, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨g, rfl⟩)
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
        obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
        rw [component_mul_form hs, if_pos hc] at ht
        refine ⟨⟨weightedHomogeneousComponent (blockWeight ι) (n - c) t,
          weightedHomogeneousComponent_mem _ _ _⟩, ?_⟩
        change Ideal.Quotient.mk I (weightedHomogeneousComponent (blockWeight ι) (n - c) t * s) =
          ((y : gradedPiece I n) : MRing ι F ⧸ I)
        rw [hyf, Ideal.Quotient.eq]
        simpa using I.neg_mem ht
    have eα : LinearMap.range α ≃ₗ[F] LinearMap.range β :=
      α.quotKerEquivRange.symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ β.quotKerEquivRange
    rw [← e1, eα.finrank_eq, e2]
    exact (Submodule.equivMapOfInjective (gradedPiece I n).subtype Subtype.val_injective
      (LinearMap.ker (π.domRestrict (gradedPiece I n)))).finrank_eq
  · rw [if_neg hc]
    have hbot : LinearMap.ker (π.domRestrict (gradedPiece I n)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨f, hf, hfL, hyf⟩ := hkerdesc y hy
      obtain ⟨t, ht⟩ := exists_sub_component_mem hI hf hfL
      rw [component_mul_form hs, if_neg hc, sub_zero] at ht
      rw [Submodule.mem_bot]
      apply Subtype.ext
      rw [hyf, ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [hbot, finrank_bot]
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
