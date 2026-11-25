-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_hilbFn_sub_le_of_regular_a8f58f594e0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:25.226175+00:00
-- url     : https://prove2.me/submissions/c8d9f670-2395-482b-a2f5-be0c6140fc75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSectionNef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_forms_mem_of_not_le_relevant_cc722a823041
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_GradedFinite_proof_4a0254b94345
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ColonMultiHomog_proof_89514dc80a8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_multiHomog_25f3cafc54d6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open MvPolynomial NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {P : Ideal (MRing ι F)} (hP : IsMultiProjPrime P) {b : K → ℤ}
    {f g : MRing ι F} (hs : IsRegularSection P b f g) :
    ∀ᶠ m in Filter.atTop, hilbFn P (m - b) ≤ hilbFn P m := by
  classical
  have := hP.isPrime
  obtain ⟨bf, bg, hf, hg, hb⟩ := hs.degrees
  set J : Ideal (MRing ι F) := (P ⊔ Ideal.span {g}).colon {f} with hJdef
  have hJh : IsMultiHomogIdeal J :=
    ColonMultiHomog.proof F K ι _ f bf
      (SupSpanMultiHomog.proof F K ι P g bg hP.multiHomog hg) hf
  have hPJ : P ≤ J := fun p hp => by
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    exact Ideal.mem_sup_left (P.mul_mem_right f hp)
  have hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W →
      ¬ J ≤ W := by
    intro W hWp hWh hWr hJW
    obtain ⟨u, v, hu, huv⟩ := hs.regular W ⟨hWp, hWh, hWr⟩ (hPJ.trans hJW)
    apply hu
    apply hJW
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    have : u * f = (u * f - v * g) + v * g := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left huv)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  obtain ⟨n, hn⟩ := exists_forms_mem_of_not_le_relevant hJh hrel
  rw [Filter.eventually_atTop]
  refine ⟨fun k => |b k| + (n * Fintype.card (ι k) : ℕ) + 1, fun m hm => ?_⟩
  have hm' : ∀ k, |b k| + (n * Fintype.card (ι k) : ℕ) + 1 ≤ m k := fun k => hm k
  have hb' : ∀ k, b k = (bf k : ℤ) - bg k := fun k => (congrFun hb k).symm
  have hm0 : ∀ k, 0 ≤ m k := fun k => by have := hm' k; have := abs_nonneg (b k); omega
  have hmb0 : ∀ k, 0 ≤ (m - b) k := fun k => by
    have := hm' k; have := le_abs_self (b k); simp only [Pi.sub_apply]; omega
  set M : K → ℕ := fun k => (m k).toNat with hM
  set M' : K → ℕ := fun k => ((m - b) k).toNat with hM'
  have hdeg : M' + bf = M + bg := by
    funext k
    have := hm0 k; have := hmb0 k; have := hb' k
    simp only [Pi.add_apply, hM, hM', Pi.sub_apply] at *
    omega
  have hbig : ∀ k, n * Fintype.card (ι k) < M' k := by
    intro k
    have := hm' k; have := le_abs_self (b k)
    simp only [hM', Pi.sub_apply]
    omega
  have hfin := (FieldNumbers.GradedFinite.proof F K ι P M).1
  have hfin' := (FieldNumbers.GradedFinite.proof F K ι P M').1
  have e1 : hilbFn P m = Module.finrank F (gradedPiece P M) := by
    unfold hilbFn; rw [if_pos hm0]
  have e2 : hilbFn P (m - b) = Module.finrank F (gradedPiece P M') := by
    unfold hilbFn; rw [if_pos hmb0]
  rw [e1, e2, Nat.cast_le]

  let φ : MRing ι F → (MRing ι F ⧸ P) →ₗ[F] (MRing ι F ⧸ P) := fun a =>
    LinearMap.mulLeft F (Ideal.Quotient.mk P a)
  have hinj : ∀ a, a ∉ P → Function.Injective (φ a) := by
    intro a ha
    exact mul_right_injective₀ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hle : (gradedPiece P M').map (φ f) ≤ (gradedPiece P M).map (φ g) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxh : IsMultiHomog x M' := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx
    have hxJ : x ∈ J := hn M' hbig x hxh
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_sup] at hxJ
    obtain ⟨p, hp, q, hq, hpq⟩ := hxJ
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    set y := weightedHomogeneousComponent (blockWeight ι) M a
    have hxf : IsMultiHomog (x * f) (M + bg) := by
      rw [← hdeg]; exact hxh.mul hf
    have hcomp := congrArg (weightedHomogeneousComponent (blockWeight ι) (M + bg)) hpq
    rw [map_add, ← component_mul_multiHomog a g M bg hg,
      hxf.weightedHomogeneousComponent_same] at hcomp
    have hpc : weightedHomogeneousComponent (blockWeight ι) (M + bg) p ∈ P :=
      hP.multiHomog p hp _
    refine ⟨Ideal.Quotient.mk P y, ⟨y, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      rfl⟩, ?_⟩
    simp only [φ, LinearMap.mulLeft_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply,
      ← map_mul]
    rw [Ideal.Quotient.eq, mul_comm f x, ← hcomp]
    have : g * y - (weightedHomogeneousComponent (blockWeight ι) (M + bg) p + y * g) =
      -weightedHomogeneousComponent (blockWeight ι) (M + bg) p := by ring
    rw [this]
    exact P.neg_mem hpc
  calc Module.finrank F (gradedPiece P M')
      = Module.finrank F ((gradedPiece P M').map (φ f)) :=
        (Submodule.equivMapOfInjective _ (hinj f hs.num_not_mem) _).finrank_eq
    _ ≤ Module.finrank F ((gradedPiece P M).map (φ g)) := by
        have : FiniteDimensional F ((gradedPiece P M).map (φ g)) :=
          Module.Finite.map _ _
        exact LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
          (Submodule.inclusion_injective hle)
    _ = Module.finrank F (gradedPiece P M) :=
        ((Submodule.equivMapOfInjective _ (hinj g hs.den_not_mem) _).finrank_eq).symm
end GroundTheory.Heights₂.Heights.Model
