-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finrank_step_0e1c7e28817d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:45.798797+00:00
-- url     : https://prove2.me/submissions/dc15df22-e7c4-49b6-a8f4-1280d7d9cfdb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finiteDimensional_piece_458f90289b82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_mem_sup_span_6525c74ca226

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
theorem _root_.solution (L : Ideal (MRing ι F)) (f : MRing ι F) (s : K → ℕ)
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) (n : K → ℕ) :
    Module.finrank F (gradedPiece L n) =
      Module.finrank F (gradedPiece (L ⊔ Ideal.span {f}) n) +
        if s ≤ n then Module.finrank F (gradedPiece (L.colon {f}) (n - s)) else 0 := by
  have : ∀ d : K → ℕ, FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) d) :=
    fun d => finiteDimensional_piece d
  have : FiniteDimensional F (gradedPiece L n) := by unfold gradedPiece; infer_instance
  let q := (Ideal.Quotient.factorₐ F (le_sup_left : L ≤ L ⊔ Ideal.span {f})).toLinearMap
  let g := q.domRestrict (gradedPiece L n)
  have hrange : LinearMap.range g = gradedPiece (L ⊔ Ideal.span {f}) n := by
    rw [LinearMap.range_domRestrict]
    unfold gradedPiece
    rw [← Submodule.map_comp]
    rfl
  have hker_mem : ∀ a : gradedPiece L n, g a = 0 → ∃ c : MRing ι F,
      (a : MRing ι F ⧸ L) = Ideal.Quotient.mk L
        (if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c else 0) := by
    rintro ⟨a, ha⟩ hga
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    have hx0 : Ideal.Quotient.mk (L ⊔ Ideal.span {f}) x = 0 := hga
    obtain ⟨c, hc⟩ := mem_sup_span hL hf hx (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
    exact ⟨c, Ideal.Quotient.eq.mpr hc⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange] at h1
  by_cases hsn : s ≤ n
  · let T := weightedHomogeneousSubmodule F (blockWeight ι) (n - s)
    have hmem : ∀ y : T, ((Ideal.Quotient.mkₐ F L).toLinearMap ∘ₗ LinearMap.mulLeft F f ∘ₗ
        T.subtype) y ∈ gradedPiece L n := fun y => by
      refine Submodule.mem_map_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_)
      have := IsWeightedHomogeneous.mul hf y.2
      rwa [add_tsub_cancel_of_le hsn] at this
    let μ := LinearMap.codRestrict (gradedPiece L n) ((Ideal.Quotient.mkₐ F L).toLinearMap ∘ₗ
      LinearMap.mulLeft F f ∘ₗ T.subtype) hmem
    let ν := (Ideal.Quotient.mkₐ F (L.colon {f})).toLinearMap.domRestrict T
    have hν : LinearMap.range ν = gradedPiece (L.colon {f}) (n - s) :=
      LinearMap.range_domRestrict _ _
    have hker : LinearMap.ker μ = LinearMap.ker ν := by
      ext y
      simp only [LinearMap.mem_ker]
      rw [← Subtype.coe_inj]
      change Ideal.Quotient.mk L (f * (y : MRing ι F)) = 0 ↔
        Ideal.Quotient.mk (L.colon {f}) (y : MRing ι F) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
        Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
    have hμg : LinearMap.range μ = LinearMap.ker g := by
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        change Ideal.Quotient.mk (L ⊔ Ideal.span {f}) (f * (y : MRing ι F)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨y, mul_comm _ _⟩)
      · intro a ha
        obtain ⟨c, hc⟩ := hker_mem a ha
        rw [if_pos hsn] at hc
        exact ⟨⟨_, weightedHomogeneousComponent_mem _ c (n - s)⟩, Subtype.ext hc.symm⟩
    have h2 := LinearMap.finrank_range_add_finrank_ker μ
    have h3 := LinearMap.finrank_range_add_finrank_ker ν
    rw [hker] at h2
    have e : Module.finrank F (LinearMap.range μ) = Module.finrank F (LinearMap.range ν) :=
      Nat.add_right_cancel (h2.trans h3.symm)
    rw [hμg, hν] at e
    rw [if_pos hsn, ← e]
    exact h1.symm
  · have hk : LinearMap.ker g = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro a ha
      obtain ⟨c, hc⟩ := hker_mem a ha
      rw [if_neg hsn, map_zero] at hc
      exact Subtype.ext hc
    rw [hk, finrank_bot] at h1
    rw [if_neg hsn]
    omega
end GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
