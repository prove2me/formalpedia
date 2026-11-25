-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_unitary_leadCoordPlane_64ab9545e835
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:39.794803+00:00
-- url     : https://prove2.me/submissions/0cebd001-e816-4d25-a3ec-34d7ce1af24b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_firstCoordVec_eq_basisFun_7b02b35d9e45

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
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hT : finrank ℂ T = m)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ T) :
    ∃ U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n),
      (∀ v ∈ leadCoordPlane n m, U v ∈ T) ∧ (∀ t ∈ T, ∃ v ∈ leadCoordPlane n m, U v = t) ∧
        U ((‖y‖ : ℂ) • firstCoordVec n) = y := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  obtain ⟨u, huT, hu1, hyu⟩ : ∃ u ∈ T, ‖u‖ = 1 ∧ (‖y‖ : ℂ) • u = y := by
    by_cases hy0 : y = 0
    · have hTne : T ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hT
        omega
      obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
      exact ⟨(‖t‖⁻¹ : ℂ) • t, T.smul_mem _ htT, norm_smul_inv_norm ht0, by simp [hy0]⟩
    · refine ⟨(‖y‖⁻¹ : ℂ) • y, T.smul_mem _ hy, norm_smul_inv_norm hy0, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.2 hy0), one_smul]
  obtain ⟨bT, hbT⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := T)
    (ι := Fin m) (v := fun _ => (⟨u, huT⟩ : T)) (s := {⟨0, hm⟩}) (by simp [hT]) (by
      refine ⟨fun i => by simpa using hu1, fun i j hij => ?_⟩
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
        (Set.mem_singleton_iff.1 j.2).symm)) hij)
  have hbT0 : (bT ⟨0, hm⟩ : EuclideanSpace ℂ (Fin n)) = u := by
    rw [hbT _ (Set.mem_singleton _)]
  set v : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun j => if h : (j : ℕ) < m then (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) else 0 with hv
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (v := v) (s := {j | (j : ℕ) < m}) (by simp) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi' : (i : ℕ) < m := hi
      have hj' : (j : ℕ) < m := hj
      simp only [Set.domRestrict, hv, dif_pos hi', dif_pos hj']
      rw [← Submodule.coe_inner, orthonormal_iff_ite.1 bT.orthonormal]
      simp [Fin.ext_iff])
  have hBv : ∀ j : Fin n, ∀ h : (j : ℕ) < m, B j = (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) := by
    intro j h
    rw [hB j h]
    simp [hv, h]
  set e := EuclideanSpace.basisFun (Fin n) ℂ with he
  have hU : ∀ w, e.equiv B (Equiv.refl _) w = ∑ j, w j • B j := by
    intro w
    conv_lhs => rw [← e.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
    rfl
  refine ⟨e.equiv B (Equiv.refl _), ?_, ?_, ?_⟩
  · intro w hw
    have hw' : ∀ j : Fin n, m ≤ (j : ℕ) → w j = 0 := hw
    rw [hU]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h : (j : ℕ) < m
    · rw [hBv j h]
      exact T.smul_mem _ (bT _).2
    · rw [hw' j (by omega), zero_smul]
      exact T.zero_mem
  · intro t ht
    have hBk : ∀ k : Fin m, B (Fin.castLE hmn k) = (bT k : EuclideanSpace ℂ (Fin n)) :=
      fun k => hBv _ (by simp)
    refine ⟨∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
      show ∀ j : Fin n, m ≤ (j : ℕ) → (e (Fin.castLE hmn k)) j = 0
      intro j hj
      have hne : j ≠ Fin.castLE hmn k := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [he, EuclideanSpace.basisFun_apply, hne]
    · calc e.equiv B (Equiv.refl _) (∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k))
            = ∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • (bT k : EuclideanSpace ℂ (Fin n)) := by
              simp [map_sum, map_smul, OrthonormalBasis.equiv_apply_basis, hBk]
        _ = ((∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • bT k : T) : EuclideanSpace ℂ (Fin n)) := by
              simp
        _ = t := by rw [bT.sum_repr]
  · rw [firstCoordVec_eq_basisFun hn, map_smul, OrthonormalBasis.equiv_apply_basis,
      Equiv.refl_apply, hBv _ hm]
    rw [show (⟨((⟨0, hn⟩ : Fin n) : ℕ), hm⟩ : Fin m) = ⟨0, hm⟩ from rfl, hbT0, hyu]
end GroundTheory.Heights₂.Heights
