-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P43.square_full_rank_dimension
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:53:47.852581+00:00
-- url     : https://prove2.me/submissions/ee94f290-550a-44a7-9f96-0b1c5d3e8cfe

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43
noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

theorem AuxSF_rank_lt {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (h : M.det = 0) : M.rank < d := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hk : 0 < Module.finrank ℂ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, LinearMap.mem_ker.mpr hv⟩,
      fun h0 => hv0 (congrArg Subtype.val h0)⟩
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at this
  rw [Matrix.rank]; omega

theorem AuxSF_sn {d : ℕ} (v : Bipartite d d) : schmidtNumber v = (coefficientEquiv v).rank := rfl

theorem _root_.solution (d : ℕ) (hd : 0 < d) :
    (∃ S : Submodule ℂ (Bipartite d d),
      HasLowerSchmidtRank S d ∧ Module.finrank ℂ S = 1) ∧
    (∀ S : Submodule ℂ (Bipartite d d), HasLowerSchmidtRank S d →
      Module.finrank ℂ S ≤ 1) := by
  set C := (coefficientEquiv : Bipartite d d ≃ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) with hC
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine ⟨⟨Submodule.span ℂ {C.symm 1}, fun v hv hv0 => ?_, ?_⟩, fun S hS => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hc : c ≠ 0 := by rintro rfl; simp at hv0
    rw [AuxSF_sn, map_smul, LinearEquiv.apply_symm_apply]
    rw [Matrix.rank_of_det_ne_zero]
    · simp
    · rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ hc
  · apply finrank_span_singleton
    intro h0
    have := congrArg C h0
    rw [LinearEquiv.apply_symm_apply, map_zero] at this
    exact one_ne_zero this
  · by_contra hlt
    push Not at hlt
    have hpos : 0 < Module.finrank ℂ S := by omega
    obtain ⟨u, huS, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp hpos |> fun h => h)
    have hnot : ¬ (S ≤ Submodule.span ℂ {u}) := fun hle => by
      have := Submodule.finrank_mono hle
      rw [finrank_span_singleton hu0] at this; omega
    obtain ⟨w, hwS, hwn⟩ := SetLike.not_le_iff_exists.mp hnot
    set A := C u with hA
    set B := C w with hB
    have hAdet : A.det ≠ 0 := by
      intro h0
      have h1 := AuxSF_rank_lt A h0
      have h2 := hS u huS hu0
      exact (not_lt.mpr h2) h1
    set X := A⁻¹ * B with hX
    obtain ⟨l, hl⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ X
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not] at hl
    have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hAdet)
    have hBl : B - l • A = -(A * (l • (1 : Matrix (Fin d) (Fin d) ℂ) - X)) := by
      rw [hX, Matrix.mul_sub, ← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_smul,
        Matrix.mul_one]
      abel
    have hdet : (B - l • A).det = 0 := by
      rw [hBl, Matrix.det_neg, Matrix.det_mul, hl, mul_zero, mul_zero]
    have hvS : w - l • u ∈ S := S.sub_mem hwS (S.smul_mem l huS)
    have hv0 : w - l • u ≠ 0 := by
      intro h0
      apply hwn
      rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have h1 := hS _ hvS hv0
    have h2 := AuxSF_rank_lt _ hdet
    have e : schmidtNumber (w - l • u) = (B - l • A).rank := by
      rw [AuxSF_sn, map_sub, map_smul]
    rw [e] at h1
    exact (not_lt.mpr h1) h2

end QAlgorithms.Papers.Independent.Intake100.P43

end
