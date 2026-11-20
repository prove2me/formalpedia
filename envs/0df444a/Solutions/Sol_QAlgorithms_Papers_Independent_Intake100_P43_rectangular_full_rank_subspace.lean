-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P43.rectangular_full_rank_subspace
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:55:13.204075+00:00
-- url     : https://prove2.me/submissions/0cf1b440-5403-4ae0-aa05-4b9c3790fd37

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43
noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

theorem _root_.solution (dA dB : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) :
    ∃ S : Submodule ℂ (Bipartite dA dB),
      HasConstantSchmidtRank S dA ∧ Module.finrank ℂ S = dB - dA + 1 := by
  set n := dB - dA + 1 with hn
  set C := (coefficientEquiv : Bipartite dA dB ≃ₗ[ℂ] Matrix (Fin dA) (Fin dB) ℂ) with hC
  let Lmat : (Fin n → ℂ) →ₗ[ℂ] Matrix (Fin dA) (Fin dB) ℂ :=
    { toFun := fun c => Matrix.of fun i j =>
        if h : (i : ℕ) ≤ j ∧ (j : ℕ) - i < n then c ⟨j - i, h.2⟩ else 0
      map_add' := by
        intro c c'; ext i j; simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := by
        intro a c; ext i j; simp only [Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
          RingHom.id_apply]
        split_ifs <;> simp }
  have hLapp : ∀ c i j, Lmat c i j =
      if h : (i : ℕ) ≤ j ∧ (j : ℕ) - i < n then c ⟨j - i, h.2⟩ else 0 := fun _ _ _ => rfl
  have hLinj : Function.Injective Lmat := by
    intro c c' h
    funext k
    have hk : (k : ℕ) < dB := by have := k.2; omega
    have e := congrFun (congrFun h ⟨0, hA⟩) ⟨k, hk⟩
    rw [hLapp, hLapp] at e
    have hc : (0 : ℕ) ≤ k ∧ (k : ℕ) - 0 < n := ⟨Nat.zero_le _, by simp⟩
    simp only [dif_pos hc] at e
    simpa using e
  refine ⟨LinearMap.range (C.symm.toLinearMap ∘ₗ Lmat), fun v hv hv0 => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := hv
    have hc0 : c ≠ 0 := by rintro rfl; simp at hv0
    show (C (C.symm (Lmat c))).rank = dA
    rw [LinearEquiv.apply_symm_apply]
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height (Lmat c)
    · have hex : ∃ m, ∃ h : m < n, c ⟨m, h⟩ ≠ 0 := by
        obtain ⟨k, hk⟩ := Function.ne_iff.mp hc0
        exact ⟨k, k.2, hk⟩
      classical
      set k0 := Nat.find hex with hk0
      obtain ⟨hk0n, hck0⟩ := Nat.find_spec hex
      have hmin : ∀ m (h : m < n), m < k0 → c ⟨m, h⟩ = 0 := by
        intro m h hm
        by_contra hne
        exact Nat.find_min hex hm ⟨h, hne⟩
      let g : Fin dA → Fin dB := fun i => ⟨i + k0, by have := i.2; omega⟩
      set T := (Lmat c).submatrix id g with hT
      have hTri : T.BlockTriangular id := by
        intro i i' hlt
        simp only [hT, Matrix.submatrix_apply, id, hLapp, g]
        split_ifs with h
        · exact hmin _ _ (by have : (i' : ℕ) < i := hlt; omega)
        · rfl
      have hdiag : ∀ i, T i i = c ⟨k0, hk0n⟩ := by
        intro i
        simp only [hT, Matrix.submatrix_apply, id, hLapp, g]
        rw [dif_pos ⟨by simp, by have := hk0n; omega⟩]
        congr 1; ext; simp
      have hdet : T.det ≠ 0 := by
        rw [Matrix.det_of_isUpperTriangular hTri]
        simp only [hdiag, Finset.prod_const]
        exact pow_ne_zero _ hck0
      have h1 := Matrix.rank_of_det_ne_zero hdet
      have h2 := Matrix.rank_submatrix_le (Lmat c) id g
      simp only [Fintype.card_fin] at h1
      rw [← hT, h1] at h2
      exact h2
  · rw [LinearMap.finrank_range_of_inj (f := C.symm.toLinearMap ∘ₗ Lmat)
      (fun a b h => hLinj (C.symm.injective h)), Module.finrank_fin_fun]

end QAlgorithms.Papers.Independent.Intake100.P43

end
