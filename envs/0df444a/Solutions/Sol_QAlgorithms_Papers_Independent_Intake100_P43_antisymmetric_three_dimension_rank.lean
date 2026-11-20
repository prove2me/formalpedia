-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P43.antisymmetric_three_dimension_rank
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:52:10.037326+00:00
-- url     : https://prove2.me/submissions/8fcdc9fb-91a0-45e4-8aaf-aa60b1f2e68b

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43
noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

theorem AuxAS_lower (M : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ)
    (hli : LinearIndependent ℂ ![M.mulVecLin x, M.mulVecLin y]) : 2 ≤ M.rank := by
  rw [Matrix.rank]
  have h := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h
  have hle : Submodule.span ℂ (Set.range ![M.mulVecLin x, M.mulVecLin y]) ≤
      LinearMap.range M.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp
  have := Submodule.finrank_mono hle
  rw [h] at this
  exact this

theorem AuxAS_rank (a b c : ℂ) (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    (!![0, a, b; -a, 0, c; -b, -c, 0] : Matrix (Fin 3) (Fin 3) ℂ).rank = 2 := by
  set M : Matrix (Fin 3) (Fin 3) ℂ := !![0, a, b; -a, 0, c; -b, -c, 0] with hM
  apply le_antisymm
  · have hw : M.mulVecLin ![c, -b, a] = 0 := by
      ext i; fin_cases i <;> simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
    have hw0 : (![c, -b, a] : Fin 3 → ℂ) ≠ 0 := by
      intro h0; apply h
      have h1 := congrFun h0 0; have h2 := congrFun h0 1; have h3 := congrFun h0 2
      simp at h1 h2 h3
      exact ⟨h3, h2, h1⟩
    have hk : 0 < Module.finrank ℂ (LinearMap.ker M.mulVecLin) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, LinearMap.mem_ker.mpr hw⟩,
        fun h0 => hw0 (congrArg Subtype.val h0)⟩
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fin_fun] at this
    rw [Matrix.rank]; omega
  · have key : ∀ x y : Fin 3 → ℂ, (∀ s t : ℂ, s • M.mulVecLin x + t • M.mulVecLin y = 0 →
        s = 0 ∧ t = 0) → 2 ≤ M.rank := fun x y hxy =>
      AuxAS_lower M x y (LinearIndependent.pair_iff.mpr hxy)
    by_cases ha : a ≠ 0
    · refine key ![1, 0, 0] ![0, 1, 0] fun s t hst => ?_
      have h1 : t * a = 0 := by
        have := congrFun hst 0
        simpa [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero] using this
      have h2 : s * a = 0 := by
        have := congrFun hst 1
        simpa [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero] using this
      exact ⟨(mul_eq_zero.mp h2).resolve_right ha, (mul_eq_zero.mp h1).resolve_right ha⟩
    by_cases hb : b ≠ 0
    · refine key ![1, 0, 0] ![0, 0, 1] fun s t hst => ?_
      have h1 : t * b = 0 := by
        have := congrFun hst 0
        simpa [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero] using this
      have h2 : s * b = 0 := by
        have := congrFun hst 2
        simpa [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero] using this
      exact ⟨(mul_eq_zero.mp h2).resolve_right hb, (mul_eq_zero.mp h1).resolve_right hb⟩
    have hc : c ≠ 0 := by
      intro hc; push_neg at ha hb; exact h ⟨ha, hb, hc⟩
    · refine key ![0, 1, 0] ![0, 0, 1] fun s t hst => ?_
      have h1 : t * c = 0 := by
        have := congrFun hst 1
        simpa [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero] using this
      have h2 : s * c = 0 := by
        have := congrFun hst 2
        simpa [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, -mul_eq_zero] using this
      exact ⟨(mul_eq_zero.mp h2).resolve_right hc, (mul_eq_zero.mp h1).resolve_right hc⟩

theorem _root_.solution :
    Module.finrank ℂ antisymmetricSubspace = 3 ∧
      HasConstantSchmidtRank antisymmetricSubspace 2 := by
  have hdiag : ∀ v ∈ antisymmetricSubspace, ∀ i, v (i, i) = 0 := by
    intro v hv i
    have := hv i i
    have h2 : (2 : ℂ) * v (i, i) = 0 := by linear_combination this
    simpa using h2
  set φ : antisymmetricSubspace →ₗ[ℂ] (Fin 3 → ℂ) :=
    { toFun := fun v => ![(v : Bipartite 3 3) (0, 1), (v : Bipartite 3 3) (0, 2),
        (v : Bipartite 3 3) (1, 2)]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp } with hφ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv0
    have h1 := congrFun hv0 0; have h2 := congrFun hv0 1; have h3 := congrFun hv0 2
    simp [hφ] at h1 h2 h3
    have hv := v.2
    apply Subtype.ext
    ext ⟨i, j⟩
    have hd := hdiag v.1 v.2
    fin_cases i <;> fin_cases j <;> simp [hd, h1, h2, h3, hv (1 : Fin 3) 0, hv (2 : Fin 3) 0,
      hv (2 : Fin 3) 1]
  have hsurj : Function.Surjective φ := by
    intro f
    let w : Bipartite 3 3 := WithLp.toLp 2 (fun p : Fin 3 × Fin 3 =>
      (!![0, f 0, f 1; -f 0, 0, f 2; -f 1, -f 2, 0] : Matrix (Fin 3) (Fin 3) ℂ) p.1 p.2)
    have hw : w ∈ antisymmetricSubspace := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [w]
    refine ⟨⟨w, hw⟩, ?_⟩
    ext i; fin_cases i <;> simp [hφ, w]
  refine ⟨?_, fun v hv hv0 => ?_⟩
  · rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩), Module.finrank_fin_fun]
  · have hd := hdiag v hv
    have hM : Matrix.of (fun (i : Fin 3) (j : Fin 3) => v (i, j)) =
        !![0, v (0, 1), v (0, 2); -v (0, 1), 0, v (1, 2); -v (0, 2), -v (1, 2), 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hd, hv (1 : Fin 3) 0, hv (2 : Fin 3) 0,
        hv (2 : Fin 3) 1]
    unfold schmidtNumber
    rw [hM]
    apply AuxAS_rank
    rintro ⟨h1, h2, h3⟩
    apply hv0
    have : φ ⟨v, hv⟩ = 0 := by ext i; fin_cases i <;> simp [hφ, h1, h2, h3]
    have := hinj (this.trans (map_zero φ).symm)
    simpa using congrArg Subtype.val this

end QAlgorithms.Papers.Independent.Intake100.P43

end
