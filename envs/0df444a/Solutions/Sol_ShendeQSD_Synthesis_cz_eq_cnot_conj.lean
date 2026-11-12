-- Prove2me | solution 1 for ShendeQSD.Synthesis.cz_eq_cnot_conj
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:24:17.333846+00:00
-- url     : https://prove2.me/submissions/2802a897-c9a6-42c8-a751-39ac700b9bad

import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_ShendeQSD_Synthesis_czLib
import Definitions.Def_ShendeQSD_Synthesis_ry

open scoped Kronecker

open QAlgorithms

open ShendeQSD.Synthesis in
theorem solution :
    (∃ u ∈ Matrix.unitaryGroup Bool ℂ, ∃ v ∈ Matrix.unitaryGroup Bool ℂ,
      czMat = ((1 : Matrix Bool Bool ℂ) ⊗ₖ v) * cnot * ((1 : Matrix Bool Bool ℂ) ⊗ₖ u)) ∧
    (∃ u ∈ Matrix.unitaryGroup Bool ℂ, ∃ v ∈ Matrix.unitaryGroup Bool ℂ,
      czMat = (v ⊗ₖ (1 : Matrix Bool Bool ℂ)) * cnot.submatrix Prod.swap Prod.swap *
        (u ⊗ₖ (1 : Matrix Bool Bool ℂ))) ∧
    czMat = ((1 : Matrix Bool Bool ℂ) ⊗ₖ ry (Real.pi / 2)) * cnot *
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ ry (-(Real.pi / 2))) ∧
    czMat = (ry (Real.pi / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ)) * cnot.submatrix Prod.swap Prod.swap *
      (ry (-(Real.pi / 2)) ⊗ₖ (1 : Matrix Bool Bool ℂ)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hr : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hk2 : k ^ 2 = 1 / 2 := by
    rw [hk, ← Complex.ofReal_pow, hr]
    norm_num
  have hkstar : star k = k := by
    rw [hk]
    exact Complex.conj_ofReal _
  have hkconj : (starRingEnd ℂ) k = k := hkstar
  have hc1 : Real.cos (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring]
    exact Real.cos_pi_div_four
  have hs1 : Real.sin (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring]
    exact Real.sin_pi_div_four
  have hc2 : Real.cos (-(Real.pi / 2) / 2) = Real.sqrt 2 / 2 := by
    rw [show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring, Real.cos_neg]
    exact Real.cos_pi_div_four
  have hs2 : Real.sin (-(Real.pi / 2) / 2) = -(Real.sqrt 2 / 2) := by
    rw [show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring, Real.sin_neg, Real.sin_pi_div_four]
  obtain ⟨V, hV⟩ : ∃ V, V = ry (Real.pi / 2) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = ry (-(Real.pi / 2)) := ⟨_, rfl⟩
  have hVff : V false false = k := by rw [hV, hk]; simp [ry, hc1]
  have hVft : V false true = k := by rw [hV, hk]; simp [ry, hs1]
  have hVtf : V true false = -k := by rw [hV, hk]; simp [ry, hs1]
  have hVtt : V true true = k := by rw [hV, hk]; simp [ry, hc1]
  have hUff : U false false = k := by rw [hU, hk]; simp [ry, hc2]
  have hUft : U false true = -k := by rw [hU, hk]; simp [ry, hs2]
  have hUtf : U true false = k := by rw [hU, hk]; simp [ry, hs2]
  have hUtt : U true true = k := by rw [hU, hk]; simp [ry, hc2]
  have hVu : V ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    cases i <;> cases j
    all_goals (try simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, hVff, hVft, hVtf,
      hVtt, hkstar, hkconj])
    all_goals (try ring_nf)
    all_goals (try simp only [hk2])
    all_goals (try norm_num)
  have hUu : U ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    cases i <;> cases j
    all_goals (try simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, hUff, hUft, hUtf,
      hUtt, hkstar, hkconj])
    all_goals (try ring_nf)
    all_goals (try simp only [hk2])
    all_goals (try norm_num)
  have h3 : czMat = ((1 : Matrix Bool Bool ℂ) ⊗ₖ V) * cnot * ((1 : Matrix Bool Bool ℂ) ⊗ₖ U) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d
    all_goals (try simp [czMat, cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Matrix.kroneckerMap_apply, Matrix.one_apply, hVff, hVft, hVtf, hVtt, hUff, hUft, hUtf, hUtt])
    all_goals (try ring_nf)
    all_goals (try simp only [hk2])
    all_goals (try norm_num)
  have h4 : czMat = (V ⊗ₖ (1 : Matrix Bool Bool ℂ)) * cnot.submatrix Prod.swap Prod.swap *
      (U ⊗ₖ (1 : Matrix Bool Bool ℂ)) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d
    all_goals (try simp [czMat, cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.submatrix_apply, hVff, hVft, hVtf, hVtt,
      hUff, hUft, hUtf, hUtt])
    all_goals (try ring_nf)
    all_goals (try simp only [hk2])
    all_goals (try norm_num)
  refine ⟨⟨U, hUu, V, hVu, h3⟩, ⟨U, hUu, V, hVu, h4⟩, ?_, ?_⟩
  · rw [← hV, ← hU]
    exact h3
  · rw [← hV, ← hU]
    exact h4
