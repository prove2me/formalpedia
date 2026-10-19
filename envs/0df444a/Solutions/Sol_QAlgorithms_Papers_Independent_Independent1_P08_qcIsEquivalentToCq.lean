-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.qcIsEquivalentToCq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:02:04.609703+00:00
-- url     : https://prove2.me/submissions/8c35d032-b8d9-40cc-be33-a814643b8c24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
set_option autoImplicit false

/-! Ruskai, Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3.
All locators are PDF pages. Convexity is real; ambiguous claims are in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P08
open QAlgorithms.Entanglement QAlgorithms.QubitChannels

/-- QC to CQ, PDF pp.6-7, with independent unitary bases. -/
theorem gq_act_ket (W : Matrix Bool Bool ℂ) (c i : Bool) : (act W (ket c)) i = W i c := by
  cases c <;> cases i <;> simp [act, ket, Matrix.mulVec, dotProduct, Fintype.sum_bool]

theorem gq_pd_apply (W : Matrix Bool Bool ℂ) (c i j : Bool) :
    pureDensity (act W (ket c)) i j = W i c * star (W j c) := by
  simp [pureDensity, gq_act_ket]

theorem gq_pd_density (W : Matrix.unitaryGroup Bool ℂ) (c : Bool) :
    IsDensityMatrix (pureDensity (act (W : Matrix Bool Bool ℂ) (ket c))) := by
  constructor
  · have : pureDensity (act (W : Matrix Bool Bool ℂ) (ket c)) =
        Matrix.vecMulVec (fun i => (W : Matrix Bool Bool ℂ) i c) (star fun i => (W : Matrix Bool Bool ℂ) i c) := by
      ext i j; simp [gq_pd_apply, Matrix.vecMulVec_apply]
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  · have h := congrFun (congrFun (Unitary.coe_star_mul_self W) c) c
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    rw [Matrix.trace]
    simp only [Matrix.diag, gq_pd_apply]
    rw [← h]; apply Finset.sum_congr rfl; intro i _; ring

theorem gq_one_decomp (W : Matrix.unitaryGroup Bool ℂ) :
    (1 : Matrix Bool Bool ℂ) = ∑ c, pureDensity (act (W : Matrix Bool Bool ℂ) (ket c)) := by
  have h := Unitary.coe_mul_star_self W
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [← hij]
  simp [Matrix.mul_apply, gq_pd_apply, Matrix.sum_apply]

theorem gq_F_decomp (F : Matrix Bool Bool ℂ) (hF : F.IsHermitian) :
    F = ∑ c, ((hF.eigenvalues c : ℝ) : ℂ) • pureDensity (act (hF.eigenvectorUnitary : Matrix Bool Bool ℂ) (ket c)) := by
  conv_lhs => rw [hF.spectral_theorem]
  ext i j
  simp [Matrix.mul_apply, gq_pd_apply, Matrix.sum_apply, Matrix.diagonal, Fintype.sum_bool]
  ring

theorem solution (Phi : QMap) (hPhi : IsQC Phi) :
    ∃ U V : Matrix.unitaryGroup Bool ℂ, ∃ Psi : QMap,
      IsCQMap Psi ∧ Phi = changeBases U V Psi := by
  obtain ⟨U, F, ⟨hpos, hsum⟩, rfl⟩ := hPhi
  have hF0 := (hpos false).isHermitian
  set W := hF0.eigenvectorUnitary with hW
  set ev := hF0.eigenvalues with hev
  set P : Bool → Matrix Bool Bool ℂ := fun c => pureDensity (act (W : Matrix Bool Bool ℂ) (ket c)) with hP
  set Q : Bool → Matrix Bool Bool ℂ := fun b => pureDensity (act (U : Matrix Bool Bool ℂ) (ket b)) with hQ
  have h0 : F false = ∑ c, ((ev c : ℝ) : ℂ) • P c := gq_F_decomp _ hF0
  have h1 : F true = ∑ c, ((1 - ev c : ℝ) : ℂ) • P c := by
    have : F true = 1 - F false := by
      rw [← hsum]; simp [Fintype.sum_bool]
    rw [this, h0, gq_one_decomp W]
    simp [Fintype.sum_bool, sub_smul, P]
  have hle : ∀ c, ev c ≤ 1 := by
    intro c
    have hv := hF0.eigenvalues_eq c
    have hn : star ⇑(hF0.eigenvectorBasis c) ⬝ᵥ ⇑(hF0.eigenvectorBasis c) = 1 := by
      have h := congrFun (congrFun (Unitary.coe_star_mul_self W) c) c
      simpa [Matrix.mul_apply, dotProduct, hW] using h
    have hp := (hpos true).re_dotProduct_nonneg ⇑(hF0.eigenvectorBasis c)
    have : F true = 1 - F false := by
      rw [← hsum]; simp [Fintype.sum_bool]
    rw [this, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hn, map_sub] at hp
    rw [hev, hv]; simpa using hp
  refine ⟨1, 1, holevoMap (fun c => ((ev c : ℝ) : ℂ) • Q false + ((1 - ev c : ℝ) : ℂ) • Q true) P, ?_, ?_⟩
  · refine ⟨W, _, ?_, rfl⟩
    intro c
    have hQ0 := gq_pd_density U false
    have hQ1 := gq_pd_density U true
    have e0 : 0 ≤ ev c := (hpos false).eigenvalues_nonneg c
    have e1 : 0 ≤ 1 - ev c := by linarith [hle c]
    constructor
    · exact (hQ0.1.smul (by exact_mod_cast e0)).add (hQ1.1.smul (by exact_mod_cast e1))
    · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hQ0.2, hQ1.2]
      simp
  · apply LinearMap.ext; intro X
    have hcb : ∀ Y, (changeBases 1 1 (holevoMap (fun c => ((ev c : ℝ) : ℂ) • Q false + ((1 - ev c : ℝ) : ℂ) • Q true) P)) Y =
        holevoMap (fun c => ((ev c : ℝ) : ℂ) • Q false + ((1 - ev c : ℝ) : ℂ) • Q true) P Y := by
      intro Y; simp [changeBases, conjSuperop]
    rw [hcb]
    simp only [holevoMap, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_bool]
    rw [h0, h1]
    simp only [Fintype.sum_bool, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      smul_add, smul_smul, smul_eq_mul]
    module

