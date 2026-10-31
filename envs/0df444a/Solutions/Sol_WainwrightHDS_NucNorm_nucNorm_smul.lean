-- Prove2me | solution 1 for WainwrightHDS.NucNorm.nucNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:27:57.788382+00:00
-- url     : https://prove2.me/submissions/0e4991f7-48e0-4f01-82c1-d219d073078d

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace WainwrightHDS.NucNorm

open Module End List

theorem eigenspace_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →ₗ[ℝ] E) {r : ℝ} (hr : r ≠ 0) (y : ℝ) :
    eigenspace (r • S) y = eigenspace S (y / r) := by
  ext v
  simp only [mem_eigenspace_iff, LinearMap.smul_apply]
  constructor
  · intro h
    have h1 : r⁻¹ • (r • S v) = r⁻¹ • (y • v) := by rw [h]
    rw [inv_smul_smul₀ hr] at h1
    rw [h1, smul_smul, inv_mul_eq_div]
  · intro h
    rw [h, smul_smul, mul_div_cancel₀ _ hr]

lemma antitone_ext_of_multiset_eq {n : ℕ} {f g : Fin n → ℝ}
    (hf : Antitone f) (hg : Antitone g)
    (h_multi : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    f = g := by
  have h_perm : List.ofFn f ~ List.ofFn g := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
    exact h_multi
  have h_sort_f : (List.ofFn f).Pairwise (· ≥ ·) := by
    rw [← List.sortedGE_iff_pairwise]
    exact hf.sortedGE_ofFn
  have h_sort_g : (List.ofFn g).Pairwise (· ≥ ·) := by
    rw [← List.sortedGE_iff_pairwise]
    exact hg.sortedGE_ofFn
  exact List.ofFn_injective (h_perm.eq_of_pairwise' h_sort_f h_sort_g)

lemma count_map_univ {n : ℕ} (f : Fin n → ℝ) (x : ℝ) :
    Multiset.count x (Multiset.map f Finset.univ.val) =
      (Finset.univ.filter (fun i : Fin n => f i = x)).card := by
  rw [Multiset.count_map]
  have : (Finset.univ.val.filter fun a => x = f a) =
      (Finset.univ.filter (fun a => f a = x)).val := by
    rw [Finset.filter_val]
    congr 1
    ext a
    simp [eq_comm]
  rw [this]
  rfl

theorem eigenvalues_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    {S S' : E →ₗ[ℝ] E} (hS : S.IsSymmetric) (hS' : S'.IsSymmetric)
    {r : ℝ} (hr : 0 < r) (hS'_eq : S' = r • S) :
    hS'.eigenvalues hn = fun i => r * hS.eigenvalues hn i := by
  have hf_anti : Antitone (hS'.eigenvalues hn) := hS'.eigenvalues_antitone hn
  have hg_anti : Antitone (fun i => r * hS.eigenvalues hn i) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (hS.eigenvalues_antitone hn hij) hr.le
  apply antitone_ext_of_multiset_eq hf_anti hg_anti
  apply Multiset.ext.mpr
  intro y
  rw [count_map_univ, count_map_univ]
  have h_card_f : (Finset.univ.filter (fun i => hS'.eigenvalues hn i = y)).card = finrank ℝ (eigenspace S' y) :=
    hS'.card_filter_eigenvalues_eq hn y
  have h_set_g : (Finset.univ.filter (fun i : Fin n => r * hS.eigenvalues hn i = y)) =
      (Finset.univ.filter (fun i : Fin n => hS.eigenvalues hn i = y / r)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← h, mul_div_cancel_left₀ _ hr.ne']
    · intro h
      rw [h, mul_div_cancel₀ _ hr.ne']
  have h_card_g : (Finset.univ.filter (fun i => r * hS.eigenvalues hn i = y)).card =
      finrank ℝ (eigenspace S (y / r)) := by
    rw [h_set_g]
    exact hS.card_filter_eigenvalues_eq hn (y / r)
  rw [h_card_f, h_card_g, hS'_eq, eigenspace_smul S hr.ne']

theorem singularValues_smul {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) (c : ℝ) (j : ℕ) :
    (c • T).singularValues j = |c| * T.singularValues j := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  set n := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = n := rfl
  by_cases hj : n ≤ j
  · have hle : Module.finrank ℝ E ≤ j := hn.symm ▸ hj
    rw [(c • T).singularValues_of_finrank_le hle,
        T.singularValues_of_finrank_le hle,
        mul_zero]
  have hj_lt : j < n := not_le.mp hj
  have hS'_eq : LinearMap.adjoint (c • T) ∘ₗ (c • T) = (c ^ 2) • (LinearMap.adjoint T ∘ₗ T) := by
    ext v; simp [smul_smul, sq]
  have hr_pos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have heig := eigenvalues_smul hn
    (T.isSymmetric_adjoint_comp_self)
    ((c • T).isSymmetric_adjoint_comp_self)
    hr_pos hS'_eq
  rw [(c • T).singularValues_of_lt hn hj_lt, T.singularValues_of_lt hn hj_lt]
  have heig_j : ((c • T).isSymmetric_adjoint_comp_self).eigenvalues hn ⟨j, hj_lt⟩ =
      c ^ 2 * (T.isSymmetric_adjoint_comp_self).eigenvalues hn ⟨j, hj_lt⟩ := by
    have := congr_fun heig ⟨j, hj_lt⟩
    exact this
  rw [heig_j, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem nucNorm_smul {d₁ d₂ : ℕ} (c : ℝ) (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    nucNorm (c • A) = |c| * nucNorm A := by
  dsimp [nucNorm, singVal]
  simp_rw [map_smul, singularValues_smul, ← Finset.mul_sum]

abbrev solution := @nucNorm_smul

end WainwrightHDS.NucNorm

abbrev solution := @WainwrightHDS.NucNorm.nucNorm_smul
