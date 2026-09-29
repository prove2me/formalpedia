-- Prove2me | solution 1 for Pencil.exists_covector_sum_log_ge_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/18b49d33-cfb4-54c3-9432-bd81b9eca0d3

import Mathlib
import Theorems.Thm_Pencil_exists_rootOfUnity_torus_covector_sum_log_ge
import Theorems.Thm_RingHom_mem_range_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Pencil_exists_covector_sum_log_ge_of_ringHom
p2m_attr_erase "simp" "MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

theorem solution {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {r : ℕ} (v : Fin r → F) {i₀ : Fin r}
    (hi₀ : ∀ i, ‖σ (v i)‖ ≤ ‖σ (v i₀)‖)
    {ι : Type*} (T : Finset ι) (w : ι → Fin r → ℂ) (n : ι → ℕ)
    (hw : ∀ t ∈ T, ∃ p : Fin r × Fin r, σ (v p.1) * w t p.2 - σ (v p.2) * w t p.1 ≠ 0) :
    ∃ a : Fin r → F, (∑ i, v i * a i = 0) ∧
      (∀ i, ‖σ (a i)‖ ≤ r * ‖σ (v i₀)‖) ∧ (∀ i, i ≠ i₀ → ‖σ (a i)‖ = ‖σ (v i₀)‖) ∧
      ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖σ (v p.1) * w t p.2 - σ (v p.2) * w t p.1‖)
          - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2 + 1)
        ≤ ∑ t ∈ T, (n t : ℝ) * Real.log ‖∑ i, σ (a i) * w t i‖ := by
  classical
  obtain ⟨z, hz, hineq⟩ :=
    Pencil.exists_rootOfUnity_torus_covector_sum_log_ge (fun i ↦ σ (v i)) hi₀ T w n hw
  have hzF : ∀ j, ∃ ζ : F, σ ζ = z j := fun j ↦ by
    obtain ⟨m, hm, hzm⟩ := hz j
    obtain ⟨ζ, hζ⟩ := RingHom.mem_range_of_pow_eq_one σ hm hzm
    exact ⟨ζ, hζ⟩
  choose ζ hζ using hzF
  have hz1 : ∀ j, ‖z j‖ = 1 := fun j ↦ by
    obtain ⟨m, hm, hzm⟩ := hz j
    exact Complex.norm_eq_one_of_pow_eq_one hzm hm.ne'
  let a : Fin r → F := fun i ↦ v i₀ * ζ i - if i = i₀ then ∑ j, ζ j * v j else 0
  have hσa : ∀ i, σ (a i) = σ (v i₀) * z i - if i = i₀ then ∑ j, z j * σ (v j) else 0 := by
    intro i
    simp only [a, map_sub, map_mul, hζ]
    split_ifs
    · simp [map_sum, hζ]
    · simp
  have hrhs : ∀ t, ∑ i, σ (a i) * w t i = ∑ j, z j * (σ (v i₀) * w t j - σ (v j) * w t i₀) := by
    intro t
    simp only [hσa, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_sub, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  ·
    simp only [a, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum]
    exact sub_eq_zero.mpr (Finset.sum_congr rfl fun i _ ↦ by ring)
  ·
    intro i
    rw [hσa]
    split_ifs with hi
    · subst hi
      have : σ (v i) * z i - ∑ j, z j * σ (v j) = -∑ j ∈ Finset.univ.erase i, z j * σ (v j) := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]; ring
      rw [this, norm_neg]
      calc ‖∑ j ∈ Finset.univ.erase i, z j * σ (v j)‖
          ≤ ∑ j ∈ Finset.univ.erase i, ‖σ (v i)‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
            rw [norm_mul, hz1, one_mul]; exact hi₀ j
        _ = (r - 1 : ℝ) * ‖σ (v i)‖ := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin, Nat.cast_sub (Fin.pos i), Nat.cast_one]
        _ ≤ r * ‖σ (v i)‖ := by nlinarith [norm_nonneg (σ (v i))]
    · rw [sub_zero, norm_mul, hz1, mul_one]
      have : (1 : ℝ) ≤ r := by exact_mod_cast Fin.pos i
      nlinarith [norm_nonneg (σ (v i₀))]
  · intro i hi
    rw [hσa, if_neg hi, sub_zero, norm_mul, hz1, mul_one]
  · calc _ ≤ _ := hineq
      _ = _ := Finset.sum_congr rfl fun t _ ↦ by rw [hrhs]

end S_Pencil_exists_covector_sum_log_ge_of_ringHom
end P2MW
export P2MW.S_Pencil_exists_covector_sum_log_ge_of_ringHom (solution)
