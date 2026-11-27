-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_proof_269581f951aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:34.998713+00:00
-- url     : https://prove2.me/submissions/19b379af-5fdf-4e30-bfb4-351831dc51ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_dvd_of_vanish_ea25bc3f8fad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_prime_X_sub_X_9d4656d4106e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_pair_of_dvd_1dbdfd65ac66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_swap_c2b194cb1d66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_open_4ef6119401a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_prod_dvd_of_primes_e23e47e272ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_homogeneousComponent_mul_of_isHomogeneous_7d8e3d96fdd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_block_chain_f2c1248d48d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_rename_swap_delta_dfcab9823831
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_isHomogeneous_delta_18346ae04145

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open AntisymDivisible
namespace GroundTheory.Heights₂.Heights
namespace AntisymDivisible
theorem _root_.solution : AntisymDivisible.Statement := by
  intro T _ _ N j P hP hvan
  obtain ⟨hPh, hPa⟩ := hP

  have anti : ∀ (τ : T) (a b : Fin N), a.val < b.val → (b.val < j ∨ j ≤ a.val) →
      rename (Equiv.swap (τ, a) (τ, b)) P = -P := by
    intro τ
    refine block_chain (fun a b => rename (Equiv.swap (τ, a) (τ, b)) P = -P) ?_ ?_
    · intro a b hb hbl
      exact hPa _ ⟨τ, a, b, hb, hbl, rfl⟩
    · intro a c b hac hcb hbl h1 h2
      have hca : (τ, a) ≠ (τ, c) := by simp [Fin.ext_iff]; omega
      have hba : (τ, a) ≠ (τ, b) := by simp [Fin.ext_iff]; omega
      have e := Equiv.swap_apply_apply (Equiv.swap (τ, c) (τ, b)) (τ, a) (τ, c)
      rw [Equiv.swap_apply_of_ne_of_ne hca hba, Equiv.swap_apply_left, Equiv.swap_inv] at e
      rw [e, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← rename_rename, ← rename_rename,
        h2, map_neg, h1, neg_neg, h2]

  set S : Finset (T × Fin N × Fin N) := Finset.univ.filter (fun t => t.2.1 < t.2.2) with hS
  let f : T × Fin N × Fin N → MvPolynomial (T × Fin N) ℝ := fun t => X (t.1, t.2.1) - X (t.1, t.2.2)
  have hΔ : antisymDelta T N = ∏ t ∈ S, f t := by
    simp only [antisymDelta, S, f, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext b
    simp
  have hprime : ∀ t ∈ S, Prime (f t) := by
    intro t ht
    simp only [S, Finset.mem_filter] at ht
    exact prime_X_sub_X (by simp [Fin.ext_iff]; omega)
  have hΔdvd : antisymDelta T N ∣ P := by
    rw [hΔ]
    refine prod_dvd_of_primes S f P hprime ?_ ?_
    · rintro ⟨τ, a, b⟩ ht ⟨τ', a', b'⟩ ht' hne hdv
      simp only [S, Finset.mem_filter] at ht ht'
      rcases pair_of_dvd (by simp [Fin.ext_iff]; omega) hdv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Prod.mk.injEq] at h1 h2
        exact hne (by rw [h1.1, h1.2, h2.2])
      · simp only [Prod.mk.injEq] at h1 h2
        rw [h1.2, h2.2] at ht'
        exact absurd (ht.2.trans ht'.2) (lt_irrefl _)
    · rintro ⟨τ, a, b⟩ ht
      simp only [S, Finset.mem_filter] at ht
      apply dvd_of_vanish
      by_cases hc : a.val < j ∧ j ≤ b.val
      · obtain ⟨O, hO, hne, h0⟩ := hvan τ a b hc.1 hc.2
        exact vanish_of_open _ _ P O hO hne h0
      · exact vanish_of_swap _ _ P (anti τ a b ht.2 (by omega))
  obtain ⟨l, hl⟩ := hΔdvd

  have hΔh := isHomogeneous_delta (T := T) (N := N)
  have hP1 : P = antisymDelta T N * homogeneousComponent 1 l := by
    have := homogeneousComponent_mul_of_isHomogeneous hΔh l 1
    rw [← hl, homogeneousComponent_of_mem hPh, if_pos rfl] at this
    exact this
  have hΔ0 : antisymDelta T N ≠ 0 := by
    rw [hΔ, Finset.prod_ne_zero_iff]
    exact fun t ht => (hprime t ht).ne_zero
  set l₁ := homogeneousComponent 1 l with hl₁
  have hl₁h : l₁ ∈ homogeneousSubmodule (T × Fin N) ℝ 1 := homogeneousComponent_isHomogeneous 1 l

  have inv : ∀ (τ : T) (a b : Fin N), a.val < b.val → (b.val < j ∨ j ≤ a.val) →
      rename (Equiv.swap (τ, a) (τ, b)) l₁ = l₁ := by
    intro τ a b hab hbl
    have h1 := anti τ a b hab hbl
    have h2 := rename_swap_delta (T := T) τ (ne_of_lt hab)
    rw [hP1, map_mul, h2] at h1
    apply mul_left_cancel₀ hΔ0
    linear_combination -h1

  rw [homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun] at hl₁h
  obtain ⟨c, hc⟩ := hl₁h
  have coeff_lin : ∀ (g : T × Fin N → T × Fin N) (u : T × Fin N),
      coeff (Finsupp.single u 1) (∑ w, c w • (X (g w) : MvPolynomial (T × Fin N) ℝ)) =
        ∑ w, if g w = u then c w else 0 := by
    intro g u
    simp only [coeff_sum, coeff_smul, coeff_X, Finsupp.single_left_inj one_ne_zero, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
  have const : ∀ (τ : T) (a b : Fin N), a.val < b.val → (b.val < j ∨ j ≤ a.val) →
      c (τ, a) = c (τ, b) := by
    intro τ a b hab hbl
    have h := congrArg (coeff (Finsupp.single (τ, a) 1)) (inv τ a b hab hbl)
    rw [← hc, map_sum] at h
    simp only [map_smul, rename_X] at h
    rw [coeff_lin, coeff_lin] at h
    simp only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, id] at h
    exact h.symm
  refine ⟨l₁, ⟨?_, ?_⟩, hP1⟩
  · exact homogeneousComponent_isHomogeneous 1 l
  · intro g hg
    rw [← hc, map_sum]
    simp only [map_smul, rename_X]
    have hcg : ∀ w, c (g w) = c w := by
      rintro ⟨τ, a⟩
      obtain ⟨h1, h2⟩ := hg (τ, a)
      rcases hga : g (τ, a) with ⟨τ', a'⟩
      rw [hga] at h1 h2
      simp only at h1 h2
      subst h1
      rcases lt_trichotomy a.val a'.val with h | h | h
      · refine (const τ' a a' h ?_).symm
        by_cases ha : a.val < j
        · exact Or.inl (h2.2 ha)
        · exact Or.inr (by omega)
      · rw [Fin.ext h]
      · refine const τ' a' a h ?_
        by_cases ha : a.val < j
        · exact Or.inl ha
        · exact Or.inr (by have := mt h2.1 ha; omega)
    calc ∑ w, c w • X (g w) = ∑ w, c (g w) • (X (g w) : MvPolynomial (T × Fin N) ℝ) := by
          simp_rw [hcg]
      _ = ∑ w, c w • X w := Equiv.sum_comp g (fun w => c w • (X w : MvPolynomial (T × Fin N) ℝ))
end AntisymDivisible
end GroundTheory.Heights₂.Heights
