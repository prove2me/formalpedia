-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtE_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:10.874891+00:00
-- url     : https://prove2.me/submissions/37f227e8-03b1-4615-af40-9be47b9dccc0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtE_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtB_dual_short
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtC_prim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtD_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule
private theorem exists_int_inner_of_mem_span_int' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (b : Fin k → E) (y : E) (h : ∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) (v : E)
    (hv : v ∈ span ℤ (Set.range b)) : ∃ m : ℤ, inner ℝ y v = m := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  choose f hf using h
  refine ⟨∑ j, c j * f j, ?_⟩
  rw [inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hf j]
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (n : ℕ) : ∀ (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : ℝ), 0 < lam →
    (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) →
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam := by
  induction n with
  | zero =>
    intro b lam hlam hmin
    exact ⟨fun i ↦ Fin.elim0 i, linearIndependent_empty_type, fun i ↦ Fin.elim0 i,
      fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
    intro b lam hlam hmin
    classical
    obtain ⟨y1, hy1, hint1, hy1n⟩ := gtB_dual_short (Nat.succ_pos m) b lam hlam hmin
    obtain ⟨y0, xu, hxu, hy0, hint0, hy0n, h01⟩ := gtC_prim b y1 hy1 hint1
    obtain ⟨bW, hWL, hproj⟩ := gtD_lat b y0 xu hy0 hxu h01 hint0
    have hfin : Module.finrank ℝ (ℝ ∙ y0)ᗮ = m := by
      rw [Module.finrank_eq_card_basis bW, Fintype.card_fin]
    set φ : (ℝ ∙ y0)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
      ((stdOrthonormalBasis ℝ (ℝ ∙ y0)ᗮ).reindex (finCongr hfin)).repr with hφ
    set bE : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) := bW.map φ.toLinearEquiv with hbEdef
    have hbE : ∀ j, bE j = φ (bW j) := fun j ↦ rfl
    have hspanφ : ∀ p : (ℝ ∙ y0)ᗮ, p ∈ span ℤ (Set.range bW) → φ p ∈ span ℤ (Set.range bE) := by
      intro p hp
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_zsmul, hbE]
    have hspanφ' : ∀ x, x ∈ span ℤ (Set.range bE) → φ.symm x ∈ span ℤ (Set.range bW) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_zsmul, hbE, LinearIsometryEquiv.symm_apply_apply]
    have hminE : ∀ x ∈ span ℤ (Set.range bE), x ≠ 0 → lam ≤ ‖x‖ := by
      intro x hx hx0
      have h1 := hmin _ (hWL _ (hspanφ' x hx)) (by
        intro h
        apply hx0
        have h2 : φ.symm x = 0 := Subtype.ext h
        simpa using congrArg φ h2)
      exact h1.trans (le_of_eq (φ.symm.norm_map x))
    obtain ⟨z, hzli, hzint, hzn⟩ := ih bE lam hlam hminE
    set w : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ ((φ.symm (z i) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) with hw
    have hwy0 : ∀ i, inner ℝ y0 (w i) = 0 := fun i ↦
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (φ.symm (z i)).2
    have hwn : ∀ i, ‖w i‖ = ‖z i‖ := fun i ↦ φ.symm.norm_map (z i)
    have hwli : LinearIndependent ℝ w :=
      (hzli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker).map'
        (ℝ ∙ y0)ᗮ.subtype (Submodule.ker_subtype _)
    set u : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ w i - (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) • y0 with hu
    refine ⟨Fin.cons y0 u, ?_, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hexp : ∑ i : Fin m, g i.succ • u i = ∑ i : Fin m, g i.succ • w i -
          (∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) • y0 := by
        simp only [hu, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
      rw [hexp] at hg
      have hin := congrArg (fun v ↦ inner ℝ y0 v) hg
      simp only [inner_add_right, inner_sub_right, inner_sum, real_inner_smul_right, hwy0,
        mul_zero, Finset.sum_const_zero, inner_zero_right, real_inner_self_eq_norm_sq] at hin
      have hy0sq : ‖y0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy0)
      have hg0 : g 0 = ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) := by
        have h3 : (g 0 - ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) *
            ‖y0‖ ^ 2 = 0 := by linear_combination hin
        rcases mul_eq_zero.mp h3 with h | h
        · linarith
        · exact absurd h hy0sq
      have hX : ∑ i : Fin m, g i.succ • w i = 0 := by
        have h4 := hg
        rw [hg0] at h4
        simpa using h4
      have hsucc : ∀ i : Fin m, g i.succ = 0 := Fintype.linearIndependent_iff.mp hwli _ hX
      intro i
      cases i using Fin.cases with
      | zero => rw [hg0]; simp [hsucc]
      | succ k => exact hsucc k
    · intro i j
      cases i using Fin.cases with
      | zero => simpa using hint0 j
      | succ k =>
        simp only [Fin.cons_succ]
        obtain ⟨p, hp, hpeq⟩ := hproj (b j) (Submodule.subset_span ⟨j, rfl⟩)
        obtain ⟨k0, hk0⟩ := hint0 j
        obtain ⟨mp, hmp⟩ := exists_int_inner_of_mem_span_int' bE (z k) (hzint k) (φ p) (hspanφ p hp)
        refine ⟨mp + k0 * round (inner ℝ (w k) xu), ?_⟩
        have hb : b j = (p : EuclideanSpace ℝ (Fin (m + 1))) + inner ℝ y0 (b j) • xu := by
          rw [hpeq]; abel
        have hwp : inner ℝ (w k) (p : EuclideanSpace ℝ (Fin (m + 1))) = inner ℝ (z k) (φ p) := by
          show inner ℝ ((φ.symm (z k) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1)))
            (p : EuclideanSpace ℝ (Fin (m + 1))) = _
          rw [← Submodule.coe_inner, ← φ.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
        have h1 : inner ℝ (w k) (b j) = mp + k0 * inner ℝ (w k) xu := by
          conv_lhs => rw [hb]
          rw [inner_add_right, real_inner_smul_right, hk0, hwp, hmp]
        have h2 : inner ℝ (u k) (b j) = inner ℝ (w k) (b j) -
            (inner ℝ (w k) xu - round (inner ℝ (w k) xu)) * inner ℝ y0 (b j) := by
          simp only [hu, inner_sub_left, real_inner_smul_left]
        rw [h2, h1, hk0]
        push_cast
        ring
    · intro i
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        calc ‖y0‖ ≤ ‖y1‖ := hy0n
          _ ≤ ((m + 1 : ℕ) : ℝ) / lam := hy1n
          _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / lam := by gcongr; exact le_self_pow₀ h1 two_ne_zero
      | succ k =>
        simp only [Fin.cons_succ]
        have hc' : |inner ℝ (w k) xu - round (inner ℝ (w k) xu)| ≤ 1 / 2 := abs_sub_round _
        have hwy0' : inner ℝ (w k) y0 = 0 := by rw [real_inner_comm]; exact hwy0 k
        have hsq : ‖u k‖ ^ 2 = ‖w k‖ ^ 2 +
            (|inner ℝ (w k) xu - round (inner ℝ (w k) xu)| * ‖y0‖) ^ 2 := by
          simp only [hu]
          rw [norm_sub_sq_real, real_inner_smul_right, hwy0', norm_smul, Real.norm_eq_abs]
          ring
        have hA : ‖w k‖ ≤ (m : ℝ) ^ 2 / lam := by rw [hwn]; exact hzn k
        have hN : ‖y0‖ ≤ ((m : ℝ) + 1) / lam := by
          have := hy0n.trans hy1n
          simpa using this
        have hbd := gtE_bound m lam ‖w k‖ _ ‖y0‖ (Nat.cast_nonneg m) hlam (norm_nonneg _) hA
          (abs_nonneg _) hc' (norm_nonneg _) hN
        rw [← hsq] at hbd
        have h5 : ‖u k‖ ≤ ((m : ℝ) + 1) ^ 2 / lam :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hbd
        simpa using h5
end ReciprocityTheory.ChartRestriction.G.T0
