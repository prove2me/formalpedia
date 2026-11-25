-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.size_reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:55.972901+00:00
-- url     : https://prove2.me/submissions/4f3bc494-cc35-41c0-b4a2-9eff58e5d7e1

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_SizeReduce
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_span_tri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
private lemma span_gs_Iio_le_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (j : Fin d) : span ℝ (gs b '' Set.Iio j) ≤ (ℝ ∙ gs b j)ᗮ := by
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (gramSchmidt_orthogonal (𝕜 := ℝ) (f := b) (ne_of_lt hi).symm)
private lemma sub_gs_mem_span_gs_Iio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (j : Fin d) : b j - gs b j ∈ span ℝ (gs b '' Set.Iio j) := by
  have h := gramSchmidt_def'' (𝕜 := ℝ) (f := b) (n := j)
  nth_rewrite 1 [h]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
private lemma mu_eq_zero_of_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) {l j : Fin d} (hlj : l < j) : mu b l j = 0 := by
  have hm : b l ∈ span ℝ (gs b '' Set.Iio j) := by
    have h1 := mem_span_gramSchmidt (𝕜 := ℝ) (f := b) (le_refl l)
    refine Submodule.span_mono ?_ h1
    exact Set.image_mono (fun i hi => lt_of_le_of_lt hi hlj)
  have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b j hm)
  simp only [mu]
  rw [h0, zero_div]
private lemma mu_diag_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (hli : LinearIndependent ℝ b) (j : Fin d) : mu b j j = 1 := by
  have hne : gs b j ≠ 0 := gramSchmidt_ne_zero (𝕜 := ℝ) (n := j) hli
  have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b j (sub_gs_mem_span_gs_Iio b j))
  rw [inner_sub_right] at h0
  simp only [mu]
  rw [sub_eq_zero.mp h0, real_inner_self_eq_norm_sq]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
private lemma gs_sub_sum_lower_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : Fin d → E) (c : Fin d → Fin d → ℝ) (hc : ∀ i l, i ≤ l → c i l = 0) :
    gs (fun i => b i - ∑ l, c i l • b l) = gs b := by
  set b' : Fin d → E := fun i => b i - ∑ l, c i l • b l with hb'
  funext n
  have hV : span ℝ (b' '' Set.Iio n) = span ℝ (b '' Set.Iio n) :=
    (span_tri b c hc (Set.Iio n) (fun i hi l hl => lt_trans hl hi)).symm
  have hV' : span ℝ (gs b' '' Set.Iio n) = span ℝ (gs b '' Set.Iio n) := by
    rw [span_gramSchmidt_Iio, span_gramSchmidt_Iio, hV]
  have hu : gs b n - gs b' n ∈ span ℝ (gs b '' Set.Iio n) := by
    have e1 : gs b n - gs b' n = (b' n - gs b' n) - (b n - gs b n) + (b n - b' n) := by abel
    rw [e1]
    refine add_mem (sub_mem ?_ (sub_gs_mem_span_gs_Iio b n)) ?_
    · rw [← hV']
      exact sub_gs_mem_span_gs_Iio b' n
    · rw [span_gramSchmidt_Iio]
      show b n - (b n - ∑ l, c n l • b l) ∈ span ℝ (b '' Set.Iio n)
      rw [sub_sub_cancel]
      refine Submodule.sum_mem _ fun l _ => ?_
      by_cases hl : l < n
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
      · rw [hc n l (not_lt.mp hl), zero_smul]
        exact Submodule.zero_mem _
  have hu' : gs b n - gs b' n ∈ span ℝ (gs b' '' Set.Iio n) := by
    rw [hV']
    exact hu
  have hu1 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b n hu)
  have hu2 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (span_gs_Iio_le_orthogonal b' n hu')
  have h3 := inner_sub_left (𝕜 := ℝ) (gs b n) (gs b' n) (gs b n - gs b' n)
  rw [hu1, hu2, sub_zero] at h3
  have h4 := inner_self_eq_zero.mp h3
  exact (sub_eq_zero.mp h4).symm
private lemma exists_basis_sub_sum_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (e0 : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (W : Fin d → Fin d → ℤ)
    (hW : ∀ i l, i ≤ l → W i l = 0) :
    ∃ e1 : Module.Basis (Fin d) ℤ (Fin d → ℤ), ∀ i, e1 i = e0 i - ∑ l, W i l • e0 l := by
  set v : Fin d → (Fin d → ℤ) := fun i => e0 i - ∑ l, W i l • e0 l with hv
  have hfv : (fun i => f (v i)) = fun i => f (e0 i) - ∑ l, (W i l : ℝ) • f (e0 l) := by
    funext i
    simp only [hv, map_sub, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  have hspR : span ℝ (Set.range (fun i => f (v i))) = span ℝ (Set.range (fun i => f (e0 i))) := by
    rw [hfv, ← Set.image_univ, ← Set.image_univ]
    exact (span_tri (fun i => f (e0 i)) (fun i l => (W i l : ℝ)) (fun i l h => by simp [hW i l h])
      Set.univ (fun i _ l _ => Set.mem_univ l)).symm
  have hliR : LinearIndependent ℝ (fun i => f (v i)) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspR]
    exact linearIndependent_iff_card_eq_finrank_span.mp (hli e0)
  have hliZ : LinearIndependent ℤ v :=
    LinearIndependent.of_comp f (hliR.restrict_scalars
      (fun (a b : ℤ) (h : a • (1 : ℝ) = b • (1 : ℝ)) => by simpa using h))
  have hspZ : ⊤ ≤ span ℤ (Set.range v) := by
    have h := span_tri e0 W hW Set.univ (fun i _ l _ => Set.mem_univ l)
    rw [Set.image_univ, Set.image_univ, e0.span_eq] at h
    exact le_of_eq h
  exact ⟨Module.Basis.mk hliZ hspZ, fun i => Module.Basis.mk_apply hliZ hspZ i⟩
private lemma exists_basis_size_reduce_column {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (e0 : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d) :
    ∃ e1 : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      gs (fun i => f (e1 i)) = gs (fun i => f (e0 i)) ∧
      (∀ i, j < i → |mu (fun i => f (e1 i)) i j| ≤ 1 / 2) ∧
      ∀ i j', j < j' → mu (fun i => f (e1 i)) i j' = mu (fun i => f (e0 i)) i j' := by
  set b : Fin d → E := fun i => f (e0 i) with hb
  obtain ⟨e1, he1⟩ := exists_basis_sub_sum_lower f hli e0
    (fun i l => if l = j ∧ j < i then round (mu b i j) else 0)
    (fun i l h => if_neg (by rintro ⟨rfl, h2⟩; exact absurd h (not_le.mpr h2)))
  have hfe1 : (fun i => f (e1 i)) = fun i => b i -
      ∑ l, ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b l := by
    funext i
    rw [he1 i]
    simp only [map_sub, map_sum, map_zsmul, Int.cast_smul_eq_zsmul, hb]
  have hsum : ∀ i, ∑ l, ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b l
      = ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b j := by
    intro i
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hfe : ∀ i, f (e1 i) = b i - ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) • b j := by
    intro i
    have h := congrFun hfe1 i
    rw [h, hsum i]
  have hgs : gs (fun i => f (e1 i)) = gs b := by
    rw [hfe1]
    exact gs_sub_sum_lower_smul b (fun i l => ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ))
      (fun i l h => by
        show ((if l = j ∧ j < i then round (mu b i j) else 0 : ℤ) : ℝ) = 0
        rw [if_neg (by rintro ⟨rfl, h2⟩; exact absurd h (not_le.mpr h2)), Int.cast_zero])
  have hmu : ∀ i j', mu (fun i => f (e1 i)) i j' =
      mu b i j' - ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) * mu b j j' := by
    intro i j'
    have hfi := hfe i
    generalize ((if j < i then round (mu b i j) else 0 : ℤ) : ℝ) = r at hfi ⊢
    simp only [mu]
    rw [hgs, hfi, inner_sub_right, inner_smul_right]
    ring
  refine ⟨e1, hgs, fun i hi => ?_, fun i j' hj' => ?_⟩
  · rw [hmu, if_pos hi, mu_diag_eq_one b (hli e0) j, mul_one]
    exact abs_sub_round _
  · rw [hmu, mu_eq_zero_of_lt b hj', mul_zero, sub_zero]
end ReciprocityTheory.ReducedBases.T2
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    ∃ e' : Module.Basis (Fin d) ℤ (Fin d → ℤ), gs (fun i => f (e' i)) = gs (fun i => f (e i)) ∧
      ∀ i j : Fin d, j < i → |mu (fun i => f (e' i)) i j| ≤ 1 / 2 := by
  have key : ∀ k : ℕ, ∃ e' : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      gs (fun i => f (e' i)) = gs (fun i => f (e i)) ∧
      ∀ i j : Fin d, d ≤ j.val + k → j < i → |mu (fun i => f (e' i)) i j| ≤ 1 / 2 := by
    intro k
    induction k with
    | zero => exact ⟨e, rfl, fun i j h _ => absurd h (by have := j.isLt; omega)⟩
    | succ k ih =>
      obtain ⟨e', hgs', hred⟩ := ih
      by_cases hk : k < d
      · obtain ⟨e'', hgs'', hred'', hsame⟩ := exists_basis_size_reduce_column f hli e' ⟨d - k - 1, by omega⟩
        refine ⟨e'', hgs''.trans hgs', fun i j hj hji => ?_⟩
        by_cases hjv : j.val = d - k - 1
        · have hj0 : j = ⟨d - k - 1, by omega⟩ := Fin.ext hjv
          rw [hj0] at hji ⊢
          exact hred'' i hji
        · have hlt : (⟨d - k - 1, by omega⟩ : Fin d) < j := by
            rw [Fin.lt_iff_val_lt_val]
            show d - k - 1 < j.val
            omega
          rw [hsame i j hlt]
          exact hred i j (by omega) hji
      · exact ⟨e', hgs', fun i j _ hji => hred i j (by omega) hji⟩
  obtain ⟨e', hgs', hred⟩ := key d
  exact ⟨e', hgs', fun i j hji => hred i j (by omega) hji⟩
end ReciprocityTheory.ReducedBases.T2
