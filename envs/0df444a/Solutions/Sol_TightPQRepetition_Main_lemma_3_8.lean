-- Prove2me | solution 1 for TightPQRepetition.Main.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T21:20:49.382201+00:00
-- url     : https://prove2.me/submissions/3285d69a-bd3c-45c4-b136-ce48fa106bde

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Jordan

namespace TightPQRepetition.Main
open scoped InnerProductSpace

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure Blk (PA PB : H →L[ℂ] H) where
  S : Submodule ℂ H
  v : H
  vperp : H
  w : H
  wperp : H
  sv : ℝ
  span_v : S = Submodule.span ℂ {v, vperp}
  span_w : S = Submodule.span ℂ {w, wperp}
  act_A : ∀ x ∈ S, PA x = ⟪v, x⟫_ℂ • v
  act_B : ∀ x ∈ S, PB x = ⟪w, x⟫_ℂ • w
  dim : Module.finrank ℂ S = 1 ∨ Module.finrank ℂ S = 2
  one_dim : Module.finrank ℂ S = 1 →
    ((‖v‖ = 1 ∧ vperp = 0) ∨ (v = 0 ∧ ‖vperp‖ = 1)) ∧
    ((‖w‖ = 1 ∧ wperp = 0) ∨ (w = 0 ∧ ‖wperp‖ = 1))
  two_dim : Module.finrank ℂ S = 2 →
    ‖v‖ = 1 ∧ ‖vperp‖ = 1 ∧ ⟪v, vperp⟫_ℂ = 0 ∧
    ‖w‖ = 1 ∧ ‖wperp‖ = 1 ∧ ⟪w, wperp⟫_ℂ = 0 ∧ 0 < sv ∧ sv < 1
  overlap : ⟪w, v⟫_ℂ = (sv : ℂ)
  sv_nonneg : 0 ≤ sv

lemma inner_self_of_norm {x : H} (hx : ‖x‖ = 1) : ⟪x, x⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hx]; simp

lemma norm_of_inner_self {z : H} (h : ⟪z, z⟫_ℂ = 1) : ‖z‖ = 1 := by
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖z‖ ^ 2 = 1 := by
    have : ((‖z‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; exact h
    exact_mod_cast this
  have : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith

lemma finrank_pair {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (h : ⟪x, y⟫_ℂ = 0) :
    Module.finrank ℂ (Submodule.span ℂ {x, y}) = 2 := by
  have ho : Orthonormal ℂ ![x, y] := by
    rw [orthonormal_iff_ite]
    intro i j
    have hxx := inner_self_of_norm hx
    have hyy := inner_self_of_norm hy
    have h' : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, h]; simp
    fin_cases i <;> fin_cases j <;> simp [hxx, hyy, h, h', hx, hy]
  have := finrank_span_eq_card ho.linearIndependent
  have hr : Set.range ![x, y] = {x, y} := by
    simp [Matrix.range_cons, Set.pair_comm]
  rw [hr] at this
  simpa using this

lemma one_block {PA PB : H →L[ℂ] H} (K : Submodule ℂ H) (x v vperp w wperp : H) (sv : ℝ)
    (hx : ‖x‖ = 1) (hxK : x ∈ K)
    (hv : (v = x ∧ vperp = 0) ∨ (v = 0 ∧ vperp = x))
    (hw : (w = x ∧ wperp = 0) ∨ (w = 0 ∧ wperp = x))
    (hA : PA x = ⟪v, x⟫_ℂ • v) (hB : PB x = ⟪w, x⟫_ℂ • w)
    (hov : ⟪w, v⟫_ℂ = (sv : ℂ)) (hsv : 0 ≤ sv) :
    ∃ b : Blk PA PB, x ∈ b.S ∧ b.S ≤ K := by
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hfr : Module.finrank ℂ (Submodule.span ℂ {x}) = 1 := finrank_span_singleton hx0
  refine ⟨⟨Submodule.span ℂ {x}, v, vperp, w, wperp, sv, ?_, ?_, ?_, ?_, Or.inl hfr, ?_, ?_, hov, hsv⟩, ?_, ?_⟩
  · rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | rw [Set.pair_comm, Submodule.span_insert_zero] | rw [Submodule.span_insert_zero]
  · rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | rw [Set.pair_comm, Submodule.span_insert_zero] | rw [Submodule.span_insert_zero]
  · intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, hA, inner_smul_right, smul_smul]
  · intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, hB, inner_smul_right, smul_smul]
  · intro _
    constructor
    · rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hx, rfl⟩
      · exact Or.inr ⟨rfl, hx⟩
    · rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hx, rfl⟩
      · exact Or.inr ⟨rfl, hx⟩
  · intro h; simp only [hfr] at h; omega
  · exact Submodule.mem_span_singleton_self x
  · rw [Submodule.span_le]; simpa using hxK

lemma two_block {PA PB : H →L[ℂ] H} (K : Submodule ℂ H) (x w : H) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s ^ 2 + t ^ 2 = 1) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hxK : x ∈ K) (hwK : w ∈ K)
    (hxw : ⟪x, w⟫_ℂ = (s : ℂ))
    (hAx : PA x = x) (hAw : PA w = (s : ℂ) • x) (hBx : PB x = (s : ℂ) • w) (hBw : PB w = w) :
    ∃ b : Blk PA PB, x ∈ b.S ∧ b.S ≤ K := by
  have hwx : ⟪w, x⟫_ℂ = (s : ℂ) := by rw [← inner_conj_symm, hxw]; simp
  have hxx := inner_self_of_norm hx
  have hww := inner_self_of_norm hw
  have hst' : (s : ℂ) ^ 2 + (t : ℂ) ^ 2 = 1 := by exact_mod_cast hst
  have htt : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  set vp : H := ((t⁻¹ : ℝ) : ℂ) • (w - (s : ℂ) • x) with hvp
  set wp : H := ((t⁻¹ : ℝ) : ℂ) • (x - (s : ℂ) • w) with hwp
  have hti : ((t⁻¹ : ℝ) : ℂ) = ((t : ℂ))⁻¹ := Complex.ofReal_inv t
  have hw_eq : w = (t : ℂ) • vp + (s : ℂ) • x := by
    rw [hvp, hti, smul_smul, mul_inv_cancel₀ htt, one_smul]; abel
  have hx_eq : x = (t : ℂ) • wp + (s : ℂ) • w := by
    rw [hwp, hti, smul_smul, mul_inv_cancel₀ htt, one_smul]; abel
  have h1 : ⟪vp, vp⟫_ℂ = 1 := by
    rw [hvp, hti]
    simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hxx, hww, hxw, hwx,
      map_inv₀, Complex.conj_ofReal, Complex.conj_ofReal]
    field_simp
    linear_combination (-1 : ℂ) * hst'
  have h2 : ⟪wp, wp⟫_ℂ = 1 := by
    rw [hwp, hti]
    simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hxx, hww, hxw, hwx,
      map_inv₀, Complex.conj_ofReal]
    field_simp
    linear_combination (-1 : ℂ) * hst'
  have h3 : ⟪x, vp⟫_ℂ = 0 := by
    rw [hvp, inner_smul_right, inner_sub_right, inner_smul_right, hxw, hxx]; simp
  have h4 : ⟪w, wp⟫_ℂ = 0 := by
    rw [hwp, inner_smul_right, inner_sub_right, inner_smul_right, hwx, hww]; simp
  have hn1 := norm_of_inner_self h1
  have hn2 := norm_of_inner_self h2
  have hfr : Module.finrank ℂ (Submodule.span ℂ {x, vp}) = 2 := finrank_pair hx hn1 h3
  have hS1 : Submodule.span ℂ {x, w} = Submodule.span ℂ {x, vp} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · rw [hw_eq]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have hS2 : Submodule.span ℂ {x, w} = Submodule.span ℂ {w, wp} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      rcases hy with rfl | rfl
      · rw [hx_eq]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have hfr' : Module.finrank ℂ (Submodule.span ℂ {x, w}) = 2 := by rw [hS1]; exact hfr
  refine ⟨⟨Submodule.span ℂ {x, w}, x, vp, w, wp, s, hS1, hS2, ?_, ?_, Or.inr hfr', ?_, ?_, hwx, hs.le⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [map_add, map_smul, map_smul, hAx, hAw, inner_add_right, inner_smul_right, inner_smul_right,
      hxx, hxw, smul_smul, ← add_smul, mul_one]
  · intro y hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [map_add, map_smul, map_smul, hBx, hBw, inner_add_right, inner_smul_right, inner_smul_right,
      hww, hwx, smul_smul, ← add_smul, mul_one]
  · intro h; simp only [hfr'] at h; omega
  · intro _
    refine ⟨hx, hn1, h3, hw, hn2, h4, hs, ?_⟩
    nlinarith
  · exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hxK
    · exact hwK

variable [FiniteDimensional ℂ H]

lemma proj_symm {P : H →L[ℂ] H} (h : IsHermitianProjector P) (x y : H) :
    ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h.1) x y

lemma proj_idem {P : H →L[ℂ] H} (h : IsHermitianProjector P) (x : H) : P (P x) = P x := by
  have := DFunLike.congr_fun h.2.eq x
  simpa using this

lemma exists_unit_smul {x : H} (hx : x ≠ 0) : ∃ r : ℂ, ‖r • x‖ = 1 := by
  refine ⟨((‖x‖⁻¹ : ℝ) : ℂ), ?_⟩
  rw [norm_smul]; simp [hx]

lemma block_of_fixed {PA PB : H →L[ℂ] H} (hA : IsHermitianProjector PA)
    (hB : IsHermitianProjector PB) (K : Submodule ℂ H) (hKB : ∀ z ∈ K, PB z ∈ K)
    (x : H) (hx : ‖x‖ = 1) (hxK : x ∈ K) (hAx : PA x = x) (c : ℂ) (hc : PA (PB x) = c • x) :
    ∃ b : Blk PA PB, x ∈ b.S ∧ b.S ≤ K := by
  have hxx := inner_self_of_norm hx
  set u := PB x with hu
  have huK : u ∈ K := hKB x hxK
  have hidem : PB u = u := proj_idem hB x
  have hxu : ⟪x, u⟫_ℂ = (‖u‖ : ℂ) ^ 2 := by
    calc ⟪x, u⟫_ℂ = ⟪x, PB u⟫_ℂ := by rw [hidem]
      _ = ⟪PB x, u⟫_ℂ := (proj_symm hB x u).symm
      _ = (‖u‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K u
  have hcv : c = ⟪x, u⟫_ℂ := by
    have h1 : ⟪x, PA u⟫_ℂ = ⟪PA x, u⟫_ℂ := (proj_symm hA x u).symm
    rw [hAx, hc, inner_smul_right, hxx, mul_one] at h1
    exact h1
  have hperp : ⟪u, x - u⟫_ℂ = 0 := by
    have : ⟪PB x, x - u⟫_ℂ = ⟪x, PB (x - u)⟫_ℂ := proj_symm hB x _
    rw [map_sub, hidem, ← hu, sub_self, inner_zero_right] at this
    exact this
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (x - u) hperp
  rw [add_sub_cancel, hx] at hpy
  by_cases hs0 : ‖u‖ = 0
  · have hu0 : u = 0 := norm_eq_zero.1 hs0
    refine one_block K x x 0 0 x 0 hx hxK (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) ?_ ?_ ?_ le_rfl
    · rw [hAx, hxx, one_smul]
    · rw [← hu, hu0]; simp
    · simp
  by_cases ht0 : ‖x - u‖ = 0
  · have hux : u = x := (sub_eq_zero.1 (norm_eq_zero.1 ht0)).symm
    refine one_block K x x 0 x 0 1 hx hxK (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) ?_ ?_ ?_ zero_le_one
    · rw [hAx, hxx, one_smul]
    · rw [← hu, hux, hxx, one_smul]
    · rw [hxx]; simp
  have hs : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs0)
  have ht : 0 < ‖x - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0)
  set s := ‖u‖ with hsdef
  set t := ‖x - u‖ with htdef
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hti : ((s⁻¹ : ℝ) : ℂ) = (s : ℂ)⁻¹ := Complex.ofReal_inv s
  set w : H := ((s⁻¹ : ℝ) : ℂ) • u with hw
  have hwK : w ∈ K := Submodule.smul_mem _ _ huK
  have hnw : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, norm_inv, Real.norm_of_nonneg hs.le]
    exact inv_mul_cancel₀ hs.ne'
  have hAu : PA u = (s : ℂ) ^ 2 • x := by rw [hc, hcv, hxu]
  refine two_block K x w s t hs ht (by nlinarith) hx hnw hxK hwK ?_ hAx ?_ ?_ ?_
  · rw [hw, inner_smul_right, hxu, hti]; field_simp
  · rw [hw, map_smul, hAu, hti, smul_smul]; congr 1; field_simp
  · rw [hw, hti, smul_smul, mul_inv_cancel₀ hsC, one_smul]
  · rw [hw, map_smul, hidem]

lemma block_of_killed {PA PB : H →L[ℂ] H} (K : Submodule ℂ H)
    (x : H) (hx : ‖x‖ = 1) (hxK : x ∈ K) (hAx : PA x = 0) (hBx : PB x = x ∨ PB x = 0) :
    ∃ b : Blk PA PB, x ∈ b.S ∧ b.S ≤ K := by
  have hxx := inner_self_of_norm hx
  rcases hBx with h | h
  · refine one_block K x 0 x x 0 0 hx hxK (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) ?_ ?_ ?_ le_rfl
    · rw [hAx]; simp
    · rw [h, hxx, one_smul]
    · simp
  · refine one_block K x 0 x 0 x 0 hx hxK (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) ?_ ?_ ?_ le_rfl
    · rw [hAx]; simp
    · rw [h]; simp
    · simp

lemma exists_block {PA PB : H →L[ℂ] H} (hA : IsHermitianProjector PA)
    (hB : IsHermitianProjector PB) (K : Submodule ℂ H) (hKA : ∀ z ∈ K, PA z ∈ K)
    (hKB : ∀ z ∈ K, PB z ∈ K) (hK : K ≠ ⊥) :
    ∃ b : Blk PA PB, b.S ≤ K ∧ b.S ≠ ⊥ := by
  suffices h : ∃ b : Blk PA PB, (∃ x ∈ b.S, x ≠ 0) ∧ b.S ≤ K by
    obtain ⟨b, ⟨x, hx, hx0⟩, hb⟩ := h
    exact ⟨b, hb, fun h => hx0 (by rw [h] at hx; simpa using hx)⟩
  by_cases hex : ∃ z ∈ K, PA z ≠ 0
  · obtain ⟨z, hzK, hz⟩ := hex
    let Kr : Submodule ℂ H := K ⊓ LinearMap.ker ((PA : H →ₗ[ℂ] H) - LinearMap.id)
    have hmem : ∀ y, y ∈ Kr ↔ y ∈ K ∧ PA y = y := by
      intro y
      simp [Kr, sub_eq_zero]
    have hzr : PA z ∈ Kr := (hmem _).2 ⟨hKA z hzK, proj_idem hA z⟩
    have hKr : Nontrivial Kr :=
      ⟨⟨⟨PA z, hzr⟩, 0, fun h => hz (by simpa using congrArg Subtype.val h)⟩⟩
    let f : Kr →ₗ[ℂ] Kr := LinearMap.restrict ((PA * PB : H →L[ℂ] H) : H →ₗ[ℂ] H)
      (p := Kr) (q := Kr) (by
        intro y hy
        rw [hmem] at hy ⊢
        refine ⟨hKA _ (hKB _ hy.1), ?_⟩
        simpa using proj_idem hA (PB y))
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
    have hy0 : (y : H) ≠ 0 := fun h => hy.2 (Subtype.ext h)
    have hfy : PA (PB (y : H)) = c • (y : H) := by
      have := congrArg Subtype.val hy.apply_eq_smul
      simpa [f] using this
    have hyp := (hmem _).1 y.2
    obtain ⟨r, hr⟩ := exists_unit_smul hy0
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    obtain ⟨b, hb1, hb2⟩ := block_of_fixed hA hB K hKB (r • (y : H)) hr
      (Submodule.smul_mem _ _ hyp.1) (by rw [map_smul, hyp.2])
      c (by rw [map_smul, map_smul, hfy, smul_comm])
    refine ⟨b, ⟨r • (y : H), hb1, ?_⟩, hb2⟩
    exact smul_ne_zero hr0 hy0
  · push_neg at hex
    obtain ⟨z, hzK, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
    by_cases hPz : PB z = 0
    · obtain ⟨r, hr⟩ := exists_unit_smul hz0
      obtain ⟨b, hb1, hb2⟩ := block_of_killed (PA := PA) (PB := PB) K (r • z) hr
        (Submodule.smul_mem _ _ hzK) (by rw [map_smul, hex z hzK, smul_zero])
        (Or.inr (by rw [map_smul, hPz, smul_zero]))
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr
      exact ⟨b, ⟨r • z, hb1, smul_ne_zero hr0 hz0⟩, hb2⟩
    · obtain ⟨r, hr⟩ := exists_unit_smul hPz
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr
      obtain ⟨b, hb1, hb2⟩ := block_of_killed (PA := PA) (PB := PB) K (r • PB z) hr
        (Submodule.smul_mem _ _ (hKB z hzK)) (by rw [map_smul, hex _ (hKB z hzK), smul_zero])
        (Or.inl (by rw [map_smul, proj_idem hB]))
      exact ⟨b, ⟨r • PB z, hb1, smul_ne_zero hr0 hPz⟩, hb2⟩

lemma exists_family {PA PB : H →L[ℂ] H} (hA : IsHermitianProjector PA)
    (hB : IsHermitianProjector PB) : ∀ (n : ℕ) (K : Submodule ℂ H), Module.finrank ℂ K = n →
    (∀ z ∈ K, PA z ∈ K) → (∀ z ∈ K, PB z ∈ K) →
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → Blk PA PB),
      (∀ i j, i ≠ j → (b i).S ⟂ (b j).S) ∧ (∀ i, (b i).S ≤ K) ∧ ⨆ i, (b i).S = K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn hKA hKB
  by_cases hK : K = ⊥
  · refine ⟨Empty, inferInstance, fun e => e.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    simp [hK]
  obtain ⟨b0, hb0K, hb0⟩ := exists_block hA hB K hKA hKB hK
  set K' : Submodule ℂ H := K ⊓ b0.Sᗮ with hK'
  have hSA : ∀ z ∈ b0.S, PA z ∈ b0.S := by
    intro z hz
    rw [b0.act_A z hz]
    exact Submodule.smul_mem _ _ (by rw [b0.span_v]; exact Submodule.subset_span (by simp))
  have hSB : ∀ z ∈ b0.S, PB z ∈ b0.S := by
    intro z hz
    rw [b0.act_B z hz]
    exact Submodule.smul_mem _ _ (by rw [b0.span_w]; exact Submodule.subset_span (by simp))
  have hK'A : ∀ z ∈ K', PA z ∈ K' := by
    intro z hz
    rw [hK', Submodule.mem_inf] at hz ⊢
    refine ⟨hKA z hz.1, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro s hs
    rw [← proj_symm hA]
    exact hz.2 _ (hSA s hs)
  have hK'B : ∀ z ∈ K', PB z ∈ K' := by
    intro z hz
    rw [hK', Submodule.mem_inf] at hz ⊢
    refine ⟨hKB z hz.1, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro s hs
    rw [← proj_symm hB]
    exact hz.2 _ (hSB s hs)
  have hlt : K' < K := by
    refine lt_of_le_of_ne inf_le_left ?_
    obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb0
    intro h
    have hxK' : x ∈ K' := by rw [h]; exact hb0K hxS
    have := (Submodule.mem_inf.1 hxK').2 x hxS
    exact hx0 (inner_self_eq_zero.1 this)
  obtain ⟨ι', inst', b', hort, hle, hsup⟩ :=
    ih (Module.finrank ℂ K') (by rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt hlt) K' rfl
      hK'A hK'B
  have hperp : ∀ j, (b' j).S ⟂ b0.S := fun j => (hle j).trans inf_le_right
  refine ⟨Option ι', inferInstance, fun o => o.elim b0 b', ?_, ?_, ?_⟩
  · intro i j hij
    rcases i with _ | i <;> rcases j with _ | j
    · exact absurd rfl hij
    · exact (hperp j).symm
    · exact hperp i
    · exact hort i j (fun h => hij (by rw [h]))
  · intro i
    rcases i with _ | i
    · exact hb0K
    · exact (hle i).trans inf_le_left
  · rw [iSup_option]
    simp only [Option.elim_none, Option.elim_some]
    rw [hsup, hK', inf_comm]
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hb0K

end

theorem jordan_main {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (PA PB : H →L[ℂ] H) (hA : IsHermitianProjector PA)
    (hB : IsHermitianProjector PB) :
    Nonempty (JordanDecomposition PA PB) := by
  obtain ⟨ι, inst, b, hort, -, hsup⟩ := exists_family hA hB _ ⊤ rfl (fun _ _ => trivial)
    (fun _ _ => trivial)
  exact ⟨⟨ι, inst, fun i => (b i).S, hort, hsup, fun j => (b j).dim, fun j => (b j).v,
    fun j => (b j).vperp, fun j => (b j).w, fun j => (b j).wperp, fun j => (b j).sv,
    fun j => (b j).span_v, fun j => (b j).span_w, fun j => (b j).act_A, fun j => (b j).act_B,
    fun j => (b j).one_dim, fun j => (b j).two_dim, fun j => (b j).overlap,
    fun j => (b j).sv_nonneg⟩⟩

end TightPQRepetition.Main

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (PA PB : H →L[ℂ] H)
    (hA : TightPQRepetition.Main.IsHermitianProjector PA)
    (hB : TightPQRepetition.Main.IsHermitianProjector PB) :
    Nonempty (TightPQRepetition.Main.JordanDecomposition PA PB) :=
  TightPQRepetition.Main.jordan_main PA PB hA hB
