-- Prove2me | solution 1 for RegularSingular.exists_twoLevel_expansion_of_commuting_systems
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cfcc7730-3467-527d-8581-bece644ac5d4

import Theorems.Thm_RegularSingular_exists_logDepth_le_natDegree_norm_sub_expansion_le
import Theorems.Thm_RegularSingular_hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
import Theorems.Thm_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le
import Theorems.Thm_Matrix_aeval_const_term_eq_zero_of_forall_pos
import Theorems.Thm_RegularSingular_exists_expansion_coeff_of_folded_system
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_exists_twoLevel_expansion_of_commuting_systems

set_option autoImplicit false
set_option maxHeartbeats 6400000

open Finset Filter Topology

section Reindex

private theorem sum_reindex_family_smul {E : Type*} [AddCommGroup E] [Module ℂ E]
    {n J D : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (S : Finset ℂ)
    (hcov : ∀ μ ∈ S, ∃ i, e i = μ) (hD : D ≤ J) (w : ℂ → ℕ → ℂ) (v : ℂ → ℕ → E) :
    ∑ μ ∈ S, ∑ j ∈ Finset.range D, w μ j • v μ j =
      ∑ i : Fin n, ∑ j : Fin J, w (e i) j • (if e i ∈ S ∧ (j : ℕ) < D then v (e i) j else 0) := by
  classical
  have hinner : ∀ μ : ℂ, ∑ j ∈ Finset.range D, w μ j • v μ j =
      ∑ j : Fin J, w μ j • (if (j : ℕ) < D then v μ j else 0) := by
    intro μ
    rw [Fin.sum_univ_eq_sum_range (fun j => w μ j • (if j < D then v μ j else 0)) J]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range J) (fun j => j < D)]
    have h1 : (Finset.range J).filter (fun j => j < D) = Finset.range D := by
      ext j; simp [Finset.mem_filter, Finset.mem_range]; omega
    have h2 : ∑ j ∈ (Finset.range J).filter (fun j => ¬ j < D), w μ j • (if j < D then v μ j else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      simp [hj.2]
    rw [h1, h2, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp [hj]
  have himg : S = (Finset.univ.filter (fun i : Fin n => e i ∈ S)).image e := by
    ext μ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hμ
      obtain ⟨i, hi⟩ := hcov μ hμ
      exact ⟨i, hi ▸ hμ, hi⟩
    · rintro ⟨i, hi, rfl⟩
      exact hi
  rw [Finset.sum_congr rfl fun μ _ => hinner μ]
  have hL : ∑ μ ∈ S, ∑ j : Fin J, w μ j • (if (j : ℕ) < D then v μ j else 0) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => e i ∈ S), ∑ j : Fin J,
        w (e i) j • (if (j : ℕ) < D then v (e i) j else 0) := by
    conv_lhs => rw [himg]
    exact Finset.sum_image (fun i _ j _ hij => he hij)
  rw [hL, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => e i ∈ S)]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ e i ∈ S), ∑ j : Fin J,
      w (e i) j • (if e i ∈ S ∧ (j : ℕ) < D then v (e i) j else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_filter] at hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi.2]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_filter] at hi
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [hi.2]

private theorem cpow_add_natCast_mul (z : ℂ) (k : ℕ) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (z + k) = (y : ℂ) ^ z * (y : ℂ) ^ k := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hy.ne'), Complex.cpow_natCast]

end Reindex

section FirstLevel

private theorem firstLevel_on_strip
    {n J R d d₂ : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (q : Polynomial ℂ) (hq : q ≠ 0)
    (hcov : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hgq : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hJ : q.natDegree ≤ J)
    (P : Type*) [TopologicalSpace P]
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (hMc : ∀ b, Continuous fun p => Mc p b) (hA : ∀ k b, Continuous fun p => A p k b)
    (L : ℝ) (hMcL : ∀ p b i j, ‖Mc p b i j‖ ≤ L) (hAL : ∀ p k b, ‖A p k b‖ ≤ L)
    (hq0 : ∀ p, ∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc p b) q = 0)
    (Z : ℝ) (hZ : 1 ≤ Z)
    (F Fy : P → ℝ → ℝ → (Fin R → ℂ))
    (hF : ContinuousOn (fun w : P × ℝ × ℝ => F w.1 w.2.1 w.2.2) (Set.univ ×ˢ Set.Ioc 0 1 ×ˢ Set.Ioc 0 Z))
    (hsysY : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F p y z) (Fy p y z) y ∧
      (y : ℂ) • Fy p y z =
        (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc p b i j) • F p y z j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A p k b (F p y z))
    (m B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y z‖ ≤ B * y ^ (-m) * z ^ (-m)) :
    ∃ (c : Fin n → Fin J → P → ℝ → (Fin R → ℂ)) (K₁ : ℝ), 0 ≤ K₁ ∧
      (∀ i j, ContinuousOn (fun w : P × ℝ => c i j w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 Z)) ∧
      (∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ‖c i j p z‖ ≤ K₁ * z ^ (-m)) ∧
      (∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y z - ∑ i : Fin n, ∑ j : Fin J,
            ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • c i j p z‖ ≤ K₁ * z ^ (-m) * y ^ (ρ + δ)) := by
  classical
  obtain ⟨D, hD, hE⟩ := RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le q hq

  set Pset : Set (P × ℝ) := Set.univ ×ˢ Set.Ioc (0 : ℝ) Z with hPset
  have hzmem : ∀ w : Pset, w.1.2 ∈ Set.Ioc (0 : ℝ) Z := fun w => (Set.mem_prod.1 w.2).2
  have hz_cont : Continuous fun w : Pset => ((w.1.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_snd.comp continuous_subtype_val)
  have hp_cont : Continuous fun w : Pset => w.1.1 := continuous_fst.comp continuous_subtype_val
  have hzpos : ∀ w : Pset, 0 < w.1.2 := fun w => (hzmem w).1
  have hzle : ∀ w : Pset, w.1.2 ≤ Z := fun w => (hzmem w).2

  let M₁ : Pset → Matrix (Fin R) (Fin R) ℂ := fun w => ∑ b : Fin (d₂ + 1), ((w.1.2 : ℂ) ^ (b : ℕ)) • Mc w.1.1 b
  let A₁ : Pset → Fin d → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)) :=
    fun w k => ∑ b : Fin (d₂ + 1), ((w.1.2 : ℂ) ^ (b : ℕ)) • A w.1.1 k b
  have hM₁c : Continuous M₁ := by
    refine continuous_finsetSum _ fun b _ => ?_
    exact (hz_cont.pow _).smul ((hMc b).comp hp_cont)
  have hA₁c : ∀ k, Continuous fun w => A₁ w k := by
    intro k
    refine continuous_finsetSum _ fun b _ => ?_
    exact (hz_cont.pow _).smul ((hA k b).comp hp_cont)
  set L₁ : ℝ := ((d₂ : ℝ) + 1) * Z ^ d₂ * |L| with hL₁
  have hzpow : ∀ (w : Pset) (b : Fin (d₂ + 1)), ‖((w.1.2 : ℝ) : ℂ) ^ (b : ℕ)‖ ≤ Z ^ d₂ := by
    intro w b
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hzpos w)]
    calc w.1.2 ^ (b : ℕ) ≤ Z ^ (b : ℕ) := pow_le_pow_left₀ (hzpos w).le (hzle w) _
      _ ≤ Z ^ d₂ := pow_le_pow_right₀ hZ (Nat.lt_succ_iff.1 b.2)
  have hM₁L : ∀ w i j, ‖M₁ w i j‖ ≤ L₁ := by
    intro w i j
    have h1 : M₁ w i j = ∑ b : Fin (d₂ + 1), ((w.1.2 : ℂ) ^ (b : ℕ)) * Mc w.1.1 b i j := by
      simp [M₁, Matrix.sum_apply, Matrix.smul_apply]
    rw [h1]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b : Fin (d₂ + 1), ‖((w.1.2 : ℝ) : ℂ) ^ (b : ℕ) * Mc w.1.1 b i j‖
        ≤ ∑ _b : Fin (d₂ + 1), Z ^ d₂ * |L| := Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul (hzpow w b) ((hMcL _ _ _ _).trans (le_abs_self L)) (norm_nonneg _)
            (pow_nonneg (by linarith) _)
      _ = L₁ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL₁]; push_cast; ring
  have hA₁L : ∀ w k, ‖A₁ w k‖ ≤ L₁ := by
    intro w k
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b : Fin (d₂ + 1), ‖((w.1.2 : ℝ) : ℂ) ^ (b : ℕ) • A w.1.1 k b‖
        ≤ ∑ _b : Fin (d₂ + 1), Z ^ d₂ * |L| := Finset.sum_le_sum fun b _ => by
          rw [norm_smul]
          exact mul_le_mul (hzpow w b) ((hAL _ _ _).trans (le_abs_self L)) (norm_nonneg _)
            (pow_nonneg (by linarith) _)
      _ = L₁ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL₁]; push_cast; ring
  have hM₁q : ∀ w : Pset, Polynomial.aeval (M₁ w) q = 0 := fun w => hq0 w.1.1 w.1.2 (hzpos w)

  have hφ : Continuous fun v : Pset × ℝ => ((v.1.1.1, v.2, v.1.1.2) : P × ℝ × ℝ) := by fun_prop
  have hF₁c : ContinuousOn (fun v : Pset × ℝ => F v.1.1.1 v.2 v.1.1.2) (Set.univ ×ˢ Set.Ioc 0 1) := by
    refine hF.comp hφ.continuousOn ?_
    intro v hv
    exact Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨(Set.mem_prod.1 hv).2, hzmem v.1⟩⟩

  let B₁ : Pset → ℝ := fun w => B * w.1.2 ^ (-m)
  have hB₁c : Continuous B₁ := by
    refine continuous_const.mul ?_
    exact (continuous_snd.comp continuous_subtype_val).rpow_const fun w => Or.inl (hzpos w).ne'
  have hB₁loc : ∀ w₀ : Pset, ∃ B₀ : ℝ, ∀ᶠ w in nhds w₀, B₁ w ≤ B₀ := by
    intro w₀
    refine ⟨B₁ w₀ + 1, ?_⟩
    have h := hB₁c.tendsto w₀
    exact (h.eventually (Iio_mem_nhds (by linarith : B₁ w₀ < B₁ w₀ + 1))).mono fun w hw => le_of_lt hw
  have hsys₁ : ∀ w : Pset, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F w.1.1 y w.1.2) (Fy w.1.1 y w.1.2) y ∧
      (y : ℂ) • Fy w.1.1 y w.1.2 = (fun i => ∑ j, M₁ w i j • F w.1.1 y w.1.2 j) +
        ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A₁ w k (F w.1.1 y w.1.2) := by
    intro w y hy
    obtain ⟨h1, h2⟩ := hsysY w.1.1 w.1.2 (hzmem w) y hy
    refine ⟨h1, ?_⟩
    rw [h2]
    congr 1
    · funext i
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp [M₁, Matrix.sum_apply, Matrix.smul_apply]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [A₁, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  have hbound₁ : ∀ w : Pset, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F w.1.1 y w.1.2‖ ≤ B₁ w * y ^ (-m) := by
    intro w y hy
    have h := hbound w.1.1 w.1.2 (hzmem w) y hy
    calc _ ≤ B * y ^ (-m) * w.1.2 ^ (-m) := h
      _ = B₁ w * y ^ (-m) := by simp only [B₁]; ring

  have hθ : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + δ < (e₀ + k).re := by
    intro e₀ he₀ k hk
    have h := hgq e₀ he₀ k hk
    linarith

  obtain ⟨S, κ, hS, hP⟩ := hE ℂ R d L₁ m ρ (ρ + δ) hθ
  obtain ⟨c₁, hc₁c, hc₁⟩ := hP Pset M₁ A₁ hM₁c hM₁L hM₁q hA₁c hA₁L
    (fun w y => F w.1.1 y w.1.2) (fun w y => Fy w.1.1 y w.1.2) B₁ hF₁c hB₁loc hsys₁ hbound₁
  have hcovS : ∀ μ ∈ S, ∃ i, e i = μ := by
    intro μ hμ
    obtain ⟨hre, e₀, k, hr, hk⟩ := hS μ hμ
    obtain ⟨i, hi⟩ := hcov e₀ hr k (hk ▸ hre)
    exact ⟨i, hi.trans hk.symm⟩
  have hDJ : D ≤ J := hD.trans hJ
  have hmemP : ∀ (p : P) (z : ℝ), z ∈ Set.Ioc (0 : ℝ) Z → ((p, z) : P × ℝ) ∈ Pset :=
    fun p z hz => Set.mem_prod.2 ⟨Set.mem_univ _, hz⟩

  refine ⟨fun i j p z => if h : ((p, z) : P × ℝ) ∈ Pset then
      (if e i ∈ S ∧ (j : ℕ) < D then c₁ (e i) j ⟨(p, z), h⟩ else 0) else 0,
    |κ| * B, mul_nonneg (abs_nonneg κ) hB, ?_, ?_, ?_⟩
  ·
    intro i j
    rw [continuousOn_iff_continuous_restrict]
    by_cases hij : e i ∈ S ∧ (j : ℕ) < D
    · have hres : Pset.domRestrict (fun w : P × ℝ =>
          if h : ((w.1, w.2) : P × ℝ) ∈ Pset then
            (if e i ∈ S ∧ (j : ℕ) < D then c₁ (e i) j ⟨(w.1, w.2), h⟩ else 0) else 0) = c₁ (e i) j := by
        funext w
        simp only [Set.domRestrict_apply, Prod.mk.eta, dif_pos w.2, if_pos hij]
      rw [hres]
      exact hc₁c (e i) j
    · have hres : Pset.domRestrict (fun w : P × ℝ =>
          if h : ((w.1, w.2) : P × ℝ) ∈ Pset then
            (if e i ∈ S ∧ (j : ℕ) < D then c₁ (e i) j ⟨(w.1, w.2), h⟩ else 0) else 0) = fun _ => 0 := by
        funext w
        simp only [Set.domRestrict_apply, Prod.mk.eta, dif_pos w.2, if_neg hij]
      rw [hres]
      exact continuous_const
  ·
    intro p i j z hz
    simp only [dif_pos (hmemP p z hz)]
    have hzm : 0 ≤ z ^ (-m) := Real.rpow_nonneg hz.1.le _
    split_ifs with hij
    · have h := (hc₁ ⟨(p, z), hmemP p z hz⟩).1 (e i) j
      calc _ ≤ κ * B₁ ⟨(p, z), hmemP p z hz⟩ := h
        _ = κ * B * z ^ (-m) := by simp only [B₁]; ring
        _ ≤ |κ| * B * z ^ (-m) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self κ) hB) hzm
    · rw [norm_zero]; positivity
  ·
    intro p z hz y hy
    have hmain := (hc₁ ⟨(p, z), hmemP p z hz⟩).2.2 y hy
    have hsum : ∑ μ ∈ S, ∑ j ∈ Finset.range D,
        ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c₁ μ j ⟨(p, z), hmemP p z hz⟩ =
        ∑ i : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
          (if h : ((p, z) : P × ℝ) ∈ Pset then
            (if e i ∈ S ∧ (j : ℕ) < D then c₁ (e i) j ⟨(p, z), h⟩ else 0) else 0) := by
      rw [sum_reindex_family_smul e he S hcovS hDJ (fun μ j => (y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j)
        (fun μ j => c₁ μ j ⟨(p, z), hmemP p z hz⟩)]
      simp only [dif_pos (hmemP p z hz)]
    rw [← hsum]
    refine hmain.trans ?_
    have hyθ : 0 ≤ y ^ (ρ + δ) := Real.rpow_nonneg hy.1.le _
    have hzm : 0 ≤ z ^ (-m) := Real.rpow_nonneg hz.1.le _
    calc κ * B₁ ⟨(p, z), hmemP p z hz⟩ * y ^ (ρ + δ) = κ * B * z ^ (-m) * y ^ (ρ + δ) := by
          simp only [B₁]; ring
      _ ≤ |κ| * B * z ^ (-m) * y ^ (ρ + δ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self κ) hB) hzm) hyθ

end FirstLevel

section SecondSystem

private noncomputable def Vlin {R d' d₂' : ℕ} (Mc' : Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (a : Fin (d₂' + 1)) (z : ℝ) :
    (Fin R → ℂ) →ₗ[ℂ] (Fin R → ℂ) :=
  Matrix.mulVecLin (Mc' a) + ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • ((A' k a : (Fin R → ℂ) →L[ℂ] (Fin R → ℂ)) :
    (Fin R → ℂ) →ₗ[ℂ] (Fin R → ℂ))

private theorem Vlin_apply {R d' d₂' : ℕ} (Mc' : Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (a : Fin (d₂' + 1)) (z : ℝ)
    (v : Fin R → ℂ) :
    Vlin Mc' A' a z v = Matrix.mulVec (Mc' a) v + ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' k a v := by
  simp [Vlin, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem rhs_eq_sum_Vlin {R d' d₂' : ℕ} (Mc' : Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (y z : ℝ) (v : Fin R → ℂ) :
    ((fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' a i j) • v j) +
        ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' k a v) =
      ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z v := by
  have h1 : (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' a i j) • v j) =
      ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Matrix.mulVec (Mc' a) v := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' k a v =
      ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' k a v := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, mul_comm]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Vlin_apply, smul_add]

private theorem norm_Vlin_le {R d' d₂' : ℕ} (Mc' : Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (L : ℝ)
    (hMcL' : ∀ a i j, ‖Mc' a i j‖ ≤ L) (hAL' : ∀ k a, ‖A' k a‖ ≤ L)
    (a : Fin (d₂' + 1)) (z : ℝ) (hz : z ∈ Set.Ioc (0 : ℝ) 2) (v : Fin R → ℂ) :
    ‖Vlin Mc' A' a z v‖ ≤ ((R : ℝ) * |L| + (d' : ℝ) * 2 ^ d' * |L|) * ‖v‖ := by
  classical
  rw [Vlin_apply]
  have hL0 : 0 ≤ |L| := abs_nonneg L
  have h1 : ‖Matrix.mulVec (Mc' a) v‖ ≤ (R : ℝ) * |L| * ‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin R, ‖Mc' a i j * v j‖ ≤ ∑ _j : Fin R, |L| * ‖v‖ := Finset.sum_le_sum fun j _ => by
            rw [norm_mul]
            exact mul_le_mul ((hMcL' a i j).trans (le_abs_self L)) (norm_le_pi_norm v j) (norm_nonneg _) hL0
      _ = (R : ℝ) * |L| * ‖v‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h2 : ‖∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' k a v‖ ≤ (d' : ℝ) * 2 ^ d' * |L| * ‖v‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k : Fin d', ‖((z : ℂ) ^ ((k : ℕ) + 1)) • A' k a v‖ ≤ ∑ _k : Fin d', 2 ^ d' * |L| * ‖v‖ :=
          Finset.sum_le_sum fun k _ => by
            rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz.1]
            have hzk : z ^ ((k : ℕ) + 1) ≤ 2 ^ d' :=
              (pow_le_pow_left₀ hz.1.le hz.2 _).trans (pow_le_pow_right₀ (by norm_num) (by omega))
            calc z ^ ((k : ℕ) + 1) * ‖A' k a v‖ ≤ 2 ^ d' * (|L| * ‖v‖) :=
                  mul_le_mul hzk ((ContinuousLinearMap.le_opNorm _ _).trans
                    (mul_le_mul_of_nonneg_right ((hAL' k a).trans (le_abs_self L)) (norm_nonneg _)))
                    (norm_nonneg _) (by positivity)
              _ = 2 ^ d' * |L| * ‖v‖ := by ring
      _ = (d' : ℝ) * 2 ^ d' * |L| * ‖v‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc _ ≤ ‖Matrix.mulVec (Mc' a) v‖ + ‖∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' k a v‖ := norm_add_le _ _
    _ ≤ (R : ℝ) * |L| * ‖v‖ + (d' : ℝ) * 2 ^ d' * |L| * ‖v‖ := add_le_add h1 h2
    _ = _ := by ring

private theorem continuousOn_Vlin_comp {R d' d₂' : ℕ} (Mc' : Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (a : Fin (d₂' + 1))
    {s : Set ℝ} {u : ℝ → (Fin R → ℂ)} (hu : ContinuousOn u s) :
    ContinuousOn (fun z => Vlin Mc' A' a z (u z)) s := by
  have h : (fun z => Vlin Mc' A' a z (u z)) =
      fun z => Matrix.mulVec (Mc' a) (u z) + ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' k a (u z) := by
    funext z; rw [Vlin_apply]
  rw [h]
  refine ContinuousOn.add ?_ ?_
  · exact (continuous_const.matrix_mulVec continuous_id).comp_continuousOn hu
  · refine continuousOn_finsetSum _ fun k _ => ?_
    exact ((Complex.continuous_ofReal.pow _).continuousOn).smul ((A' k a).continuous.comp_continuousOn hu)

private theorem rpow_neg_le_window (m z₀ z : ℝ) (hz₀ : 0 < z₀) (hz : z₀ / 2 ≤ z) (hz2 : z ≤ 2) :
    z ^ (-m) ≤ max ((z₀ / 2) ^ (-m)) (2 ^ (-m)) := by
  have hzpos : 0 < z := by linarith
  rcases le_or_gt 0 (-m) with h | h
  · exact (Real.rpow_le_rpow hzpos.le hz2 h).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos (by linarith) hz h.le).trans (le_max_left _ _)

private theorem hasDerivAt_coeff_of_second_system
    {n J R d' d₂' : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (Mc' : Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (L : ℝ) (hMcL' : ∀ a i j, ‖Mc' a i j‖ ≤ L) (hAL' : ∀ k a, ‖A' k a‖ ≤ L)
    (Z : ℝ) (hZ : 2 ≤ Z)
    (F Fz : ℝ → ℝ → (Fin R → ℂ))
    (hsysZ : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) Z,
      HasDerivAt (fun z => F y z) (Fz y z) z ∧
      (z : ℂ) • Fz y z =
        (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' a i j) • F y z j) +
          ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' k a (F y z))
    (c : Fin n → Fin J → ℝ → (Fin R → ℂ)) (hc : ∀ i j, ContinuousOn (c i j) (Set.Ioc 0 Z))
    (K₁ m : ℝ) (hK₁ : 0 ≤ K₁) (hcb : ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ‖c i j z‖ ≤ K₁ * z ^ (-m))
    (hexp : ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y z - ∑ i : Fin n, ∑ j : Fin J,
          ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • c i j z‖ ≤ K₁ * z ^ (-m) * y ^ (ρ + δ)) :
    ∀ i' j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (c i' j) ((z : ℂ)⁻¹ • ∑ a : Fin (d₂' + 1), ∑ i : Fin n,
        if e i + (a : ℕ) = e i' then Vlin Mc' A' a z (c i j z) else 0) z := by
  classical

  set w : Fin n → Fin J → ℝ → (Fin R → ℂ) := fun i' j z =>
    ∑ a : Fin (d₂' + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then Vlin Mc' A' a z (c i j z) else 0 with hw
  set g : Fin n → Fin J → ℝ → (Fin R → ℂ) := fun i' j z => (z : ℂ)⁻¹ • w i' j z with hg
  set CV : ℝ := (R : ℝ) * |L| + (d' : ℝ) * 2 ^ d' * |L| with hCV
  have hCV0 : 0 ≤ CV := by positivity
  have hθlt : ∀ i, (e i).re < ρ + δ := fun i => by linarith [hre i]

  have hFcz : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ContinuousOn (fun z => F y z) (Set.Ioc 0 Z) :=
    fun y hy z hz => ((hsysZ y hy z hz).1.continuousAt).continuousWithinAt
  have hsub2 : Set.Ioc (0 : ℝ) 2 ⊆ Set.Ioc (0 : ℝ) Z := fun z hz => ⟨hz.1, hz.2.trans hZ⟩

  have hFz_eq : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) Z,
      Fz y z = (z : ℂ)⁻¹ • ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z (F y z) := by
    intro y hy z hz
    have h := (hsysZ y hy z hz).2
    rw [rhs_eq_sum_Vlin] at h
    have hz0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.1.ne'
    rw [← h, smul_smul, inv_mul_cancel₀ hz0, one_smul]

  have hmain := RegularSingular.hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
    (ι := Fin n × Fin J) R (fun ij => e ij.1) (fun ij => (ij.2 : ℕ))
    (by
      intro ij ij' h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (he h.1) (Fin.ext h.2))
    (ρ + δ) (fun ij => hθlt ij.1) F Fz (fun ij z => c ij.1 ij.2 z) (fun ij z => g ij.1 ij.2 z)
    (fun y hy z hz => (hsysZ y hy z (hsub2 hz)).1)
    (by

      intro y hy
      have hcont : ContinuousOn (fun z : ℝ => ((z : ℝ) : ℂ)⁻¹ • ∑ a : Fin (d₂' + 1),
          ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z (F y z)) (Set.Ioc 0 2) := by
        refine ContinuousOn.fun_smul ?_ ?_
        · exact (Complex.continuous_ofReal.continuousOn.inv₀ fun z hz => by exact_mod_cast hz.1.ne')
        · refine continuousOn_finsetSum _ fun a _ => ?_
          exact (continuousOn_Vlin_comp Mc' A' a ((hFcz y hy).mono hsub2)).const_smul ((y : ℂ) ^ (a : ℕ))
      exact hcont.congr fun z hz => hFz_eq y hy z (hsub2 hz))
    (by

      rintro ⟨i', j⟩
      show ContinuousOn (fun z => g i' j z) (Set.Ioc 0 2)
      simp only [hg, hw]
      refine ContinuousOn.fun_smul ?_ ?_
      · exact (Complex.continuous_ofReal.continuousOn.inv₀ fun z hz => by exact_mod_cast hz.1.ne')
      · refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun i _ => ?_
        split_ifs
        · exact continuousOn_Vlin_comp Mc' A' a ((hc i j).mono hsub2)
        · exact continuousOn_const)
    (by

      intro z hz
      refine ⟨K₁ * z ^ (-m), fun y hy => ?_⟩
      have h := hexp z (hsub2 hz) y hy
      rw [Fintype.sum_prod_type]
      exact h)
    (by

      intro z₀ hz₀
      set zm₀ : ℝ := max ((z₀ / 2) ^ (-m)) (2 ^ (-m)) with hzm₀
      have hzm₀0 : 0 ≤ zm₀ := le_max_of_le_right (Real.rpow_nonneg (by norm_num) _)
      set Mv : ℝ := CV * (K₁ * zm₀) with hMv
      set Cf : ℝ := ((d₂' : ℝ) + 1) * n * Mv * ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ) with hCf
      set Ctot : ℝ := Cf + ((d₂' : ℝ) + 1) * CV * (K₁ * zm₀) with hCtot
      refine ⟨2 / z₀ * Ctot, z₀ / 2, by linarith [hz₀.1], ?_⟩
      intro z hz hzz y hy
      have hzlo : z₀ / 2 ≤ z := by
        have := (abs_lt.1 hzz).1
        linarith
      have hzpos : 0 < z := hz.1
      have hz0 : (z : ℂ) ≠ 0 := by exact_mod_cast hzpos.ne'
      have hzZ : z ∈ Set.Ioc (0 : ℝ) Z := hsub2 hz
      have hy0 : 0 < y := hy.1
      have hzm : z ^ (-m) ≤ zm₀ := rpow_neg_le_window m z₀ z hz₀.1 hzlo hz.2

      set φ : Fin n → Fin J → ℂ := fun i j => (y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ) with hφ
      set Sm : Fin R → ℂ := ∑ i : Fin n, ∑ j : Fin J, φ i j • c i j z with hSm
      set Rem : Fin R → ℂ := F y z - Sm with hRem
      set v : Fin (d₂' + 1) → Fin n → Fin J → (Fin R → ℂ) := fun a i j => Vlin Mc' A' a z (c i j z) with hv

      have hvb : ∀ a i j, ‖v a i j‖ ≤ Mv := by
        intro a i j
        calc ‖v a i j‖ ≤ CV * ‖c i j z‖ := norm_Vlin_le Mc' A' L hMcL' hAL' a z hz _
          _ ≤ CV * (K₁ * zm₀) := mul_le_mul_of_nonneg_left
              ((hcb i j z hzZ).trans (mul_le_mul_of_nonneg_left hzm hK₁)) hCV0

      have hlin : ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z Sm =
          ∑ a : Fin (d₂' + 1), ∑ i : Fin n, ∑ j : Fin J,
            ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [hSm, map_sum, map_smul, Finset.smul_sum, smul_smul, hv, hφ]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [cpow_add_natCast_mul (e i) a y hy0]
        ring_nf
      have hkey : (z : ℂ) • Fz y z - ∑ i' : Fin n, ∑ j : Fin J, φ i' j • w i' j z =
          ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z Rem +
          ((∑ a : Fin (d₂' + 1), ∑ i : Fin n, ∑ j : Fin J,
              ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) -
            ∑ i' : Fin n, ∑ j : Fin J, φ i' j • w i' j z) := by
        have h1 : (z : ℂ) • Fz y z = ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z (F y z) := by
          rw [hFz_eq y hy z hzZ, smul_smul, mul_inv_cancel₀ hz0, one_smul]
        have h2 : F y z = Sm + Rem := by rw [hRem]; abel
        rw [h1, h2]
        simp only [map_add, smul_add, Finset.sum_add_distrib]
        rw [hlin]
        abel

      have hfold := RegularSingular.norm_sum_shifted_sub_sum_reindexed_le e he ρ δ hδ hcl hgap d₂' v Mv hvb y hy
      have hwv : ∀ i' j, w i' j z = ∑ a : Fin (d₂' + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then v a i j else 0 := by
        intro i' j
        simp only [hw, hv]
      have hRemb : ‖Rem‖ ≤ K₁ * zm₀ * y ^ (ρ + δ) := by
        have h := hexp z hzZ y hy
        rw [hRem, hSm]
        refine h.trans ?_
        have hyθ : 0 ≤ y ^ (ρ + δ) := Real.rpow_nonneg hy0.le _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzm hK₁) hyθ
      have hA : ‖∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z Rem‖ ≤
          ((d₂' : ℝ) + 1) * CV * (K₁ * zm₀) * y ^ (ρ + δ) := by
        refine (norm_sum_le _ _).trans ?_
        have hya : ∀ a : Fin (d₂' + 1), ‖((y : ℝ) : ℂ) ^ (a : ℕ)‖ ≤ 1 := by
          intro a
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
          exact pow_le_one₀ hy0.le hy.2
        calc ∑ a : Fin (d₂' + 1), ‖((y : ℝ) : ℂ) ^ (a : ℕ) • Vlin Mc' A' a z Rem‖
            ≤ ∑ _a : Fin (d₂' + 1), CV * (K₁ * zm₀ * y ^ (ρ + δ)) := Finset.sum_le_sum fun a _ => by
              rw [norm_smul]
              calc ‖((y : ℝ) : ℂ) ^ (a : ℕ)‖ * ‖Vlin Mc' A' a z Rem‖ ≤ 1 * (CV * ‖Rem‖) :=
                    mul_le_mul (hya a) (norm_Vlin_le Mc' A' L hMcL' hAL' a z hz Rem) (norm_nonneg _) zero_le_one
                _ ≤ CV * (K₁ * zm₀ * y ^ (ρ + δ)) := by
                    rw [one_mul]; exact mul_le_mul_of_nonneg_left hRemb hCV0
          _ = ((d₂' : ℝ) + 1) * CV * (K₁ * zm₀) * y ^ (ρ + δ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
      have hB : ‖(∑ a : Fin (d₂' + 1), ∑ i : Fin n, ∑ j : Fin J,
              ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) -
            ∑ i' : Fin n, ∑ j : Fin J, φ i' j • w i' j z‖ ≤ Cf * y ^ (ρ + δ) := by
        simp only [hwv, hφ]
        exact hfold

      have hsum_g : ∑ ij : Fin n × Fin J, ((y : ℂ) ^ e ij.1 * ((Real.log y : ℝ) : ℂ) ^ (ij.2 : ℕ)) • g ij.1 ij.2 z =
          (z : ℂ)⁻¹ • ∑ i' : Fin n, ∑ j : Fin J, φ i' j • w i' j z := by
        rw [Fintype.sum_prod_type, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hg, hφ]
        rw [smul_comm]
      rw [hsum_g]
      have hfac : Fz y z - (z : ℂ)⁻¹ • ∑ i' : Fin n, ∑ j : Fin J, φ i' j • w i' j z =
          (z : ℂ)⁻¹ • ((z : ℂ) • Fz y z - ∑ i' : Fin n, ∑ j : Fin J, φ i' j • w i' j z) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hz0, one_smul]
      rw [hfac, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos, hkey]
      have hzinv : z⁻¹ ≤ 2 / z₀ := by
        rw [inv_eq_one_div, div_le_div_iff₀ hzpos (by linarith [hz₀.1])]
        linarith
      have hyθ : 0 ≤ y ^ (ρ + δ) := Real.rpow_nonneg hy0.le _
      have hCtot0 : 0 ≤ Ctot := by
        have h1 : 0 ≤ Cf := by
          rw [hCf]
          refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
            (mul_nonneg hCV0 (mul_nonneg hK₁ hzm₀0))) ?_
          exact Finset.sum_nonneg fun _ _ => by positivity
        rw [hCtot]
        exact add_nonneg h1 (mul_nonneg (mul_nonneg (by positivity) hCV0) (mul_nonneg hK₁ hzm₀0))
      calc z⁻¹ * ‖∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Vlin Mc' A' a z Rem +
            ((∑ a : Fin (d₂' + 1), ∑ i : Fin n, ∑ j : Fin J,
                ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) -
              ∑ i' : Fin n, ∑ j : Fin J, φ i' j • w i' j z)‖
          ≤ z⁻¹ * (((d₂' : ℝ) + 1) * CV * (K₁ * zm₀) * y ^ (ρ + δ) + Cf * y ^ (ρ + δ)) :=
            mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hA hB)) (inv_pos.2 hzpos).le
        _ = z⁻¹ * (Ctot * y ^ (ρ + δ)) := by rw [hCtot]; ring
        _ ≤ 2 / z₀ * (Ctot * y ^ (ρ + δ)) :=
            mul_le_mul_of_nonneg_right hzinv (mul_nonneg hCtot0 hyθ)
        _ = 2 / z₀ * Ctot * y ^ (ρ + δ) := by ring)
  intro i' j z hz
  have h := hmain (i', j) z ⟨hz.1, lt_of_le_of_lt hz.2 one_lt_two⟩
  simpa only [hg, hw] using h

end SecondSystem

theorem solution
    {n J R d d₂ d' d₂' : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hcov : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hcov' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hgq : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hgq' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hJ : q.natDegree ≤ J) (hJ' : n * q'.natDegree ≤ J)
    (P : Type*) [TopologicalSpace P]
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (Mc' : P → Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : P → Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (hMc : ∀ b, Continuous fun p => Mc p b) (hA : ∀ k b, Continuous fun p => A p k b)
    (hMc' : ∀ a, Continuous fun p => Mc' p a) (hA' : ∀ k a, Continuous fun p => A' p k a)
    (L : ℝ) (hMcL : ∀ p b i j, ‖Mc p b i j‖ ≤ L) (hAL : ∀ p k b, ‖A p k b‖ ≤ L)
    (hMcL' : ∀ p a i j, ‖Mc' p a i j‖ ≤ L) (hAL' : ∀ p k a, ‖A' p k a‖ ≤ L)
    (hq0 : ∀ p, ∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc p b) q = 0)
    (hq0' : ∀ p, ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' p a) q' = 0)
    (Z : ℝ) (hZ : 2 ≤ Z)
    (F Fy Fz : P → ℝ → ℝ → (Fin R → ℂ))
    (hF : ContinuousOn (fun w : P × ℝ × ℝ => F w.1 w.2.1 w.2.2) (Set.univ ×ˢ Set.Ioc 0 1 ×ˢ Set.Ioc 0 Z))
    (hsysY : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F p y z) (Fy p y z) y ∧
      (y : ℂ) • Fy p y z =
        (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc p b i j) • F p y z j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A p k b (F p y z))
    (hsysZ : ∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) Z,
      HasDerivAt (fun z => F p y z) (Fz p y z) z ∧
      (z : ℂ) • Fz p y z =
        (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' p a i j) • F p y z j) +
          ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' p k a (F p y z))
    (m B : ℝ)
    (hbound : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y z‖ ≤ B * y ^ (-m) * z ^ (-m)) :
    ∃ (c : Fin n → Fin J → P → ℝ → (Fin R → ℂ)) (c₂ : Fin n → Fin J → Fin n → Fin J → P → (Fin R → ℂ))
      (C : ℝ),
      (∀ i j, ContinuousOn (fun w : P × ℝ => c i j w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 Z)) ∧
      (∀ i j i' j', Continuous (c₂ i j i' j')) ∧
      (∀ p i j i' j', ‖c₂ i j i' j' p‖ ≤ C) ∧
      (∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ‖c i j p z‖ ≤ C * z ^ (-m)) ∧
      (∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y z - ∑ i : Fin n, ∑ j : Fin J,
            ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • c i j p z‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
      (∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
        ‖c i j p z - ∑ i' : Fin n, ∑ j' : Fin J,
            ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)) • c₂ i j i' j' p‖ ≤ C * z ^ (ρ + δ)) := by
  classical
  have hZ1 : 1 ≤ Z := by linarith

  have hbound' : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F p y z‖ ≤ max B 0 * y ^ (-m) * z ^ (-m) := by
    intro p z hz y hy
    refine (hbound p z hz y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.1.le _))
      (Real.rpow_nonneg hz.1.le _)

  obtain ⟨c, K₁, hK₁, hcc, hcb, hexp⟩ := firstLevel_on_strip e he ρ δ hδ q hq hcov hgq hJ P Mc A hMc hA L
    hMcL hAL hq0 Z hZ1 F Fy hF hsysY m (max B 0) (le_max_right _ _) hbound'

  have hcz : ∀ p i j, ContinuousOn (fun z => c i j p z) (Set.Ioc 0 Z) := by
    intro p i j
    have hmap : Continuous fun z : ℝ => ((p, z) : P × ℝ) := by fun_prop
    exact (hcc i j).comp hmap.continuousOn fun z hz => Set.mem_prod.2 ⟨Set.mem_univ _, hz⟩

  have hderiv : ∀ p i' j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun z => c i' j p z) ((z : ℂ)⁻¹ • ∑ a : Fin (d₂' + 1), ∑ i : Fin n,
        if e i + (a : ℕ) = e i' then Vlin (Mc' p) (A' p) a z (c i j p z) else 0) z := by
    intro p
    exact hasDerivAt_coeff_of_second_system e he ρ δ hδ hre hcl hgap (Mc' p) (A' p) L (hMcL' p) (hAL' p)
      Z hZ (F p) (Fz p) (hsysZ p) (fun i j z => c i j p z) (hcz p) K₁ m hK₁ (fun i j z hz => hcb p i j z hz)
      (hexp p)

  have hann : ∀ p, Polynomial.aeval (Mc' p 0) q' = 0 :=
    fun p => Matrix.aeval_const_term_eq_zero_of_forall_pos (Mc' p) q' (hq0' p)
  have hθ' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + δ < (e₀ + k).re := by
    intro e₀ he₀ k hk
    have h := hgq' e₀ he₀ k hk
    linarith

  obtain ⟨D₂, S₂, κ₂, hD₂, hS₂, c₂, hc₂c, hc₂⟩ :=
    RegularSingular.exists_expansion_coeff_of_folded_system e he P Mc' A' L hMc' hMcL' hA' hAL' q' hq' hann
      (fun p i j z => c i j p z)
      (fun p i' j z => (z : ℂ)⁻¹ • ∑ a : Fin (d₂' + 1), ∑ i : Fin n,
        if e i + (a : ℕ) = e i' then Vlin (Mc' p) (A' p) a z (c i j p z) else 0)
      (fun i j => (hcc i j).mono (Set.prod_mono le_rfl (Set.Ioc_subset_Ioc le_rfl hZ1)))
      (by
        intro p i j z hz
        refine ⟨hderiv p i j z hz, ?_⟩
        have hz0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.1.ne'
        rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i' _ => ?_
        split_ifs
        · rw [Vlin_apply]
        · rfl)
      m (fun _ => K₁) (fun _ => ⟨K₁, Filter.Eventually.of_forall fun _ => le_rfl⟩)
      (fun p i j z hz => hcb p i j z (Set.Ioc_subset_Ioc le_rfl hZ1 hz)) ρ (ρ + δ) hθ'
  have hcovS₂ : ∀ μ ∈ S₂, ∃ i, e i = μ := by
    intro μ hμ
    obtain ⟨hre, e₀, k, hr, hk⟩ := hS₂ μ hμ
    obtain ⟨i, hi⟩ := hcov' e₀ hr k (hk ▸ hre)
    exact ⟨i, hi.trans hk.symm⟩
  have hD₂J : D₂ ≤ J := hD₂.trans hJ'

  set C : ℝ := max (|κ₂| * K₁) K₁ with hC
  have hK₁C : K₁ ≤ C := le_max_right _ _
  have hκC : |κ₂| * K₁ ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := hK₁.trans hK₁C
  refine ⟨c, fun i j i' j' p => if e i' ∈ S₂ ∧ (j' : ℕ) < D₂ then c₂ (e i') j' p i j else 0, C, hcc,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i j i' j'
    by_cases hij : e i' ∈ S₂ ∧ (j' : ℕ) < D₂
    · simp only [if_pos hij]
      exact hc₂c (e i') j' i j
    · simp only [if_neg hij]
      exact continuous_const
  · intro p i j i' j'
    dsimp only
    split_ifs
    · calc _ ≤ κ₂ * K₁ := (hc₂ p i j).1 (e i') j'
        _ ≤ |κ₂| * K₁ := mul_le_mul_of_nonneg_right (le_abs_self _) hK₁
        _ ≤ C := hκC
    · rw [norm_zero]; exact hC0
  · intro p i j z hz
    exact (hcb p i j z hz).trans (mul_le_mul_of_nonneg_right hK₁C (Real.rpow_nonneg hz.1.le _))
  · intro p z hz y hy
    exact (hexp p z hz y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK₁C (Real.rpow_nonneg hz.1.le _)) (Real.rpow_nonneg hy.1.le _))
  · intro p i j z hz
    have hmain := (hc₂ p i j).2 z hz
    have hsum : ∑ μ ∈ S₂, ∑ j₂ ∈ Finset.range D₂,
        ((z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂) • c₂ μ j₂ p i j =
        ∑ i' : Fin n, ∑ j' : Fin J, ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)) •
          (if e i' ∈ S₂ ∧ (j' : ℕ) < D₂ then c₂ (e i') j' p i j else 0) :=
      sum_reindex_family_smul e he S₂ hcovS₂ hD₂J (fun μ j₂ => (z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂)
        (fun μ j₂ => c₂ μ j₂ p i j)
    rw [← hsum]
    refine hmain.trans ?_
    have hzθ : 0 ≤ z ^ (ρ + δ) := Real.rpow_nonneg hz.1.le _
    calc κ₂ * K₁ * z ^ (ρ + δ) ≤ |κ₂| * K₁ * z ^ (ρ + δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hK₁) hzθ
      _ ≤ C * z ^ (ρ + δ) := mul_le_mul_of_nonneg_right hκC hzθ

end S_RegularSingular_exists_twoLevel_expansion_of_commuting_systems
end P2MW
export P2MW.S_RegularSingular_exists_twoLevel_expansion_of_commuting_systems (solution)
