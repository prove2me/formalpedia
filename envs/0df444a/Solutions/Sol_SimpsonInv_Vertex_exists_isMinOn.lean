-- Prove2me | solution 1 for SimpsonInv.Vertex.exists_isMinOn
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:48:14.071489+00:00
-- url     : https://prove2.me/submissions/34bbaa3f-0320-4a2e-9474-b471bb27c2b6

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting



namespace SimpsonInv.Vertex

lemma sv_ext_affine {m : ℕ} (S0 Sn a b : ℝ) (hab : a + b = 1) (x y : Fin m → ℝ) (i : ℕ) :
    extVec S0 Sn (a • x + b • y) i = a * extVec S0 Sn x i + b * extVec S0 Sn y i := by
  unfold extVec
  split_ifs
  · linear_combination (-S0) * hab
  · simp
  · linear_combination (-Sn) * hab

lemma sv_rad_affine {m : ℕ} (T : ℕ → ℝ) (S0 Sn a b : ℝ) (hab : a + b = 1) (x y : Fin m → ℝ) (i : ℕ) :
    radicand T S0 Sn (a • x + b • y) i
      = a * radicand T S0 Sn x i + b * radicand T S0 Sn y i := by
  unfold radicand
  rw [sv_ext_affine S0 Sn a b hab, sv_ext_affine S0 Sn a b hab]
  linear_combination (-(T i)) * hab

lemma sv_ext_cont {m : ℕ} (S0 Sn : ℝ) (i : ℕ) : Continuous (fun S : Fin m → ℝ => extVec S0 Sn S i) := by
  unfold extVec
  split_ifs <;> fun_prop

lemma sv_rad_cont {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (i : ℕ) :
    Continuous (fun S : Fin m → ℝ => radicand T S0 Sn S i) := by
  unfold radicand
  exact ((sv_ext_cont S0 Sn _).sub (sv_ext_cont S0 Sn _)).add continuous_const

lemma sv_convex {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) : Convex ℝ (dom (m := m) T S0 Sn) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun j => ?_, fun i hi => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · rw [sv_rad_affine T S0 Sn a b hab]
    exact add_nonneg (mul_nonneg ha (hx.2 i hi)) (mul_nonneg hb (hy.2 i hi))

lemma sv_closed {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) : IsClosed (dom (m := m) T S0 Sn) := by
  have : dom (m := m) T S0 Sn = (⋂ j : Fin m, {S : Fin m → ℝ | 0 ≤ S j}) ∩
      ⋂ i ∈ Finset.Icc 1 (m + 1), {S : Fin m → ℝ | 0 ≤ radicand T S0 Sn S i} := by
    ext S; simp [dom]
  rw [this]
  exact IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
    (isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_le continuous_const (sv_rad_cont T S0 Sn i))

lemma sv_ext_bound {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) (hS : S ∈ dom (m := m) T S0 Sn) :
    ∀ i, i ≤ m → extVec S0 Sn S i ≤ S0 + ∑ k ∈ Finset.Icc 1 i, |T k| := by
  intro i
  induction i with
  | zero => intro _; simp [extVec]
  | succ n ih =>
    intro hn
    have h1 := hS.2 (n + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have h2 := ih (by omega)
    unfold radicand at h1
    simp only [Nat.add_sub_cancel] at h1
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := le_abs_self (T (n + 1))
    linarith

lemma sv_compact {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) : IsCompact (dom (m := m) T S0 Sn) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin m → ℝ))
    (b := fun _ => |S0| + ∑ k ∈ Finset.Icc 1 (m + 1), |T k|)) (sv_closed T S0 Sn) ?_
  intro S hS
  refine ⟨fun j => hS.1 j, fun j => ?_⟩
  have h := sv_ext_bound T S0 Sn S hS (j.val + 1) (by omega)
  have e : extVec S0 Sn S (j.val + 1) = S j := by
    simp [extVec]
  rw [e] at h
  have hsub : ∑ k ∈ Finset.Icc 1 (j.val + 1), |T k| ≤ ∑ k ∈ Finset.Icc 1 (m + 1), |T k| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (by omega))
      (fun _ _ _ => abs_nonneg _)
  have := le_abs_self S0
  linarith

theorem dom_cc_core {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) :
    Convex ℝ (dom (m := m) T S0 Sn) ∧ IsCompact (dom (m := m) T S0 Sn) :=
  ⟨sv_convex T S0 Sn, sv_compact T S0 Sn⟩

lemma sv_concave_gen {m : ℕ} (φ : ℝ → ℝ) (hφ : ConcaveOn ℝ (Set.Ici 0) φ) (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ r i) :
    ConcaveOn ℝ (dom (m := m) T S0 Sn) (fun S => c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * φ (radicand T S0 Sn S i)) := by
  refine ⟨sv_convex T S0 Sn, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have e1 : a * (c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * φ (radicand T S0 Sn x i)) +
      b * (c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * φ (radicand T S0 Sn y i)) =
      c + ∑ i ∈ Finset.Icc 1 (m + 1), (a * (r i * φ (radicand T S0 Sn x i)) + b * (r i * φ (radicand T S0 Sn y i))) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination c * hab
  rw [e1]
  refine add_le_add le_rfl (Finset.sum_le_sum fun i hi => ?_)
  rw [sv_rad_affine T S0 Sn a b hab]
  have h := hφ.2 (show radicand T S0 Sn x i ∈ Set.Ici (0:ℝ) from hx.2 i hi)
    (show radicand T S0 Sn y i ∈ Set.Ici (0:ℝ) from hy.2 i hi) ha hb hab
  simp only [smul_eq_mul] at h
  calc a * (r i * φ (radicand T S0 Sn x i)) + b * (r i * φ (radicand T S0 Sn y i))
      = r i * (a * φ (radicand T S0 Sn x i) + b * φ (radicand T S0 Sn y i)) := by ring
    _ ≤ r i * φ (a * radicand T S0 Sn x i + b * radicand T S0 Sn y i) :=
        mul_le_mul_of_nonneg_left h (hr i hi)

theorem cost_concaveOn_core {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ r i) :
    ConcaveOn ℝ (dom (m := m) T S0 Sn) (cost c r T S0 Sn) :=
  sv_concave_gen Real.sqrt Real.strictConcaveOn_sqrt.concaveOn c S0 Sn r T hr

lemma sv_cost_cont {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) : Continuous (cost (m := m) c r T S0 Sn) := by
  unfold cost
  exact continuous_const.add (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Real.continuous_sqrt.comp (sv_rad_cont T S0 Sn i)))

theorem exists_isMinOn_core {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ dom (m := m) T S0 Sn, IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v :=
  (sv_compact T S0 Sn).exists_isMinOn hD (sv_cost_cont c S0 Sn r T).continuousOn

lemma sv_bauer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (f : E → ℝ)
    (hK : IsCompact K) (hKc : Convex ℝ K) (hne : K.Nonempty) (hf : ContinuousOn f K)
    (hc : ConcaveOn ℝ K f) : ∃ v ∈ K.extremePoints ℝ, IsMinOn f K v := by
  obtain ⟨m, hmK, hm⟩ := hK.exists_isMinOn hne hf
  have hcl : IsClosed (K ∩ f ⁻¹' Set.Iic (f m)) :=
    hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic
  have hMc : IsCompact (K ∩ f ⁻¹' Set.Iic (f m)) :=
    IsCompact.of_isClosed_subset hK hcl Set.inter_subset_left
  have hext : IsExtreme ℝ K (K ∩ f ⁻¹' Set.Iic (f m)) := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro x₁ hx₁ x₂ hx₂ x hx hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    have hcon := hc.2 hx₁ hx₂ ha.le hb.le hab
    simp only [smul_eq_mul] at hcon
    have h1 : f m ≤ f x₁ := hm hx₁
    have h2 : f m ≤ f x₂ := hm hx₂
    have h3 : f (a • x₁ + b • x₂) ≤ f m := hx.2
    have hfm : a * f m + b * f m = f m := by rw [← add_mul, hab, one_mul]
    have key : a * (f x₁ - f m) + b * (f x₂ - f m) ≤ 0 := by linarith
    have h4 : f x₁ ≤ f m := by
      by_contra hcon'
      push Not at hcon'
      nlinarith [mul_pos ha (sub_pos.2 hcon'), mul_nonneg hb.le (sub_nonneg.2 h2)]
    have h5 : f x₂ ≤ f m := by
      by_contra hcon'
      push Not at hcon'
      nlinarith [mul_pos hb (sub_pos.2 hcon'), mul_nonneg ha.le (sub_nonneg.2 h1)]
    exact (show x₁ ∈ K ∩ f ⁻¹' Set.Iic (f m) from ⟨hx₁, h4⟩)
  obtain ⟨v, hv⟩ := hMc.extremePoints_nonempty ⟨m, Set.mem_inter hmK (show f m ≤ f m from le_rfl)⟩
  refine ⟨v, hext.extremePoints_subset_extremePoints hv, fun y hy => ?_⟩
  exact le_trans (show f v ≤ f m from hv.1.2) (show f m ≤ f y from hm hy)

theorem theorem_I_rpow_core {m : ℕ} (k c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hk : 1 / 2 ≤ k) (hk1 : k ≤ 1)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ Set.extremePoints ℝ (dom (m := m) T S0 Sn),
      IsMinOn (costPow k c r T S0 Sn) (dom (m := m) T S0 Sn) v := by
  have hcc := sv_concave_gen (fun x : ℝ => x ^ k) (Real.concaveOn_rpow (by linarith) hk1) c S0 Sn r T
    (fun i hi => (hr i hi).le)
  have hcont : Continuous (costPow (m := m) k c r T S0 Sn) := by
    unfold costPow
    exact continuous_const.add (continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((Real.continuous_rpow_const (by linarith)).comp (sv_rad_cont T S0 Sn i)))
  exact sv_bauer (costPow k c r T S0 Sn) (sv_compact T S0 Sn) (sv_convex T S0 Sn) hD hcont.continuousOn hcc

end SimpsonInv.Vertex

open SimpsonInv.Vertex


theorem solution {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ dom (m := m) T S0 Sn, IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v := by
  exact exists_isMinOn_core c S0 Sn r T hD
