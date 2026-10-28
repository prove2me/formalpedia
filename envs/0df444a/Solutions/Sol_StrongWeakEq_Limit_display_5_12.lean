-- Prove2me | solution 1 for StrongWeakEq.Limit.display_5_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T01:12:45.084661+00:00
-- url     : https://prove2.me/submissions/b5aac356-1bc1-439d-bc50-0c38e884bcfd

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
import Definitions.Def_StrongWeakEq_Limit_Discretization

namespace Aux_SWE_512

open StrongWeakEq.Limit StrongWeakEq.Discrete MeasureTheory

lemma stoch_pow {N : ℕ} (un : Matrix (Fin N) (Fin N) ℝ)
    (hun : ∀ i, (∀ j, 0 ≤ un i j) ∧ ∑ j, un i j = 1) :
    ∀ t i, (∀ j, 0 ≤ (un ^ t) i j) ∧ ∑ j, (un ^ t) i j = 1 := by
  intro t
  induction t with
  | zero =>
    intro i
    refine ⟨fun j => ?_, ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ t ih =>
    intro i
    rw [pow_succ]
    refine ⟨fun j => ?_, ?_⟩
    · rw [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg ((ih i).1 k) ((hun k).1 j)
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, (hun _).2, mul_one]
      exact (ih i).2

lemma entry_le {N : ℕ} (v : Fin N → ℝ) (h0 : ∀ j, 0 ≤ v j) (h1 : ∑ j, v j = 1) (j : Fin N) :
    v j ≤ 1 := by
  rw [← h1]; exact Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)

lemma summ_phi (φ : ℝ → ℝ) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T) (hφ0 : ∀ s, 0 ≤ φ s)
    (hint : IntegrableOn φ (Set.Ici 0)) (hanti : AntitoneOn φ (Set.Ici T)) :
    Summable (fun t : ℕ => φ (t * δ)) := by
  set M : ℕ := ⌈T / δ⌉₊
  have hM : T / δ ≤ M := Nat.le_ceil _
  have hMδ : T ≤ M * δ := by rwa [div_le_iff₀ hδ] at hM
  refine AntitoneOn.summable_of_integrableOn_Ioi (f := fun x => φ (x * δ)) (N := M) ?_ ?_ ?_
  · intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    exact hanti (by simp only [Set.mem_Ici]; nlinarith) (by simp only [Set.mem_Ici]; nlinarith)
      (by nlinarith)
  · rw [integrableOn_Ioi_comp_mul_right_iff _ _ hδ]
    refine hint.mono_set ?_
    intro s hs
    simp only [Set.mem_Ioi] at hs
    simp only [Set.mem_Ici]
    have : (0 : ℝ) ≤ M * δ := by positivity
    linarith
  · intro t _; exact hφ0 _

end Aux_SWE_512

open StrongWeakEq.Limit StrongWeakEq.Discrete MeasureTheory Aux_SWE_512 in
theorem solution {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : StrongWeakEq.Existence.Standing D f)
    (h58 : EventuallyNonincreasing D f) (δ : ℝ) (hδ : 0 < δ)
    (un : Matrix (Fin N) (Fin N) ℝ)
    (heq : StrongWeakEq.Discrete.IsDEquilibrium (admRows D δ) (kappaN f δ) un) :
    ∀ i, ∀ u ∈ StrongWeakEq.Discrete.DControls (admRows D δ),
      kappaN f δ 0 i (u i) + (fun j => StrongWeakEq.Discrete.dH (kappaN f δ) un j) ⬝ᵥ u i ≤
        kappaN f δ 0 i (un i) + (fun j => StrongWeakEq.Discrete.dH (kappaN f δ) un j) ⬝ᵥ un i := by
  intro i u hu
  have hunA : ∀ j, un j ∈ admRows D δ j := heq.1
  have hunS : ∀ j, (∀ k, 0 ≤ un j k) ∧ ∑ k, un j k = 1 := fun j => (hunA j).1
  have hpow := stoch_pow un hunS
  -- summability of the kernel along un
  obtain ⟨T, hT, hanti⟩ := h58
  set κ := kappaN f δ with hκ
  have hsk : ∀ j, Summable (fun t : ℕ => |κ t j (un j)|) := by
    intro j
    set q : Fin N → ℝ := δ⁻¹ • (un j - Pi.single j (1 : ℝ)) with hq
    have hqD : q ∈ D j := (hunA j).2
    have hqn : ‖q‖ ≤ δ⁻¹ + 1 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
      simp only [hq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_inv, abs_of_pos hδ]
      have h0 := (hunS j).1 k
      have h1 := entry_le (un j) (hunS j).1 (hunS j).2 k
      have : |un j k - (Pi.single j (1 : ℝ) : Fin N → ℝ) k| ≤ 1 := by
        rw [abs_le, Pi.single_apply]
        split_ifs <;> constructor <;> linarith
      have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
      nlinarith
    obtain ⟨g, hg, hgb⟩ := hS.integ (δ⁻¹ + 1) (by positivity)
    set φ : ℝ → ℝ := fun s => |f s j q| with hφ
    have hφint : IntegrableOn φ (Set.Ici 0) := by
      have hcont : ContinuousOn φ (Set.Ici 0) := (hS.cont j q hqD).abs
      refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ici) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ici fun s hs => ?_
      simp only [hφ, Real.norm_eq_abs, abs_abs]
      exact hgb s hs j q hqD hqn
    have hsum := summ_phi φ δ T hδ hT (fun s => abs_nonneg _) hφint (hanti j q hqD)
    refine (hsum.mul_right δ).congr fun t => ?_
    simp only [hκ, kappaN, hφ, abs_mul, abs_of_pos hδ]
    rfl
  -- the series appearing in dH
  set a : Fin N → ℕ → ℝ := fun k t => ∑ j, (un ^ t) k j * κ (t + 1) j (un j) with ha
  have hsa : ∀ k, Summable (a k) := by
    intro k
    have hs : Summable (fun t : ℕ => ∑ j, |κ (t + 1) j (un j)|) :=
      summable_sum fun j _ => (summable_nat_add_iff 1).mpr (hsk j)
    refine Summable.of_norm_bounded hs fun t => ?_
    simp only [ha, Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    have h0 := (hpow t k).1 j
    have h1 := entry_le _ (hpow t k).1 (hpow t k).2 j
    rw [abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  have hdH : ∀ k, dH κ un k = ∑' t, a k t := fun k => rfl
  have hrow : ∀ (W : Matrix (Fin N) (Fin N) ℝ) (t : ℕ),
      ∑ j, (W * un ^ t) i j * κ (t + 1) j (un j) = ∑ k, W i k * a k t := by
    intro W t
    simp only [Matrix.mul_apply, Finset.sum_mul, ha, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hseries : ∀ W : Matrix (Fin N) (Fin N) ℝ,
      ∑' t : ℕ, ∑ j, (W * un ^ t) i j * κ (t + 1) j (un j) = ∑ k, W i k * dH κ un k := by
    intro W
    simp only [hrow]
    rw [Summable.tsum_finsetSum (fun k _ => (hsa k).mul_left (W i k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tsum_mul_left, hdH]
  -- concatenated value
  have hconc : dConcatValue κ u un i =
      κ 0 i (u i) + (fun j => dH κ un j) ⬝ᵥ u i := by
    unfold dConcatValue
    rw [hseries u]
    simp only [dotProduct]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- equilibrium value
  have hb : Summable (fun t : ℕ => ∑ j, (un ^ t) i j * κ t j (un j)) := by
    have hs : Summable (fun t : ℕ => ∑ j, |κ t j (un j)|) :=
      summable_sum fun j _ => hsk j
    refine Summable.of_norm_bounded hs fun t => ?_
    rw [Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg ((hpow t i).1 j)]
    exact mul_le_of_le_one_left (abs_nonneg _) (entry_le _ (hpow t i).1 (hpow t i).2 j)
  have hval : dValue κ un i = κ 0 i (un i) + (fun j => dH κ un j) ⬝ᵥ un i := by
    unfold dValue
    rw [hb.tsum_eq_zero_add]
    congr 1
    · simp [Matrix.one_apply]
    · have : ∀ t : ℕ, ∑ j, (un ^ (t + 1)) i j * κ (t + 1) j (un j) =
          ∑ j, (un * un ^ t) i j * κ (t + 1) j (un j) := fun t => by rw [pow_succ']
      simp only [this]
      rw [hseries un]
      simp only [dotProduct]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have := heq.2 i u hu
  rw [hconc, hval] at this
  exact this
