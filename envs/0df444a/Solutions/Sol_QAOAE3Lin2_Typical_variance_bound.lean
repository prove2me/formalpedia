-- Prove2me | solution 1 for QAOAE3Lin2.Typical.variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T12:54:12.502919+00:00
-- url     : https://prove2.me/submissions/6e6a2f95-2b7a-4e5c-8572-70e5967b0211

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting
import Theorems.Thm_QAOAE3Lin2_Typical_eq_55
import Theorems.Thm_QAOAE3Lin2_Typical_eq_57
import Theorems.Thm_QAOAE3Lin2_Typical_linked_card_le
import Theorems.Thm_QAOAE3Lin2_Typical_clauseTerm_abs_le

open QAOAE3Lin2.Typical

/-! Linearity and monotonicity of the instance average. -/

theorem vb_avgD_add {m : ℕ} (f g : (Fin m → Bool) → ℝ) :
    avgD (fun r => f r + g r) = avgD f + avgD g := by
  simp only [avgD, Finset.sum_add_distrib, mul_add]

theorem vb_avgD_sub {m : ℕ} (f g : (Fin m → Bool) → ℝ) :
    avgD (fun r => f r - g r) = avgD f - avgD g := by
  simp only [avgD, Finset.sum_sub_distrib, mul_sub]

theorem vb_avgD_const_mul {m : ℕ} (a : ℝ) (f : (Fin m → Bool) → ℝ) :
    avgD (fun r => a * f r) = a * avgD f := by
  simp only [avgD, ← Finset.mul_sum]
  ring

theorem vb_avgD_const {m : ℕ} (a : ℝ) : avgD (fun _ : Fin m → Bool => a) = a := by
  have h2 : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = (2 : ℝ) ^ m := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp only [avgD]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc, inv_mul_cancel₀ h2,
    one_mul]

theorem vb_avgD_finset_sum {m : ℕ} {ι : Type} (s : Finset ι) (f : ι → (Fin m → Bool) → ℝ) :
    avgD (fun r => ∑ i ∈ s, f i r) = ∑ i ∈ s, avgD (f i) := by
  simp only [avgD]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem vb_avgD_mono {m : ℕ} (f g : (Fin m → Bool) → ℝ) (h : ∀ r, f r ≤ g r) :
    avgD f ≤ avgD g := by
  simp only [avgD]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => h r) (by positivity)

/-- Covariance identity: `E[(f − Ef)(g − Eg)] = E[fg] − Ef · Eg`. -/
theorem vb_cov {m : ℕ} (f g : (Fin m → Bool) → ℝ) :
    avgD (fun r => (f r - avgD f) * (g r - avgD g)) =
      avgD (fun r => f r * g r) - avgD f * avgD g := by
  have h : (fun r => (f r - avgD f) * (g r - avgD g)) =
      fun r => f r * g r - (avgD g * f r + avgD f * g r - avgD f * avgD g) := by
    funext r; ring
  rw [h, vb_avgD_sub (fun r => f r * g r) (fun r => avgD g * f r + avgD f * g r - avgD f * avgD g),
    vb_avgD_sub (fun r => avgD g * f r + avgD f * g r) (fun _ => avgD f * avgD g),
    vb_avgD_add (fun r => avgD g * f r) (fun r => avgD f * g r),
    vb_avgD_const_mul (avgD g) f, vb_avgD_const_mul (avgD f) g, vb_avgD_const (avgD f * avgD g)]
  ring

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri) (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (γ : ℝ) :
    varD (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4)) ≤
      (m : ℝ) * (6 * D + 3) * (D + 1) / 4 := by
  classical
  let T : Fin m → (Fin m → Bool) → ℝ := fun i rhs => clauseTerm tri rhs i γ
  let μ : Fin m → ℝ := fun i => avgD (T i)
  have hT : ∀ i rhs, |T i rhs| ≤ 1 / 2 := fun i rhs => clauseTerm_abs_le tri rhs i γ
  -- covariances of the clause terms
  let c : Fin m → Fin m → ℝ := fun i i' => avgD (fun r => (T i r - μ i) * (T i' r - μ i'))
  -- (55): the objective is `m/2` plus the sum of the clause terms
  have hg : (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4)) =
      fun rhs => (m : ℝ) / 2 + ∑ i, T i rhs := by
    funext rhs
    exact eq_55 tri rhs γ
  have havg : avgD (fun rhs => (m : ℝ) / 2 + ∑ i, T i rhs) = (m : ℝ) / 2 + ∑ i, μ i := by
    rw [vb_avgD_add (fun _ => (m : ℝ) / 2) (fun rhs => ∑ i, T i rhs), vb_avgD_const,
      vb_avgD_finset_sum Finset.univ T]
  -- the variance is the sum of all covariances
  have hvar : varD (fun rhs => (m : ℝ) / 2 + ∑ i, T i rhs) = ∑ i, ∑ i', c i i' := by
    have hfun : (fun rhs => ((m : ℝ) / 2 + ∑ i, T i rhs -
          avgD (fun rhs => (m : ℝ) / 2 + ∑ i, T i rhs)) ^ 2) =
        fun rhs => ∑ i, ∑ i', (T i rhs - μ i) * (T i' rhs - μ i') := by
      funext rhs
      have hc : (m : ℝ) / 2 + ∑ i, T i rhs - ((m : ℝ) / 2 + ∑ i, μ i) =
          ∑ i, (T i rhs - μ i) := by
        rw [Finset.sum_sub_distrib]; ring
      rw [havg, hc, sq, Finset.sum_mul_sum]
    show avgD (fun rhs => ((m : ℝ) / 2 + ∑ i, T i rhs -
          avgD (fun rhs => (m : ℝ) / 2 + ∑ i, T i rhs)) ^ 2) = _
    rw [hfun, vb_avgD_finset_sum Finset.univ
      (fun i rhs => ∑ i', (T i rhs - μ i) * (T i' rhs - μ i'))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact vb_avgD_finset_sum Finset.univ (fun i' rhs => (T i rhs - μ i) * (T i' rhs - μ i'))
  -- (57): unlinked equations are uncorrelated
  have hzero : ∀ i i', Disjoint (deps tri i) (deps tri i') → c i i' = 0 := by
    intro i i' hdis
    have h57 := eq_57 tri htri i i' hdis γ
    have hcov := vb_cov (T i) (T i')
    show avgD (fun r => (T i r - avgD (T i)) * (T i' r - avgD (T i'))) = 0
    rw [hcov]
    have : avgD (fun r => T i r * T i' r) = avgD (T i) * avgD (T i') := h57
    rw [this, sub_self]
  -- every covariance is at most 1/4
  have hsq : ∀ i, avgD (fun r => (T i r - μ i) ^ 2) ≤ 1 / 4 := by
    intro i
    have hcov := vb_cov (T i) (T i)
    have h1 : avgD (fun r => (T i r - μ i) ^ 2) = avgD (fun r => T i r * T i r) - μ i * μ i := by
      have : (fun r => (T i r - μ i) ^ 2) = fun r => (T i r - avgD (T i)) * (T i r - avgD (T i)) := by
        funext r; ring
      rw [this]; exact hcov
    have h2 : avgD (fun r => T i r * T i r) ≤ avgD (fun _ => (1 / 4 : ℝ)) :=
      vb_avgD_mono _ _ (fun r => by
        have := abs_le.mp (hT i r)
        nlinarith [this.1, this.2])
    rw [vb_avgD_const] at h2
    nlinarith [mul_self_nonneg (μ i)]
  have hquarter : ∀ i i', c i i' ≤ 1 / 4 := by
    intro i i'
    have hpt : ∀ r, (T i r - μ i) * (T i' r - μ i') ≤
        (1 / 2) * (T i r - μ i) ^ 2 + (1 / 2) * (T i' r - μ i') ^ 2 := by
      intro r
      nlinarith [sq_nonneg ((T i r - μ i) - (T i' r - μ i'))]
    have hle := vb_avgD_mono _ _ hpt
    rw [vb_avgD_add (fun r => (1 / 2) * (T i r - μ i) ^ 2) (fun r => (1 / 2) * (T i' r - μ i') ^ 2),
      vb_avgD_const_mul (1 / 2) (fun r => (T i r - μ i) ^ 2),
      vb_avgD_const_mul (1 / 2) (fun r => (T i' r - μ i') ^ 2)] at hle
    have h1 := hsq i
    have h2 := hsq i'
    show avgD (fun r => (T i r - μ i) * (T i' r - μ i')) ≤ 1 / 4
    linarith
  -- sum over the linked pairs
  have hrow : ∀ i, ∑ i', c i i' ≤ ((6 * D + 3) * (D + 1) : ℝ) / 4 := by
    intro i
    let L : Finset (Fin m) := Finset.univ.filter fun i' => ¬ Disjoint (deps tri i) (deps tri i')
    have hL : L.card ≤ (6 * D + 3) * (D + 1) := linked_card_le tri D htri hocc i
    have hsplit : ∑ i', c i i' = ∑ i' ∈ L, c i i' := by
      symm
      apply Finset.sum_subset (Finset.subset_univ L)
      intro i' _ hi'
      have : Disjoint (deps tri i) (deps tri i') := by
        by_contra hnd
        exact hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ i', hnd⟩)
      exact hzero i i' this
    rw [hsplit]
    calc ∑ i' ∈ L, c i i' ≤ ∑ _i' ∈ L, (1 / 4 : ℝ) := Finset.sum_le_sum (fun i' _ => hquarter i i')
      _ = (L.card : ℝ) * (1 / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((6 * D + 3) * (D + 1) : ℕ) : ℝ) * (1 / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact_mod_cast hL
      _ = ((6 * D + 3) * (D + 1) : ℝ) / 4 := by push_cast; ring
  rw [hg, hvar]
  calc ∑ i, ∑ i', c i i' ≤ ∑ _i : Fin m, ((6 * D + 3) * (D + 1) : ℝ) / 4 :=
        Finset.sum_le_sum (fun i _ => hrow i)
    _ = (m : ℝ) * (6 * D + 3) * (D + 1) / 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
