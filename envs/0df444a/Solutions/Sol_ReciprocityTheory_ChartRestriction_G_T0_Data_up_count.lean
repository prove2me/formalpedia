-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.up_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:41.605793+00:00
-- url     : https://prove2.me/submissions/8da485ca-7a40-4cd6-a773-310fb7fe2bc2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_log_le_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (hdel : 1 ≤ d.del) :
    Real.log (cardUX d.D d.N d.n96 d.n96') + d.PO ≤ d.n96 := by
  obtain ⟨M, hM⟩ : ∃ M, M = (d.D + 2) * (d.N + 1) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 1 + ⌈d.PO⌉₊ := ⟨_, rfl⟩
  have hD := hd.D_ge
  have hM2 : d.D + 2 ≤ M := by rw [hM]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hn : d.n96 = 8 * M ^ 2 * (d.D + 1) * d.del * t := by rw [hM, ht]; rfl
  have hn' : d.n96' = 8 * d.n96 * M * (d.D + 1) * d.del := by rw [hM]; rfl
  have ht1 : 1 ≤ t := by omega
  have hM1 : 1 ≤ M := by omega
  have hnM : 32 * M ^ 2 * t ≤ d.n96 := by
    rw [hn]
    have : 32 * M ^ 2 * t ≤ 8 * M ^ 2 * 4 * 1 * t := by ring_nf; exact le_refl _
    calc 32 * M ^ 2 * t = 8 * M ^ 2 * 4 * 1 * t := by ring
      _ ≤ 8 * M ^ 2 * (d.D + 1) * d.del * t := by gcongr <;> omega
  have hnpos : 2 ≤ d.n96 := by nlinarith
  set n := d.n96 with hnn

  have hnn' : d.n96' * M ≤ n * n := by
    rw [hn']
    calc 8 * n * M * (d.D + 1) * d.del * M = n * (8 * M ^ 2 * (d.D + 1) * d.del) := by ring
      _ ≤ n * (8 * M ^ 2 * (d.D + 1) * d.del * t) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ ht1)
      _ = n * n := by rw [hn]
  have hA : n + d.D + 1 ≤ n ^ 2 := by nlinarith
  have hB : d.n96' + M ≤ n ^ 2 := by nlinarith
  have hcard : cardUX d.D d.N n d.n96' ≤ n ^ (4 * M) := by
    unfold cardUX
    rw [← hM]
    calc (n + d.D + 1).choose (d.D + 1) * (d.n96' + M).choose M
        ≤ (n ^ 2) ^ (d.D + 1) * (n ^ 2) ^ M :=
          Nat.mul_le_mul ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hA _))
            ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hB _))
      _ = n ^ (2 * (d.D + 1 + M)) := by ring
      _ ≤ n ^ (4 * M) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcpos : 0 < cardUX d.D d.N n d.n96' := by
    unfold cardUX
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hlog1 : Real.log (cardUX d.D d.N n d.n96') ≤ (4 * M : ℕ) * Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast hcpos) (by exact_mod_cast hcard)
  have hlogn : Real.log n ≤ n / (16 * M) + 3 * Real.log 2 + M / 2 := by
    have h8 : (0 : ℝ) < 8 * M := by positivity
    have e : (n : ℝ) = n / (8 * M) * (8 * M) := by field_simp
    rw [e, Real.log_mul (by positivity) h8.ne', Real.log_mul (by norm_num) (by positivity)]
    have : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [this]
    have a1 := log_le_half (show (0 : ℝ) < n / (8 * M) by positivity)
    have a2 := log_le_half (show (0 : ℝ) < M by positivity)
    have : (n : ℝ) / (8 * M) / 2 = n / (8 * M) * (8 * M) / (16 * M) := by field_simp; ring
    linarith
  have hl2 := Real.log_two_lt_d9
  have hPO : d.PO ≤ t := by
    have := Nat.le_ceil d.PO
    rw [ht]; push_cast; linarith
  have hnMR : 32 * (M : ℝ) ^ 2 * t ≤ n := by exact_mod_cast hnM
  have key : (4 * M : ℝ) * (n / (16 * M)) = n / 4 := by field_simp; ring
  have h4 : ((4 * M : ℕ) : ℝ) = 4 * M := by push_cast; ring
  rw [h4] at hlog1
  have : (4 * M : ℝ) * Real.log n ≤ n / 4 + 12 * M * Real.log 2 + 2 * M ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlogn (by positivity : (0 : ℝ) ≤ 4 * M)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left htR (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 2),
    mul_le_mul_of_nonneg_left hMR (by positivity : (0 : ℝ) ≤ (M : ℝ))]
end ReciprocityTheory.ChartRestriction.G.T0.Data
