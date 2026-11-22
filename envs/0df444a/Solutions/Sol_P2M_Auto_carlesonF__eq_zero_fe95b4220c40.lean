-- Prove2me | solution 1 for P2M_Auto_carlesonF__eq_zero_fe95b4220c40
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:00:25.089402+00:00
-- url     : https://prove2.me/submissions/09863639-6cc7-4ce6-89d6-9d9fc0082127

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonBump_eq_zero
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {g : ℝ → ℂ} {L : ℝ} (hg : ∀ x, L < |x| → g x = 0) {p : ℝ × ℝ}
    (hp : p ∉ carlesonBox L) : carlesonF₁ g p = 0 := by
  unfold carlesonBox at hp
  by_cases h₁ : L < |-p.1 - p.2|
  · simp [carlesonF₁, hg _ h₁]
  have h₂ : 9 ≤ |p.1 - p.2| := by
    by_contra h₂
    rw [not_lt, abs_le] at h₁
    rw [not_le, abs_lt] at h₂
    exact hp ⟨by constructor <;> linarith, by constructor <;> linarith⟩
  simp [carlesonF₁, carlesonBump_eq_zero carlesonBump₁ (x := p.1 - p.2) h₂]
end Auto
