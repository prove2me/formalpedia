-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_hermite_032dc7ca396f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:56.949807+00:00
-- url     : https://prove2.me/submissions/ccc18417-5bc0-4ba7-b259-42ef723af075

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pi_ne_da2d4218d599
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_den_fin_769de51a4e46
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_pow_3b8b2f5fe473
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.MainNotions.G
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)
local notation "π" => algebraMap W Q ϖ
include hϖ
variable {k : ℕ}
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (L : Submodule W (Fin k → Q)) (hL : IsLattice W L) :
    ∃ (A : Matrix (Fin k) (Fin k) Q) (n : Fin k → ℤ), (∀ i j, i < j → A i j = 0) ∧ (∀ a, A a a = π ^ n a) ∧
      L = colSpan W A := by
  classical
  have hp := pi_ne (Q := Q) ϖ hϖ
  obtain ⟨g, hg, rfl⟩ := hL

  obtain ⟨N, hN⟩ := exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g x.1 x.2)
  have hbd : ∀ y ∈ colSpan W g, ∀ i, π ^ N * y i ∈ (algebraMap W Q).range := by
    intro y hy i
    unfold colSpan at hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨c, rfl⟩ := hy; exact hN (i, c)
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      rw [Pi.add_apply, mul_add]; exact (algebraMap W Q).range.add_mem h1 h2
    | smul r y _ h1 =>
      rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact (algebraMap W Q).range.mul_mem ⟨r, rfl⟩ h1

  obtain ⟨N', hN'⟩ := exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g⁻¹ x.1 x.2)
  have hunit : ∀ c : Fin k, (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) ∈ colSpan W g := by
    intro c
    choose a ha using fun j : Fin k => hN' (j, c)
    have : (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) = ∑ j, a j • (fun i => g i j) := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def, ha, smul_eq_mul]
      have h1 : (g * g⁻¹) i c = (1 : Matrix (Fin k) (Fin k) Q) i c := by rw [Matrix.mul_nonsing_inv g hg]
      rw [Matrix.mul_apply] at h1
      have h2 : ∑ j, π ^ N' * g⁻¹ j c * g i j = π ^ N' * ∑ j, g i j * g⁻¹ j c := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [h2, h1, Matrix.one_apply, Pi.single_apply]
      by_cases hic : i = c <;> simp [hic]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hgen : ∀ c : Fin k, ∃ n : ℤ, (∃ x ∈ tailL (colSpan W g) c.val, x c = π ^ n) ∧
      ∀ y ∈ tailL (colSpan W g) c.val, ∃ a : W, y c = algebraMap W Q a * π ^ n := by
    intro c
    obtain ⟨n, h1, h2⟩ := exists_gen_pow (Q := Q) ϖ hϖ
      ((tailL (colSpan W g) c.val).map (LinearMap.proj (R := W) (φ := fun _ : Fin k => Q) c))
      ⟨π ^ N', ⟨_, ⟨hunit c, fun i hi => by
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Fin.ne_of_lt hi), smul_zero]⟩, by simp⟩, pow_ne_zero _ hp⟩ N
      (by rintro _ ⟨y, hy, rfl⟩; exact hbd y hy.1 c)
    obtain ⟨x, hx, hxc⟩ := h1
    exact ⟨n, ⟨x, hx, hxc⟩, fun y hy => h2 _ ⟨y, hy, rfl⟩⟩
  choose n hx hy using hgen
  choose x hxm hxc using hx
  refine ⟨fun i c => x c i, n, fun i j hij => (hxm j).2 i hij, fun a => hxc a, ?_⟩
  apply le_antisymm
  · have key : ∀ d : ℕ, ∀ y ∈ colSpan W g, (∀ i : Fin k, i.val + d < k → y i = 0) →
        y ∈ colSpan W (fun i c => x c i) := by
      intro d
      induction d with
      | zero =>
        intro y _ h0
        have : y = 0 := funext fun i => h0 i (by simpa using i.2)
        rw [this]; exact Submodule.zero_mem _
      | succ d ih =>
        intro y hyL h0
        by_cases hd : d < k
        · let c : Fin k := ⟨k - (d + 1), by omega⟩
          have hyt : y ∈ tailL (colSpan W g) c.val := ⟨hyL, fun i hi => h0 i (by
            have : i.val < k - (d + 1) := hi
            omega)⟩
          obtain ⟨a, ha⟩ := hy c y hyt
          have h2 : y - a • x c ∈ colSpan W (fun i c => x c i) := by
            refine ih _ (Submodule.sub_mem _ hyL (Submodule.smul_mem _ _ (hxm c).1)) fun i hi => ?_
            rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def]
            by_cases hic : i.val < c.val
            · rw [hyt.2 i hic, (hxm c).2 i hic, mul_zero, sub_zero]
            · have : i = c := Fin.ext (by
                have h3 : c.val = k - (d + 1) := rfl
                omega)
              rw [this, ha, hxc c, sub_self]
          have h3 : y = (y - a • x c) + a • x c := by abel
          rw [h3]
          exact Submodule.add_mem _ h2 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))
        · exact ih y hyL fun i hi => absurd hi (by omega)
    exact fun y hyL => key k y hyL fun i hi => absurd hi (by omega)
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact (hxm c).1
end Formalism.BasicNotions.Examples₂.NZ
