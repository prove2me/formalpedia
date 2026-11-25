-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_sep_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:05:03.447249+00:00
-- url     : https://prove2.me/submissions/a0064a73-047b-4cb4-9b89-398ed25a2584

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_shell_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_uMap_sep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_finrank_IR_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_two_le_dstar
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) :
    ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m := by
  classical
  set d := dstar (E := E) P.m with hd
  have hd2 : 2 ≤ d := tof_two_le_dstar P
  have hDd : Module.finrank ℝ (IR I) ≤ d := tof_finrank_IR_le P hI
  have hyR : ∀ y ∈ F, y ∈ IR I := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hF y hy
    exact (IR I).starProjection_apply_mem _
  let e := (stdOrthonormalBasis ℝ (IR I)).repr
  let g : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ (IR I))) := fun y =>
    e ⟨(IR I).starProjection (y - u), (IR I).starProjection_apply_mem _⟩
  have hproj : ∀ y ∈ F, (IR I).starProjection (y - u) = y - u := fun y hy =>
    (Submodule.starProjection_eq_self_iff).mpr ((IR I).sub_mem (hyR y hy) hu)
  have hgn : ∀ y ∈ F, ‖g y‖ = ‖u - y‖ := by
    intro y hy
    simp only [g, LinearIsometryEquiv.norm_map, Submodule.coe_norm, hproj y hy]
    rw [norm_sub_rev]
  have hgd : ∀ y ∈ F, ∀ y' ∈ F, dist (g y) (g y') = ‖y - y'‖ := by
    intro y hy y' hy'
    rw [dist_eq_norm]
    simp only [g, ← map_sub, LinearIsometryEquiv.norm_map]
    simp only [Submodule.coe_norm, Submodule.coe_sub, hproj y hy, hproj y' hy']
    congr 1
    abel
  have hsep : ∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → 1 ≤ ‖y - y'‖ := by
    intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := hF y hy
    obtain ⟨x', hx', rfl⟩ := hF y' hy'
    exact tof_uMap_sep P hI hx hx' hne
  set K := (F.sup fun y => ⌊‖u - y‖⌋₊) + 1 with hK
  have hmaps : ∀ y ∈ F, ⌊‖u - y‖⌋₊ ∈ Finset.range K := by
    intro y hy
    rw [Finset.mem_range, hK]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun y => ⌊‖u - y‖⌋₊) hy)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (tof_shell_sum d K hd2)
  set Fk := F.filter (fun y => ⌊‖u - y‖⌋₊ = k) with hFk
  have hFkF : ∀ y ∈ Fk, y ∈ F := fun y hy => (Finset.mem_filter.mp hy).1
  have hterm : ∀ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
    intro y hy
    have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
    have hle : (k : ℝ) ≤ ‖u - y‖ := by
      rw [← hk]
      exact Nat.floor_le (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have : (k : ℝ) ^ 2 ≤ ‖u - y‖ ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hle 2
    nlinarith [Real.pi_pos]
  have hinj : Set.InjOn g Fk := by
    intro y hy y' hy' hgg
    by_contra hne
    have h1 := hsep y (hFkF y hy) y' (hFkF y' hy') hne
    have h2 := hgd y (hFkF y hy) y' (hFkF y' hy')
    rw [hgg, dist_self] at h2
    linarith
  have hcard : (Fk.card : ℝ) ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) := by
    rw [← Finset.card_image_of_injOn hinj]
    have hpk := hP (Module.finrank ℝ (IR I)) (Fk.image g) 1 ((k : ℝ) + 1) one_pos
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by
        intro p hp
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        rw [hgn y (hFkF y hy)]
        have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
        rw [← hk]
        exact (Nat.lt_floor_add_one _).le)
      (by
        intro p hp p' hp' hne
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hp'
        rw [hgd y (hFkF y hy) y' (hFkF y' hy')]
        exact hsep y (hFkF y hy) y' (hFkF y' hy') (fun h => hne (by rw [h])))
    simpa using hpk
  calc ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2)
      ≤ ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (Fk.card : ℝ) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
    _ ≤ (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
end ReciprocityTheory.ChartRestriction.G.I2
