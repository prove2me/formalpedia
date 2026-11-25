-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_pack_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:04:59.917985+00:00
-- url     : https://prove2.me/submissions/dd329eea-bb0e-4390-9168-05eacf0787ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneLeKappaMulPhase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_isU_uMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_uMap_sep


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
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) (R : ℝ) (hR : 1 ≤ R)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x)
    (hFR : ∀ y ∈ F, ‖u - y‖ ≤ R) : (F.card : ℝ) ≤ (3 * R) ^ Module.finrank ℝ (IR I) := by
  classical

  let K : Submodule ℝ (Vsp X.dim) := IR I
  let B := stdOrthonormalBasis ℝ K
  let φ : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) :=
    fun v => B.repr (K.orthogonalProjectionOnto (v - u))
  have hmem : ∀ y ∈ F, y - u ∈ K := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := hF y hy
    exact K.sub_mem (isU_uMap I x).1 hu
  have hpr : ∀ y (hy : y ∈ F), K.orthogonalProjectionOnto (y - u) = ⟨y - u, hmem y hy⟩ := fun y hy =>
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y - u, hmem y hy⟩
  have hφ : ∀ y ∈ F, ∀ y' ∈ F, ‖φ y - φ y'‖ = ‖y - y'‖ := by
    intro y hy y' hy'
    show ‖B.repr (K.orthogonalProjectionOnto (y - u)) - B.repr (K.orthogonalProjectionOnto (y' - u))‖
      = ‖y - y'‖
    rw [hpr y hy, hpr y' hy', ← map_sub, LinearIsometryEquiv.norm_map]
    show ‖(y - u) - (y' - u)‖ = ‖y - y'‖
    congr 1
    abel
  have hinj : Set.InjOn φ F := by
    intro y hy y' hy' h
    have e := hφ y hy y' hy'
    rw [h, sub_self, norm_zero] at e
    exact sub_eq_zero.mp (norm_eq_zero.mp e.symm)
  have hcard : ((F.image φ).card : ℝ) ≤ (3 * R / 1) ^ Module.finrank ℝ K := by
    apply hP (Module.finrank ℝ K) (F.image φ) 1 R one_pos hR
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      show ‖B.repr (K.orthogonalProjectionOnto (y - u))‖ ≤ R
      rw [hpr y hy, LinearIsometryEquiv.norm_map]
      show ‖y - u‖ ≤ R
      rw [norm_sub_rev]
      exact hFR y hy
    · intro z hz z' hz' hne
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      rw [dist_eq_norm, hφ y hy y' hy']
      have hyy : y ≠ y' := fun h => hne (by rw [h])
      obtain ⟨x, hx, rfl⟩ := hF y hy
      obtain ⟨x', hx', rfl⟩ := hF y' hy'
      exact tof_uMap_sep P hI hx hx' hyy
  rw [Finset.card_image_of_injOn hinj, div_one] at hcard
  exact hcard
end ReciprocityTheory.ChartRestriction.G.I2
