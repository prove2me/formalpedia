-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.genRel_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:37.488155+00:00
-- url     : https://prove2.me/submissions/7b34e109-343f-4574-a113-553333347da6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_top_le_iff_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_toStk_valF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {F : Type} [Field F] {X : Scheme.{0}}
variable {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) (z : Sp F) :
    GenRel w t t₀ x ↔ (∀ k, pt k ≫ φ = pt₀ k) ∧ ∀ (j : K → M.ι) (j₀ : K → M₀.ι), (∀ k, φ (pt k z) ∈ M₀.U (j₀ k)) →
      (∀ k, pt k z ∈ M.U (j k)) →
      ((∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val := by
  refine and_congr_right fun hp => forall_congr' fun j => forall_congr' fun j₀ => ?_
  have key : (∀ k, φ (pt k z) ∈ M₀.U (j₀ k)) → (∀ k, pt k z ∈ M.U (j k)) →
      (valF (𝟙 (Sp F)) _ (t.s j).val =
        x * (∏ k, valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val ^ (-ε k)) * valF (𝟙 (Sp F)) _ (t₀.s j₀).val ↔
      ((∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val) := by
    intro h₀ h₁
    have a₁ := toStk_valF (𝟙 (Sp F)) (LB.wchart M pt j) z (Set.mem_iInter.2 h₁) (t.s j)
    have a₂ := toStk_valF (𝟙 (Sp F)) (LB.wchart M₀ pt₀ j₀) z (Set.mem_iInter.2 fun k => by
      have := h₀ k
      rw [← hp k]; exact this) (t₀.s j₀)
    have a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val) = (gw w (pt k) z (j₀ k) (j k)).val := fun k =>
      toStk_valF (pt k) ((M₀.pull φ).U (fun _ => j₀ k) ⊓ M.U (j k)) z ⟨mem_pull.2 (h₀ k), h₁ k⟩ _
    have a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val ^ (-ε k)) =
        ((∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k)⁻¹).val := by
      have hu : ∀ k, valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val ≠ 0 := fun k h0 => by
        have := a₃ k
        rw [h0, map_zero] at this
        exact (gw w (pt k) z (j₀ k) (j k)).ne_zero this.symm
      rw [map_prod, ← Finset.prod_inv_distrib, Units.coe_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      have e : Units.map (toStk z).toMonoidHom (Units.mk0 _ (hu k)) = gw w (pt k) z (j₀ k) (j k) := Units.ext (a₃ k)
      rw [← e, ← zpow_neg, ← map_zpow]
      show _ = toStk z _
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← (toStk z).injective.eq_iff, map_mul, map_mul, a₄]
    refine Iff.trans (Eq.congr a₁ (congrArg _ a₂)) ?_
    rw [Units.val_mul, mul_comm (toStk z x), _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
  constructor
  · intro H h₀ h₁
    exact (key h₀ h₁).1 (H fun k => (top_le_iff_mem _ _ z).2 ⟨mem_pull.2 (h₀ k), h₁ k⟩)
  · intro H h
    have h₀ := fun k => mem_pull.1 ((top_le_iff_mem _ _ z).1 (h k)).1
    have h₁ := fun k => ((top_le_iff_mem _ _ z).1 (h k)).2
    exact (key h₀ h₁).2 (H h₀ h₁)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
