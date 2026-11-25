-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.sc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:29.287687+00:00
-- url     : https://prove2.me/submissions/be058e76-6547-4e72-ac5b-2e47b2eca286

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCMain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_cc_hL
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_SCPf_expS_zero__1ec350a48525
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_cc_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_cc_liftX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_cc_ordEval_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_delta_pow_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_intAA_liftX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_kapW_supp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_liftX_eq_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_liftX_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_ordNabla_wick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_secondOrder_iterate_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_divided_power_integrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (hN1 : ConnectionIntegrality) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : SCSt := by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 P hPint e he f hf
  set x := (m : k) • B.hL k h w0 with hx
  have hx0 : constantCoeff x = 0 := by
    rw [hx, smul_eq_C_mul, map_mul, constantCoeff_C, cc_hL B h hcg w0, mul_zero]
  set E0 := liftX k (FB.expS k x) with hE0def
  set E1 := liftX k (FB.expS k (-x)) with hE1def
  have hE : E0 * E1 = 1 := by
    rw [hE0def, hE1def, ← liftX_mul, ← WickVanishing.gt_expS_add _ _ hx0 (by rw [map_neg, hx0, neg_zero]),
      add_neg_cancel, expS_zero', liftX_eq_rename, map_one]
  have hE0 : constantCoeff E0 = 1 := by rw [hE0def, cc_liftX, cc_expS _ hx0]
  have hgood : ∀ l X, GoodE R E0 X → GoodE R E0 (nablaL B h m (ξh l).1 (ξh l).2 X) := by
    rintro l X ⟨G, hG, rfl⟩
    refine ⟨E1 * nabla k B h m (ξh l).1 (ξh l).2 (E0 * G),
      hN1 R d O k hRQ B h hcg w0 hw0 m (ξh l) (hH l) G hG, ?_⟩
    rw [← mul_assoc, hE, one_mul]
    rfl
  have hσ : GoodE R E0 (liftX k (FB.expS k x * f)) := ⟨liftX k f, intAA_liftX f hf, liftX_mul _ _⟩
  have haa : ∀ l l', s l = s l' → betaH k (ξh l) (ξh l') = 0 := fun l l' e' => h11 l l' fun hh => hh.2 e'
  have hab : ∀ l l', s l = s l' → betaH k (ξh l) (0, ψ l') = 0 := fun l l' e' => h12 l l' fun hh => hh.2 e'
  have hκ : ∀ l l', kapW m s ξh (fun l => (0, ψ l)) l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false := by
    intro l l' hne
    obtain ⟨hs, hs'⟩ := kapW_supp m s ξh _ l l' hne
    refine ⟨?_, hs, hs'⟩
    by_contra hc
    apply hne
    unfold kapW
    rw [if_pos ⟨hs, hs'⟩, h21 l l' (fun hh => hc hh.1), mul_zero]
  have hκJ : ∀ i j, kapE s (kapW m s ξh (fun l => (0, ψ l))) i j ∈ J := by
    intro i j
    unfold kapE kapW
    split_ifs
    · obtain ⟨u, φ, hu⟩ := hH ((sideE s).symm (Sum.inr j))
      rw [hu]
      unfold betaH
      simp only [Pi.zero_apply, mul_zero, zero_sub]
      rw [← nsmul_eq_mul]
      refine J.toAddSubmonoid.nsmul_mem (J.sum_mem fun t _ => J.neg_mem ?_) m
      rw [mul_comm, ← Algebra.smul_def]
      exact J.smul_mem _ (hψ _ t)
    · exact J.zero_mem
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (MvPolynomial.map (algebraMap R k)) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun a ha => ?_
    obtain ⟨n', _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    exact RingHom.mem_range.mp (hPint n')
  rw [ordNabla_wick hN2 hN3 B h m s ξh (fun l => (0, ψ l)) (fun _ => rfl) haa hab P (FB.expS k x * f), map_sum]
  refine Submodule.sum_mem _ fun n _ => ?_
  refine cc_ordEval_mem J e E0 hE0 (opL B h m s ξh) (opR B h m s ξh) (fun i => hgood _) (fun j => hgood _) _ hσ _
    fun mo => ?_
  by_cases hne : n ≤ e
  · refine pow_le_pow_right' (Submodule.one_le.mpr hJ1) hne ?_
    have key := (_root_.divided_power_integrality R k _ _ J _ hκJ (MvPolynomial.rename (sideE s) P0) n).1 mo
    rw [← delta_pow_rename s _ (kapW_supp m s ξh _) n P, ← hP0, ← MvPolynomial.map_rename]
    exact key
  · rw [secondOrder_iterate_eq_zero c s _ hκ P e he n (by omega), map_zero, smul_zero, MvPolynomial.coeff_zero]
    exact Submodule.zero_mem _
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
