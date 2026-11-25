-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.gauge_exp_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:50.990072+00:00
-- url     : https://prove2.me/submissions/d6cba84f-8184-47ae-99c1-fab89cb1e87a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_wickExp_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable [Algebra ℚ k]
open G2
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hH : HalfSt) : GaugeExpSt := by
  have hW := wickExp_of hH
  intro R _ d O _ _ k _ _ _ B h h' hh hh' w0 m ι _ u Q f
  have hpt : ∀ (j : Fin 1) (i : Fin d), constantCoeff ((![pt k d 0] : Fin 1 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp [pt]
  have hpz : ∀ (j : Fin 2) (i : Fin d), constantCoeff ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · first
      | exact MvPowerSeries.constantCoeff_X _
      | simp [pt]
    · show constantCoeff (0 : PS k 1 d) = 0
      exact map_zero _
  have ha : ∀ (j : Fin 2) (i : Fin d),
      constantCoeff ((![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · first
      | exact MvPowerSeries.constantCoeff_X _
      | simp [pt]
    · show constantCoeff (ev ![pt k d 0] (B.actK k w0 i)) = 0
      rw [hE k d 1 1 ![pt k d 0] (B.actK k w0 i) hpt]
      show constantCoeff (MvPowerSeries.map (algebraMap R k) (B.A.act w0 i)) = 0
      first
      | rw [MvPowerSeries.constantCoeff_map, B.A.const w0 i, map_zero]
      | simp [B.A.const w0 i]
  have hh0 : constantCoeff h = 0 := by
    rw [← hE k d 2 1 ![pt k d 0, 0] h hpz, hh.ax1, map_zero]
  obtain ⟨hq0, hq1, hq2⟩ := hQ R d O k B (h' - h) (hG R d O k B h h' hh hh') w0
  have evAdd : ∀ (a : Fin 2 → Pt k 1 d), (∀ j i, constantCoeff (a j i) = 0) →
      ∀ f g : PS k 2 d, ev a (f + g) = ev a f + ev a g := by
    intro a hz f g
    have hs : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => a p.1 p.2) := by
      first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hz p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [hz p.1 p.2]; exact IsNilpotent.zero)
      | exact ⟨fun p => by rw [hz p.1 p.2]; exact IsNilpotent.zero, fun e => Set.toFinite _⟩
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hz p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => hz p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
          (fun p => by rw [hz p.1 p.2]; exact IsNilpotent.zero)
    unfold ev
    first
    | exact MvPowerSeries.subst_add hs f g
    | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_add _ f g)
  have hsplit : B.hL k h' w0 =
      B.hL k h w0 + ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h) := by
    unfold FB.hL
    rw [← evAdd _ ha]
    congr 1
    ring
  have hc1 : constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul]
    unfold FB.hL
    rw [hE k d 2 1 _ h ha, hh0, mul_zero]
  have hc2 : constantCoeff ((m : k) • ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h)) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq0, mul_zero]
  unfold FB.nabVal
  rw [hsplit, smul_add, hA k 1 d _ _ hc1 hc2, ← mul_assoc]
  exact hW k d (B.FK k) ι u
    (fun l l' => dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
    Q _ (fun l l' => add_comm _ _) hq0 (fun l => hq1 (u l)) (fun l l' => hq2 (u l) (u l')) (m : k) _
end ReciprocityTheory.ChartRestriction.G.TB.GE
