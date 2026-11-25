-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___isGen_8ccbc68b0b48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:38:16.002349+00:00
-- url     : https://prove2.me/submissions/be6478f0-1e99-473d-b868-5142558e08fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
import Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg__At_trans_8cc8ae9ac14b
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_rigAt_trans
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_gAt_congr

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
theorem _root_.solution (χ χ' : D.X) : (D.τ χ χ').IsGen := by
  intro j j'
  have w : ∀ k, LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j ⊓
      LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j' ≤
      laφ D.P.A (D.cK χ) (D.cK χ') k ⁻¹ᵁ (D.P.L.U (j k) ⊓ D.P.L.U (j' k)) := fun k =>
    le_inf (inf_le_left.trans (LB.wchart_le D.P.L _ j k))
      (inf_le_right.trans (LB.wchart_le D.P.L _ j' k))
  have e0 : (D.cK (χ + χ')).left = laφ D.P.A (D.cK χ) (D.cK χ') 0 :=
    congrArg (fun f : genPt R ⟶ D.P.A => f.left) (D.cT_add (genPt R) χ χ')
  have key : ∀ {A : Type} [CommGroup A] {a b c d a' b' c' d' g0 g0' g1 g2 g3 : A},
      g0 = g0' → a = g0⁻¹ * a' → b = g1⁻¹ * b' → c = g2⁻¹ * c' → d = g3 * d' →
      a * b⁻¹ * c⁻¹ * d⁻¹ = (g0' ^ (-1 : ℤ) * g1 ^ (1 : ℤ) * g2 ^ (1 : ℤ) * g3 ^ (-1 : ℤ)) *
        (a' * b'⁻¹ * c'⁻¹ * d'⁻¹) := by
    intro A _ a b c d a' b' c' d' g0 g0' g1 g2 g3 e h0 h1 h2 h3
    subst e h0 h1 h2 h3
    simp only [zpow_neg, zpow_one, mul_inv, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hg : (LB.LinComb D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) laDualε).g j j' =
      D.gAt _ _ _ _ (w 0) ^ (-1 : ℤ) * D.gAt _ _ _ _ (w 1) ^ (1 : ℤ) *
        D.gAt _ _ _ _ (w 2) ^ (1 : ℤ) * D.gAt _ _ _ _ (w 3) ^ (-1 : ℤ) :=
    Fin.prod_univ_four _
  have hm : ∀ {A A' : Type} [CommGroup A] [CommGroup A'] (φ : A →* A') (a b c d : A),
      φ (a * b⁻¹ * c⁻¹ * d⁻¹) = φ a * (φ b)⁻¹ * (φ c)⁻¹ * (φ d)⁻¹ := by
    intro A A' _ _ φ a b c d
    simp only [map_mul, map_inv]
  have w0 : LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j ⊓
      LB.wchart D.P.L (laφ D.P.A (D.cK χ) (D.cK χ')) j' ≤
      (D.cK (χ + χ')).left ⁻¹ᵁ (D.P.L.U (j 0) ⊓ D.P.L.U (j' 0)) := by
    rw [e0]; exact w 0
  refine (hm _ _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) hg (hm _ _ _ _ _)).symm)
  exact key (D.gAt_congr e0 (j 0) (j' 0) _ w0 (w 0))
    (D.ψAt_trans (χ + χ') (j 0) (j' 0) _ _ _ _ w0)
    (D.ψAt_trans χ (j 1) (j' 1) _ _ _ _ (w 1)) (D.ψAt_trans χ' (j 2) (j' 2) _ _ _ _ (w 2))
    (D.rigAt_trans (j 3) (j' 3) _ _ _ _ (w 3))
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
