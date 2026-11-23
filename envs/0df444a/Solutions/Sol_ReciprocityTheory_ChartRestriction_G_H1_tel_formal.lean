-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.tel_formal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:03.7883+00:00
-- url     : https://prove2.me/submissions/1f2f2f15-b6c0-4d20-9685-f9e652530ae5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_FinOrdExists
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_trPt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_trPt_mul

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (y α : D.X) (hb : DegPre.trF D F y = DegPre.trPt D F (b ^ k))
    {U : Type} [CommGroup U] (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    (∏ i ∈ Finset.range k, ∏ j : Fin 4 ⊕ Fin 4,
        h ((DegPre.trPt D F (b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F y (α + i • y) b j) ^ DegPre.deltaε k j) *
      ∏ j : Fin 4 ⊕ Fin 4, h (DegPre.deltaφ D F k α y j) ^ (-DegPre.deltaε k j) = 1 := by
  have hi : ∀ i ∈ Finset.range k, ∏ j : Fin 4 ⊕ Fin 4,
      h ((DegPre.trPt D F (b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F y (α + i • y) b j) ^ DegPre.deltaε k j =
        famTr b k (k - (i + 1)) (α + (i + 1) • y) h / famTr b k (k - i) (α + i • y) h := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [Fintype.prod_sum_type, div_eq_mul_inv, famTr, famTr, ← Finset.prod_inv_distrib]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun j _ => ?_) (Finset.prod_congr rfl fun j _ => ?_)
    · simp only [DegPre.phiφ, DegPre.deltaε, Sum.elim_inl]
      rw [show k - 1 - i = k - (i + 1) by omega, succ_nsmul, add_assoc]
    · simp only [DegPre.phiφ, DegPre.deltaε, Sum.elim_inr, zpow_neg]
      rw [← Category.assoc, ← Over.comp_left, trPt_mul, ← pow_succ, show k - 1 - i + 1 = k - i by omega]
  have tel := Finset.prod_range_div (fun i => famTr b k (k - i) (α + i • y) h) k
  beta_reduce at tel
  rw [Finset.prod_congr rfl hi, tel, Fintype.prod_sum_type]
  simp only [famTr, DegPre.deltaφ, DegPre.deltaε, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, Nat.sub_self,
    pow_zero, trPt_one, Over.id_left, Category.id_comp, Nat.sub_zero, zero_smul, add_zero, hb,
    Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
  abel
end ReciprocityTheory.ChartRestriction.G.H1
