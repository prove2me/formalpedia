-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:16:42.16359+00:00
-- url     : https://prove2.me/submissions/eebc6b52-50a1-41b2-aec6-f62a44443a8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_FinOrdExists
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_trPt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_tr_left_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (u : ∀ α : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)))
    (hu : ∀ α, (u α).IsGen)
    (hc : ∀ α, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (u α) (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w))
    (ss : Fin (k + 1) → Fam D F k) (H : ∀ i : Fin k, PhiRel D F k p w (ss i.castSucc) (ss i.succ)) :
    ∀ (n : ℕ) (hn : n < k + 1) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J),
      Good D.P.L z J →
      sval ((ss ⟨n, hn⟩).s (α + n • p.y)) r z J = sval ((ss 0).s α) (r ≫ (DegPre.trPt D F (p.g.b ^ n)).left) z J *
        (∏ i ∈ Finset.range n, val (u (α + i • p.y)) (r ≫ (DegPre.trPt D F (p.g.b ^ (n - 1 - i))).left) z J).val := by
  intro n
  induction n with
  | zero =>
    intro hn α Z r z J _
    rw [zero_nsmul, add_zero]
    simp only [pow_zero, trPt_one, Over.id_left, Category.comp_id, Finset.prod_range_zero,
      Units.val_one, _root_.mul_one, Fin.mk_zero]
  | succ n ih =>
    intro hn α Z r z J hJ
    have hR := H ⟨n, by omega⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hR
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (u (α + n • p.y))).1
      (hR (α + n • p.y) (u _) (hu _) (hc _)) Z r z J hJ
    have e' := ih (by omega) α Z (r ≫ (DegPre.trPt D F p.g.b).left) z J hJ
    rw [show α + (n + 1) • p.y = α + n • p.y + p.y by rw [succ_nsmul, add_assoc], e, e', Finset.prod_range_succ,
      Units.val_mul, Nat.add_sub_cancel, Nat.sub_self, pow_zero, trPt_one, Over.id_left, Category.comp_id,
      tr_left_pow, _root_.mul_assoc]
    refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun i hi => ?_)) rfl)
    have hi' := Finset.mem_range.1 hi
    rw [tr_left_pow, show n - 1 - i + 1 = n - i by omega]
end ReciprocityTheory.ChartRestriction.G.H1
