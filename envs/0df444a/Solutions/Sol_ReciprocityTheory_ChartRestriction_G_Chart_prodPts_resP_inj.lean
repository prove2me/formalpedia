-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.prodPts_resP_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:55:38.686929+00:00
-- url     : https://prove2.me/submissions/ebc871bf-29b5-492a-be90-018d201e0aa0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_prodPts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_prodPts_resP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_prodPts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_prime_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable (p : Ideal S) [p.IsPrime]
variable [∀ s : S, Smooth (Gs G s).hom]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {d : ℕ} {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u)
    {a b : Fin d → Localization.AtPrime p}
    (h : prodPts a (fun i => resP p (u i)) = prodPts b (fun i => resP p (u i))) : a = b := by
  classical
  unfold Geo.Tor.IsLieBasis at hu
  obtain ⟨hT, hU⟩ := hu
  have hTS : ∀ i, TanS (u i) := fun i => (isTan_iff (u i)).2 (hT i)
  obtain ⟨⟨s, hs⟩, hint⟩ := IsLocalization.exist_integer_multiples (M := p.primeCompl)
    (Finset.univ : Finset (Fin d ⊕ Fin d)) (Sum.elim a b)
  have hint' : ∀ j, ∃ y : S, algebraMap S (Localization.AtPrime p) y = s • Sum.elim a b j :=
    fun j => hint j (Finset.mem_univ _)
  choose y hy using hint'
  let a' : Fin d → S := fun i => y (Sum.inl i)
  let b' : Fin d → S := fun i => y (Sum.inr i)
  have ea : algebraMap S (Localization.AtPrime p) s • a = fun i => algebraMap S _ (a' i) := by
    funext i
    simp only [a', hy, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Algebra.smul_def]
  have eb : algebraMap S (Localization.AtPrime p) s • b = fun i => algebraMap S _ (b' i) := by
    funext i
    simp only [b', hy, Pi.smul_apply, smul_eq_mul, Sum.elim_inr, Algebra.smul_def]
  have h2 : spMap (scaleD (algebraMap S (Localization.AtPrime p) s)) ≫ prodPts a (fun i => resP p (u i)) =
      spMap (scaleD (algebraMap S (Localization.AtPrime p) s)) ≫ prodPts b (fun i => resP p (u i)) := by
    rw [h]
  rw [scale_prodPts, scale_prodPts, ea, eb] at h2
  have h3 := congrArg (pushR G) h2
  rw [pushR_prodPts_resP, pushR_prodPts_resP] at h3
  have hA : TanS (prodPts a' u) := tanS_prodPts a' hTS
  have hB : TanS (prodPts b' u) := tanS_prodPts b' hTS
  have hx : TanS (prodPts a' u * (prodPts b' u)⁻¹) := by
    unfold TanS at hA hB ⊢
    change preH (spMap (TrivSqZeroExt.fstHom S S S)) (prodPts a' u * (prodPts b' u)⁻¹) = 1
    rw [map_mul, map_inv]
    change (spMap (TrivSqZeroExt.fstHom S S S) ≫ prodPts a' u) *
      (spMap (TrivSqZeroExt.fstHom S S S) ≫ prodPts b' u)⁻¹ = 1
    rw [hA, hB, _root_.inv_one, _root_.mul_one]
  have hx1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫
      (prodPts a' u * (prodPts b' u)⁻¹) = 1 := by
    change preH (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))))
      (prodPts a' u * (prodPts b' u)⁻¹) = 1
    rw [map_mul, map_inv]
    change (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts a' u) *
      (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts b' u)⁻¹ = 1
    rw [h3, _root_.mul_inv_cancel]
  obtain ⟨q, hq, hq1⟩ := tan_prime_uniq (p := p) hx hx1
  change preH (spMap (scaleS (S := S) q)) (prodPts a' u * (prodPts b' u)⁻¹) = 1 at hq1
  rw [map_mul, map_inv, _root_.mul_inv_eq_one] at hq1
  have hq2 : prodPts (q • a') u = prodPts (q • b') u := by
    rw [← scale_prodPts, ← scale_prodPts]
    exact hq1
  have hw : Geo.Tor.IsTangent (prodPts (q • a') u) := (isTan_iff _).1 (tanS_prodPts _ hTS)
  obtain ⟨c, _, huniq⟩ := hU _ hw
  have e1 := huniq (q • a') ((isLieComb_iff _ _ _).2 rfl)
  have e2 := huniq (q • b') ((isLieComb_iff _ _ _).2 hq2)
  have hab : q • a' = q • b' := e1.trans e2.symm
  funext i
  have hi := congrArg (algebraMap S (Localization.AtPrime p)) (congrFun hab i)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, a', b', hy, Sum.elim_inl, Sum.elim_inr,
    Algebra.smul_def] at hi
  have hqu : IsUnit (algebraMap S (Localization.AtPrime p) q) :=
    IsLocalization.map_units (M := p.primeCompl) _ ⟨q, hq⟩
  have hsu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (M := p.primeCompl) _ ⟨s, hs⟩
  rw [hqu.mul_right_inj, hsu.mul_right_inj] at hi
  exact hi
end ReciprocityTheory.ChartRestriction.G.Chart
