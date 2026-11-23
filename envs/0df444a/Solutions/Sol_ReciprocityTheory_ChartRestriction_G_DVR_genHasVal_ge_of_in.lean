-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_ge_of_in
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:48.2223+00:00
-- url     : https://prove2.me/submissions/e3377d56-c4a2-4731-a318-1525cf19025e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_ne_zero_of_hasVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_chart_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_mul_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_unique


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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (x : Spec (CommRingCat.of V) ⟶ X) (x' : Spec (CommRingCat.of (FractionRing V)) ⟶ X) (hx : x' = jK V ≫ x)
    (ε : ℤ) (t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε))) (k : ℕ)
    (hin : ∀ (j : PUnit → L.ι) (W : (Spec (CommRingCat.of V)).Opens), IsAffineOpen W →
      W ≤ x ⁻¹ᵁ L.U (j PUnit.unit) →
      ∀ h : jK V ⁻¹ᵁ W ≤ (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε)).U j,
        ∃ r ∈ (IsLocalRing.maximalIdeal V ^ k).map (DegPre.toOpen W),
          ((jK V).app W).hom r =
            ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE h).op).hom (t.s j).val)
    {n : ℤ} (hn : GenHasVal ϖ L (fun _ => x) (fun _ => x') (fun _ => hx) (fun _ => ε) t n) : (k : ℤ) ≤ n := by
  subst hx
  obtain ⟨j₀, htop⟩ := exists_chart_top L hL (fun _ : PUnit => x) (fun _ => ε)
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun _ : PUnit => jK V ≫ x) j₀ := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L (fun _ : PUnit => x) j₀ := by
      rw [htop]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k : PUnit, x.base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    show y ∈ (⋂ k : PUnit, (jK V ≫ x).base ⁻¹' (L.U (j₀ k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  obtain ⟨c, hc, eV, hX⟩ := genHasVal_top L (fun _ : PUnit => x) (fun _ => ε) t hn j₀ htop hK
  have hW : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ x ⁻¹ᵁ L.U (j₀ PUnit.unit) := by
    intro y _
    have hy : y ∈ LB.wchart L (fun _ : PUnit => x) j₀ := by
      rw [htop]
      trivial
    have hy' : y ∈ (⋂ k : PUnit, x.base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    exact Set.mem_iInter.1 hy' PUnit.unit
  obtain ⟨r, hrm, hr⟩ := hin j₀ ⊤ (isAffineOpen_top _) hW (le_top.trans hK)
  have hcomp : ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom).comp
      (DegPre.toOpen (⊤ : (Spec (CommRingCat.of V)).Opens)) = RingHom.id V := by
    ext v
    show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
      (((Spec (CommRingCat.of V)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom v)) = v
    rw [CategoryTheory.Functor.map_id]
    simp
  have hr' : (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r ∈ IsLocalRing.maximalIdeal V ^ k := by
    have h1 := Ideal.mem_map_of_mem ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) hrm
    rwa [Ideal.map_map, hcomp, Ideal.map_id] at h1
  have hval : algebraMap V (FractionRing V) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r) =
      c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hX]
    have e1 := congrArg (fun m => m.hom r)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    exact e1.symm.trans
      (congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom z) hr)
  set r' := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r with hr'def
  rw [Irreducible.maximalIdeal_eq hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr'
  obtain ⟨s, hs⟩ := hr'
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hc0 : c * algebraMap V (FractionRing V) (eV : V) ≠ 0 :=
    mul_ne_zero (ne_zero_of_hasVal hϖ hc)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 eV.ne_zero)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hc0
    rw [← hval, hs, mul_zero, map_zero]
  obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have hv1 : HasVal ϖ (algebraMap V (FractionRing V) r') ((k : ℤ) + (m : ℤ)) := by
    refine ⟨w, ?_⟩
    rw [hs, hw, zpow_add₀ hπ, zpow_natCast, zpow_natCast]
    simp only [map_mul, map_pow]
    ring
  have hv2 := hasVal_mul_unit hc eV
  rw [← hval] at hv2
  have h3 := hasVal_unique hϖ hv1 hv2
  omega
end ReciprocityTheory.ChartRestriction.G.DVR
