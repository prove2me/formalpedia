-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.eq_of_comb_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:57.740592+00:00
-- url     : https://prove2.me/submissions/3a552f74-a463-4ef2-a19c-f1e3597d5071

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LiePush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G']
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
include h
omit h
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [IsLocalRing S] [Smooth G'.hom] {d : ℕ} {v : Fin d → (epsR S ⟶ G')} (hv : ∀ i, IsTangent (v i))
    {w : epsR S ⟶ G'} (hw : IsTangent w) (j : Fin d) (hc : IsLieComb (Pi.single j 1) v w) : w = v j := by
  obtain ⟨u, hu, rfl⟩ := hc
  have oneL : ∀ {Y : Scheme.{0}} (T H : Over Y) [GrpObj H], (1 : T ⟶ H).left = T.hom ≫ η[H].left := by
    intro Y T H _
    show (toUnit T ≫ η[H]).left = _
    rw [Over.comp_left]
    congr 1
    all_goals first
      | simpa using Over.w (toUnit T)
      | (have e := Over.w (toUnit T)
         rwa [show (𝟙_ (Over Y)).hom = 𝟙 Y from rfl, Category.comp_id] at e)
  have single : ∀ {m : ℕ} (a : Fin m → (epsR S ⟶ G')) (k : Fin m), (∀ i, i ≠ k → a i = 1) →
      (List.ofFn a).prod = a k := by
    intro m
    induction m with
    | zero => intro a k; exact k.elim0
    | succ m ih =>
      intro a k ha
      rw [List.ofFn_succ, List.prod_cons]
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
      · have ht : (fun i : Fin m => a i.succ) = fun _ => 1 := funext fun i => ha _ (Fin.succ_ne_zero i)
        rw [ht]
        simp
      · rw [ha 0 (Fin.succ_ne_zero k').symm, _root_.one_mul]
        exact ih (fun i => a i.succ) k' (fun i hi => ha _ (fun e => hi (Fin.succ_injective _ e)))
  have hv' : ∀ i, Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (v i).left = η[G'].left := hv
  have h0 : Geo.Tor.spMap (epsScaleR (0 : S)) =
      (epsR S).hom ≫ Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    all_goals (ext r <;> first
      | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [epsScaleR]; done))
  have h1 : Geo.Tor.spMap (epsScaleR (1 : S)) = 𝟙 _ := by
    simp only [Geo.Tor.spMap]
    rw [← Spec.map_id]
    congr 1
    all_goals (ext r <;> first
      | (simp [epsScaleR]; done)
      | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done))
  have hu1 : ∀ i, i ≠ j → u i = 1 := by
    intro i hi
    apply Over.OverMorphism.ext
    rw [hu i, Pi.single_eq_of_ne hi, h0, oneL, Category.assoc, hv' i]
  have huj : u j = v j := by
    apply Over.OverMorphism.ext
    rw [hu j, Pi.single_eq_same, h1, Category.id_comp]
  rw [single u j hu1, huj]
end ReciprocityTheory.ChartRestriction.G.Chart
