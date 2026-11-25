-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.trans_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:05.4825+00:00
-- url     : https://prove2.me/submissions/27c616f5-a466-4eb1-b9f8-a573dd008d9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_TransPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor
private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (x : Γ(X, U)ˣ) : res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl
private theorem pullU_res_lemma_2 {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (x : Γ(X, U)ˣ) : pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  ext
  change (X.presheaf.map (homOfLE h).op ≫ f.app V).hom (x : Γ(X, U)) =
    (f.app U ≫ Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom (x : Γ(X, U))
  rw [f.naturality]
  rfl
private theorem app_map_lemma_3 {X Y : Scheme.{0}} (φ ψ : Y ⟶ X) (e : φ = ψ) (U : X.Opens)
    {W : Y.Opens} (h₁ : W ≤ φ ⁻¹ᵁ U) (h₂ : W ≤ ψ ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h₁ (pullU φ U x) = res h₂ (pullU ψ U x) := by
  subst e
  rfl
private theorem fin_lemma_4 {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    {A B : Y.Opens} (k₁ : A ≤ g ⁻¹ᵁ U) (k₂ : B ≤ A) (x : Γ(X, U)ˣ) :
    res (f.preimage_mono (k₂.trans k₁)) (pullU (f ≫ g) U x) =
      pullU f B (res k₂ (res k₁ (pullU g U x))) := by
  rw [res_res_lemma, pullU_res_lemma_2]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution {G' G B' B : Scheme.{0}} (a : G' ⟶ G) (q : G ⟶ B) (q' : G' ⟶ B') (F : B' ⟶ B)
    (hqb : q' ≫ F = a ≫ q) (L : LB B) (i i' : L.ι) {U U' : B.Opens} (hU : U ≤ L.U i)
    (hU' : U' ≤ L.U i') {V V' : B'.Opens} (hVi : V ≤ (L.pull F).U (pidx L F i))
    (hVi' : V' ≤ (L.pull F).U (pidx L F i'))
    (u : Γ(G, q ⁻¹ᵁ U)ˣ) (u' : Γ(G, q ⁻¹ᵁ U')ˣ)
    (h : res (q.preimage_mono (inf_le_right : U ⊓ U' ≤ U')) u' =
      pullU q _ (res (le_inf (inf_le_left.trans hU) (inf_le_right.trans hU')) (L.g i i')) *
        res (q.preimage_mono (inf_le_left : U ⊓ U' ≤ U)) u)
    (p : q' ⁻¹ᵁ V ≤ a ⁻¹ᵁ (q ⁻¹ᵁ U)) (p' : q' ⁻¹ᵁ V' ≤ a ⁻¹ᵁ (q ⁻¹ᵁ U')) :
    res (q'.preimage_mono (inf_le_right : V ⊓ V' ≤ V')) (res p' (pullU a _ u')) =
      pullU q' _ (res (le_inf (inf_le_left.trans hVi) (inf_le_right.trans hVi'))
        ((L.pull F).g (pidx L F i) (pidx L F i'))) *
        res (q'.preimage_mono (inf_le_left : V ⊓ V' ≤ V)) (res p (pullU a _ u)) := by
  have hW1 : q' ⁻¹ᵁ (V ⊓ V') ≤ a ⁻¹ᵁ (q ⁻¹ᵁ U) :=
    (q'.preimage_mono (inf_le_left : V ⊓ V' ≤ V)).trans p
  have hW2 : q' ⁻¹ᵁ (V ⊓ V') ≤ a ⁻¹ᵁ (q ⁻¹ᵁ U') :=
    (q'.preimage_mono (inf_le_right : V ⊓ V' ≤ V')).trans p'
  have hW : q' ⁻¹ᵁ (V ⊓ V') ≤ a ⁻¹ᵁ (q ⁻¹ᵁ (U ⊓ U')) := le_inf hW1 hW2
  have h1 := congrArg (fun y => res hW (pullU a (q ⁻¹ᵁ (U ⊓ U')) y)) h
  simp only [map_mul, pullU_res_lemma_2, res_res_lemma] at h1
  simp only [LB.pull, LB.LinComb, pidx, Fintype.prod_unique, zpow_one, pullU_res_lemma_2,
    res_res_lemma]
  rw [h1]
  congr 1
  exact (app_map_lemma_3 (a ≫ q) (q' ≫ F) hqb.symm (L.U i ⊓ L.U i') _ _ (L.g i i')).trans
    (fin_lemma_4 q' F (L.U i ⊓ L.U i') _ _ (L.g i i'))
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
