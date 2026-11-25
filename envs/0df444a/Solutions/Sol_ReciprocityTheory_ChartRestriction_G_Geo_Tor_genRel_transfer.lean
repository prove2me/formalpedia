-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.genRel_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:46.461308+00:00
-- url     : https://prove2.me/submissions/b06d6774-ea50-4445-bae0-a086c65390e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_genRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
theorem _root_.solution {φ : B ⟶ B₀} {Φ : B' ⟶ B} {w : LB.Iso M (M₀.pull φ)} {wD : LB.Iso M' (M.pull Φ)}
    {w' : LB.Iso M' (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') (hM : M.IsLB) (hM' : M'.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hc : ∀ k, pt' k ≫ Φ = 𝟙 _ ≫ pt k)
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M' pt' ε)} (H : PMaps wD pt' pt ε t' t (𝟙 _))
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) : GenRel w t t₀ x ↔ GenRel w' t' t₀ x := by
  have z : Sp F := (default : PrimeSpectrum F)
  have hc' : ∀ k, pt' k ≫ Φ = pt k := fun k => (hc k).trans (Category.id_comp _)
  have pe : ∀ k, pt k z = Φ (pt' k z) := fun k => congrArg (fun g => g z) (hc' k).symm
  have key : ∀ (j₀ : K → M₀.ι) (i : K → M.ι) (q : K → M'.ι), (∀ k, φ (Φ (pt' k z)) ∈ M₀.U (j₀ k)) →
      (∀ k, Φ (pt' k z) ∈ M.U (i k)) → (∀ k, pt' k z ∈ M'.U (q k)) →
      (∏ k, gw w' (pt' k) z (j₀ k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M' pt' q) (t'.s q) =
        (∏ k, gw w (pt k) z (j₀ k) (i k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt i) (t.s i) := by
    intro j₀ i q h₀ h₁ h₂
    have a := T.prod (ε := ε) hc _ (𝟙 _) z j₀ i q h₀ h₁ h₂
    have b := H _ (𝟙 _) z i q h₁ h₂
    simp only [Category.id_comp] at a b
    rw [a, b, _root_.mul_assoc]
  rw [genRel_iff w t t₀ x z, genRel_iff w' t' t₀ x z]
  refine and_congr (forall_congr' fun k => by rw [← Category.assoc, hc']) ⟨fun H' q j₀ h₀ h₂ => ?_, fun H' i j₀ h₀ h₁ => ?_⟩
  · choose i hi using fun k => exists_chart hM (Φ (pt' k z))
    rw [key j₀ i q h₀ hi h₂]
    exact H' i j₀ (fun k => by rw [pe]; exact h₀ k) (fun k => by rw [pe]; exact hi k)
  · choose q hq using fun k => exists_chart hM' (pt' k z)
    have h₀' : ∀ k, φ (Φ (pt' k z)) ∈ M₀.U (j₀ k) := fun k => by rw [← pe]; exact h₀ k
    rw [← key j₀ i q h₀' (fun k => by rw [← pe]; exact h₁ k) hq]
    exact H' q j₀ h₀' hq
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
