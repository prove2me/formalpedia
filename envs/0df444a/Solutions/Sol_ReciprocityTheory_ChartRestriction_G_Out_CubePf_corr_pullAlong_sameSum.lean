-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.corr_pullAlong_sameSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:19.052555+00:00
-- url     : https://prove2.me/submissions/ca8875e3-33fe-4be2-8b2a-b74527c67d44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_Transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_prod_sameSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_gU_pullAlong_idx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_idx_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext


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
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution {X X' Y Y' : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (ψ : K → (Y' ⟶ X')) (ψ' : K' → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (hψ' : ∀ k, ψ' k ≫ F = h ≫ φ' k)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen)
    (ht' : t'.IsGen) (hc : LB.Gen.Corr L φ ε φ' ε' t t') (hS : LB.SameSum ψ ε ψ' ε') :
    LB.Gen.Corr (L.pull F) ψ ε ψ' ε' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t)
      (GeneratorPullback.pullAlong L F h φ' ε' ψ' hψ' t') := by
  classical
  intro j j' cj cj' cjj
  apply unit_ext
  intro y hy
  refine (gU_res _ y hy _).trans (Eq.trans ?_ (gU_res _ y hy _).symm)
  obtain ⟨idx, hidx⟩ := TLinPf.idx_exists L hL y
  have hF : ∀ (ζ : Y' ⟶ X') (a : (L.pull F).ι), ζ y ∈ (L.pull F).U a → F (ζ y) ∈ L.U (a ⟨⟩) :=
    fun ζ a hz => Set.mem_iInter.1 hz ⟨⟩
  have mk : ∀ k, y ∈ (ψ k ≫ F) ⁻¹ᵁ (L.U (j k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F))) := fun k =>
    ⟨show (ψ k ≫ F) y ∈ L.U (j k ⟨⟩) by
      rw [Scheme.Hom.comp_apply]; exact hF _ _ (Set.mem_iInter.1 hy.1 k), hidx _⟩
  have mk' : ∀ k, y ∈ (ψ' k ≫ F) ⁻¹ᵁ (L.U (j' k ⟨⟩) ⊓ L.U (idx (ψ' k ≫ F))) := fun k =>
    ⟨show (ψ' k ≫ F) y ∈ L.U (j' k ⟨⟩) by
      rw [Scheme.Hom.comp_apply]; exact hF _ _ (Set.mem_iInter.1 hy.2 k), hidx _⟩
  have mem0 : h y ∈ LB.wchart L φ (fun k => idx (ψ k ≫ F)) := Set.mem_iInter.2 fun k => by
    show (φ k) (h y) ∈ L.U (idx (ψ k ≫ F))
    rw [← Scheme.Hom.comp_apply, ← hψ k]; exact hidx _
  have mem0' : h y ∈ LB.wchart L φ' (fun k => idx (ψ' k ≫ F)) := Set.mem_iInter.2 fun k => by
    show (φ' k) (h y) ∈ L.U (idx (ψ' k ≫ F))
    rw [← Scheme.Hom.comp_apply, ← hψ' k]; exact hidx _
  refine (gU_pullAlong_idx L F h φ ε ψ hψ t ht j y hy.1 idx mk mem0).trans
    (Eq.trans ?_ (gU_pullAlong_idx L F h φ' ε' ψ' hψ' t' ht' j' y hy.2 idx mk' mem0').symm)

  have hmid : gU (h y) mem0 (t.s (fun k => idx (ψ k ≫ F))) =
      gU (h y) mem0' (t'.s (fun k => idx (ψ' k ≫ F))) := by
    have hc0 := hc (fun k => idx (ψ k ≫ F)) (fun k => idx (ψ' k ≫ F))
      (fun k1 k2 e => congrArg idx (by rw [hψ k1, hψ k2, e]))
      (fun k1 k2 e => congrArg idx (by rw [hψ' k1, hψ' k2, e]))
      (fun k k' e => congrArg idx (by rw [hψ k, hψ' k', e]))
    have := congrArg (gU (h y) (⟨mem0, mem0'⟩ : h y ∈ LB.wchart L φ (fun k => idx (ψ k ≫ F)) ⊓
      LB.wchart L φ' (fun k => idx (ψ' k ≫ F)))) hc0
    exact (gU_res _ (h y) _ _).symm.trans (this.trans (gU_res _ (h y) _ _))

  let Jf : (Y' ⟶ X') → L.ι := fun ζ =>
    if hz : ∃ k, ψ k = ζ then j hz.choose ⟨⟩
    else if hz' : ∃ k', ψ' k' = ζ then j' hz'.choose ⟨⟩ else idx (ζ ≫ F)
  have hJ : ∀ k, Jf (ψ k) = j k ⟨⟩ := by
    intro k
    have hz : ∃ k', ψ k' = ψ k := ⟨k, rfl⟩
    show (if hz : ∃ k', ψ k' = ψ k then j hz.choose ⟨⟩ else _) = _
    rw [dif_pos hz]
    exact congrFun (cj _ _ hz.choose_spec) ⟨⟩
  have hJ' : ∀ k', Jf (ψ' k') = j' k' ⟨⟩ := by
    intro k'
    show (if hz : ∃ k, ψ k = ψ' k' then j hz.choose ⟨⟩
      else if hz' : ∃ k'', ψ' k'' = ψ' k' then j' hz'.choose ⟨⟩ else idx (ψ' k' ≫ F)) = _
    by_cases hz : ∃ k, ψ k = ψ' k'
    · rw [dif_pos hz]; exact congrFun (cjj _ _ hz.choose_spec) ⟨⟩
    · have hz' : ∃ k'', ψ' k'' = ψ' k' := ⟨k', rfl⟩
      rw [dif_neg hz, dif_pos hz']; exact congrFun (cj' _ _ hz'.choose_spec) ⟨⟩
  let B : (Y' ⟶ X') → (Y'.presheaf.stalk y)ˣ := fun ζ =>
    if hm : y ∈ (ζ ≫ F) ⁻¹ᵁ (L.U (Jf ζ) ⊓ L.U (idx (ζ ≫ F))) then
      gU y hm (pullU (ζ ≫ F) _ (L.g (Jf ζ) (idx (ζ ≫ F)))) else 1
  have hgc : ∀ (ζ : Y' ⟶ X) (a b c : L.ι) (hab : a = b) (hm : y ∈ ζ ⁻¹ᵁ (L.U a ⊓ L.U c))
      (hm' : y ∈ ζ ⁻¹ᵁ (L.U b ⊓ L.U c)),
      gU y hm (pullU ζ _ (L.g a c)) = gU y hm' (pullU ζ _ (L.g b c)) := by
    intro ζ a b c hab hm hm'; subst hab; rfl
  have hB : ∀ k, gU y (mk k) (pullU (ψ k ≫ F) _ (L.g (j k ⟨⟩) (idx (ψ k ≫ F)))) = B (ψ k) := by
    intro k
    have hm : y ∈ (ψ k ≫ F) ⁻¹ᵁ (L.U (Jf (ψ k)) ⊓ L.U (idx (ψ k ≫ F))) := by
      rw [hJ k]; exact mk k
    show _ = (if hm : _ then _ else _)
    rw [dif_pos hm]
    exact hgc _ _ _ _ (hJ k).symm _ _
  have hB' : ∀ k, gU y (mk' k) (pullU (ψ' k ≫ F) _ (L.g (j' k ⟨⟩) (idx (ψ' k ≫ F)))) = B (ψ' k) := by
    intro k
    have hm : y ∈ (ψ' k ≫ F) ⁻¹ᵁ (L.U (Jf (ψ' k)) ⊓ L.U (idx (ψ' k ≫ F))) := by
      rw [hJ' k]; exact mk' k
    show _ = (if hm : _ then _ else _)
    rw [dif_pos hm]
    exact hgc _ _ _ _ (hJ' k).symm _ _
  refine congrArg₂ (· * ·) ?_ (congrArg _ hmid)
  exact ((Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (hB k)).trans
    (prod_sameSum B ψ ψ' ε ε' hS)).trans
    (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε' k) (hB' k)).symm
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
