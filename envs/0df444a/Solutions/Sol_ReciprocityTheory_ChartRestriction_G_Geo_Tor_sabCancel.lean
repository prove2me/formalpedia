-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabCancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:25.266537+00:00
-- url     : https://prove2.me/submissions/9abccbf4-e6ec-4b39-b399-d85c8abac1d0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hC : PullCubCancelSt) : SABCancelSt := by
  intro E _ _ _ H S S' S'' t t' t'' f g m n
  have hP := m.cart.1
  have hn : n.cm.F ≫ t.G.hom = t''.G.hom ≫ (g ≫ f) := n.cart.1.w
  let F' : t''.G.left ⟶ t'.G.left := hP.lift n.cm.F (t''.G.hom ≫ g) (by rw [hn, Category.assoc])
  have hF1 : F' ≫ m.cm.F = n.cm.F := hP.lift_fst _ _ _
  have hF2 : F' ≫ t'.G.hom = t''.G.hom ≫ g := hP.lift_snd _ _ _
  have hF1' : ∀ {Z : Scheme.{0}} (k : t.G.left ⟶ Z), F' ≫ m.cm.F ≫ k = n.cm.F ≫ k := by
    intro Z k; rw [← Category.assoc, hF1]
  have hF2' : ∀ {Z : Scheme.{0}} (k : S' ⟶ Z), F' ≫ t'.G.hom ≫ k = t''.G.hom ≫ g ≫ k := by
    intro Z k; rw [← Category.assoc, hF2, Category.assoc]
  let T : Over S' := Over.mk ((G3 t''.G).hom ≫ g)
  let p : Fin 3 → (T ⟶ t'.G) := fun i => Over.homMk ((x3 t''.G i).left ≫ F') (by
      show ((x3 t''.G i).left ≫ F') ≫ t'.G.hom = (G3 t''.G).hom ≫ g
      rw [Category.assoc, hF2, ← Category.assoc, Over.w (x3 t''.G i)])
  let L3 : T ⟶ G3 t'.G := lift (p 0) (lift (p 1) (p 2))
  let F3' : (G3 t''.G).left ⟶ (G3 t'.G).left := L3.left
  have hF3x : ∀ i, F3' ≫ (x3 t'.G i).left = (x3 t''.G i).left ≫ F' := by
    intro i
    show L3.left ≫ (x3 t'.G i).left = _
    rw [← Over.comp_left]
    fin_cases i <;> simp [L3, x3, p]
  have hF3 : F3' ≫ m.cm.F3 = n.cm.F3 := by
    apply hom_ext_triple t.G
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three m.cm i, ← Category.assoc, hF3x i, Category.assoc, hF1,
      cubeMap_comp_proj_three n.cm i]
  have hT : F3' ≫ (G3 t'.G).hom = (G3 t''.G).hom ≫ g := Over.w L3
  let cm : CubeMap t''.G t'.G :=
    { F := F'
      F3 := F3'
      e := g
      e_comm := by
        apply hP.hom_ext
        · simp only [Category.assoc, hF1]
          rw [n.cm.e_comm, m.cm.e_comm, n.base, m.base, Category.assoc]
        · simp only [Category.assoc, hF2]
          have k1 := Over.w (η[t''.G] : 𝟙_ (Over S'') ⟶ t''.G)
          have k2 := Over.w (η[t'.G] : 𝟙_ (Over S') ⟶ t'.G)
          simp only [eSec]
          rw [← Category.assoc, k1, k2]
          simp
      psum_comm := fun I => by
        apply hP.hom_ext
        · simp only [Category.assoc, hF1, m.cm.psum_comm I]
          rw [n.cm.psum_comm I, ← Category.assoc, hF3]
        · have a1 := Over.w (psum t''.G (x3 t''.G) I)
          have a2 := Over.w (psum t'.G (x3 t'.G) I)
          rw [Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hT] }
  have hcart : IsGrpPullback t''.G t.G (g ≫ f) (F' ≫ m.cm.F) := by
    have k := n.cart
    rw [← hF1] at k
    exact k
  refine ⟨{ cm := cm, cart := IsGrpPullback.cancel m.cart hcart hF2, base := rfl, act := ?_, lin := ?_ },
    hF1.symm⟩
  · intro a
    show (t''.act.act a).left ≫ F' = F' ≫ (t'.act.act a).left
    apply hP.hom_ext
    · simp only [Category.assoc, hF1, m.act a, hF1']
      rw [n.act a]
    · have a1 := Over.w (t''.act.act a)
      have a2 := Over.w (t'.act.act a)
      rw [Category.assoc, hF2, ← Category.assoc, a1, Category.assoc, a2, hF2]
  · exact hC S S' S'' t.G t'.G t''.G m.cm cm n.cm t.PP t'.PP t''.PP t.cub t'.cub t''.cub
      hF1.symm hF3.symm (by show n.cm.e = g ≫ m.cm.e; rw [n.base, m.base]) m.lin n.lin
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
