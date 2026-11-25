-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.expIdent_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:53:27.070259+00:00
-- url     : https://prove2.me/submissions/0ca6cb7b-8188-4529-993b-1b95c4ba6827

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sum_attach_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) {S S' : Finset D.toPre.X} (hSS : S ⊆ S')
    (hvan : ∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0)
    (h : ExpIdent U e k σ f S) : ExpIdent U e k σ f S' := by
  classical
  intro p j₁ jf jt hj hcoh'
  set m : PUnit.{1} ⊕ ((S × Fin 4) ⊕ (S × Fin 4)) → PUnit.{1} ⊕ ((S' × Fin 4) ⊕ (S' × Fin 4)) :=
    Sum.map id (Sum.map (fun a => (⟨a.1.1, hSS a.1.2⟩, a.2)) (fun a => (⟨a.1.1, hSS a.1.2⟩, a.2)))
    with hm
  have hcoh : CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
        (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
          (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
      (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    intro a b hab
    have h1 := hcoh' (m a) (m b) (by
      rcases a with a | a | a <;> rcases b with b | b | b <;> exact hab)
    rcases a with a | a | a <;> rcases b with b | b | b <;> exact h1
  have hS := h p j₁ jf jt hj hcoh
  have hle : U.expW e p j₁ S' jf jt ≤ U.expW e p j₁ S jf jt :=
    inf_le_inf_left _ (Finset.inf_mono hSS)
  have key := congrArg (rs hle) hS
  simp only [rs, res, Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow, map_sum] at key
  rw [sum_attach_mono hSS _ (fun α hα => by
    have h0 := hvan α.1 hα (jf α.1)
    erw [h0, map_zero, zero_mul])]
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at key
  convert key using 4
  all_goals first | rfl | exact Subsingleton.elim _ _ | skip
  all_goals (erw [Units.coe_map, Units.coe_map]; exact (rs_rs _ hle _).symm)
end ReciprocityTheory.ChartRestriction.G.DVR
