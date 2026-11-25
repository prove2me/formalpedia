-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.secCorr_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:02.401509+00:00
-- url     : https://prove2.me/submissions/d34a718e-1421-4646-905e-097bcf331391

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenRank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_rs_resTop
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Rel
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
private lemma exists_coh_extending_of_mem_wchart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j' : K' → L.ι)
    (hj' : LB.Coh L φ' j') (y : Y) (hy : y ∈ LB.wchart L φ' j') :
    ∃ j : K → L.ι, LB.Coh L φ j ∧ (∀ k k', φ k = φ' k' → j k = j' k') ∧ y ∈ LB.wchart L φ j := by
  classical
  have memw : ∀ {T : Type} [Fintype T] (ψ : T → (Y ⟶ X)) (i : T → L.ι),
      y ∈ LB.wchart L ψ i ↔ ∀ t, (ψ t).base y ∈ L.U (i t) := by
    intro T _ ψ i
    first
    | exact Set.mem_iInter
    | simp [LB.wchart]
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := by
    intro x
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let g : (Y ⟶ X) → L.ι := fun ψ =>
    if h : ∃ k', φ' k' = ψ then j' h.choose else (hcov (ψ.base y)).choose
  refine ⟨fun k => g (φ k), ?_, ?_, ?_⟩
  · intro k₁ k₂ h
    show g (φ k₁) = g (φ k₂)
    rw [h]
  · intro k k' h
    have hex : ∃ k'', φ' k'' = φ k := ⟨k', h.symm⟩
    show g (φ k) = j' k'
    simp only [g, dif_pos hex]
    exact hj' _ _ (hex.choose_spec.trans h)
  · rw [memw]
    intro k
    have hy' := (memw φ' j').mp hy
    show (φ k).base y ∈ L.U (g (φ k))
    by_cases hex : ∃ k'', φ' k'' = φ k
    · simp only [g, dif_pos hex]
      have := hy' hex.choose
      rw [hex.choose_spec] at this
      exact this
    · simp only [g, dif_neg hex]
      exact (hcov _).choose_spec
private lemma sections_eq_of_locally_rs_eq {Z : Scheme.{0}} {W : Z.Opens} (a b : Γ(Z, W))
    (h : ∀ z ∈ W, ∃ (V : Z.Opens) (hV : V ≤ W), z ∈ V ∧ rs hV a = rs hV b) : a = b := by
  first
  | (apply TopCat.Presheaf.section_ext Z.sheaf W a b
     intro z hz
     obtain ⟨V, hV, hzV, he⟩ := h z hz
     have ha := congrArg (fun f => f.hom a) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hb := congrArg (fun f => f.hom b) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hc := congrArg (Z.presheaf.germ V z hzV).hom he
     exact ha.symm.trans (hc.trans hb))
  | (choose V hV hzV he using h
     exact TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun z : W => V z.1 z.2) W
       (fun z => homOfLE (hV z.1 z.2))
       (by intro z hz; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV z hz⟩) a b
       (fun z => he z.1 z.2))
private lemma map_mul_rs {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (a b : Γ(Z, U)) :
    rs h (a * b) = rs h a * rs h b := by
  first
  | exact map_mul _ a b
  | simp [rs]
end Rel
section SameSum
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)
end SameSum
section Rank
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} (D : DegData R I)
end Rank
end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    {s₁ s₂ : LB.Sec (LB.LinComb L φ ε)} {x₁ x₂ : LB.Sec (LB.LinComb L φ' ε')}
    (h1 : SecCorr φ ε φ' ε' s₁ x₁) (h2 : SecCorr φ ε φ' ε' s₂ x₂) (c d : Γ(Y, ⊤))
    (hx : ∀ j' : K' → L.ι, resTop _ c * x₁.f j' = resTop _ d * x₂.f j') :
    ∀ j : K → L.ι, resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
  have memE : ∀ z : Y, z ∈ LB.wchart L (K := Empty) (fun e => e.elim : Empty → (Y ⟶ X)) (fun e => e.elim) := by
    intro z
    first
    | exact Set.mem_iInter.mpr (fun e => e.elim)
    | simp [LB.wchart]
  have stepA : ∀ j : K → L.ι, LB.Coh L φ j → resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
    intro j hj
    apply sections_eq_of_locally_rs_eq
    intro z hz
    obtain ⟨j', hj', hjj, hzj'⟩ := exists_coh_extending_of_mem_wchart (K := K') (K' := K) hL φ' φ j hj z hz
    have hcomp : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' h => (hjj k' k h.symm).symm
    refine ⟨LB.wchart L φ j ⊓ LB.wchart L φ' j', inf_le_left, ?_, ?_⟩
    · first
      | exact ⟨hz, hzj'⟩
      | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hzj'⟩
    · have e1 := h1 j j' hj hj' hcomp
      have e2 := h2 j j' hj hj' hcomp
      have e3 := congrArg (rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _)) (hx j')
      have m1 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (s₁.f j)
      have m2 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (s₂.f j)
      have m3 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (x₁.f j')
      have m4 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (x₂.f j')
      rw [rs_resTop] at m1 m2 m3 m4
      exact m1.trans ((congrArg (fun t => resTop _ c * t) e1).trans (m3.symm.trans (e3.trans
        (m4.trans ((congrArg (fun t => resTop _ d * t) e2.symm).trans m2.symm)))))
  intro j
  apply sections_eq_of_locally_rs_eq
  intro z hz
  obtain ⟨j'', hj'', -, hz''⟩ := exists_coh_extending_of_mem_wchart (K' := Empty) hL φ
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) z (memE z)
  refine ⟨(LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'', inf_le_left, ?_, ?_⟩
  · first
    | exact ⟨hz, hz''⟩
    | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hz''⟩
  · have e1 := s₁.compat j j''
    have e2 := s₂.compat j j''
    have e3 := congrArg (rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _))
      (stepA j'' hj'')
    have m1 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j)
    have m2 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j)
    have m3 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j'')
    have m4 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j'')
    rw [rs_resTop] at m1 m2 m3 m4
    have key := m3.symm.trans (e3.trans m4)
    rw [m1, m2]
    dsimp only [rs]
    rw [e1, e2, _root_.mul_left_comm, _root_.mul_left_comm (resTop _ d)]
    congr 1
end ReciprocityTheory.ChartRestriction.G.DVR.TG
