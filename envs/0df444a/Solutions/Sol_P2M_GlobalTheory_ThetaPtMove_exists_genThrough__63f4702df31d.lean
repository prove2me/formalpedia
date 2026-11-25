-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaPtMove_exists_genThrough__63f4702df31d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:44.110779+00:00
-- url     : https://prove2.me/submissions/dba623da-b6e4-4fed-9e56-314a13c41e6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_snd__014c8d7c58c3
import Theorems.Thm_GlobalTheory_ConstFam_exists_gen_through
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
variable {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
namespace GlobalTheory.ThetaPtMove
theorem _root_.solution (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    (α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, b])) (hα₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, b]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ b) * val α r z J' := by
  obtain ⟨α, hα, H⟩ := exists_gen_through (φ' := ![(snd T A).left, m.left]) (h := psi hp τ hτ) hw hL₀ hL₁
    (fun i => by
      fin_cases i
      · exact (psi_snd' hp τ hτ).symm
      · exact h.symm) α₀ hα₀
  refine ⟨α, hα, fun Z r z J J' hJ hJ' => (H Z r z J J' hJ hJ').trans ?_⟩
  rw [Fin.prod_univ_two]
  rfl
end GlobalTheory.ThetaPtMove
