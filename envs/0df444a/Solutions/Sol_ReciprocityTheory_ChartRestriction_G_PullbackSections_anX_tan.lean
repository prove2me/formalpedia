-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:29.251032+00:00
-- url     : https://prove2.me/submissions/c3a70d73-9836-4d38-b7e9-788b7ba1eddc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anX_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ex_zero_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_spMap_epsMul_zero_jetTan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_epsMul_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_aug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_tan

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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
private theorem prod_ofFn_single_lemma {M : Type*} [Monoid M] :
    ∀ (n : ℕ) (u : Fin n → M) (j : Fin n), (∀ i, i ≠ j → u i = 1) → (List.ofFn u).prod = u j := by
  intro n
  induction n with
  | zero => intro u j; exact j.elim0
  | succ n ih =>
    intro u j h
    rw [List.ofFn_succ, List.prod_cons]
    cases j using Fin.cases with
    | zero =>
      have h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact h i.succ (Fin.succ_ne_zero i)
      rw [h1, _root_.mul_one]
    | succ j' =>
      rw [h 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]
      exact ih (fun i => u i.succ) j' (fun i hi => h i.succ (fun e => hi (Fin.succ_injective _ e)))
end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (j0 : Fin g) (vt : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)
    (hd : IsDerivAt0 (anE F i P) (Pi.single j0 1) vt) :
    IsCombAt y.x (m := g)
      (fun j => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫
        anX F i P hP y hy (0 + 1)).left) (fun j => if j = j0 then 1 else 0) vt := by
  refine ⟨fun k => if k = j0 then homAt y.x (jetTan ((0 : Fin 1), j0) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ anX F i P hP y hy (0 + 1) else 1, fun k => ?_, ?_⟩
  · by_cases hk : k = j0
    · subst hk
      simp only [if_true, epsMul_one]
      simp [spMap]
    · simp only [if_neg hk]
      rw [one_left'']
      simp only [Over.comp_left, homAt, Over.homMk_left, anX_left]
      rw [← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug]
      unfold anE
      rw [ex_zero_eq_one F i P hP, one_left'']
      simp only [Over.mk_hom, Category.assoc, hy]
  · rw [prod_ofFn_single_lemma g _ j0 (fun k hk => if_neg hk), if_pos rfl]
    simp only [Over.comp_left, homAt, Over.homMk_left, anX_left]
    exact jetPt_tan (anE F i P) (anHol F i P hP) ((0 : Fin 1), j0) vt hd
end ReciprocityTheory.ChartRestriction.G.PullbackSections
