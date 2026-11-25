-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:26.882976+00:00
-- url     : https://prove2.me/submissions/71dc10db-31e4-4721-b964-dc922d5ca6c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_trF_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_trF_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_fe_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

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
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
private theorem sval_eq_zero_of_sec_f_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) : sval s r z J = 0 := by
  have h' := h (fun k => J (r ≫ φ k))
  unfold sval
  rw [h']
  unfold gs
  split_ifs with hm
  · erw [map_zero, map_zero]
  · rfl
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA
theorem _root_.solution (hG : GlobalFnsSt) (hB : D.TauBimult) (k : ℕ) (ρ : D.X)
    (hcls : ∀ a b : D.X, ρ + k • a = ρ + k • b → a = b)
    (σ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F ρ) (DegPre.famε k))) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 := by
  classical
  have hL : D.P.L.IsLB := D.P.isLB
  choose u hu hcu using fun mu : D.X => (gen_fe (F := F) hG k mu ρ).1
  have hval : ∀ (mu : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ' : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J → val (u mu) ρ'.left z J =
        uVal D F k ρ (cP D _ mu) ρ' z J * val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J :=
    fun mu => (gen_fe (F := F) hG k mu ρ).2 (u mu) (hu mu) (hcu mu)
  have hF : ∀ mu : D.X, FormEq (Sum.elim (fun i => (DegPre.trF D F mu).left ≫ DegPre.famφ D F ρ i)
      (DegPre.deltaφ D F k ρ mu)) (Sum.elim (DegPre.famε k) (DegPre.deltaε k))
      (DegPre.famφ D F (ρ + k • mu)) (DegPre.famε k) := by
    intro mu U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, DegPre.deltaφ, DegPre.deltaε, zpow_neg]
    rw [Finset.prod_inv_distrib, mul_left_comm, mul_inv_cancel, _root_.mul_one]
  choose tm htm using fun mu : D.X =>
    exists_sec hL (hF mu) (pullMulSec σ (DegPre.trF D F mu).left (u mu) (hu mu))
  have hX0 : ∀ (T : Over (Spec (CommRingCat.of R))) (ρ' : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J →
      uVal D F k ρ (cP D _ 0) ρ' z J * val (DegPre.famMult D F k 0 ρ) (ρ' ≫ fst _ _).left z J = 1 := by
    intro T ρ' z J hJ
    have e := fe_cocycle hB ρ' hJ k ρ 0 0
    rw [trF_zero, Category.comp_id, smul_zero, add_zero, add_zero] at e
    exact mul_eq_left.mp e
  let cst : ∀ {a b : D.X}, a = b → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F a) (DegPre.famε k)) →
      LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F b) (DegPre.famε k)) := fun h x => h ▸ x
  let S : ∀ β : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k)) := fun β =>
    if hβ : ρ = β then cst hβ σ else
      if h : ∃ mu, ρ + k • mu = β then cst h.choose_spec (tm h.choose) else (0 : Fam D F k).s β
  have hSρ : S ρ = σ := by
    dsimp only [S]
    rw [dif_pos rfl]
  have hA : ∀ (mu β : D.X), ρ + k • mu = β → ∀ (T : Over (Spec (CommRingCat.of R)))
      (ρ' : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      sval (S β) ρ'.left z J = sval σ (ρ' ≫ DegPre.trF D F mu).left z J *
        (uVal D F k ρ (cP D _ mu) ρ' z J * val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J).val := by
    intro mu β e T ρ' z J hJ
    by_cases hβ : ρ = β
    · subst hβ
      obtain rfl : mu = 0 := hcls _ _ (by rw [smul_zero, add_zero]; exact e)
      rw [hSρ, hX0 T ρ' z J hJ, trF_zero, Category.comp_id, Units.val_one, _root_.mul_one]
    · subst e
      have hex : ∃ mu', ρ + k • mu' = ρ + k • mu := ⟨mu, rfl⟩
      have key : ∀ (c : D.X) (ec : ρ + k • c = ρ + k • mu),
          sval (cst ec (tm c)) ρ'.left z J = sval σ (ρ' ≫ DegPre.trF D F mu).left z J *
            (uVal D F k ρ (cP D _ mu) ρ' z J *
              val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J).val := by
        intro c ec
        obtain rfl : c = mu := hcls _ _ ec
        change sval (tm c) ρ'.left z J = _
        rw [htm c _ ρ'.left z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, hval c T ρ' z J hJ]
        simp only [Over.comp_left]
      dsimp only [S]
      rw [dif_neg hβ, dif_pos hex]
      exact key _ _
  have hZ : ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (S β).f j = 0 := by
    intro β hβ j
    have h1 : ¬ ρ = β := fun h => hβ 0 (by rw [smul_zero, add_zero]; exact h)
    have h2 : ¬ ∃ mu, ρ + k • mu = β := fun ⟨mu, h⟩ => hβ mu h
    dsimp only [S]
    rw [dif_neg h1, dif_neg h2]
    exact zero_f _ _
  refine ⟨⟨S, ?_⟩, hSρ, hZ⟩
  intro mu' α v hv hcv
  have hvv := (gen_fe (F := F) hG k mu' α).2 v hv hcv
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ v).2 ?_
  intro y J hJ
  by_cases hα : ∃ nu, ρ + k • nu = α
  · obtain ⟨nu, rfl⟩ := hα
    have hfst : DegPre.trF D F mu' ≫ fst (TF (R := R) F) D.P.A = fst _ _ := by
      simp [DegPre.trF]
    have c1 := fe_cocycle hB (𝟙 (DegPre.BF D F)) hJ k ρ nu mu'
    have e1 := hA (nu + mu') (ρ + k • nu + k • mu') (by rw [smul_add, add_assoc]) _
      (𝟙 (DegPre.BF D F)) y J hJ
    have e2 := hA nu (ρ + k • nu) rfl _ (DegPre.trF D F mu') y J hJ
    have e3 := hvv _ (𝟙 (DegPre.BF D F)) y J hJ
    simp only [Over.id_left, Category.id_comp, hfst] at c1 e1 e2 e3
    rw [Category.id_comp, e1, e2, e3, trF_add, add_comm mu' nu, ← c1]
    simp only [Units.val_mul]
    ring
  · have h1 : ∀ mu, ρ + k • mu ≠ α + k • mu' := fun mu h =>
      hα ⟨mu - mu', by rw [smul_sub, ← add_sub_assoc, h, add_sub_cancel_right]⟩
    have h2 : ∀ mu, ρ + k • mu ≠ α := fun mu h => hα ⟨mu, h⟩
    rw [sval_eq_zero_of_sec_f_eq_zero (hZ _ h1), sval_eq_zero_of_sec_f_eq_zero (hZ _ h2), zero_mul]
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
