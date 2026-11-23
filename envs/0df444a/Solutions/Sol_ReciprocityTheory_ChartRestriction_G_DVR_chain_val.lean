-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.chain_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:34.5578+00:00
-- url     : https://prove2.me/submissions/0935cf1d-f6fa-42de-b2b2-f46689377520

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {D F} {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {k : ℕ} (p : QkPt D F k) (mu : D.X) :
    val (D.tau p.y mu) (σ.left ≫ jFK (R := R) F) z J * cubN (th D z J) k 1 (σ ≫ p.g.b) (cP D T mu) =
      val (p.g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hι⟩ := p.eq
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = p.g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ p.g.b) (cP D T mu) = val (p.g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * p.g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ p.g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hι.2 mu) σ.left).trans (val_pull hJ _ _ _)).symm rfl
end ReciprocityTheory.ChartRestriction.G.DVR
