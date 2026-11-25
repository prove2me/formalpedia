-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_cubN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:16.495859+00:00
-- url     : https://prove2.me/submissions/14b60095-82cc-4539-8b92-26f853f00362

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {T : Over S} (a m x : T ⟶ G) (k : ℕ) :
    ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 8) ![(a * m ^ k * x).left, (a * m ^ k).left, (a * x).left, a.left,
        (m * x).left, m.left, x.left, (1 : T ⟶ G).left] ![1, -1, -1, 1, -k, k, k, -k]), t.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
        val t ρ.left z J = cubN (cubV c z J) k (ρ ≫ a) (ρ ≫ m) (ρ ≫ x) := by
  induction k with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen L.isLB (φ' := ![(a * m ^ 0 * x).left, (a * m ^ 0).left, (a * x).left, a.left,
        (m * x).left, m.left, x.left, (1 : T ⟶ G).left]) (ε' := ![1, -1, -1, 1, -(0 : ℕ), (0 : ℕ), (0 : ℕ), -(0 : ℕ)])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen L.L (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun T' ρ z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  | succ k ih =>
    obtain ⟨t, ht, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen L.isLB (φ' := ![(a * m ^ (k + 1) * x).left, (a * m ^ (k + 1)).left, (a * x).left,
        a.left, (m * x).left, m.left, x.left, (1 : T ⟶ G).left])
      (ε' := ![1, -1, -1, 1, -(k + 1 : ℕ), (k + 1 : ℕ), (k + 1 : ℕ), -(k + 1 : ℕ)]) (fun U _ h => by
        refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub (a * m ^ k) m x h))).trans ?_
        rw [pow_succ m, ← _root_.mul_assoc a]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
        module)
      (LB.mulGen L.L _ _ _ _ t (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a * m ^ k) (lift m x)).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ c.isGen _))
    refine ⟨t', ht', fun T' ρ z J hJ => ?_⟩
    refine ((hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T' ρ z J hJ)
      (val_cub c ρ hJ _ _ _)))).trans ?_
    rw [cubN, cubN, Finset.prod_range_succ]
    congr 2
    exact (map_mul (preHom ρ) _ _).trans (congrArg _ (map_pow (preHom ρ) _ _))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
