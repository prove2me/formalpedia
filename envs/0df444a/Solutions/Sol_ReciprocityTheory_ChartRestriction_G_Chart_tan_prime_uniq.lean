-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tan_prime_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:37.382514+00:00
-- url     : https://prove2.me/submissions/4c60b6de-5067-4084-97db-170cfab39161

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ofId_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_away_not_mem
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fp_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_res_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_pow_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_away_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_ext_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]
variable (p : Ideal S) [p.IsPrime]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {w : sp (R₀ := S) (DualNumber S) ⟶ G} (hw : TanS w)
    (h1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w = 1) :
    ∃ q ∈ p.primeCompl, spMap (scaleS (S := S) q) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := exists_cover G
  have C : ∀ k, Chart (Gs G (s k)) := fun k => (hC k).some
  obtain ⟨k0, hk0⟩ := exists_away_not_mem s hs p
  have hle : Submonoid.powers (s k0) ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).mpr hk0
  let _ := awayAtPrime p (s k0) hk0
  have : IsScalarTower S (Localization.Away (s k0)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have : Algebra.FinitePresentation (Localization.Away (s k0)) Γ((Gs G (s k0)).left, (C k0).U) := fp_chart (C k0)
  let M := p.primeCompl.map (algebraMap S (Localization.Away (s k0)))
  have hM : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M) (Localization.AtPrime p) := by
    have e : Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M = M := by
      rw [Algebra.algebraMapSubmonoid, Algebra.algebraMap_self]
      ext x
      simp
    rw [e]
    exact IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have hwk : ∀ k, TanS (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w) :=
    fun k => tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra S A], TanS (1 : sp (R₀ := S) (DualNumber A) ⟶ G) :=
    fun A _ _ => comp_one' _
  obtain ⟨_, ⟨q₀, hq₀, rfl⟩, hc0⟩ := tanS_uniq (C k0) (A := Localization.Away (s k0))
    (A' := Localization.AtPrime p) M (hwk k0) (hone _) (by
      rw [res_res, comp_one', show (IsScalarTower.toAlgHom S (Localization.Away (s k0)) (Localization.AtPrime p)).comp
        (Algebra.ofId S (Localization.Away (s k0))) = Algebra.ofId S (Localization.AtPrime p) from ofId_ext _ _, h1])
  rw [comp_one'] at hc0
  have h2 : ∀ k, ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) q₀)) ≫
        spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w =
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫ 1 := by
    intro k
    apply tanS_away_uniq (C k) (A := Localization.Away (s k)) (s k0) (tanS_scale _ (hwk k)) (hone _)
    rw [comp_one', res_scale, res_res, AlgHom.commutes,
      show (qL (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k))) =
        (qR (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k0))) from ofId_ext _ _,
      ← res_res, show algebraMap S (Qv (s k) (s k0)) q₀ = qR (s k) (s k0) (algebraMap S (Localization.Away (s k0)) q₀)
        from ((qR (s k) (s k0)).commutes q₀).symm, ← res_scale]
    rw [show algebraMap (Localization.Away (s k0)) (Localization.Away (s k0)) (algebraMap S (Localization.Away (s k0)) q₀) =
      algebraMap S (Localization.Away (s k0)) q₀ from rfl] at hc0
    rw [hc0, comp_one']
  choose N hN using h2
  let N₂ := Finset.univ.sup N
  refine ⟨s k0 ^ N₂ * q₀, p.primeCompl.mul_mem (p.primeCompl.pow_mem hk0 N₂) hq₀, ?_⟩
  refine tan_ext_cover s hs fun k => ?_
  rw [comp_one', res_scale, Algebra.ofId_apply, map_mul, map_pow, ← scale_scale,
    scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), comp_one']
end ReciprocityTheory.ChartRestriction.G.Chart
