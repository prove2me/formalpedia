-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.tcoord_jet_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:58.681636+00:00
-- url     : https://prove2.me/submissions/348af9a0-70bc-4930-a415-365060c84943

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SubstTanSnd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_TcoordJetLin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_fst_jetTan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_ker_jetAug_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_snd_lin


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
theorem _root_.solution {n : ℕ} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    {x : ∀ m, Chart.sp (R₀ := V) (Chart.JetR V (Fin n) m) ⟶ G} (hx : Chart.IsUnivChart G n x)
    (y : Chart.sp (R₀ := V) (Jet V (Fin 1 × Fin d) 1) ⟶ G)
    (hy : Chart.spMap ((jetAug : Jet V (Fin 1 × Fin d) 1 →ₐ[V] V)) ≫ y = 1)
    (φ : Jet V (Fin 1 × Fin d) 1 →ₐ[V] DualNumber V) (hφ : ∀ w, (φ w).fst = jetAug w)
    (h : Chart.IsTan (Chart.spMap φ ≫ y))
    (hk : ∀ k : Fin d, Chart.IsTan (Chart.spMap (jetTan (R := V) (m := 0) ((0 : Fin 1), k)) ≫ y)) :
    Chart.tcoord hx _ h = ∑ k, (φ (zk k)).snd • Chart.tcoord hx _ (hk k) := by
  obtain ⟨ψ, ⟨hψa, hψy⟩, -⟩ := hx.2.2 (Jet V (Fin 1 × Fin d) 1) jetAug 1 ker_jetAug_sq y hy
  have key : ∀ (χ : Jet V (Fin 1 × Fin d) 1 →ₐ[V] DualNumber V), (∀ w, (χ w).fst = jetAug w) →
      ∀ hχ : Chart.IsTan (Chart.spMap χ ≫ y),
        Chart.tcoord hx _ hχ = fun j => (χ (ψ (Chart.zR 1 j))).snd := by
    intro χ hχf hχ
    apply Chart.tcoord_eq
    have hc : (Chart.fstD V).comp (χ.comp ψ) = Chart.jetAug V (Fin n) 1 := by
      refine AlgHom.ext fun a => ?_
      have h1 := hχf (ψ a)
      have h2 := AlgHom.congr_fun hψa a
      simp only [AlgHom.comp_apply] at h2 ⊢
      exact h1.trans h2
    rw [hψy, ← Category.assoc, Chart.spMap_comp]
    exact congrArg (fun f => Chart.spMap f ≫ x 1) (Chart.eq_dualLift (χ.comp ψ) hc)
  have hk' : ∀ k, Chart.tcoord hx _ (hk k) =
      fun j => (jetTan (R := V) (m := 0) ((0 : Fin 1), k) (ψ (Chart.zR 1 j))).snd :=
    fun k => key _ (fst_jetTan k) (hk k)
  rw [key φ hφ h]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hk']
  exact snd_lin φ hφ (ψ (Chart.zR 1 j))
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
