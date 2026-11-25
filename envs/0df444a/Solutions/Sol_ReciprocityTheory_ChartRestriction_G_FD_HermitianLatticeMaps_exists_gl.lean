-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.exists_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:40.251822+00:00
-- url     : https://prove2.me/submissions/4d56b54f-3300-4132-acf6-df48b54c1a3c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_phi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
open Matrix NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (f f' : Basis ι ℤ X.Λ)
variable {f f'}
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
theorem _root_.solution (h : ty X f = ty X f') :
    ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧
      (∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f i : Fin r → E) = f' i) ∧
      ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X f').repr v i • (f i : Fin r → E) := by
  have h' : ty X f' = ty X f := h.symm
  have hc : (phiE X h).comp (phiE X h') = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f' f v
  have hc' : (phiE X h').comp (phiE X h) = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f f' v
  have hMM : LinearMap.toMatrix' (phiE X h) * LinearMap.toMatrix' (phiE X h') = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id]
  have hMM' : LinearMap.toMatrix' (phiE X h') * LinearMap.toMatrix' (phiE X h) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc', LinearMap.toMatrix'_id]
  have hv : ∀ v, LinearMap.toMatrix' (phiE X h) *ᵥ v = phi X f f' v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h) v
  have hv' : ∀ v, LinearMap.toMatrix' (phiE X h') *ᵥ v = phi X f' f v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h') v
  refine ⟨⟨LinearMap.toMatrix' (phiE X h), LinearMap.toMatrix' (phiE X h'), hMM, hMM'⟩,
    ⟨fun x y => ?_, fun x => ?_⟩, fun i => ?_, fun v => ?_⟩
  · show herm X.Gm (LinearMap.toMatrix' (phiE X h) *ᵥ x) (LinearMap.toMatrix' (phiE X h) *ᵥ y) = _
    rw [hv, hv, phi_herm X h]
  · show x ∈ X.Λ ↔ LinearMap.toMatrix' (phiE X h) *ᵥ x ∈ X.Λ
    rw [hv]
    refine ⟨phi_mem X f f', fun hx => ?_⟩
    rw [← phi_phi X f f' x]
    exact phi_mem X f' f hx
  · show LinearMap.toMatrix' (phiE X h) *ᵥ _ = _
    rw [hv, phi_f]
  · show LinearMap.toMatrix' (phiE X h') *ᵥ v = _
    rw [hv', phi, Basis.constr_apply_fintype]
    simp only [Basis.equivFun_apply]
end ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
