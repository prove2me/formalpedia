-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ClearDenominators_proof_2cf1ed1069ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:46.619113+00:00
-- url     : https://prove2.me/submissions/37dc58ea-5948-4424-93c0-65ac1be8af05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_res_res_ee0c529cdd77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_modules_exists_glue_1b1b7795f46c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_a6b9ec1c007e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pullSectionOn_eq_nsmul_of_basis_f891758361c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_top_f6a301beb699


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
namespace ClearDenominators
theorem _root_.solution (hPB : PullbackBasis.Statement.{0})
    (hRL : RatLocalAffine.Statement) : ClearDenominators.Statement := by
  classical
  intro X f _ _ _ L hL s
  have good : ∀ x : X, ∀ V : X.Opens, x ∈ V → ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V ∧
      ∃ (n : ℕ) (t : Fin n → Γ(L, W)), IsBasisOn L W t := by
    intro x V hxV
    obtain ⟨U, -, hxU, n, t, ht⟩ := hL x
    obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
    exact ⟨W, hW, hxW, hWle.trans inf_le_right, n, _, ht.restrict (hWle.trans inf_le_left)⟩

  have inj : ∀ V : X.Opens, Function.Injective (pullSectionOn (baseChangeMap f ℚ) L V) := by
    intro V
    rw [injective_iff_map_eq_zero]
    intro τ hτ
    apply modules_eq_of_locally L τ 0
    intro x hx
    obtain ⟨W, hW, hxW, hWV, n, t, ht⟩ := good x V hx
    refine ⟨W, hWV, hxW, ?_⟩
    rw [map_zero]
    apply pullSectionOn_injective_of_basis hPB hRL f L hW ht
    rw [pullSectionOn_res (baseChangeMap f ℚ) L hWV (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone hWV)) τ, hτ, map_zero,
      map_zero]

  choose W hW hxW _hle n t ht using fun x : X => good x ⊤ trivial
  have hcl := fun x : X => exists_pullSectionOn_eq_nsmul_of_basis hPB hRL f L (hW x) (ht x)
    ((((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map
      (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W x ≤ ⊤))).op).hom s)
  choose N hN τ hτ using hcl
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  have hcov : ∀ x : X, ∃ a : F, x ∈ W a := by
    intro x
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩

  let c : F → ℕ := fun a => ∏ y ∈ F.erase a, N y
  have hc : ∀ a : F, c a * N a = ∏ y ∈ F, N y := fun a => Finset.prod_erase_mul _ _ a.2
  let τ' : ∀ a : F, Γ(L, W a) := fun a => c a • τ a
  have hτ' : ∀ a : F, pullSectionOn (baseChangeMap f ℚ) L (W a) (τ' a) = (∏ y ∈ F, N y) •
      (((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map
        (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W a ≤ ⊤))).op).hom s := by
    intro a
    simp only [τ', map_nsmul, hτ, smul_smul, hc]
  obtain ⟨T', hT'⟩ := modules_exists_glue L (V := ⊤) (fun a : F => W a) (fun _ => le_top)
    (fun x _ => hcov x) τ' (fun a b => by
      apply inj
      rw [pullSectionOn_res (baseChangeMap f ℚ) L inf_le_left (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_left)),
        pullSectionOn_res (baseChangeMap f ℚ) L inf_le_right (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_right)),
        hτ', hτ', map_nsmul, map_nsmul, res_res, res_res _ _ _
          (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W a ⊓ W b ≤ ⊤)))])
  refine ⟨∏ y ∈ F, N y, Finset.prod_pos fun y _ => hN y, T', ?_⟩
  apply modules_eq_of_locally
  intro y _
  obtain ⟨a, ha⟩ := hcov ((baseChangeMap f ℚ).base y)
  refine ⟨(baseChangeMap f ℚ) ⁻¹ᵁ W a, (Opens.map (baseChangeMap f ℚ).base).monotone le_top, ha, ?_⟩
  rw [← pullSectionOn_top, ← pullSectionOn_res (baseChangeMap f ℚ) L le_top, hT', hτ', map_nsmul]
end ClearDenominators
end GroundTheory.Heights₂.Heights.Model
