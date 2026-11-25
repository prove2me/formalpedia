-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_main_de3e7704d2b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:22.331719+00:00
-- url     : https://prove2.me/submissions/470b9a38-23db-4734-9a3c-4f2db8c4ee65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_hom_3ff6d176c247
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_modules_exists_glue_1b1b7795f46c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_res_res_ee0c529cdd77


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
open GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
variable {Y T : Scheme.{0}} (π : T ⟶ Y) (p : ℕ)
namespace GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
theorem _root_.solution (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) (fY : Y ⟶ SpecZ) [CompactSpace Y]
    (hden : ∀ W : Y.Opens, IsAffineOpen W → ∀ b : Γ(T, π ⁻¹ᵁ W),
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {F G : Y.Modules} (hF : IsVectorBundle F) (hG : IsVectorBundle G)
    (φ : (Scheme.Modules.pullback π).obj F ⟶ (Scheme.Modules.pullback π).obj G)
    {m₀ : ℕ} (hm₀ : 0 < m₀) (hpm₀ : ¬ p ∣ m₀)
    (hinj : ∀ n : ℕ, 0 < n → m₀ ∣ n → ¬ p ∣ n → ∀ V : Y.Opens, V ≤ invOpen fY n →
      Function.Injective (pullSectionOn π G V)) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ p ∣ n →
      ∀ V : Y.Opens, V ≤ invOpen fY n → ∀ s : Γ(F, V), ∃ t : Γ(G, V),
        pullSectionOn π G V t = φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by
  classical

  have chart : ∀ y : Y, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧
      ∀ V : Y.Opens, V ≤ W → ∀ s : Γ(F, V), ∃ τ : Γ(G, V),
        pullSectionOn π G V τ = N • φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by
    intro y
    obtain ⟨U₁, -, hy₁, k, e, he⟩ := hF y
    obtain ⟨U₂, -, hy₂, k', e', he'⟩ := hG y
    obtain ⟨W, hW, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show y ∈ U₁ ⊓ U₂ from ⟨hy₁, hy₂⟩)
    obtain ⟨N, hN, hpN, hτ⟩ := exists_pull_eq_nsmul_hom π p hp h₂ (hden W hW) φ
      (he.restrict (hWle.trans inf_le_left)) (he'.restrict (hWle.trans inf_le_right))
    exact ⟨W, hW, hyW, N, hN, hpN, hτ⟩
  choose W hW hyW N hN hpN hτ using chart

  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  have hcov : ∀ x : Y, ∃ y : S, x ∈ W y := by
    intro x
    obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hx⟩
  refine ⟨m₀ * ∏ y ∈ S, N y, Nat.mul_pos hm₀ (Finset.prod_pos fun y _ => hN y), ?_,
    fun n hn hmn hpn V hV s => ?_⟩
  · rw [(Nat.Prime.prime hp).dvd_mul, (Nat.Prime.prime hp).dvd_finsetProd_iff]
    rintro (h | ⟨y, -, hy⟩)
    exacts [hpm₀ h, hpN y hy]
  have hinjV := hinj n hn (dvd_trans (dvd_mul_right _ _) hmn) hpn

  have loc : ∀ y : S, ∃ t : Γ(G, V ⊓ W y),
      pullSectionOn π G _ t = (((Scheme.Modules.pullback π).obj G).presheaf.map
        (homOfLE ((Opens.map π.base).monotone (inf_le_left : V ⊓ W y ≤ V))).op).hom
          (φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s)) := by
    intro y
    obtain ⟨τ, hτy⟩ := hτ y (V ⊓ W y) inf_le_right
      ((F.presheaf.map (homOfLE (inf_le_left : V ⊓ W y ≤ V)).op).hom s)
    have hu : IsUnit ((N y : ℕ) : Γ(Y, V ⊓ W y)) := by
      have h1 := isUnit_intCast_of_le_invOpen fY (n : ℤ) (V := V ⊓ W y) (inf_le_left.trans hV)
      obtain ⟨c, hc⟩ := (Finset.dvd_prod_of_mem N y.2).trans ((dvd_mul_left _ _).trans hmn)
      rw [hc] at h1
      push_cast at h1
      exact isUnit_of_mul_isUnit_left h1
    refine ⟨(hu.unit⁻¹).val • τ, ?_⟩
    rw [pullSectionOn_smul, hτy, ← Nat.cast_smul_eq_nsmul (R := Γ(T, π ⁻¹ᵁ (V ⊓ W y))), smul_smul,
      ← map_natCast (π.app (V ⊓ W y)).hom, ← map_mul, IsUnit.val_inv_mul, map_one, one_smul,
      pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map π.base).monotone inf_le_left)),
      app_map_apply]
  choose t ht using loc

  obtain ⟨t', ht'⟩ := modules_exists_glue G (V := V) (fun y : S => V ⊓ W y)
    (fun _ => inf_le_left) (fun x _ => by obtain ⟨y, hy⟩ := hcov x; exact ⟨y, ‹_›, hy⟩) t
    (fun y z => by
      apply hinjV _ (inf_le_left.trans (inf_le_left.trans hV))
      rw [pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map π.base).monotone inf_le_left)),
        pullSectionOn_res _ _ inf_le_right (homOfLE ((Opens.map π.base).monotone inf_le_right)),
        ht, ht, res_res _ _ _ (homOfLE ((Opens.map π.base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ W y ⊓ (V ⊓ W z) ≤ V))),
        res_res _ _ _ (homOfLE ((Opens.map π.base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ W y ⊓ (V ⊓ W z) ≤ V)))])
  refine ⟨t', ?_⟩
  apply modules_eq_of_locally
  intro z hz
  obtain ⟨y, hy⟩ := hcov (π.base z)
  refine ⟨π ⁻¹ᵁ (V ⊓ W y), (Opens.map _).monotone inf_le_left, ⟨hz, hy⟩, ?_⟩
  rw [← pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map π.base).monotone inf_le_left)), ht', ht]
end GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
