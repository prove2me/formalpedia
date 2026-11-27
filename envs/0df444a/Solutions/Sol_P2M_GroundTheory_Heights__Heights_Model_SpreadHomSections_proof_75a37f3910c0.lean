-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_proof_75a37f3910c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:07.262835+00:00
-- url     : https://prove2.me/submissions/c020d843-6814-4d1e-a11f-c24f8f08a9a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsRatDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_hom_fa87e4e2089e
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
namespace GroundTheory.Heights₂.Heights.Model
namespace SpreadHomSections
theorem _root_.solution (h₁ : RatDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    (h₃ : GenericPullInj.Statement) : SpreadHomSections.Statement := by
  classical
  intro X f _ _ a ha F G hF hG φ
  obtain ⟨m₀, hm₀, hinj⟩ := h₃ X f a ha G hG
  have hq : IsUnit (((a : ℕ) : ℤ) : ℚ) := isUnit_intCast_rat a (by exact_mod_cast ha.ne')

  have chart : ∀ y : (invOpen f (a : ℤ) : Scheme.{0}), ∃ U : X.Opens, IsAffineOpen U ∧
      y ∈ (invOpen f a).ι ⁻¹ᵁ U ∧ ∃ N : ℕ, 0 < N ∧
        ∀ (V : (invOpen f a : Scheme.{0}).Opens), V ≤ (invOpen f a).ι ⁻¹ᵁ U →
          ∀ s : Γ(F, V), ∃ τ : Γ(G, V),
            pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G V τ =
              N • φ.app (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) ⁻¹ᵁ V)
                (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) F V s) := by
    intro y
    obtain ⟨U₁, -, hy₁, k, e, he⟩ := hF y
    obtain ⟨U₂, -, hy₂, k', e', he'⟩ := hG y
    obtain ⟨U, hU, hyU, hUle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show (invOpen f a).ι.base y ∈ (invOpen f a).ι ''ᵁ (U₁ ⊓ U₂) from ⟨y, ⟨hy₁, hy₂⟩, rfl⟩)
    have hW : (invOpen f a).ι ⁻¹ᵁ U ≤ U₁ ⊓ U₂ :=
      ((Opens.map (invOpen f a).ι.base).monotone hUle).trans
        ((invOpen f a).ι.preimage_image_eq (U₁ ⊓ U₂)).le
    obtain ⟨N, hN, hτ⟩ := SpreadHomSections.exists_pull_eq_nsmul_hom f a _ h₁ h₂ hU φ
      (he.restrict (hW.trans inf_le_left)) (he'.restrict (hW.trans inf_le_right))
    exact ⟨U, hU, hyU, N, hN, hτ⟩

  have hcpt : IsCompact ((invOpen f (a : ℤ) : X.Opens) : Set X) :=
    QuasiCompact.isCompact_preimage (f := f) _ (PrimeSpectrum.basicOpen _).isOpen
      (PrimeSpectrum.isCompact_basicOpen _)
  have : CompactSpace (invOpen f (a : ℤ) : Scheme.{0}) := isCompact_iff_compactSpace.mp hcpt
  choose U hU hyU N hN hτ using chart
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun y => (((invOpen f a).ι ⁻¹ᵁ U y : (invOpen f (a : ℤ) : Scheme.{0}).Opens) :
      Set (invOpen f (a : ℤ) : Scheme.{0})))
    (fun y => ((invOpen f a).ι ⁻¹ᵁ U y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩)
  have hcov : ∀ x : (invOpen f (a : ℤ) : Scheme.{0}), ∃ y : S, x ∈ (invOpen f a).ι ⁻¹ᵁ U y := by
    intro x
    obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hx⟩
  refine ⟨m₀ * ∏ y ∈ S, N y, Nat.mul_pos hm₀ (Finset.prod_pos fun y _ => hN y),
    fun n hn hmn V hV s => ?_⟩
  have hinjV := hinj n hn (dvd_trans (dvd_mul_right _ _) hmn)

  have loc : ∀ y : S, ∃ t : Γ(G, V ⊓ (invOpen f a).ι ⁻¹ᵁ U y),
      pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G _ t =
        (((Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj
          G).presheaf.map (homOfLE ((Opens.map (toInvOpen f ℚ a
            (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))).base).monotone
            (inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ≤ V))).op).hom
          (φ.app (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) ⁻¹ᵁ V)
            (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) F V s)) := by
    intro y
    obtain ⟨τ, hτy⟩ := hτ y (V ⊓ _) inf_le_right
      ((F.presheaf.map (homOfLE (inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ≤ V)).op).hom s)
    have hu : IsUnit ((N y : ℕ) : Γ((invOpen f (a : ℤ) : Scheme.{0}), V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)) := by
      have h1 := isUnit_intCast_of_le_invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n)
        (V := V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)
        (inf_le_left.trans hV)
      have hd : ((N y : ℕ) : ℤ) ∣ (a : ℤ) * n := by
        refine dvd_mul_of_dvd_right ?_ _
        exact_mod_cast (Finset.dvd_prod_of_mem N y.2).trans ((dvd_mul_left _ _).trans hmn)
      obtain ⟨c, hc⟩ := hd
      rw [hc, Int.cast_mul] at h1
      exact_mod_cast isUnit_of_mul_isUnit_left h1
    refine ⟨(hu.unit⁻¹).val • τ, ?_⟩
    rw [pullSectionOn_smul, hτy, ← Nat.cast_smul_eq_nsmul (R := Γ(baseChange f ℚ,
      toInvOpen f ℚ a hq ⁻¹ᵁ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y))), smul_smul,
      ← map_natCast ((toInvOpen f ℚ a hq).app (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)).hom,
      ← map_mul, IsUnit.val_inv_mul, map_one, one_smul,
      pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)),
      app_map_apply]
  choose t ht using loc

  obtain ⟨T, hT⟩ := modules_exists_glue G (V := V) (fun y : S => V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)
    (fun _ => inf_le_left) (fun x _ => by obtain ⟨y, hy⟩ := hcov x; exact ⟨y, ‹_›, hy⟩) t
    (fun y z => by
      apply hinjV _ (inf_le_left.trans (inf_le_left.trans hV))
      rw [pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)),
        pullSectionOn_res _ _ inf_le_right (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_right)),
        ht, ht, res_res _ _ _ (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ⊓ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U z) ≤ V))),
        res_res _ _ _ (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ⊓ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U z) ≤ V)))])
  refine ⟨T, ?_⟩
  apply modules_eq_of_locally
  intro z hz
  obtain ⟨y, hy⟩ := hcov ((toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))).base z)
  refine ⟨toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) ⁻¹ᵁ
    (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y), (Opens.map _).monotone inf_le_left, ⟨hz, hy⟩, ?_⟩
  rw [← pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)), hT, ht]
end SpreadHomSections
end GroundTheory.Heights₂.Heights.Model
