-- Prove2me | solution 1 for P2M_CrystallinePoints_Pd_resSurj_coreD__df1d08f12504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:55.849146+00:00
-- url     : https://prove2.me/submissions/e6a0fd0c-e122-4cf8-9f4d-103a04cda2fc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoincareDeRhamDuality_DeRhamPerfectPairing_ResSurjD
import Theorems.Thm_CrystallinePoints_Pd_surjective_of_sup_smulD
import Theorems.Thm_CrystallinePoints_Pd_finrank_res
import Theorems.Thm_CrystallinePoints_Pd_oneT_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct
open CrystallinePoints CrystallinePoints.Pd
namespace CrystallinePoints.Pd
namespace resSurj_coreD
theorem _root_.solution.{u} :
  ∀ (R : Type) [CommRing R] (H : Type 1) [AddCommGroup H] [Module R H] (M : Type u) [AddCommGroup M] [Module R M]
    (g : ℕ) (F N : Submodule R H), IsCompl F N → Module.Finite R H → Module.Projective R H →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk H p = 2 * g) → Module.Finite R F → Module.Projective R F →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk F p = g) → Module.Finite R M → Module.Projective R M →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) → ∀ γ : H →ₗ[R] M,
    (∀ m : Ideal R, m.IsMaximal → ∀ q : H, γ q ∈ m • (⊤ : Submodule R M) → q ∈ F ⊔ m • (⊤ : Submodule R H)) →
    Function.Surjective γ := by
  intro R _ H _ _ M _ _ g F N hc fH pH rH fF pF rF fM pM rM γ hγ
  refine surjective_of_sup_smulD γ fun m hm ↦ ?_
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let π : H →ₗ[R] N := Submodule.linearProjOfIsCompl N F hc.symm
  have hπ : ∀ n : N, π n = n := fun n ↦ Submodule.linearProjOfIsCompl_apply_left hc.symm n
  have hπF : ∀ x ∈ F, π x = 0 := fun x hx ↦ Submodule.linearProjOfIsCompl_apply_right' hc.symm hx
  haveI : Module.Finite R N := Module.Finite.of_surjective π fun n ↦ ⟨n, hπ n⟩
  have d1 := finrank_res m H
  have d2 := finrank_res m F
  have d3 := finrank_res m M
  rw [rH] at d1
  rw [rF] at d2
  rw [rM] at d3
  have d4 : Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N) = g := by
    have e : (R ⧸ m) ⊗[R] H ≃ₗ[R ⧸ m] ((R ⧸ m) ⊗[R] F) × ((R ⧸ m) ⊗[R] N) :=
      (LinearEquiv.baseChange R (R ⧸ m) _ _ (Submodule.prodEquivOfIsCompl F N hc).symm).trans
        (TensorProduct.prodRight R (R ⧸ m) (R ⧸ m) F N)
    have := e.finrank_eq
    rw [Module.finrank_prod, d1, d2] at this
    omega
  have su : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  let δ := (γ ∘ₗ N.subtype).baseChange (R ⧸ m)
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, rfl⟩ := TensorProduct.mk_surjective R N (R ⧸ m) su z
    have h1 : γ n ∈ m • (⊤ : Submodule R M) := (oneT_iff m _).1 hz
    obtain ⟨f, hf, w, hw, e⟩ := Submodule.mem_sup.1 (hγ m hm n h1)
    refine (oneT_iff m n).2 ?_
    have e2 : n = π w := by rw [← hπ n, ← e, map_add, hπF f hf, zero_add]
    rw [e2]
    have : π w ∈ Submodule.map π (m • ⊤) := Submodule.mem_map_of_mem hw
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hs : Function.Surjective δ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (d4.trans d3.symm)).1 hinj
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz⟩ := hs ((1 : R ⧸ m) ⊗ₜ y)
  obtain ⟨n, rfl⟩ := TensorProduct.mk_surjective R N (R ⧸ m) su z
  have h2 : y - γ n ∈ m • (⊤ : Submodule R M) := by
    refine (oneT_iff m _).1 ?_
    rw [TensorProduct.tmul_sub, ← hz]
    exact sub_self _
  exact Submodule.mem_sup.2 ⟨γ n, ⟨n, rfl⟩, _, h2, add_sub_cancel _ _⟩
end resSurj_coreD
end CrystallinePoints.Pd
