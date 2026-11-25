-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.FinCd2.of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:52.457739+00:00
-- url     : https://prove2.me/submissions/0f974dbe-c119-4e4e-9841-73249bc002ee

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_Transport
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_H0_comp_equiv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_H1_comp_equiv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_H2_comp_equiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
private theorem nonempty_Hn_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) (m : ℕ) :
    Nonempty (Hn (rho.comp (e : G →* G')) (m + 1) ≃ Hn rho (m + 1)) := by
  let φk : ∀ k : ℕ, ((Fin k → G') → M) ≃ₗ[R] ((Fin k → G) → M) := fun k =>
    LinearEquiv.funCongrLeft R M (Equiv.piCongrRight fun _ => e.toMulEquiv.toEquiv)
  have hC : ∀ k, (Cn rho k).map (φk k).toLinearMap = Cn (rho.comp (e : G →* G')) k := by
    intro k
    unfold Cn
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (show Continuous y from hy).comp
        (continuous_pi fun i => (map_continuous e).comp (continuous_apply i))
    · intro hf
      refine ⟨fun x => f (fun i => e.symm (x i)), (show Continuous f from hf).comp
        (continuous_pi fun i => (map_continuous e.symm).comp (continuous_apply i)), ?_⟩
      funext g
      show f (fun i => e.symm (e (g i))) = f g
      simp
  have hd : ∀ k, (φk (k + 1)).toLinearMap ∘ₗ dn rho k =
      dn (rho.comp (e : G →* G')) k ∘ₗ (φk k).toLinearMap := by
    intro k
    refine LinearMap.ext fun f => funext fun g => ?_
    show dn rho k f (fun i => e (g i)) =
      dn (rho.comp (e : G →* G')) k (fun x => f (fun i => e (x i))) g
    unfold dn
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.comp_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    funext i
    simp only [Fin.contractNth]
    split_ifs <;> simp [map_mul]
  have hZ : (Zn rho (m + 1)).map (φk (m + 1)).toLinearMap = Zn (rho.comp (e : G →* G')) (m + 1) := by
    unfold Zn
    ext f
    simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, ⟨hyC, hyK⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hC]
        exact ⟨y, hyC, rfl⟩
      · calc dn (rho.comp (e : G →* G')) (m + 1) (φk (m + 1) y)
            = φk (m + 1 + 1) (dn rho (m + 1) y) := (LinearMap.congr_fun (hd (m + 1)) y).symm
          _ = 0 := by rw [hyK, map_zero]
    · rintro ⟨hfC, hfK⟩
      refine ⟨(φk (m + 1)).symm f, ⟨?_, ?_⟩, (φk (m + 1)).apply_symm_apply f⟩
      · rw [← hC] at hfC
        obtain ⟨y, hy, hyf⟩ := hfC
        rw [← hyf]
        simpa using hy
      · apply (φk (m + 1 + 1)).injective
        rw [map_zero]
        calc φk (m + 1 + 1) (dn rho (m + 1) ((φk (m + 1)).symm f))
            = dn (rho.comp (e : G →* G')) (m + 1) (φk (m + 1) ((φk (m + 1)).symm f)) :=
              LinearMap.congr_fun (hd (m + 1)) _
          _ = 0 := by rw [LinearEquiv.apply_symm_apply]; exact hfK
  have hB : (Bn rho (m + 1)).map (φk (m + 1)).toLinearMap = Bn (rho.comp (e : G →* G')) (m + 1) := by
    show (Submodule.map (dn rho m) (Cn rho m)).map (φk (m + 1)).toLinearMap =
      Submodule.map (dn (rho.comp (e : G →* G')) m) (Cn (rho.comp (e : G →* G')) m)
    rw [← Submodule.map_comp, hd m, Submodule.map_comp, hC m]
  let fZ : Zn rho (m + 1) ≃ₗ[R] Zn (rho.comp (e : G →* G')) (m + 1) :=
    ((φk (m + 1)).submoduleMap (Zn rho (m + 1))).trans (LinearEquiv.ofEq _ _ hZ)
  unfold Hn
  refine ⟨(Submodule.Quotient.equiv _ _ fZ ?_).toEquiv.symm⟩
  ext w
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hB]
    exact ⟨z, hz, rfl⟩
  · intro hw
    rw [← hB] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    refine ⟨fZ.symm w, ?_, fZ.apply_symm_apply w⟩
    have h3 : ((fZ.symm w : Zn rho (m + 1)) : (Fin (m + 1) → G') → M) = y := by
      apply (φk (m + 1)).injective
      rw [show φk (m + 1) y = (w : (Fin (m + 1) → G) → M) from hyw]
      exact congrArg Subtype.val (fZ.apply_symm_apply w)
    rw [h3]
    exact hy
end ReciprocityTheory.Neutral.Bridge
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
namespace ReciprocityTheory.Neutral.Bridge
namespace FinCd2
theorem _root_.solution (e : G ≃ₜ* G') {rho : Representation R G' M} (h : FinCd2 (rho.comp (e : G →* G'))) :
    FinCd2 rho := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, fun n hn => ?_⟩
  · haveI := h0
    exact Nat.finite_of_card_ne_zero (by rw [← card_H0_comp_equiv e rho]; exact Nat.card_pos.ne')
  · haveI := h1
    exact Nat.finite_of_card_ne_zero (by rw [← card_H1_comp_equiv e rho]; exact Nat.card_pos.ne')
  · haveI := h2
    exact Nat.finite_of_card_ne_zero (by rw [← card_H2_comp_equiv e rho]; exact Nat.card_pos.ne')
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨f⟩ := nonempty_Hn_comp_equiv e rho m
    haveI := h3 (m + 1) hn
    exact f.symm.subsingleton
end FinCd2
end ReciprocityTheory.Neutral.Bridge
