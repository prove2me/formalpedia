-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isNoetherianRing_holGerms_option_226d87cbc67c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:55.906938+00:00
-- url     : https://prove2.me/submissions/133649f4-049d-414e-b63f-e9c382caf427

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) (σ : Type) [Fintype σ]
    (hR : IsNoetherianRing (holGerms (0 : σ → ℂ))) :
    IsNoetherianRing (holGerms (0 : Option σ → ℂ)) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact Submodule.fg_bot
  obtain ⟨φ, hφI, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := by
    intro h
    apply hφ0
    apply Subtype.ext
    rw [← hfφ]
    exact Germ.coe_eq.2 h
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz

  let Pl : (Option σ → ℂ) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) (some i)).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let Tl : (Option σ → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let ι : holGerms (0 : σ → ℂ) →+* holGerms (0 : Option σ → ℂ) := germPull Pl (Pl.analyticAt 0) (map_zero Pl)
  let τ : holGerms (0 : Option σ → ℂ) := ⟨↑(Tl : (Option σ → ℂ) → ℂ), Tl, Tl.analyticAt 0, rfl⟩
  let Φ : (Fin d → holGerms (0 : σ → ℂ)) → holGerms (0 : Option σ → ℂ) :=
    fun a => ∑ j : Fin d, ι (a j) * τ ^ (j : ℕ)
  have Φ_add : ∀ a b, Φ (a + b) = Φ a + Φ b := fun a b => by
    simp only [Φ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have Φ_smul : ∀ (r : holGerms (0 : σ → ℂ)) a, Φ (r • a) = ι r * Φ a := fun r a => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]
  have Φ_zero : Φ 0 = 0 := by simp [Φ]
  let N : Submodule (holGerms (0 : σ → ℂ)) (Fin d → holGerms (0 : σ → ℂ)) :=
    { carrier := {a | Φ a ∈ I}
      add_mem' := fun {a b} ha hb => by
        change Φ (a + b) ∈ I
        rw [Φ_add]; exact I.add_mem ha hb
      zero_mem' := by
        change Φ 0 ∈ I
        rw [Φ_zero]; exact I.zero_mem
      smul_mem' := fun r a ha => by
        change Φ (r • a) ∈ I
        rw [Φ_smul]; exact Ideal.mul_mem_left I _ ha }
  obtain ⟨s, hs⟩ : N.FG := IsNoetherian.noetherian N
  refine ⟨insert φ (s.image Φ), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro ψ hψ
    rw [Finset.coe_insert, Set.mem_insert_iff] at hψ
    rcases hψ with rfl | hψ
    · exact hφI
    · rw [Finset.coe_image] at hψ
      obtain ⟨a, ha, rfl⟩ := hψ
      have : a ∈ N := hs ▸ Submodule.subset_span ha
      exact this
  · intro ψ hψ
    obtain ⟨g, hg, hgψ⟩ := ψ.2
    have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)
    have hgA : AnalyticAt ℂ (g ∘ A) 0 := hg.comp_of_eq (A.analyticAt 0) (map_zero A)
    obtain ⟨q, a, hq, ha, hev⟩ := hD σ d (f ∘ A) (g ∘ A) hfA hgA hAd
    have hqB : AnalyticAt ℂ (q ∘ A.symm) 0 := hq.comp_of_eq (A.symm.analyticAt 0) (map_zero _)
    let Q : holGerms (0 : Option σ → ℂ) := ⟨↑(q ∘ A.symm), q ∘ A.symm, hqB, rfl⟩
    let a' : Fin d → holGerms (0 : σ → ℂ) := fun j => ⟨↑(a j), a j, ha j, rfl⟩
    have hev' : ∀ᶠ y in 𝓝 (0 : Option σ → ℂ),
        g y = q (A.symm y) * f y + ∑ j : Fin d, a j (Pl y) * Tl y ^ (j : ℕ) := by
      have hB : Tendsto A.symm (𝓝 0) (𝓝 0) := by
        simpa using A.symm.continuous.tendsto (0 : Option σ → ℂ)
      filter_upwards [hB.eventually hev] with y hy
      simpa [Pl, Tl] using hy
    have key : ψ = Q * φ + Φ a' := by
      apply Subtype.ext
      have hι : ∀ j, ((ι (a' j) : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
          ↑(a j ∘ Pl) := fun j => germPull_coe _ _ _ (a' j) (a j) rfl
      simp only [Φ, Subring.coe_add, Subring.coe_mul, ← hfφ, ← hgψ]
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [Subring.coe_mul, Subring.coe_pow, hι]
      change (↑g : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = Germ.coeRingHom _ (q ∘ A.symm) * Germ.coeRingHom _ f +
        ∑ j : Fin d, Germ.coeRingHom _ (a j ∘ Pl) * Germ.coeRingHom _ (Tl : (Option σ → ℂ) → ℂ) ^ (j : ℕ)
      simp only [← map_mul, ← map_pow, ← map_sum, ← map_add]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev'] with y hy
      simp [hy, Finset.sum_apply]
    have hΦ : Φ a' ∈ I := by
      have : Φ a' = ψ - Q * φ := by rw [key]; ring
      rw [this]; exact I.sub_mem hψ (Ideal.mul_mem_left I _ hφI)
    have ha'N : a' ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))) := by
      rw [hs]; exact hΦ
    have hgen : ∀ x ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))),
        Φ x ∈ Ideal.span (↑(insert φ (s.image Φ)) : Set (holGerms (0 : Option σ → ℂ))) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Ideal.subset_span (by
          rw [Finset.coe_insert, Finset.coe_image]
          exact Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
      | zero => rw [Φ_zero]; exact Ideal.zero_mem _
      | add x y _ _ hx hy => rw [Φ_add]; exact Ideal.add_mem _ hx hy
      | smul r x _ hx => rw [Φ_smul]; exact Ideal.mul_mem_left _ _ hx
    have hspan := hgen a' ha'N
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) hspan
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
