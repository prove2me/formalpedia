-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_division_after_coordinates_2cab62082ae2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:44.787279+00:00
-- url     : https://prove2.me/submissions/93d407c6-2143-4a00-97ae-64478cda52fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep

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
    (hG : GeneralLinearCoordinates.Statement) {σ : Type} [Fintype σ] {m : ℕ} (hm : Fintype.card σ = m + 1)
    (w : σ → ℂ) (φ : holGerms w) (hφ : φ ≠ 0) :
    ∃ (π : (σ → ℂ) →L[ℂ] (Fin m → ℂ)) (T : (σ → ℂ) →L[ℂ] ℂ) (n : ℕ),
      ∀ ψ : holGerms w, ∃ (r : holGerms w) (a : Fin n → holGerms (π w)),
        ψ = r * φ + ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T (-T w) ^ (j : ℕ) := by
  classical
  let eo : Option (Fin m) ≃ σ := (finSuccEquiv m).symm.trans (Fintype.equivFinOfCardEq hm).symm
  let e : (σ → ℂ) ≃L[ℂ] (Option (Fin m) → ℂ) := (LinearEquiv.funCongrLeft ℂ ℂ eo).toContinuousLinearEquiv
  obtain ⟨f, hf, hfφ⟩ := φ.2
  let F0 : (Option (Fin m) → ℂ) → ℂ := fun y => f (e.symm y + w)
  have hF0 : AnalyticAt ℂ F0 0 :=
    hf.comp_of_eq ((e.symm.analyticAt 0).add analyticAt_const) (by simp)
  have he : Tendsto (fun z : σ → ℂ => e (z - w)) (𝓝 w) (𝓝 0) := by
    have := ((e : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ)).continuous.comp (continuous_sub_right w)).tendsto w
    rw [Function.comp_apply, sub_self, map_zero] at this
    exact this
  have hnz : ¬ ∀ᶠ y in 𝓝 (0 : Option (Fin m) → ℂ), F0 y = 0 := by
    intro h
    apply hφ
    apply Subtype.ext
    rw [← hfφ]
    exact Germ.coe_eq.2 ((he.eventually h).mono fun z hz => by simpa [F0] using hz)
  obtain ⟨A, n, hAn⟩ := hG (Fin m) F0 hF0 hnz
  let M : (σ → ℂ) ≃L[ℂ] (Option (Fin m) → ℂ) := e.trans A.symm
  let Pl : (Option (Fin m) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin m) => ℂ) (some i)
  let π : (σ → ℂ) →L[ℂ] (Fin m → ℂ) := Pl.comp (M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ))
  let T : (σ → ℂ) →L[ℂ] ℂ := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin m) => ℂ) none).comp
    (M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ))
  have hMt : Tendsto (fun z : σ → ℂ => M (z - w)) (𝓝 w) (𝓝 0) := by
    have := ((M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ)).continuous.comp (continuous_sub_right w)).tendsto w
    rw [Function.comp_apply, sub_self, map_zero] at this
    exact this
  have hinv : ∀ z, e.symm (A (M (z - w))) + w = z := fun z => by simp [M]
  have hsome : ∀ z, (fun i => M (z - w) (some i)) = π z - π w := fun z => by
    funext i; simp [π, Pl, map_sub]
  have hnone : ∀ z, M (z - w) none = T z + -T w := fun z => by simp [T, sub_eq_add_neg]
  refine ⟨π, T, n, fun ψ => ?_⟩
  obtain ⟨h, hh, hhψ⟩ := ψ.2
  let g : (Option (Fin m) → ℂ) → ℂ := fun y => F0 (A y)
  let H : (Option (Fin m) → ℂ) → ℂ := fun y => h (e.symm (A y) + w)
  have hg : AnalyticAt ℂ g 0 := hF0.comp_of_eq (A.analyticAt 0) (map_zero A)
  have hH : AnalyticAt ℂ H 0 :=
    hh.comp_of_eq (((e.symm.analyticAt _).comp (A.analyticAt 0)).add analyticAt_const) (by simp)
  obtain ⟨q, a, hq, ha, hev⟩ := hD (Fin m) n g H hg hH hAn
  have hev' : ∀ᶠ z in 𝓝 w, h z = q (M (z - w)) * f z +
      ∑ j : Fin n, a j (π z - π w) * (T z + -T w) ^ (j : ℕ) := by
    filter_upwards [hMt.eventually hev] with z hz
    simp only [H, g, F0, hinv, hsome, hnone] at hz
    exact hz
  let a' : Fin n → holGerms (π w) := fun j =>
    ⟨↑(fun u => a j (u - π w)), fun u => a j (u - π w),
      (ha j).comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self _), rfl⟩
  have hMa : AnalyticAt ℂ (fun z : σ → ℂ => M (z - w)) w :=
    (M.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  let r : holGerms w := ⟨↑(fun z => q (M (z - w))), fun z => q (M (z - w)),
    hq.comp_of_eq hMa (by simp), rfl⟩
  refine ⟨r, a', ?_⟩
  have hι : ∀ j, ((germPull π (π.analyticAt w) rfl (a' j) : holGerms w) : Germ (𝓝 w) ℂ) =
      ↑((fun u => a j (u - π w)) ∘ π) := fun j => germPull_coe _ _ rfl (a' j) _ rfl
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_mul, ← hfφ, ← hhψ]
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [Subring.coe_mul, Subring.coe_pow, hι]
  change (↑h : Germ (𝓝 w) ℂ) = Germ.coeRingHom _ (fun z => q (M (z - w))) * Germ.coeRingHom _ f +
    ∑ j : Fin n, Germ.coeRingHom _ ((fun u => a j (u - π w)) ∘ π) *
      Germ.coeRingHom _ (fun z : σ → ℂ => T z + -T w) ^ (j : ℕ)
  simp only [← map_mul, ← map_pow, ← map_sum, ← map_add]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hev'] with z hz
  simp [hz, Finset.sum_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
