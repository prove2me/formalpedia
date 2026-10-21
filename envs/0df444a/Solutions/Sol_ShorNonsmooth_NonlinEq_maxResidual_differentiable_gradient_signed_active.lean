-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.maxResidual_differentiable_gradient_signed_active
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T12:24:19.52251+00:00
-- url     : https://prove2.me/submissions/e23e9be3-0c1d-4aa3-8102-bfcf1c11f991

import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ y ∈ V, maxResidual ψ y ≠ 0 →
      DifferentiableAt ℝ (maxResidual ψ) y →
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧
          gradient (maxResidual ψ) y = σ • gradient (ψ i) y ∧
          σ * ψ i y = maxResidual ψ y ∧ |ψ i y| = maxResidual ψ y := by
  classical
  rcases mem_nhds_iff.mp hU with ⟨O, hOU, hOopen, hxO⟩
  refine ⟨O, hOopen.mem_nhds hxO, ?_⟩
  intro y hyO hFne hFdiff
  have hyU : U ∈ nhds y := Filter.mem_of_superset (hOopen.mem_nhds hyO) hOU
  have hψdiff : ∀ i, DifferentiableAt ℝ (ψ i) y := fun i =>
    ((hψ i).contDiffAt hyU).differentiableAt_one
  have hne : Nonempty (Fin n) := by
    by_contra h
    haveI : IsEmpty (Fin n) := not_nonempty_iff.mp h
    apply hFne
    simp [maxResidual]
  haveI := hne
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
    (f := fun i => |ψ i y|)
  have hiF : |ψ i y| = maxResidual ψ y := hi
  have make : ∀ σ : ℝ, σ ^ 2 = 1 → σ * ψ i y = maxResidual ψ y →
      (∀ z, σ • ψ i z ≤ maxResidual ψ z) →
      ∃ i' : Fin n, ∃ σ' : ℝ, σ' ^ 2 = 1 ∧
        gradient (maxResidual ψ) y = σ' • gradient (ψ i') y ∧
        σ' * ψ i' y = maxResidual ψ y ∧ |ψ i' y| = maxResidual ψ y := by
    intro σ hσ2 hσy hσle
    let H := fun z => maxResidual ψ z - σ • ψ i z
    have hHnonneg : ∀ z, 0 ≤ H z := by
      intro z
      have := hσle z
      simpa [H, smul_eq_mul] using sub_nonneg.mpr this
    have hHy : H y = 0 := by
      simp [H, hσy, smul_eq_mul]
    have hmin : IsLocalMin H y :=
      Filter.Eventually.of_forall (fun z => by
        rw [hHy]
        exact hHnonneg z)
    have hzero : fderiv ℝ H y = 0 := hmin.fderiv_eq_zero
    have hderiv : fderiv ℝ H y =
        fderiv ℝ (maxResidual ψ) y - σ • fderiv ℝ (ψ i) y := by
      have hsub := fderiv_sub hFdiff ((hψdiff i).const_smul σ)
      have hsmul := fderiv_fun_const_smul (hψdiff i) σ
      have hpoint : (σ • ψ i) = (fun z => σ • ψ i z) := by
        funext z
        rfl
      calc
        fderiv ℝ H y = fderiv ℝ (maxResidual ψ - σ • ψ i) y := by rfl
        _ = fderiv ℝ (maxResidual ψ) y - fderiv ℝ (σ • ψ i) y := hsub
        _ = fderiv ℝ (maxResidual ψ) y -
              fderiv ℝ (fun z => σ • ψ i z) y := by rw [hpoint]
        _ = fderiv ℝ (maxResidual ψ) y - σ • fderiv ℝ (ψ i) y := by
          rw [hsmul]
    have hfderiv : fderiv ℝ (maxResidual ψ) y = σ • fderiv ℝ (ψ i) y := by
      rw [hderiv] at hzero
      exact sub_eq_zero.mp hzero
    have hgrad : gradient (maxResidual ψ) y = σ • gradient (ψ i) y := by
      have := congrArg (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm hfderiv
      simpa [gradient, map_smul] using this
    exact ⟨i, σ, hσ2, hgrad, hσy, hiF⟩
  by_cases hp : 0 ≤ ψ i y
  · let σ : ℝ := 1
    have hσ2 : σ ^ 2 = 1 := by norm_num [σ]
    have hσy : σ * ψ i y = maxResidual ψ y := by
      rw [show σ = 1 by rfl, one_mul, ← hiF, abs_of_nonneg hp]
    have hσle : ∀ z, σ • ψ i z ≤ maxResidual ψ z := by
      intro z
      simpa [σ] using (le_abs_self (ψ i z)).trans
        (by simpa [maxResidual] using (Finite.le_ciSup (fun j => |ψ j z|) i))
    simpa [σ] using make σ hσ2 hσy hσle
  · have hn : ψ i y < 0 := lt_of_not_ge hp
    let σ : ℝ := -1
    have hσ2 : σ ^ 2 = 1 := by norm_num [σ]
    have hσy : σ * ψ i y = maxResidual ψ y := by
      rw [show σ = -1 by rfl, neg_one_mul, ← hiF, abs_of_neg hn]
    have hσle : ∀ z, σ • ψ i z ≤ maxResidual ψ z := by
      intro z
      simpa [σ] using (neg_le_abs (ψ i z)).trans
        (by simpa [maxResidual] using (Finite.le_ciSup (fun j => |ψ j z|) i))
    simpa [σ] using make σ hσ2 hσy hσle
