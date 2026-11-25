-- Prove2me | solution 1 for PI.LocLatSat.UnitaryGroupMassFormula.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:36.568415+00:00
-- url     : https://prove2.me/submissions/2c8e2299-4d77-42a3-ba53-cde37863f8f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_baseChange_apply_baseChange
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_bcG_sub
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_bcG_smulR
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
namespace PI.LocLatSat.UnitaryGroupMassFormula
theorem _root_.solution (Λ : Submodule R (Fin n → K)) (f : (Fin n → K) →ₗ[K] K)
    (hI : IsFractional R⁰ (Λ.map (f.restrictScalars R)))
    {x : Fin n → S} (hx : x ∈ latG φ O Λ) (h0 : fP φ f x = 0) :
    x ∈ latG φ O (Λ ⊓ (LinearMap.ker f).restrictScalars R) := by
  set I : FractionalIdeal R⁰ K := ⟨Λ.map (f.restrictScalars R), hI⟩ with hIdef
  by_cases hI0 : I = 0
  ·
    have hv : ∀ v ∈ Λ, f v = 0 := by
      intro v hv
      have hmem : f v ∈ (I : Submodule R K) :=
        Submodule.mem_map_of_mem (f := f.restrictScalars R) hv
      rw [hI0, FractionalIdeal.coe_zero, Submodule.mem_bot] at hmem
      exact hmem
    have he : Λ ⊓ (LinearMap.ker f).restrictScalars R = Λ := by
      refine inf_eq_left.mpr (fun v hv' => ?_)
      simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker]
      exact hv v hv'
    rw [he]
    exact hx
  · have hmul : I * I⁻¹ = 1 := mul_inv_cancel₀ hI0
    have hmul' : I⁻¹ * I = 1 := by rw [mul_comm]; exact hmul
    set M := latG φ O (Λ ⊓ (LinearMap.ker f).restrictScalars R) with hMdef

    have claim : ∀ t ∈ (I : Submodule R K) * ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K),
        φ t • x ∈ M := by
      intro t ht
      refine Submodule.mul_induction_on (C := fun t => φ t • x ∈ M) ht ?_ ?_
      · intro a ha b hb
        obtain ⟨lam, hlam, hfl⟩ := Submodule.mem_map.mp ha
        have hab : a * b ∈ (1 : FractionalIdeal R⁰ K) := by
          rw [← hmul]
          exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp ha) (FractionalIdeal.mem_coe.mp hb)
        obtain ⟨r1, hr1⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hab
        have hgen : ∀ y ∈ latG φ O Λ, φ (a * b) • y - (fP φ f y * φ b) • bcG φ lam ∈ M := by
          intro y hy
          unfold latG at hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨v, hv, rfl⟩ := hy
            have hfv : f v ∈ (I : Submodule R K) :=
              Submodule.mem_map_of_mem (f := f.restrictScalars R) hv
            have hbf : b * f v ∈ (1 : FractionalIdeal R⁰ K) := by
              rw [← hmul']
              exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp hb) (FractionalIdeal.mem_coe.mp hfv)
            obtain ⟨r2, hr2⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hbf
            have hfl' : f lam = a := hfl
            have hwΛ : r1 • v - r2 • lam ∈ Λ := Λ.sub_mem (Λ.smul_mem r1 hv) (Λ.smul_mem r2 hlam)
            have hwk : f (r1 • v - r2 • lam) = 0 := by
              rw [map_sub, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, Algebra.smul_def,
                Algebra.smul_def, hr1, hr2, hfl']
              ring
            have hw : bcG φ (r1 • v - r2 • lam) = φ (a * b) • bcG φ v - (fP φ f (bcG φ v) * φ b) • bcG φ lam := by
              rw [bcG_sub, bcG_smulR, bcG_smulR, hr1, hr2, baseChange_apply_baseChange, map_mul, map_mul, mul_comm (φ b)]
            rw [← hw]
            apply Submodule.subset_span
            exact ⟨r1 • v - r2 • lam, ⟨hwΛ, hwk⟩, rfl⟩
          | zero => simpa using M.zero_mem
          | add y z _ _ hy hz =>
            have e : φ (a * b) • (y + z) - (fP φ f (y + z) * φ b) • bcG φ lam =
                (φ (a * b) • y - (fP φ f y * φ b) • bcG φ lam) +
                  (φ (a * b) • z - (fP φ f z * φ b) • bcG φ lam) := by
              rw [map_add, add_mul, add_smul, smul_add]
              abel
            rw [e]
            exact M.add_mem hy hz
          | smul o y _ hy =>
            have e : φ (a * b) • (o • y) - (fP φ f (o • y) * φ b) • bcG φ lam =
                o • (φ (a * b) • y - (fP φ f y * φ b) • bcG φ lam) := by
              rw [Subring.smul_def, Subring.smul_def, map_smul, smul_eq_mul, smul_sub, smul_smul, smul_smul,
                smul_smul]
              congr 2 <;> ring
            rw [e]
            exact M.smul_mem o hy
        have := hgen x hx
        rwa [h0, zero_mul, zero_smul, sub_zero] at this
      · intro t1 t2 h1 h2
        simp only [map_add, add_smul]
        exact M.add_mem h1 h2
    have h1 : (1 : K) ∈ (I : Submodule R K) * ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
      rw [← FractionalIdeal.coe_mul, hmul]
      exact FractionalIdeal.one_mem_one _
    have := claim 1 h1
    rwa [map_one, one_smul] at this
end PI.LocLatSat.UnitaryGroupMassFormula
