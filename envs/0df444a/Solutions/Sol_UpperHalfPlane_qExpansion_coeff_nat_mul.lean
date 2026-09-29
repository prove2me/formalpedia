-- Prove2me | solution 1 for UpperHalfPlane.qExpansion_coeff_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2540d4a5-8397-5303-af49-d9ded16c964a

import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_qExpansion_coeff_nat_mul

set_option autoImplicit false

noncomputable section

open Complex Filter Function UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass

open scoped Real MatrixGroups Topology Manifold

def W26FnLike : Type := ℍ → ℂ

scoped instance : FunLike W26FnLike ℍ ℂ where
  coe f := f
  coe_injective _ _ h := h

theorem solution {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ} (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h) (hhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) {M : ℕ} (hM : 0 < M) (n : ℕ) : (qExpansion (M * h) F).coeff n = if M ∣ n then (qExpansion h F).coeff (n / M) else 0 := by
  have hMh : 0 < (M : ℝ) * h := by positivity
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hper' : Periodic (F ∘ ofComplex) (((M : ℝ) * h : ℝ) : ℂ) := by
    simpa using hper.nat_mul M
  have han : AnalyticAt ℂ (cuspFunction (M * h) F) 0 :=
    analyticAt_cuspFunction_zero hMh hper' hhol hbdd

  set c : ℕ → ℂ := fun n ↦ if M ∣ n then (qExpansion h F).coeff (n / M) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) (F τ) := by
    intro τ
    have hq : Periodic.qParam h τ = Periodic.qParam (M * h) τ ^ M := by
      simp only [Periodic.qParam, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    have hs := hasSum_qExpansion hh hper hhol hbdd τ
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Injective (fun m : ℕ ↦ M * m) := mul_right_injective₀ hM.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ M * m),
        (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ M ∣ x := by
        rintro ⟨d, rfl⟩
        exact hx ⟨d, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ hM]

  have key := qExpansion_coeff_unique (F := W26FnLike) (show W26FnLike from F) hMh han hsum n
  exact key.symm

end

end S_UpperHalfPlane_qExpansion_coeff_nat_mul
end P2MW
export P2MW.S_UpperHalfPlane_qExpansion_coeff_nat_mul (solution)
