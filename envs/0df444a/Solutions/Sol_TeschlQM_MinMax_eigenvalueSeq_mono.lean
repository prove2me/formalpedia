-- Prove2me | solution 1 for TeschlQM.MinMax.eigenvalueSeq_mono
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T12:24:58.83227+00:00
-- url     : https://prove2.me/submissions/78f783c1-75e3-4583-9c78-c20b0a597037

import Mathlib
import Definitions.Def_TeschlQM_MinMax_eigenvalueSeq
import Definitions.Def_TeschlQM_MinMax_minMaxSet
import Theorems.Thm_TeschlQM_MinMax_min_max

open scoped InnerProductSpace

open TeschlQM.MinMax

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdom : A.domain ≤ B.domain)
    (hAB : ∀ (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain),
      0 ≤ (⟪ψ, A ⟨ψ, hψA⟩ - B ⟨ψ, hψB⟩⟫_ℂ).re)
    (n : ℕ) (hn : 1 ≤ n) :
    eigenvalueSeq B n ≤ eigenvalueSeq A n := by
  rw [min_max A hA n hn, min_max B hB n hn]
  refine iSup_mono fun ψ => le_iInf₂ fun φ hφ => ?_
  set φ' : B.domain := ⟨φ, hdom φ.2⟩
  have hφ' : φ' ∈ minMaxSet B ψ := hφ
  have hle : (⟪(φ' : H), B φ'⟫_ℂ).re ≤ (⟪(φ : H), A φ⟫_ℂ).re := by
    have := hAB φ φ.2 (hdom φ.2)
    rw [inner_sub_right, Complex.sub_re] at this
    simpa [φ'] using this
  calc (⨅ χ ∈ minMaxSet B ψ, ((⟪(χ : H), B χ⟫_ℂ).re : EReal))
      ≤ ((⟪(φ' : H), B φ'⟫_ℂ).re : EReal) := iInf₂_le φ' hφ'
    _ ≤ ((⟪(φ : H), A φ⟫_ℂ).re : EReal) := EReal.coe_le_coe_iff.mpr hle
