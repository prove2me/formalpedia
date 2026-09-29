-- Prove2me | solution 1 for WeierstrassCurve.veluQuotient_j_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a1e46da9-d905-525a-bca7-d43db67c6c2f

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Theorems.Thm_WeierstrassCurve_j_mem_of_a_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluQuotient_j_mem_of_mem

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ b₂ a₄ a₂ a₆ Δ j veluGx veluGy veluT veluU veluW veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ j_mem_of_a_mem"
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_j_mem_of_mem.WeierstrassCurve"

variable {L : Type*} [CommRing L] {S : Type*} [SetLike S L] [SubringClass S L]
variable (V : WeierstrassCurve L) (A : S)

private theorem _root_.WeierstrassCurve.veluGx_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₄ : V.a₄ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluGx x y ∈ A := by
  rw [veluGx]
  exact sub_mem (add_mem (add_mem (mul_mem (ofNat_mem A 3) (pow_mem hx 2))
    (mul_mem (mul_mem (ofNat_mem A 2) h₂) hx)) h₄) (mul_mem h₁ hy)

p2m_export "WeierstrassCurve" "veluGx_mem"

private theorem _root_.WeierstrassCurve.veluGy_mem (h₁ : V.a₁ ∈ A) (h₃ : V.a₃ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluGy x y ∈ A := by
  rw [veluGy]
  exact neg_mem (add_mem (add_mem (mul_mem (ofNat_mem A 2) hy) (mul_mem h₁ hx)) h₃)

p2m_export "WeierstrassCurve" "veluGy_mem"

private theorem _root_.WeierstrassCurve.veluT_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A) (h₄ : V.a₄ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluT x y ∈ A := by
  rw [veluT]
  exact sub_mem (mul_mem (ofNat_mem A 2) (V.veluGx_mem A h₁ h₂ h₄ hx hy))
    (mul_mem h₁ (V.veluGy_mem A h₁ h₃ hx hy))

p2m_export "WeierstrassCurve" "veluT_mem"

private theorem _root_.WeierstrassCurve.veluU_mem (h₁ : V.a₁ ∈ A) (h₃ : V.a₃ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluU x y ∈ A := by
  rw [veluU]
  exact pow_mem (V.veluGy_mem A h₁ h₃ hx hy) 2

p2m_export "WeierstrassCurve" "veluU_mem"

private theorem _root_.WeierstrassCurve.veluW_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A) (h₄ : V.a₄ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluW x y ∈ A := by
  rw [veluW]
  exact add_mem (V.veluU_mem A h₁ h₃ hx hy)
    (mul_mem hx (V.veluT_mem A h₁ h₂ h₃ h₄ hx hy))

p2m_export "WeierstrassCurve" "veluW_mem"

private theorem _root_.WeierstrassCurve.veluTSum_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A) (h₄ : V.a₄ ∈ A)
    {K : Finset (L × L)} (hK : ∀ P ∈ K, P.1 ∈ A ∧ P.2 ∈ A) :
    V.veluTSum K ∈ A := by
  rw [veluTSum]
  exact sum_mem fun P hP => V.veluT_mem A h₁ h₂ h₃ h₄ (hK P hP).1 (hK P hP).2

p2m_export "WeierstrassCurve" "veluTSum_mem"

private theorem _root_.WeierstrassCurve.veluWSum_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A) (h₄ : V.a₄ ∈ A)
    {K : Finset (L × L)} (hK : ∀ P ∈ K, P.1 ∈ A ∧ P.2 ∈ A) :
    V.veluWSum K ∈ A := by
  rw [veluWSum]
  exact sum_mem fun P hP => V.veluW_mem A h₁ h₂ h₃ h₄ (hK P hP).1 (hK P hP).2

p2m_export "WeierstrassCurve" "veluWSum_mem"
end WeierstrassCurve

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_veluQuotient_j_mem_of_mem.WeierstrassCurve in
theorem solution {F : Type*} [Field F] {S : Type*} [SetLike S F] [SubfieldClass S F]
    (W : WeierstrassCurve F) (K : S) (T : Finset (F × F))
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K)
    (hT : ∀ P ∈ T, P.1 ∈ K ∧ P.2 ∈ K) (hΔ : (W.veluQuotient T).Δ ≠ 0) :
    haveI : (W.veluQuotient T).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient T).j ∈ K := by
  haveI : (W.veluQuotient T).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have ht : W.veluTSum T ∈ K := W.veluTSum_mem K h₁ h₂ h₃ h₄ hT
  have hw : W.veluWSum T ∈ K := W.veluWSum_mem K h₁ h₂ h₃ h₄ hT
  have hb₂ : W.b₂ ∈ K := by
    rw [b₂]; exact add_mem (pow_mem h₁ 2) (mul_mem (ofNat_mem K 4) h₂)
  refine (W.veluQuotient T).j_mem_of_a_mem K ?_ ?_ ?_ ?_ ?_
  · rw [veluQuotient_a₁]; exact h₁
  · rw [veluQuotient_a₂]; exact h₂
  · rw [veluQuotient_a₃]; exact h₃
  · rw [veluQuotient_a₄]; exact sub_mem h₄ (mul_mem (ofNat_mem K 5) ht)
  · rw [veluQuotient_a₆]
    exact sub_mem (sub_mem h₆ (mul_mem hb₂ ht)) (mul_mem (ofNat_mem K 7) hw)

end S_WeierstrassCurve_veluQuotient_j_mem_of_mem
end P2MW
export P2MW.S_WeierstrassCurve_veluQuotient_j_mem_of_mem (solution)
