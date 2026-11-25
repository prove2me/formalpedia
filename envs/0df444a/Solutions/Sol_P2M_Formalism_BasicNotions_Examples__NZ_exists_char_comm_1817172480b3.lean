-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_char_comm_1817172480b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:26.514865+00:00
-- url     : https://prove2.me/submissions/3ef171ca-b0ed-4ceb-bb5a-e0f32a0e1af2

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)
variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (Z : Type) [CommRing Z] [Algebra ℂ Z] [FiniteDimensional ℂ Z] (e : Z)
    (hi : e * e = e) (h0 : e ≠ 0) : ∃ ω : Z →ₐ[ℂ] ℂ, ω e = 1 := by
  have hne : Ideal.span {1 - e} ≠ ⊤ := by
    intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp h)
    apply h0
    calc e = (c * (1 - e)) * e := by rw [hc, one_mul]
      _ = c * (e - e * e) := by ring
      _ = 0 := by rw [hi, sub_self, mul_zero]
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ : Field (Z ⧸ m) := Ideal.Quotient.field m
  have : FiniteDimensional ℂ (Z ⧸ m) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℂ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := Z ⧸ m)
  let φ : ℂ ≃ₐ[ℂ] (Z ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (Z ⧸ m)) hb
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), ?_⟩
  have h1 : Ideal.Quotient.mkₐ ℂ m e = 1 := by
    have : Ideal.Quotient.mk m (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  show φ.symm (Ideal.Quotient.mkₐ ℂ m e) = 1
  rw [h1, map_one]
end Formalism.BasicNotions.Examples₂.NZ
