-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_bounded_frame_c1f354ee7137
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:02.790699+00:00
-- url     : https://prove2.me/submissions/96f567dd-7b54-4db6-997c-479f5dcf49d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_add_71b7a804ca0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_mul_42b9d2eba7a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_pow_mul_mem_of_le_6554d47dcac9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mem_of_forall_pow_mul_mem_0c53fdd73f20

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) :
    ∃ (f : Ω) (b : Module.Basis (Fin 2) Ω E) (N : ℕ), f ∈ chartRing ℤ x i ∧ f ≠ 0 ∧
      (∀ q, ∃ n : ℕ, f ^ n • b q ∈ B.lat i) ∧
      ∀ v ∈ B.lat i, ∀ q, f ^ N * b.repr v q ∈ chartRing ℤ x i := by
  classical
  obtain ⟨K, fs, cs, hf, hc, hsum, hb⟩ := B.frame i hi
  choose bs hli hsp hiff using hb
  obtain ⟨l₀, hl₀⟩ : ∃ l, fs l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hgen : ∀ l q, ∃ n : ℕ, fs l ^ n • bs l q ∈ B.lat i := by
    intro l q
    refine (hiff l (bs l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · rcases eq_or_ne q' q with rfl | h
      · simp
      · simp [h]
    · simp [Pi.single_apply]
  choose n hn using hgen
  let bB : Module.Basis (Fin 2) Ω E := Module.Basis.mk (hli l₀) (hsp l₀).ge
  have hbB : ⇑bB = bs l₀ := Module.Basis.coe_mk _ _
  have hcoord : ∀ p : Fin K × Fin 2 × Fin 2, ∃ m : ℕ,
      fs l₀ ^ m * bB.repr (fs p.1 ^ n p.1 p.2.1 • bs p.1 p.2.1) p.2.2 ∈ chartRing ℤ x i := by
    rintro ⟨l, q, q'⟩
    obtain ⟨a, ha, hv⟩ := (hiff l₀ _).1 ⟨0, by simpa using hn l q⟩
    have : bB.repr (fs l ^ n l q • bs l q) = a := by
      rw [hv, ← hbB]
      exact bB.repr_sum_self a
    rw [this]
    exact ha q'
  choose m hm using hcoord
  refine ⟨fs l₀, bB, Finset.univ.sup m, hf l₀, hl₀, fun q => ⟨n l₀ q, by rw [hbB]; exact hn l₀ q⟩, ?_⟩
  intro v hv q'
  refine mem_of_forall_pow_mul_mem _ fs cs hf hc hsum fun l => ?_
  obtain ⟨a, ha, hva⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
  have hterm : ∀ q, ∃ t : ℕ, fs l ^ t * (a q * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l q) q')) ∈
      chartRing ℤ x i := by
    intro q
    refine loc_mul (ha q) ⟨n l q, ?_⟩
    have h1 := pow_mul_mem_of_le (hf l₀) (Finset.le_sup (f := m) (Finset.mem_univ (l, q, q'))) (hm (l, q, q'))
    have h2 : fs l ^ n l q * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l q) q') =
        fs l₀ ^ Finset.univ.sup m * bB.repr (fs l ^ n l q • bs l q) q' := by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      ring
    rw [h2]
    exact h1
  have hsplit : fs l₀ ^ Finset.univ.sup m * bB.repr v q' =
      a 0 * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l 0) q') +
        a 1 * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l 1) q') := by
    rw [hva, Fin.sum_univ_two, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [hsplit]
  exact loc_add (hf l) (hterm 0) (hterm 1)
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
