-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.example55_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:27:38.216385+00:00
-- url     : https://prove2.me/submissions/e1ee3816-4332-4d0e-996f-b923df97c0d2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_character_orthogonality
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_irreducible_twirl
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_trivial_irrep_occurs
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A]
private lemma char_average (F : IrrepFamily G A) (a : A) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character (F.irrep a) g⁻¹ =
      if a = F.trivial then 1 else 0 := by
  have ht (g : G) : character (F.irrep F.trivial) g = 1 := by
    simp [character, F.trivial_action, Matrix.trace_one, F.trivial_dim]
  have h := character_orthogonality F F.trivial a
  simpa only [ht, one_mul, eq_comm] using h


set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.24, Example 55 Eq.(122), with explicit depolarizing action from Eq.(58). -/
theorem solution (D : Data G A n) :
    (∀ a : OccurringIrrep D, classCoefficients D (fun _ => 1) a = if a.val = D.F.trivial then 1 else 0) ∧
    spectralMap D (classCoefficients D (fun _ => 1)) = centralMap D.U D.F D.F.trivial ∧
    ∀ X : Mat n, spectralMap D (classCoefficients D (fun _ => 1)) X =
      (Matrix.trace X / n) • (1 : Mat n) := by
  classical
  have hc (a : OccurringIrrep D) : classCoefficients D (fun _ => 1) a =
      if a.val = D.F.trivial then 1 else 0 := by
    have h := char_average D.F a.val
    have he := Equiv.sum_comp (Equiv.inv G) (fun g : G => character (D.F.irrep a.val) g)
    change (∑ g, character (D.F.irrep a.val) g⁻¹) = _ at he
    rw [he] at h
    have hd : (D.F.dim a.val : ℂ) ≠ 0 := by exact_mod_cast (D.F.irrep a.val).positive.ne'
    simp only [classCoefficients, mul_one]
    split_ifs with ha
    · simpa [ha, D.F.trivial_dim, div_eq_mul_inv, mul_comm] using h
    · have hs : ∑ g : G, character (D.F.irrep a.val) g = 0 := by
        have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        simpa [ha, hg] using h
      simp [hs]
  have hm : spectralMap D (classCoefficients D (fun _ => 1)) = centralMap D.U D.F D.F.trivial := by
    let t : OccurringIrrep D := ⟨D.F.trivial,trivial_irrep_occurs D⟩
    have he (a : OccurringIrrep D) : a.val = D.F.trivial ↔ a = t := by
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp only [spectralMap, hc, he, ite_smul, one_smul, zero_smul]
    simp [t]
  refine ⟨hc,hm,?_⟩
  intro X
  rw [hm]
  have ht (g : G) : character (D.F.irrep D.F.trivial) g = 1 := by
    simp [character,D.F.trivial_action,Matrix.trace_one,D.F.trivial_dim]
  simpa [centralMap,D.F.trivial_dim,ht,one_div] using irreducible_twirl D.U X
