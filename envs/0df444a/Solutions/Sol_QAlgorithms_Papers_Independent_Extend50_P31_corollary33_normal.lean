-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary33_normal
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:51:50.615213+00:00
-- url     : https://prove2.me/submissions/ad047ec4-32f8-4895-b69a-daab53257678

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QuantumFiniteSpectral_orthonormal_spectrum_calculus
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma29_choiBasis
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition30_simultaneous
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition20_eigenmatrices
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open scoped Matrix ComplexConjugate ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

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

/-- PDF p.15, Corollary 33: normality, not necessarily Hermiticity. -/
theorem solution (D : Data G A n) (a : OccurringIrrep D) :
    (choi (centralMap D.U D.F a.val))ᴴ * choi (centralMap D.U D.F a.val) =
      choi (centralMap D.U D.F a.val) * (choi (centralMap D.U D.F a.val))ᴴ := by
  have hp : Nonempty (Pivots D) := by
    choose p hp using (proposition20_eigenmatrices D).1
    exact ⟨⟨p,hp⟩⟩
  obtain ⟨P⟩ := hp
  exact (QuantumFiniteSpectral.orthonormal_spectrum_calculus _ _ _ (lemma29_choiBasis D P).1 (lemma29_choiBasis D P).2 ((proposition30_simultaneous D P).1 a)).1

